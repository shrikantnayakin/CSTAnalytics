#!/usr/bin/env python3
"""
CST Analytics - local server (no extra packages needed, Python 3.8+).

Run:   python server.py
Open:  http://localhost:8000

What it does:
  * Serves the login page / dashboard (index.html) to YOUR browser only (127.0.0.1).
  * Logs in to Salesforce with username + password + security token (SOAP login over HTTPS).
  * Keeps only the resulting Salesforce session id in memory (never your password).
  * Fetches your Case records through the Salesforce REST API and hands them to the dashboard.
"""
import gzip
import base64
import hashlib
import hmac
import html
import http.client
import threading
import json
import os
import re
import secrets
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from concurrent.futures import Future, ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from xml.etree import ElementTree as ET
from xml.sax.saxutils import escape

BACKGROUND = "--background" in sys.argv   # started hidden (pythonw / at Windows start-up): no browser window, messages go to server.log
SHARE = "--share" in sys.argv      # python server.py --share  -> other people on your network can open it (default: this PC only)
_nums = [a for a in sys.argv[1:] if a.isdigit()]
PORT = int(_nums[0]) if _nums else 8000
API = "59.0"
# Business rule: a case is "Resolved" when the agent fixes it. If the customer does not respond within
# AUTO_CLOSE_DAYS the status moves to "Closed" automatically. So a Closed case is ALSO a resolved case.
RESOLVED_STATUSES = ["Resolved"]   # non-closed statuses that mean "resolved" (edit to match your org's picklist)
AUTO_CLOSE_DAYS = 3
RESPONSE_DELAY_DAYS = 1        # Case analysis: report every wait for an outbound e-mail that lasted more than this many CALENDAR days
HOLD_DAYS_MIN = 5            # Case audit: a case held on OUR side this many days (or more) gets the "agent active but no response" check
HOLD_DAY_MIN_HOURS = 3       # ...a calendar day counts as "held by us" when the case was on our side for at least this many hours of it
DEFAULT_PAUSED = "Pending, Waiting on Third Party"   # statuses where the ball is NOT on our side (same default as the SLA tab)
EXCLUDED_STATUSES = ["Cancelled", "Canceled", "Merged"]   # never loaded, so they appear in no tab, chart, filter or export
# Case audit: an outbound e-mail containing one of these phrases is only a holding / acknowledgement message, so it is NOT a response.
# A day on which nothing but such e-mails went out counts as a day with no outbound e-mail. Add more phrases here as needed (case and spacing are ignored).
HOLDING_PHRASES = [
    "We regret for the inconvenience caused",
    "Our team is currently reviewing the details of your case to determine the best course of action",
]
ACK_PHRASES = [      # Audit Fail: standard acknowledgement replies (checked on the newest message of an outbound e-mail)
    "Ginesys Care Team is working on your reported issue",
    "We regret for the inconvenience caused",
    "Thank you for bringing this to our attention. Our team is currently reviewing the details",
]
AUDIT_GROUP = "ERP Helpdesk-L1"   # Audit Details report is always limited to this case group
MAX_ROWS = 200000               # safety cap only; normally every matching case is returned
HERE = Path(__file__).resolve().parent
SESSION_TTL = 2 * 3600           # forget local sessions after 2 hours
SESSIONS = {}                    # cookie token -> {sid, instance, name, email, username, created}
DATA_DIR = HERE / "local_data"             # downloaded case data + settings live here, next to this app
PREFS_FILE = DATA_DIR / "prefs.json"
BUILD = "2026-11-06-audit-ackrepeat-v16"      # shown by /api/version and in the page, to tell which server.py is really running
VENDOR_LIBS = {"chart.umd.min.js": "https://cdn.jsdelivr.net/npm/chart.js@4.4.1/dist/chart.umd.min.js",
               "pptxgen.bundle.js": "https://cdn.jsdelivr.net/npm/pptxgenjs@3.12.0/dist/pptxgen.bundle.js"}
ACCESS_FILE = HERE / "access_control.json"   # who may log in through the network, and which reports each role sees (edited in the app: Access)
SAVED_FILE = HERE / "saved_login.json"   # "Remember me" credentials (plain text, owner-only permissions)

# Credentials are only ever sent to genuine Salesforce hosts.
ALLOWED_HOST = re.compile(
    r"^[a-z0-9-]+(\.[a-z0-9-]+)*\.(salesforce\.com|force\.com|cloudforce\.com|salesforce\.mil)$", re.I
)


# ---------------------------------------------------------------- access control (users + roles)
PERMANENT_ADMINS = [("Shrikant N", "shrikant.n@ginesys.in")]      # always present, role "Admin" (every report + may change the access settings); cannot be removed in the app
ADMIN_ROLE = "Admin"
ACCESS_TABS_OK = re.compile(r"^[A-Za-z0-9_*-]{1,40}$")


def clean_access(d):
    """Validate / normalise the access settings. Roles: name -> list of report ids ('*' = every report)."""
    d = d if isinstance(d, dict) else {}
    roles = {}
    for name, tabs in (d.get("roles") or {}).items() if isinstance(d.get("roles"), dict) else []:
        name = str(name).strip()[:60]
        if name and isinstance(tabs, list):
            roles[name] = sorted({str(t) for t in tabs if ACCESS_TABS_OK.match(str(t))})
    roles[ADMIN_ROLE] = ["*", "admin", "download"]      # "download" = may use the Master filter to download data from Salesforce
    users, seen = [], set()
    for u in (d.get("users") or []) if isinstance(d.get("users"), list) else []:
        if not isinstance(u, dict):
            continue
        email, name, role = str(u.get("email", "")).strip().lower()[:120], str(u.get("name", "")).strip()[:80], str(u.get("role", "")).strip()[:60]
        if "@" not in email or email in seen:
            continue
        seen.add(email)
        users.append({"name": name, "email": email, "role": role if role in roles else "", "blocked": bool(u.get("blocked"))})
    for nm, em in PERMANENT_ADMINS:
        hit = next((u for u in users if u["email"] == em), None)
        if hit:
            hit["role"], hit["blocked"] = ADMIN_ROLE, False
        else:
            users.insert(0, {"name": nm, "email": em, "role": ADMIN_ROLE, "blocked": False})
    return {"enabled": bool(d.get("enabled")), "roles": dict(list(roles.items())[:50]), "users": users[:500]}


def load_access():
    try:
        return clean_access(json.loads(ACCESS_FILE.read_text("utf-8")))
    except Exception:
        return clean_access({})


def access_for(sess, owner):
    """-> {'role', 'tabs', 'admin', 'dl'} for a signed-in user, or None when this person is not allowed in.
    tabs = report ids the role may open ('*' = all). dl = may download data from Salesforce (Master filter).
    A user who is on the list gets the rights of his role - also when he sits at the server PC itself.
    With access control off everybody has everything; the server PC with a login that is not on the list also has everything (so it can never be locked out).
    Only users whose role is "Admin" may open / change the access settings."""
    cfg = load_access()
    ids = {str(sess.get("email") or "").strip().lower(), str(sess.get("username") or "").strip().lower()} - {""}
    u = next((x for x in cfg["users"] if x["email"] in ids), None)
    if u and u.get("blocked"):
        return None
    admin = bool(u and u.get("role") == ADMIN_ROLE)
    if not cfg["enabled"]:
        return {"role": (u or {}).get("role", ""), "tabs": ["*"], "admin": admin, "dl": True, "master": True}
    if not u:
        return {"role": "Owner", "tabs": ["*"], "admin": False, "dl": True, "master": False} if owner else None
    tabs = cfg["roles"].get(u["role"], [])
    return {"role": u["role"], "tabs": tabs, "admin": admin, "dl": "download" in tabs, "master": admin}      # Master filter is shown to the Admin role only (to everybody while access control is off)


# ---------------------------------------------------------------- local data store (app folder)
def store_path(key):
    safe = re.sub(r"[^A-Za-z0-9_.@-]", "_", str(key or ""))[:150].lstrip(".")
    if not safe:
        raise ApiError(400, "Invalid key.")
    return DATA_DIR / (safe + ".json")


def atomic_write(path, data):
    DATA_DIR.mkdir(exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_bytes(data)
    tmp.replace(path)


def load_prefs():
    try:
        d = json.loads(PREFS_FILE.read_text("utf-8"))
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


# ---------------------------------------------------------------- saved login
KEY_FILE = HERE / "saved_login.key"


def _xor_stream(key, nonce, data):
    out = bytearray()
    counter = 0
    while len(out) < len(data):
        out += hmac.new(key, nonce + counter.to_bytes(8, "big"), hashlib.sha256).digest()
        counter += 1
    return bytes(a ^ b for a, b in zip(data, out))


def _dpapi(data, decrypt):
    """Windows DPAPI: encrypted to the current Windows user account. Returns bytes or None."""
    if os.name != "nt":
        return None
    try:
        import ctypes
        from ctypes import wintypes

        class BLOB(ctypes.Structure):
            _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]

        buf = ctypes.create_string_buffer(data, len(data))
        inb = BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
        outb = BLOB()
        fn = ctypes.windll.crypt32.CryptUnprotectData if decrypt else ctypes.windll.crypt32.CryptProtectData
        if not fn(ctypes.byref(inb), None, None, None, None, 0, ctypes.byref(outb)):
            return None
        try:
            return ctypes.string_at(outb.pbData, outb.cbData)
        finally:
            ctypes.windll.kernel32.LocalFree(outb.pbData)
    except Exception:
        return None


def _file_key():
    try:
        k = KEY_FILE.read_bytes()
        if len(k) == 32:
            return k
    except FileNotFoundError:
        pass
    k = os.urandom(32)
    fd = os.open(str(KEY_FILE), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "wb") as f:
        f.write(k)
    return k


def _encrypt(d):
    raw = json.dumps(d).encode("utf-8")
    blob = _dpapi(raw, False)
    if blob is not None:
        return {"v": 2, "mode": "dpapi", "data": base64.b64encode(blob).decode()}
    key = _file_key()
    nonce = os.urandom(16)
    ct = _xor_stream(key, nonce, raw)
    mac = hmac.new(key, nonce + ct, hashlib.sha256).digest()
    return {"v": 2, "mode": "key", "data": base64.b64encode(nonce + ct + mac).decode()}


def _decrypt(env):
    blob = base64.b64decode(env["data"])
    if env.get("mode") == "dpapi":
        raw = _dpapi(blob, True)
    else:
        key = KEY_FILE.read_bytes()
        nonce, ct, mac = blob[:16], blob[16:-32], blob[-32:]
        if not hmac.compare_digest(mac, hmac.new(key, nonce + ct, hashlib.sha256).digest()):
            return None
        raw = _xor_stream(key, nonce, ct)
    return json.loads(raw.decode("utf-8")) if raw else None


def load_saved():
    try:
        d = json.loads(SAVED_FILE.read_text("utf-8"))
        if not isinstance(d, dict):
            return None
        if d.get("v") == 2 and "data" in d:
            d = _decrypt(d)
        elif d.get("username"):
            try:
                write_saved(d)          # migrate old plain-text file to encrypted
            except Exception:
                pass
        return d if isinstance(d, dict) and d.get("username") else None
    except Exception:
        return None


def write_saved(d):
    tmp = SAVED_FILE.with_suffix(".tmp")
    fd = os.open(str(tmp), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)   # owner read/write only
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(_encrypt(d), f)
    tmp.replace(SAVED_FILE)


def clear_saved():
    for f in (SAVED_FILE, KEY_FILE):
        try:
            f.unlink()
        except FileNotFoundError:
            pass


# ---------------------------------------------------------------- extra Case fields
# Labels as shown in the dashboard. Each one is looked up by its Salesforce field LABEL on Case
# (then on the related Account). To force a field, add it to field_map.json next to this file, e.g.
#   {"BA Code": "Account.BA_Code__c", "Requester": "Requester__r.Name"}
EXTRA_LABELS = [
    "Account Manager (Ref.)", "BA Code", "Requester", "Application", "Application Module",
    "Helpdesk Focus Area", "Helpdesk Focus Area - Module", "Helpdesk Focus Area - SubModule",
    "Type - Module", "Type - SubModule",
]
FIELD_MAP_FILE = HERE / "field_map.json"


def _norm(t):
    return re.sub(r"[^a-z0-9]", "", (t or "").lower())


def _label_keys(label):
    n = _norm(label)
    return [n] + ([n.replace("ref", "")] if "ref" in n else [])


def _describe(sess, sobject):
    cache = sess.setdefault("_desc", {})
    if sobject not in cache:
        d = sf_get(sess, f"/services/data/v{API}/sobjects/{sobject}/describe")
        cache[sobject] = d.get("fields", [])
    return cache[sobject]


NUMBER_NAMED = {"Case": "CaseNumber", "Contract": "ContractNumber", "Order": "OrderNumber",
                "WorkOrder": "WorkOrderNumber", "Solution": "SolutionName"}


def _ref_name_field(f):
    """Name-like field of the record a lookup points to (Case has no Name, it has CaseNumber, etc.)."""
    refs = f.get("referenceTo") or []
    return NUMBER_NAMED.get(refs[0], "Name") if len(refs) == 1 else "Name"


def _select_path(prefix, f):
    """Reference (lookup) fields show the related record's Name; everything else the value itself."""
    if f.get("type") == "reference" and f.get("relationshipName"):
        return f"{prefix}{f['relationshipName']}.{_ref_name_field(f)}"
    return f"{prefix}{f['name']}"


def resolve_extra_fields(sess):
    """-> list of {label, path or None}. Never raises: a field that can't be found is just reported as missing."""
    if "_extra" in sess:
        return sess["_extra"]
    overrides = {}
    try:
        overrides = json.loads(FIELD_MAP_FILE.read_text("utf-8"))
    except Exception:
        pass
    case_f = acct_f = None
    try:
        case_f = _describe(sess, "Case")
    except ApiError:
        case_f = []
    try:
        acct_f = _describe(sess, "Account")
    except ApiError:
        acct_f = []
    idx = lambda fields: {k: f for f in fields for k in _label_keys(f.get("label")) if k}
    ci, ai = idx(case_f), idx(acct_f)
    out = []
    for label in EXTRA_LABELS:
        path = overrides.get(label)
        ftype = None
        if not path:
            f = next((ci[k] for k in _label_keys(label) if k in ci), None)
            if f:
                path, ftype = _select_path("", f), f.get("type")
            else:
                f = next((ai[k] for k in _label_keys(label) if k in ai), None)
                if f:
                    path, ftype = _select_path("Account.", f), f.get("type")
        out.append({"label": label, "path": path, "type": ftype})
    sess["_extra"] = out
    return out


_TAG_RE = re.compile(r"<[^>]*>")


def plain(v):
    """Formula fields such as HYPERLINK() come back as '<a href=...>Name</a>'; keep only the visible text."""
    if isinstance(v, str) and "<" in v and ">" in v:
        return html.unescape(_TAG_RE.sub("", v)).strip()
    return v


def rich_text(v):
    """Chatter post bodies are rich text (HTML): keep their paragraphs, line breaks and bullet lists, as Salesforce shows them."""
    if not isinstance(v, str) or "<" not in v:
        return v
    t = re.sub(r"(?i)<\s*br\s*/?\s*>", "\n", v)
    t = re.sub(r"(?i)<\s*li[^>]*>", "\n• ", t)
    t = re.sub(r"(?i)</\s*(p|div|ul|ol|h[1-6]|li|blockquote)\s*>", "\n", t)
    t = html.unescape(_TAG_RE.sub("", t))
    t = re.sub(r"[ \t\u00a0]+\n", "\n", t)
    return re.sub(r"\n{3,}", "\n\n", t).strip()


def _dig(rec, path):
    for part in path.split("."):
        rec = (rec or {}).get(part) if isinstance(rec, dict) else None
        if rec is None:
            return None
    return rec

# ---------------------------------------------------------------- Group / all-field resolution
GROUP_LABELS = ["group", "supportgroup", "assignmentgroup", "casegroup", "assignedgroup", "ownergroup",
                "supportteam", "team", "queue"]
CORE_FIELDS = {"Id", "CaseNumber", "Subject", "Status", "Priority", "Origin", "Type", "Reason", "IsClosed",
               "IsEscalated", "CreatedDate", "ClosedDate", "AccountId", "OwnerId"}
SKIP_TYPES = {"base64", "address", "location", "anyType", "complexvalue"}
SAFE_REFS = {"User", "Group", "Account", "Contact", "RecordType", "Asset", "Product2", "Entitlement",
             "ServiceContract", "BusinessHours", "SlaProcess", "Case", "Individual"}
FIELD_NAME_RE = re.compile(r"^[A-Za-z0-9_]+$")


def _overrides():
    try:
        return json.loads(FIELD_MAP_FILE.read_text("utf-8"))
    except Exception:
        return {}


FIRST_GROUP_LABELS = ["firstassignedgroup", "firstgroup", "initialgroup", "originalgroup", "initialassignedgroup",
                      "originalassignedgroup", "firstassignedqueue", "firstassignedteam", "firstassigned"]


def resolve_first_group(sess):
    """Case field holding the FIRST assigned group (override: field_map.json {"First Assigned Group": "Field__c"})."""
    return _resolve_group_field(sess, "_fgroup", "First Assigned Group", FIRST_GROUP_LABELS)


def resolve_group(sess):
    """Find the Case field that holds the support Group (override: field_map.json {"Group": "Field__c"})."""
    return _resolve_group_field(sess, "_group", "Group", GROUP_LABELS)


AGENT_LABELS = ["agent", "assignedagent", "caseagent", "supportagent", "agentname", "assignedto", "assignee"]


def resolve_agent(sess):
    """Case field labelled 'Agent' (override: field_map.json {"Agent": "Field__c"}). When the org has none,
    the dashboard falls back to the case owner."""
    return _resolve_group_field(sess, "_agent", "Agent", AGENT_LABELS)


def _resolve_group_field(sess, cache_key, override_key, labels):
    if cache_key in sess:
        return sess[cache_key]
    path, label = _overrides().get(override_key), None
    if path:
        label = path
    else:
        try:
            fields = _describe(sess, "Case")
        except ApiError:
            fields = []
        by_label = {}
        for f in fields:
            if f["name"] == "OwnerId" or f.get("type") in SKIP_TYPES:
                continue
            by_label.setdefault(_norm(f.get("label")), f)
        for g in labels:
            if g in by_label:
                f = by_label[g]
                path, label = _select_path("", f), f.get("label")
                break
    sess[cache_key] = {"path": path, "label": label}
    return sess[cache_key]


def queue_membership(sess):
    """user Id -> sorted list of queue names the user belongs to (used only when no Group field exists)."""
    c = sess.get("_qm")
    if c and time.time() - c[0] < 600:
        return c[1]
    m = {}
    try:
        res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(
            "SELECT UserOrGroupId, Group.Name FROM GroupMember WHERE Group.Type = 'Queue'"))
        while True:
            for r in res.get("records", []):
                uid = r.get("UserOrGroupId") or ""
                if uid.startswith("005"):
                    m.setdefault(uid, set()).add((r.get("Group") or {}).get("Name") or "")
            if res.get("done") or not res.get("nextRecordsUrl"):
                break
            res = sf_get(sess, res["nextRecordsUrl"])
    except ApiError:
        pass
    m = {k: sorted(x for x in v if x) for k, v in m.items()}
    sess["_qm"] = (time.time(), m)
    return m


def case_field_defs(sess, used):
    """Every readable Case field (except those already shown as dedicated columns)."""
    try:
        fields = _describe(sess, "Case")
    except ApiError:
        return []
    out = []
    for f in fields:
        t = f.get("type")
        if t in SKIP_TYPES or f["name"] in CORE_FIELDS or f["name"] in used or _select_path("", f) in used:
            continue
        rel = None
        if t == "reference" and f.get("relationshipName"):
            refs = f.get("referenceTo") or []
            if refs and all(r in SAFE_REFS or r.endswith("__c") for r in refs):
                rel = f"{f['relationshipName']}.{_ref_name_field(f)}"
        out.append({"key": "F:" + f["name"], "label": f.get("label") or f["name"], "type": t,
                    "name": f["name"], "rel": rel})
    return out


# ---------------------------------------------------------------- survey / feedback custom object
SURVEY_RE = re.compile(r"feedback|survey|csat|nps|rating", re.I)
SURVEY_SKIP = {"Id", "Name", "OwnerId", "IsDeleted", "CreatedById", "LastModifiedById", "SystemModstamp", "CreatedDate",
               "LastModifiedDate", "LastViewedDate", "LastReferencedDate", "CurrencyIsoCode", "RecordTypeId"}
SURVEY_VALUE_TYPES = {"picklist", "string", "textarea", "double", "int", "percent", "boolean", "currency", "long"}


def _case_link(fields):
    return next((f for f in fields if f.get("type") == "reference" and "Case" in (f.get("referenceTo") or [])), None)


def find_survey_objects(sess):
    """Custom objects (e.g. Feedback__c) that look like surveys and have a lookup to Case, with their fields."""
    if "_survey" in sess:
        return sess["_survey"]
    try:
        g = sf_get(sess, f"/services/data/v{API}/sobjects")
    except ApiError as e:
        if e.status == 401:
            raise
        return []
    out = []
    for o in g.get("sobjects", []):
        if not (o.get("custom") and o.get("queryable")) or not SURVEY_RE.search(o["name"] + " " + (o.get("label") or "")):
            continue
        try:
            flds = _describe(sess, o["name"])
        except ApiError as e:
            if e.status == 401:
                raise
            continue
        link = _case_link(flds)
        if not link:
            continue
        fl = []
        for f in flds:
            if f["name"] in SURVEY_SKIP or f["name"] == link["name"] or f.get("type") not in SURVEY_VALUE_TYPES:
                continue
            fl.append({"name": f["name"], "label": f.get("label") or f["name"], "type": f["type"],
                       "values": [v["value"] for v in f.get("picklistValues", []) if v.get("active")][:30]})
        out.append({"name": o["name"], "label": o.get("label") or o["name"], "caseField": link["name"], "fields": fl})
    sess["_survey"] = out[:8]
    return sess["_survey"]


def diag_case(sess, number):
    """Why is a case (or its survey record) missing from the CSAT report? Walks the same steps the report takes."""
    number = re.sub(r"[^0-9A-Za-z]", "", str(number or ""))[:20]
    if not number:
        raise ApiError(400, "Give a case number, e.g. /api/diagcase?number=00168568")
    out = {"caseNumber": number, "steps": []}
    st = out["steps"]
    q = lambda soql: sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql)).get("records", [])
    cs = q(f"SELECT Id, CaseNumber, Status, IsClosed, CreatedDate, ClosedDate, LastModifiedDate, Owner.Name FROM Case "
           f"WHERE CaseNumber = {soql_str(number)} OR CaseNumber = {soql_str(number.zfill(8))} LIMIT 1")
    if not cs:
        st.append("PROBLEM: this login cannot see the case at all (wrong number, or no access to it in Salesforce sharing).")
        return out
    c = cs[0]
    out["case"] = {k: c.get(k) for k in ("Id", "CaseNumber", "Status", "IsClosed", "CreatedDate", "ClosedDate", "LastModifiedDate")}
    out["case"]["Owner"] = (c.get("Owner") or {}).get("Name")
    if str(c.get("Status")) in EXCLUDED_STATUSES:
        st.append(f"PROBLEM: case status is {c.get('Status')}, which EXCLUDED_STATUSES in server.py leaves out of every report.")
    objs = find_survey_objects(sess)
    out["surveyObjectsFound"] = [{"object": o["name"], "label": o["label"], "caseField": o["caseField"]} for o in objs]
    if not objs:
        st.append("PROBLEM: no feedback / survey object with a lookup to Case was detected, so no survey data can be loaded.")
    for o in objs:
        try:
            recs = q(f"SELECT Id, CreatedDate FROM {o['name']} WHERE {o['caseField']} = {soql_str(c['Id'])} ORDER BY CreatedDate ASC")
        except ApiError as e:
            if e.status == 401:
                raise
            st.append(f"{o['name']}: query failed - {e.message[:200]}")
            continue
        out.setdefault("surveyRecords", {})[o["name"]] = [{"Id": r["Id"], "CreatedDate": r["CreatedDate"]} for r in recs]
        if recs:
            st.append(f"{o['name']}: {len(recs)} record(s) found; the report uses the latest one, created {recs[-1]['CreatedDate']} (UTC). "
                      f"If this is outside the dates selected on the CSAT tab, it is left out.")
        else:
            st.append(f"{o['name']}: no record is visible to this login for this case via {o['caseField']}. "
                      f"If you can see it in Salesforce, either the record's Case lookup is a different field, or the Feedback object's "
                      f"sharing hides it from this login (owner is Admin User; check the object's sharing / your profile's 'View All').")
    if not any(st_ for st_ in st if st_.startswith("PROBLEM")) and out.get("surveyRecords"):
        st.append("Server side looks fine. If it is still missing, the cause is in the browser: the survey data set was not downloaded for "
                  "this date range, or a child filter (Agent / Group / Priority / Status) hides it.")
    try:        # what the history says, so the attribution can be checked by eye
        gf, af = _history_group_field(sess), _history_group_field(sess, resolve_agent)
        flds = [x for x in ("Status", "Owner", gf, af) if x]
        hs = q(f"SELECT Field, OldValue, NewValue, CreatedDate FROM CaseHistory WHERE CaseId = {soql_str(c['Id'])} "
               f"AND Field IN ({', '.join(soql_str(x) for x in flds)}) ORDER BY CreatedDate ASC")
        out["history"] = [f"{r['CreatedDate']}  {r['Field']}: {r.get('OldValue')} -> {r.get('NewValue')}" for r in hs
                          if not any(isinstance(v, str) and ID_RE.match(v) and v.startswith(("005", "00G")) for v in (r.get("OldValue"), r.get("NewValue")))]
        out["historyFields"] = {"group": gf, "agent": af}
    except ApiError as e:
        if e.status == 401:
            raise
        out["history"] = "could not read: " + e.message[:200]
    return out


def survey_spec(sess, obj):
    spec = next((o for o in find_survey_objects(sess) if o["name"] == obj), None) if FIELD_NAME_RE.match(obj or "") else None
    if not spec:
        raise ApiError(400, "Choose a survey / feedback object in the CSAT tab to filter by survey date.")
    return spec["name"], spec["caseField"]


def survey_agent_field(sess, obj):
    """The survey record's own 'Agent' field -> (select expression, is_lookup) or None."""
    try:
        for f in _describe(sess, obj):
            if _norm(f.get("label")) == "agent" or f["name"].lower() in ("agent__c", "agentname__c"):
                if f.get("type") == "reference" and f.get("relationshipName") and "User" in (f.get("referenceTo") or []):
                    return f["relationshipName"] + ".Name"
                if f.get("type") in ("string", "picklist", "textarea") and FIELD_NAME_RE.match(f["name"]):
                    return f["name"]
    except ApiError as e:
        if e.status == 401:
            raise
    return None


def fetch_survey(sess, obj, csat, fb, where, case_ids, warnings, sdate=None):
    """Latest survey record per case: {CaseId: {csat, comment, date, extra}}."""
    spec = next((o for o in find_survey_objects(sess) if o["name"] == obj), None)
    if not spec or not FIELD_NAME_RE.match(obj):
        warnings.append("Survey object not found or not readable.")
        return {}
    by_name = {f["name"]: f for f in spec["fields"]}
    csat = csat if csat in by_name else ""
    fb = fb if fb in by_name else ""
    extras = [f for f in spec["fields"] if f["name"] not in (csat, fb)][:15]
    link = spec["caseField"]
    agx = survey_agent_field(sess, obj)
    cols = ", ".join(dict.fromkeys([link, "CreatedDate"] + [x for x in (csat, fb) if x] + [f["name"] for f in extras] + ([agx] if agx else [])))
    base = f"SELECT Id, {cols} FROM {obj} WHERE "
    recs = []

    def pull(soql):
        res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql))
        while True:
            recs.extend(res.get("records", []))
            if res.get("done") or not res.get("nextRecordsUrl"):
                break
            res = sf_get(sess, res["nextRecordsUrl"])

    try:
        if sdate is not None:                   # survey-date mode: Salesforce does not allow a semi-join inside a semi-join
            raise ApiError(0, "by id")
        pull(base + f"{link} IN (SELECT Id FROM Case {where}) ORDER BY CreatedDate ASC")
    except ApiError as e:
        if e.status == 401:
            raise
        recs.clear()
        try:                                    # look the cases up by Id in batches
            for i in range(0, len(case_ids), 300):
                ids = ", ".join("'" + x + "'" for x in case_ids[i:i + 300])
                pull(base + f"{link} IN ({ids})" + (f" AND {sdate}" if sdate else "") + " ORDER BY CreatedDate ASC")
        except ApiError as e2:
            if e2.status == 401:
                raise
            warnings.append("Could not read survey records: " + e2.message)
            return {}
    out = {}
    for r in recs:                              # ascending by date, so the latest record wins
        cid = r.get(link)
        if not cid:
            continue
        parts = []
        for f in extras:
            v = plain(r.get(f["name"]))
            if v in (None, ""):
                continue
            parts.append(f"{f['label']}: " + (("Yes" if v else "No") if isinstance(v, bool) else str(v)))
        out[cid] = {"csat": plain(r.get(csat)) if csat else None, "comment": plain(r.get(fb)) if fb else None,
                    "date": r.get("CreatedDate"), "extra": " · ".join(parts),
                    "agent": (str(plain(_dig(r, agx))).strip() if agx and plain(_dig(r, agx)) not in (None, "") else None)}
    return out


def cached(sess, key, ttl, fn):
    """Per-login cache for lookups that hardly ever change (custom-field list, group list), so a page reload or a
    switch between dashboards does not ask Salesforce the same thing again. Errors are never cached."""
    c = sess.setdefault("_ttl", {})
    hit = c.get(key)
    if hit and time.time() - hit[0] < ttl:
        return hit[1]
    v = fn()
    c[key] = (time.time(), v)
    return v


def build_meta(sess):
    try:
        fields = _describe(sess, "Case")
    except ApiError as e:
        if e.status == 401:
            raise
        fields = []
    custom = [{"name": f["name"], "label": f.get("label") or f["name"], "type": f.get("type")}
              for f in fields if f["name"].endswith("__c") and f.get("type") not in SKIP_TYPES]
    csat_re = re.compile(r"csat|satisf|survey|rating|score|nps|stars?", re.I)
    fb_re = re.compile(r"feedback|comment|remark|verbatim|suggest|survey|review", re.I)
    text_types = {"string", "textarea", "picklist", "richtext", "multipicklist"}
    cands = [f for f in custom if csat_re.search(f["label"] + " " + f["name"])]
    fbs = [f for f in custom if f["type"] in text_types and fb_re.search(f["label"] + " " + f["name"])]
    has_ent, reason = True, ""
    try:
        sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote("SELECT Id FROM CaseMilestone LIMIT 1"))
    except ApiError as e:
        if e.status == 401:
            raise
        has_ent, reason = False, e.message
    return {"customFields": custom, "csatCandidates": cands, "feedbackCandidates": fbs,
            "surveyObjects": find_survey_objects(sess), "hasEntitlements": has_ent, "reason": reason}


# ---------------------------------------------------------------- Tags (custom "Add Tag" feature on Case)
# Found automatically: a custom object with "tag" in its name / label and a lookup to Case (the tag assigned to a case),
# which points to a tag master record (name + colour). When the org keeps tags in a text / multi-select field on Case instead,
# that field is used. To force it, add to field_map.json, for example:
#   {"Tag Object": "Case_Tag__c", "Tag Name": "Tag__c", "Tag Color": "Color__c", "Tag Notes": "Notes__c", "Tag Case Field": "Tags__c"}
TAG_RE = re.compile(r"tag", re.I)
TAG_SYS = {"Id", "IsDeleted", "CreatedById", "LastModifiedById", "SystemModstamp", "LastModifiedDate", "LastViewedDate",
           "LastReferencedDate", "CurrencyIsoCode", "RecordTypeId", "CreatedDate", "OwnerId"}


def _tag_field(flds, ov_key, labels, types):
    ov = _overrides().get(ov_key)
    by = {f["name"]: f for f in flds}
    if ov and ov in by:
        return by[ov]
    for lab in labels:
        for f in flds:
            if f["name"] in TAG_SYS or f.get("type") not in types:
                continue
            if lab in _norm(f.get("label")) or lab in _norm(f["name"].replace("__c", "")):
                return f
    return None


def _name_field(flds):
    """The field holding the tag's real NAME. Standard Name is used unless it is an auto-number (TAG-0001, 00123 ...),
    in which case a text field such as 'Tag Name' / 'Title' is used. Override: field_map.json {"Tag Name": "Field__c"}."""
    by = {f["name"]: f for f in flds}
    ov = _overrides().get("Tag Name")
    if ov and ov in by:
        return by[ov]
    nm = by.get("Name")
    if nm and not nm.get("autoNumber"):
        return nm
    pool = [f for f in flds if f["name"] != "Name" and not f.get("autoNumber")]
    got = _tag_field(pool, "Tag Name", ["tagname", "tagtitle", "tagvalue", "tagtext", "title", "displayname", "label", "tag", "name"], {"string", "picklist"})
    return got or nm or {"name": "Name"}


def find_tags(sess):
    if "_tagspec" in sess:
        return sess["_tagspec"]
    ov = _overrides()
    want = str(ov.get("Tag Object") or "").strip()
    g = sf_get(sess, f"/services/data/v{API}/sobjects")
    objs = {o["name"]: o for o in g.get("sobjects", []) if o.get("queryable")}
    cands = [o for o in objs.values()
             if (o["name"].lower() == want.lower() if want else (o.get("custom") and TAG_RE.search(o["name"] + " " + (o.get("label") or ""))))]
    for o in cands:
        try:
            flds = _describe(sess, o["name"])
        except ApiError as e:
            if e.status == 401:
                raise
            continue
        link = _case_link(flds)
        if not link or not link.get("relationshipName"):
            continue
        # the tag master the assignment points to (name + colour live there)
        master = None
        for f in flds:
            if f["name"] in TAG_SYS or f["name"] == link["name"] or f.get("type") != "reference" or not f.get("relationshipName"):
                continue
            refs = [r for r in (f.get("referenceTo") or []) if r in objs and r != "Case"]
            if refs and (TAG_RE.search(refs[0] + " " + (objs[refs[0]].get("label") or "")) or refs[0].endswith("__c")):
                master = (f, refs[0])
                if TAG_RE.search(refs[0]):
                    break
        paths, notes_f, color_p, name_p = {}, _tag_field(flds, "Tag Notes", ["note", "comment", "reason", "remark", "description"], {"string", "textarea", "richtext"}), None, None
        if master:
            f, mobj = master
            try:
                mflds = _describe(sess, mobj)
            except ApiError as e:
                if e.status == 401:
                    raise
                mflds = []
            name_p = f"{f['relationshipName']}.{_name_field(mflds)['name']}"
            cf = _tag_field(mflds, "Tag Color", ["colour", "color", "hex"], {"string", "picklist", "textarea"})
            color_p = f"{f['relationshipName']}.{cf['name']}" if cf else None
            kf = _tag_field(mflds, "Tag Kind", ["type", "category", "kind", "scope"], {"string", "picklist", "boolean"})
            kind_p = f"{f['relationshipName']}.{kf['name']}" if kf else None
        else:
            name_p = _name_field(flds)["name"]
            cf = _tag_field(flds, "Tag Color", ["colour", "color", "hex"], {"string", "picklist", "textarea"})
            color_p = cf["name"] if cf else None
            kind_p = None
        spec = {"mode": "object", "label": o.get("label") or o["name"], "obj": o["name"], "rel": link["relationshipName"],
                "caseField": link["name"], "name": name_p, "color": color_p, "kind": kind_p, "notes": notes_f["name"] if notes_f else None,
                "mrel": master[0]["relationshipName"] if master else None, "mobj": master[1] if master else None}
        sess["_tagspec"] = spec
        return spec
    # fallback: tags kept in a field on Case itself
    cf = _describe(sess, "Case")
    fld = None
    ovf = ov.get("Tag Case Field")
    for f in cf:
        if f.get("type") in SKIP_TYPES or f["name"] in TAG_SYS:
            continue
        if (ovf and f["name"] == ovf) or (not ovf and f.get("type") in ("string", "textarea", "picklist", "multipicklist")
                                          and re.fullmatch(r"tags?", _norm(f.get("label")) or _norm(f["name"].replace("__c", "")))):
            fld = f
            break
    if fld:
        spec = {"mode": "field", "label": fld.get("label") or fld["name"], "field": fld["name"]}
        sess["_tagspec"] = spec
        return spec
    raise ApiError(404, "No Tag object was found in this org (a custom object with “tag” in its name and a lookup to Case, or a Tags field on Case). "
                        "Set it in field_map.json, for example {\"Tag Object\": \"Case_Tag__c\"}.")


# ---------------------------------------------------------------- Tag tab: three groups of information
#   Tag info            = fields of the tag master record (name, colour, description, active ...)
#   Tagged record info  = fields of the tag assignment record (who tagged, when, notes ...)
#   Case detail         = fields of the tagged case (+ account fields, group, agent ...)
TG_HIDE = {"IsDeleted", "SystemModstamp", "LastViewedDate", "LastReferencedDate", "Id"}
TG_GROUPS = ("tag", "rec", "case")
TG_PREFIX = {"tag": "T:", "rec": "R:", "case": "C:"}


def _fld_label(f):
    lab = f.get("label") or f["name"]
    if f.get("type") == "reference" and lab.endswith(" ID") and len(lab) > 3:
        lab = lab[:-3]
    return lab


def _fld_defs(flds, group, skip_paths):
    out = []
    for f in flds:
        n, t = f["name"], f.get("type")
        if n in TG_HIDE or t in SKIP_TYPES:
            continue
        if t == "reference":
            refs = f.get("referenceTo") or []
            if not f.get("relationshipName") or not refs or not all(r in SAFE_REFS or r.endswith("__c") for r in refs):
                continue
        path = _select_path("", f)
        if path in skip_paths:
            continue
        skip_paths.add(path)
        out.append({"key": TG_PREFIX[group] + n, "label": _fld_label(f), "type": "string" if t == "reference" else t,
                    "path": path, "g": group})
    return out


def tag_catalog(sess, spec):
    """Every field the Tag tab can show, per group, with its path relative to the group's own object.
    -> list of {key, label, type, path, full, g, d (shown by default)}.  `full` is the path from the tag-assignment row."""
    if "_tagcat" in sess:
        return sess["_tagcat"]
    cat, used = [], {"tag": set(), "rec": set(), "case": set()}

    def add(group, key, label, typ, path, full, default=False):
        if path in used[group]:
            return
        used[group].add(path)
        cat.append({"key": key, "label": label, "type": typ, "path": path, "full": full, "g": group, "d": 1 if default else 0})

    def describe(obj):
        try:
            return _describe(sess, obj)
        except ApiError as e:
            if e.status == 401:
                raise
            return []
    obj_mode = spec["mode"] == "object"
    rel = spec.get("rel")
    case_full = (lambda p: f"{rel}.{p}") if obj_mode else (lambda p: p)

    # ---- Tag info
    if obj_mode:
        if spec.get("mrel"):
            mflds = describe(spec["mobj"])
            nm_path = (spec["name"] or "").split(".")[-1]
            auto = {f["name"] for f in mflds if f.get("autoNumber")}
            for d in sorted(_fld_defs(mflds, "tag", set()), key=lambda x: x["path"] != nm_path):     # tag name first
                lab = d["label"]
                if d["path"] == nm_path:
                    lab = "Tag name"
                elif d["path"] in auto:
                    lab = "Tag number"
                dflt = d["path"] == nm_path or d["path"] == (spec["color"] or "").split(".")[-1] or d["path"] == (spec["kind"] or "").split(".")[-1] \
                    or bool(re.fullmatch(r"(?i)description|active|is active|type|category|created date|created by", lab.strip()))
                add("tag", d["key"], lab, d["type"], d["path"], f"{spec['mrel']}.{d['path']}", dflt)
        else:       # the name / colour live on the assignment record itself
            for lab, p in (("Tag name", spec["name"]), ("Colour", spec["color"]), ("Kind", spec["kind"])):
                if p:
                    add("tag", "T:" + p, lab, "string", p, p, True)
    else:
        add("tag", "T:name", "Tag name", "string", spec["field"], spec["field"], True)

    # ---- Tagged record info (the assignment record)
    if obj_mode:
        rflds = describe(spec["obj"])
        skip = {spec["caseField"], _select_path("", next((f for f in rflds if f["name"] == spec["caseField"]), {"name": spec["caseField"]}))}
        if spec.get("mrel"):                    # the lookup to the tag master is already shown as the tag name
            skip.add(f"{spec['mrel']}.Name")
        for d in _fld_defs([f for f in rflds if f["name"] != spec["caseField"]], "rec", set(skip)):
            lab = d["label"]
            dflt = d["path"] in ("CreatedBy.Name", "CreatedDate") or d["path"] == spec.get("notes") or lab.lower() in ("notes", "comments", "reason")
            add("rec", d["key"], lab, d["type"], d["path"], d["path"], dflt)

    # ---- Case detail
    cflds = describe("Case")
    core = [("CaseNumber", "Case number", "string", "CaseNumber", True), ("Subject", "Subject", "string", "Subject", True),
            ("Status", "Status", "picklist", "Status", True), ("Priority", "Priority", "picklist", "Priority", True),
            ("Account", "Account", "string", "Account.Name", True), ("Owner", "Case owner", "string", "Owner.Name", True),
            ("Origin", "Origin", "picklist", "Origin", True), ("Type", "Type", "picklist", "Type", True),
            ("CreatedDate", "Case created", "datetime", "CreatedDate", True), ("ClosedDate", "Case closed", "datetime", "ClosedDate", False)]
    for n, lab, t, p, dflt in core:
        add("case", "C:" + n, lab, t, p, case_full(p), dflt)
    for lab, res in (("Group", resolve_group(sess)), ("First assigned group", resolve_first_group(sess)), ("Agent", resolve_agent(sess))):
        if res and res.get("path"):
            add("case", "G:" + lab, lab, "string", res["path"], case_full(res["path"]), lab == "Group")
    for e in resolve_extra_fields(sess):
        if e["path"]:
            add("case", "X:" + e["label"], e["label"], e.get("type") or "string", e["path"], case_full(e["path"]), False)
    for d in _fld_defs(cflds, "case", set(used["case"])):
        add("case", d["key"], d["label"], d["type"], d["path"], case_full(d["path"]), False)
    sess["_tagcat"] = cat
    return cat


def _tg_value(rec, path):
    v = plain(_dig(rec, path))
    if isinstance(v, bool):
        return "Yes" if v else "No"
    if isinstance(v, (dict, list)):
        return json.dumps(v, ensure_ascii=False)
    return None if v in (None, "") else v


def fetch_tag_detail(sess, rid):
    """Every readable field of ONE tag assignment, split into Tag info / Tagged record info / Case detail."""
    spec = find_tags(sess)
    cat = tag_catalog(sess, spec)
    out = {"tag": [], "rec": [], "case": []}
    notes = []

    def pull(frm, rid_, paths):
        """Read paths of one record, in chunks, splitting a chunk when a field cannot be read."""
        got = {}

        def go(chunk):
            try:
                res = soql_all(sess, f"SELECT {', '.join(dict.fromkeys(['Id'] + chunk))} FROM {frm} WHERE Id = {soql_str(rid_)}")
                for r in res[:1]:
                    for p in chunk:
                        got[p] = _tg_value(r, p)
            except ApiError as e:
                if e.status == 401:
                    raise
                if len(chunk) == 1:
                    notes.append(f"{chunk[0]} could not be read.")
                    return
                mid = len(chunk) // 2
                go(chunk[:mid])
                go(chunk[mid:])
        for i in range(0, len(paths), 40):
            go(paths[i:i + 40])
        return got
    if spec["mode"] == "object":
        if not ID_RE.match(rid or ""):
            raise ApiError(400, "Invalid record.")
        rows = soql_all(sess, f"SELECT Id, {spec['caseField']} FROM {spec['obj']} WHERE Id = {soql_str(rid)}")
        if not rows:
            raise ApiError(404, "This tag record was not found (it may have been removed).")
        case_id = rows[0].get(spec["caseField"])
        vals = pull(spec["obj"], rid, [c["full"] for c in cat])
    else:
        case_id, _, tname = (rid or "").partition(":")
        if not ID_RE.match(case_id or ""):
            raise ApiError(400, "Invalid record.")
        vals = pull("Case", case_id, [c["full"] for c in cat])
    for c in cat:
        out[c["g"]].append({"key": c["key"], "label": c["label"], "type": c["type"], "value": vals.get(c["full"])})
    return {"id": rid, "caseId": case_id, "source": spec["label"], "groups": out, "notes": notes}


def user_case_groups(sess, user_ids, gp, days=90):
    """user Id -> the Case group that user mostly works in (most frequent group on the cases they own, last `days` days).
    Used for "Group of Tagged by" when the user is in no queue: it describes the person, not the ticket, so it does not
    change when the ticket is later moved to another group or left without an agent."""
    ids = sorted({u for u in user_ids if u and u.startswith("005")})
    out = {}
    if not ids or not gp:
        return out
    for i in range(0, len(ids), 100):
        chunk = ", ".join(soql_str(x) for x in ids[i:i + 100])
        try:
            rows = soql_all(sess, f"SELECT OwnerId o, {gp} g, COUNT(Id) c FROM Case WHERE OwnerId IN ({chunk}) AND {gp} != null "
                                  f"AND CreatedDate >= LAST_N_DAYS:{int(days)} GROUP BY OwnerId, {gp}")
        except ApiError as e:
            if e.status == 401:
                raise
            return out
        best = {}
        for r in rows:
            g = plain(r.get("g"))
            n = int(r.get("c") or 0)
            if g and n > best.get(r.get("o"), (None, 0))[1]:
                best[r.get("o")] = (str(g), n)
        out.update({u: v[0] for u, v in best.items()})
    return out


def fetch_tags(sess, days=0, open_only=False, cols=None, cap=5000, dfrom=None, dto=None, all_time=False):
    spec = find_tags(sess)
    cat = tag_catalog(sess, spec)
    want = set(cols or [])
    shown = [c for c in cat if c["d"] or c["key"] in want]
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    gp = None
    try:
        gp = (resolve_group(sess) or {}).get("path")
    except ApiError as e:
        if e.status == 401:
            raise
    case_paths = ["Id", "CaseNumber", "Subject", "Status", "Priority", "Origin", "Type", "IsClosed", "CreatedDate", "Account.Name", "Owner.Name"] + ([gp] if gp else [])
    cap = max(1000, min(int(cap or 5000), 50000))
    warnings = []

    def run(select, frm, where, order, limit):
        soql = f"SELECT {', '.join(dict.fromkeys(select))} FROM {frm} WHERE {where} ORDER BY {order}"
        res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql + f" LIMIT {limit}"))
        rows = list(res.get("records", []))
        while not res.get("done") and res.get("nextRecordsUrl") and len(rows) < limit:
            res = sf_get(sess, res["nextRecordsUrl"])
            rows += res.get("records", [])
        return rows[:limit], len(rows) >= limit

    def keep_good(select, frm, where, order, optional):
        """Drop optional fields this login cannot read so one bad field never breaks the tab (split in halves until isolated)."""
        optional = list(dict.fromkeys(optional))

        def ok(paths):
            if not paths:
                return []
            try:
                run(select + paths, frm, where, order, 1)
                return paths
            except ApiError as e:
                if e.status == 401:
                    raise
                if len(paths) == 1:
                    return []
            mid = len(paths) // 2
            return ok(paths[:mid]) + ok(paths[mid:])
        good = []
        for i in range(0, len(optional), 40):        # keeps every single query short enough for the REST URL
            good += ok(optional[i:i + 40])
        return good

    def dig(rec, path):
        for part in path.split("."):
            rec = rec.get(part) if isinstance(rec, dict) else None
        return rec

    out = []
    qmap = queue_membership(sess)          # group(s) of the user who added the tag
    if spec["mode"] == "object":
        rel = spec["rel"]
        base = ["Id", "CreatedDate", "CreatedById", "CreatedBy.Name", spec["caseField"], spec["name"]]
        where = f"{rel}.Status NOT IN ({ex})"
        if open_only:
            where += f" AND {rel}.IsClosed = false AND {rel}.Status NOT IN ({', '.join(soql_str(x) for x in RESOLVED_STATUSES)})"
        if dfrom and dto and not all_time:          # master filter: TAGGED date = when the tag was added
            where += f" AND CreatedDate >= {sf_datetime(dfrom)} AND CreatedDate <= {sf_datetime(dto)}"
        elif days:
            where += f" AND CreatedDate >= LAST_N_DAYS:{int(days)}"
        opt = [x for x in (spec["color"], spec["kind"], spec["notes"]) if x] + [f"{rel}.{c}" for c in case_paths if c != "Id"]
        opt += [c["full"] for c in shown if c["full"] not in opt]
        try:
            run(base, spec["obj"], where, "CreatedDate DESC", 1)
        except ApiError as e:
            if e.status == 401:
                raise
            base = ["Id", "CreatedDate", spec["caseField"], spec["name"]]
            run(base, spec["obj"], where, "CreatedDate DESC", 1)
        good = keep_good(base, spec["obj"], where, "CreatedDate DESC", opt)
        gset = set(good)
        rows, trunc = run(base + good, spec["obj"], where, "CreatedDate DESC", cap)
        ugrp = user_case_groups(sess, [r.get("CreatedById") for r in rows if not qmap.get(r.get("CreatedById") or "")], gp)
        for r in rows:
            cs = r.get(rel) or {}
            out.append({"id": r.get("Id"), "caseId": r.get(spec["caseField"]), "tag": dig(r, spec["name"]) or "(no name)",
                        "color": dig(r, spec["color"]) if spec["color"] in good else None,
                        "kind": dig(r, spec["kind"]) if spec["kind"] in good else None,
                        "notes": r.get(spec["notes"]) if spec["notes"] in good else None,
                        "by": dig(r, "CreatedBy.Name"), "byGroup": " / ".join(qmap.get(r.get("CreatedById") or "", [])) or ugrp.get(r.get("CreatedById") or ""), "at": r.get("CreatedDate"),
                        "caseNumber": cs.get("CaseNumber"), "subject": cs.get("Subject"), "status": cs.get("Status"),
                        "priority": cs.get("Priority"), "origin": cs.get("Origin"), "type": cs.get("Type"),
                        "created": cs.get("CreatedDate"), "account": dig(cs, "Account.Name"), "owner": dig(cs, "Owner.Name"),
                        "group": dig(cs, gp) if gp else None, "closed": cs.get("IsClosed"),
                        "v": {c["key"]: _tg_value(r, c["full"]) for c in shown if c["full"] in gset}})
    else:
        fld = spec["field"]
        where = f"{fld} != null AND Status NOT IN ({ex})" + (f" AND IsClosed = false AND Status NOT IN ({', '.join(soql_str(x) for x in RESOLVED_STATUSES)})" if open_only else "")
        if dfrom and dto and not all_time:          # tags are a field on Case: no tagged date, so the last-modified date stands in
            where += f" AND LastModifiedDate >= {sf_datetime(dfrom)} AND LastModifiedDate <= {sf_datetime(dto)}"
        elif days:
            where += f" AND CreatedDate >= LAST_N_DAYS:{int(days)}"
        base = ["Id", "CaseNumber", fld, "LastModifiedDate"]
        good = keep_good(base, "Case", where, "CreatedDate DESC", [c for c in case_paths if c not in ("Id", "CaseNumber")] + [c["full"] for c in shown])
        gset = set(good)
        rows, trunc = run(base + good, "Case", where, "CreatedDate DESC", cap)
        for r in rows:
            for t in re.split(r"[;,]", str(r.get(fld) or "")):
                t = t.strip()
                if t:
                    out.append({"id": r.get("Id") + ":" + t, "caseId": r.get("Id"), "tag": t, "color": None, "kind": None, "notes": None,
                                "by": None, "at": r.get("LastModifiedDate"), "caseNumber": r.get("CaseNumber"), "subject": r.get("Subject"), "status": r.get("Status"),
                                "priority": r.get("Priority"), "origin": r.get("Origin"), "type": r.get("Type"), "created": r.get("CreatedDate"),
                                "account": dig(r, "Account.Name"), "owner": dig(r, "Owner.Name"), "group": dig(r, gp) if gp else None, "closed": r.get("IsClosed"),
                                "v": {c["key"]: _tg_value(r, c["full"]) for c in shown if c["full"] in gset}})
    if trunc:
        warnings.append(f"Result cut at {cap} records – narrow the period to see the rest.")
    if spec["mode"] != "object" and dfrom and not all_time:
        warnings.append("Tags are stored on the case (no tagged date), so the case's last-modified date is used as the tagged date.")
    return {"source": spec["label"], "mode": spec["mode"], "rows": out, "truncated": trunc, "warnings": warnings,
            "columns": [{k: c[k] for k in ("key", "label", "type", "g", "d")} for c in cat],
            "loaded": [c["key"] for c in shown]}



# ---------------------------------------------------------------- Audit Details report ("Tags with Tagged Records and Case")
def fetch_audit_tags(sess, dfrom, dto, all_time=False, tags=None, groups=None):
    """One row per tag assignment, joined with its case, for tags added (Tagged date) in the range.
    tags / groups = optional lists of exact names (case-insensitive); a Salesforce filter is added where possible and the
    rest is filtered here. Agent / Group follow the same rules as the case download."""
    spec = find_tags(sess)
    tags = [t.strip() for t in (tags or []) if t and t.strip()][:50]
    groups = [AUDIT_GROUP]          # Audit Details is only for the ERP Helpdesk-L1 group, whatever the caller asks for
    gp = (resolve_group(sess) or {}).get("path")
    ap = (resolve_agent(sess) or {}).get("path")
    obj_mode = spec["mode"] == "object"
    rel = spec["rel"] if obj_mode else ""
    pre = rel + "." if obj_mode else ""
    # Master filter = TAGGED date (when the tag was added). Tag assignments carry their own CreatedDate; if tags are a
    # field on Case there is no tag date, so the case's last-modified date is the closest stand-in.
    tdate = "CreatedDate" if obj_mode else "LastModifiedDate"
    ex_st = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    where = f"WHERE {pre}Status NOT IN ({ex_st}) "
    if not all_time:
        where += f"AND {tdate} >= {sf_datetime(dfrom)} AND {tdate} <= {sf_datetime(dto)} "
    if obj_mode and tags:
        where += f"AND {spec['name']} IN ({', '.join(soql_str(t) for t in tags)}) "
    if not obj_mode:
        where += f"AND {spec['field']} != null "
    if gp and groups:
        where += f"AND {pre}{gp} IN ({', '.join(soql_str(g) for g in groups)}) "
    core = ["CaseNumber", "Subject", "Status", "Priority", "Origin", "Type", "IsClosed", "CreatedDate", "ClosedDate", "LastModifiedDate",
            "Account.Name", "OwnerId", "Owner.Name", "Owner.Type"]
    opt = [x for x in (gp, ap) if x]
    if obj_mode:
        head = ["Id", "CreatedDate", "CreatedBy.Name", spec["caseField"], spec["name"]] + ([spec["notes"]] if spec.get("notes") else [])
        paths = lambda extra: head + [pre + c for c in core + extra]
        frm, order = spec["obj"], "CreatedDate DESC"
    else:
        head = ["Id", spec["field"]]
        paths = lambda extra: head + core + extra
        frm, order = "Case", "CreatedDate DESC"

    def run(extra):
        soql = f"SELECT {', '.join(dict.fromkeys(paths(extra)))} FROM {frm} {where}ORDER BY {order}"
        return soql_all(sess, soql, cap=50000)
    warnings = []
    try:
        rows = run(opt)
    except ApiError as e:
        if e.status == 401:
            raise
        if not opt:
            raise
        rows = run([])
        gp = ap = None
        warnings.append("Group / Agent field could not be read (" + e.message[:120] + "); owner and queue are used instead.")
    cases = [(r.get(rel) or {}) if obj_mode else r for r in rows]
    ids = sorted({(r.get(spec["caseField"]) if obj_mode else r["Id"]) for r in rows if (r.get(spec["caseField"]) if obj_mode else r["Id"])})
    res_times = fetch_resolution_times(sess, "", ids) if ids else {}
    resolved_set = {x.lower() for x in RESOLVED_STATUSES}
    lo = _parse_dt(dfrom) if not all_time else None
    hi = _parse_dt(dto) if lo else None
    qmap = {} if gp else queue_membership(sess)
    want_g = {g.lower() for g in groups}
    want_t = {t.lower() for t in tags}
    out = []
    for r, c in zip(rows, cases):
        cid = r.get(spec["caseField"]) if obj_mode else r["Id"]
        if not c or not cid:
            continue
        resolved = bool(c.get("IsClosed")) or str(c.get("Status") or "").lower() in resolved_set
        rdt = None
        if resolved:
            rdt = res_times.get(cid)
            cd = _parse_dt(c["ClosedDate"]) if c.get("ClosedDate") else None
            if rdt is None:
                rdt = cd or (_parse_dt(c["LastModifiedDate"]) if c.get("LastModifiedDate") else None)
            elif cd and rdt > cd:
                rdt = cd
        tdt = _parse_dt(r["CreatedDate"]) if (obj_mode and r.get("CreatedDate")) else (_parse_dt(c["LastModifiedDate"]) if c.get("LastModifiedDate") else None)
        if lo and not (tdt and lo <= tdt <= hi):
            continue
        owner = c.get("Owner") or {}
        otype, oname = owner.get("Type"), owner.get("Name") or "—"
        agent = oname if otype == "User" else "Unassigned"
        av = _dig(c, ap) if ap else None
        if av not in (None, ""):
            agent = str(plain(av))
        elif ap:
            agent = "Unassigned"
        gv = _dig(c, gp) if gp else None
        if gv not in (None, ""):
            group = str(plain(gv))
        elif otype == "Queue":
            group = oname
        elif otype == "User" and qmap.get(c.get("OwnerId") or ""):
            group = " / ".join(qmap[c["OwnerId"]])
        else:
            group = "No group"
        if want_g and group.lower() not in want_g:
            continue
        if obj_mode:
            names = [str(_dig(r, spec["name"]) or "(no name)")]
        else:
            names = [t.strip() for t in re.split(r"[;,]", str(r.get(spec["field"]) or "")) if t.strip()]
        for nm in names:
            if want_t and nm.lower() not in want_t:
                continue
            out.append({"id": r["Id"] + ("" if obj_mode else ":" + nm), "caseId": cid, "tag": nm,
                        "taggedOn": r.get("CreatedDate") if obj_mode else (tdt.isoformat() if tdt else None),
                        "taggedBy": _dig(r, "CreatedBy.Name") if obj_mode else None,
                        "notes": str(plain(r.get(spec["notes"])) or "") if obj_mode and spec.get("notes") else "",
                        "caseNumber": c.get("CaseNumber"), "subject": c.get("Subject") or "", "status": c.get("Status") or "—",
                        "priority": c.get("Priority") or "—", "origin": c.get("Origin") or "—", "type": c.get("Type") or "—",
                        "account": (c.get("Account") or {}).get("Name") or "—", "agent": agent, "group": group,
                        "created": c.get("CreatedDate"), "resolved": rdt.isoformat() if rdt else None})
    if len(rows) >= 50000:
        warnings.append("Result cut at 50,000 records – narrow the dates.")
    if not obj_mode:
        warnings.append("Tags are stored on the case (no tagged date), so the case's last-modified date is used as the tagged date.")
    return {"rows": out, "source": spec["label"], "warnings": warnings, "tags": sorted({x["tag"] for x in out}),
            "groups": sorted({x["group"] for x in out}), "truncated": len(rows) >= 50000}


def count_unresolved(sess, group=None):
    """Total cases that are not resolved / closed right now (Cancelled and Merged are left out), plus a split by priority.
    With group set, only the open cases currently in that Group are counted."""
    skip = ", ".join(soql_str(x) for x in list(RESOLVED_STATUSES) + EXCLUDED_STATUSES)
    where = f"WHERE IsClosed = false AND Status NOT IN ({skip})"
    if group:
        gp = resolve_group(sess)["path"]
        if not gp:
            raise ApiError(400, "No Group field was found on Case (map it in field_map.json as {\"Group\": \"YourField__c\"}).")
        where += f" AND {gp} = {soql_str(group)}"
    app = None
    try:
        app = next((e for e in resolve_extra_fields(sess) if e["label"] == "Application" and e["path"]), None)
    except ApiError as e:
        if e.status == 401:
            raise
    # the three counts do not depend on each other: ask Salesforce for them at the same time
    f_tot = pfuture(sf_get, sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(f"SELECT COUNT() FROM Case {where}"))
    f_pri = pfuture(soql_all, sess, f"SELECT Priority p, COUNT(Id) c FROM Case {where} GROUP BY Priority")
    f_app = pfuture(soql_all, sess, f"SELECT {app['path']} a, COUNT(Id) c FROM Case {where} GROUP BY {app['path']}") if app else None
    total = int(f_tot.result().get("totalSize") or 0)
    by_pri = {}
    try:
        for r in f_pri.result():
            by_pri[r.get("p") or "—"] = int(r.get("c") or 0)
    except ApiError as e:
        if e.status == 401:
            raise
    # split by Application (same field as the Application column used elsewhere)
    by_app, app_found = {}, False
    try:
        if app:
            app_found = True
            for r in f_app.result():
                k = plain(r.get("a"))
                k = "Not specified" if k in (None, "", "—") else str(k)
                by_app[k] = by_app.get(k, 0) + int(r.get("c") or 0)
    except ApiError as e:
        if e.status == 401:
            raise
    return {"total": total, "byPriority": by_pri, "byApplication": by_app, "applicationFound": app_found}


def list_groups(sess):
    """Distinct Group values currently on cases (A-Z), for the Group Dashboard selector."""
    gp = resolve_group(sess)["path"]
    if not gp:
        return {"groups": [], "found": False}
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    cnt = {}
    try:
        for r in soql_all(sess, f"SELECT {gp} g, COUNT(Id) c FROM Case WHERE {gp} != null AND IsClosed = false "
                                f"AND Status NOT IN ({ex}) GROUP BY {gp}"):
            g = plain(r.get("g"))
            if g:
                cnt[str(g)] = int(r.get("c") or 0)
    except ApiError as e:
        if e.status == 401:
            raise
    try:     # picklist values (also groups with no open case right now)
        for f in _describe(sess, "Case"):
            if f["name"] == gp and f.get("picklistValues"):
                for v in f["picklistValues"]:
                    if v.get("active", True) and v.get("value"):
                        cnt.setdefault(v["value"], 0)
    except ApiError as e:
        if e.status == 401:
            raise
    return {"groups": sorted(cnt, key=lambda k: k.lower()), "open": cnt, "found": True}


def group_day(sess, group, dfrom, dto):
    """One group's day. Inward = distinct cases that came into the group in the window (created straight into it,
    or reassigned from another group). Processed = distinct cases resolved while in the group plus cases moved out to
    another group. Rows use the same shape as /api/cases so the Live Dashboard renderers can draw them."""
    group = (group or "").strip()
    gp = resolve_group(sess)["path"]
    if not group or not gp:
        raise ApiError(400, "Choose a group." if gp is None or not group else "No Group field found on Case.")
    key = group.casefold()
    lo, hi = _parse_dt(dfrom), _parse_dt(dto)
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    app = next((e for e in resolve_extra_fields(sess) if e["label"] == "Application" and e["path"]), None)
    ap = app["path"] if app else None
    sel = ("Id, CaseNumber, Subject, Status, Priority, IsClosed, CreatedDate, ClosedDate, LastModifiedDate, "
           f"Account.Name, Owner.Name, Owner.Type, {gp}" + (f", {ap}" if ap else ""))
    # three independent Salesforce reads (group history, cases created in the window, cases resolved in the window) run together
    f_hist = pfuture(fetch_case_history, sess, dfrom, dto)
    f_res = pfuture(fetch_cases, sess, "resolved", dfrom, dto)
    f_created = pfuture(soql_all, sess, f"SELECT {sel} FROM Case WHERE CreatedDate >= {sf_datetime(dfrom)} AND CreatedDate <= {sf_datetime(dto)} "
                                        f"AND Status NOT IN ({ex})", MAX_ROWS)
    hist = f_hist.result()
    moves = sorted(hist["rows"], key=lambda r: r["Date"])
    first_row = {}
    for r in moves:
        first_row.setdefault(r["CaseId"], r)
    inward, out_ev = {}, {}
    for r in moves:
        a, b = (r["From"] or "").casefold(), (r["To"] or "").casefold()
        if b == key and a != key:
            inward.setdefault(r["CaseId"], (r["Date"], None))
        elif a == key and b != key:
            out_ev.setdefault(r["CaseId"], (r["Date"], r))

    def case_rows(ids):
        ids = list(dict.fromkeys(ids))
        res = []
        for i in range(0, len(ids), 300):
            q = ", ".join(soql_str(x) for x in ids[i:i + 300])
            res += soql_all(sess, f"SELECT {sel} FROM Case WHERE Id IN ({q})", cap=MAX_ROWS)
        return {c["Id"]: c for c in res}

    # cases created in the window straight into the group (the group they started in = the From of their first history row)
    created = f_created.result()
    cmap = {c["Id"]: c for c in created}
    for c in created:
        fr = first_row.get(c["Id"])
        start = (fr["From"] if fr else plain(_dig(c, gp))) or ""
        if str(start).strip().casefold() == key:
            inward[c["Id"]] = (c["CreatedDate"], None)
    # resolved in the window while in the group
    resolved_rows = [r for r in f_res.result()["cases"]
                     if r.get("IsResolved") and r.get("ResolvedDate") and str(r.get("Group", "")).strip().casefold() == key]
    done = {r["Id"]: r for r in resolved_rows}
    need = [i for i in list(inward) + list(out_ev) if i not in cmap]
    cmap.update(case_rows(need))

    def row(c, when, resolved):
        gv = plain(_dig(c, gp))
        av = plain(_dig(c, ap)) if ap else None
        owner = c.get("Owner") or {}
        return {"Id": c["Id"], "CaseNumber": c["CaseNumber"], "Subject": c.get("Subject") or "",
                "Status": c.get("Status") or "—", "Priority": c.get("Priority") or "—",
                "CreatedDate": when if not resolved else c.get("CreatedDate"),
                "IsResolved": resolved, "ResolvedDate": when if resolved else None,
                "Account": (c.get("Account") or {}).get("Name") or "—",
                "Agent": owner.get("Name") if owner.get("Type") == "User" else "Unassigned",
                "Group": str(gv) if gv else group,
                "X:Application": "—" if av in (None, "") else av}

    def iso(v):
        return _parse_dt(v).strftime("%Y-%m-%dT%H:%M:%S.000+0000")
    in_rows = [row(cmap[i], iso(t[0]), False) for i, t in inward.items() if i in cmap and lo <= _parse_dt(t[0]) <= hi]
    proc = {}
    for i, r in done.items():
        proc[i] = dict(r, IsResolved=True, Group=group, Outcome="Resolved")      # resolved while in this group
    for i, (t, r) in out_ev.items():
        if i in proc or i not in cmap:
            continue
        proc[i] = row(cmap[i], iso(t), True)
        proc[i]["Agent"] = r.get("By") or proc[i]["Agent"]
        proc[i]["Group"] = group
        proc[i]["Outcome"] = "Forwarded"      # moved out to another group
    return {"created": in_rows, "resolved": list(proc.values()), "hasApp": bool(ap),
            "notes": hist.get("notes", []), "truncated": bool(hist.get("truncated"))}


def fetch_milestones(sess, field, dfrom, dto, all_time=False, obj=""):
    survey = survey_spec(sess, obj) if field == "survey" else None
    where = case_where(field, dfrom, dto, all_time, "Case.", survey)
    soql = ("SELECT CaseId, MilestoneType.Name, StartDate, TargetDate, CompletionDate, IsCompleted, IsViolated "
            f"FROM CaseMilestone {where}ORDER BY TargetDate DESC")
    try:
        res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql))
        rows = list(res.get("records", []))
        while not res.get("done") and len(rows) < MAX_ROWS:
            res = sf_get(sess, res["nextRecordsUrl"])
            rows += res.get("records", [])
    except ApiError as e:
        if e.status == 401:
            raise
        return {"available": False, "reason": e.message}
    return {"available": True, "truncated": not res.get("done"), "milestones": [{
        "CaseId": r["CaseId"], "Milestone": (r.get("MilestoneType") or {}).get("Name") or "Milestone",
        "StartDate": r.get("StartDate"), "TargetDate": r.get("TargetDate"),
        "CompletionDate": r.get("CompletionDate"), "IsCompleted": bool(r.get("IsCompleted")),
        "IsViolated": bool(r.get("IsViolated"))} for r in rows]}


# One long-lived pool for every parallel Salesforce call. The old code created (and threw away) a new pool per call, so each
# worker opened a brand-new HTTPS connection (TLS handshake) every time; long-lived workers keep theirs open and reuse it.
_POOL = ThreadPoolExecutor(12, thread_name_prefix="sf")
_PT = threading.local()


def _in_worker():
    return getattr(_PT, "w", False)


def _run_in_worker(fn, *a):
    _PT.w = True
    try:
        return fn(*a)
    finally:
        _PT.w = False


def pfuture(fn, *a):
    """Start fn(*a) in the background -> Future. Inside a pool worker it just runs inline (a pool must not wait on itself)."""
    if _in_worker():
        f = Future()
        try:
            f.set_result(fn(*a))
        except BaseException as e:      # noqa
            f.set_exception(e)
        return f
    return _POOL.submit(_run_in_worker, fn, *a)


def pmap(fn, items, workers=4):
    """Run fn over items in parallel (Salesforce calls are independent), keeping the order. Errors propagate."""
    items = list(items)
    if len(items) < 2 or _in_worker():
        return [fn(x) for x in items]
    futs = [_POOL.submit(_run_in_worker, fn, x) for x in items]
    return [f.result() for f in futs]


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


# ---------------------------------------------------------------- Salesforce
def soap_login(domain, username, password, token):
    body = f"""<?xml version="1.0" encoding="utf-8" ?>
<env:Envelope xmlns:xsd="http://www.w3.org/2001/XMLSchema"
              xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
              xmlns:env="http://schemas.xmlsoap.org/soap/envelope/">
  <env:Body>
    <n1:login xmlns:n1="urn:partner.soap.sforce.com">
      <n1:username>{escape(username)}</n1:username>
      <n1:password>{escape(password + token)}</n1:password>
    </n1:login>
  </env:Body>
</env:Envelope>"""
    req = urllib.request.Request(
        f"https://{domain}/services/Soap/u/{API}",
        data=body.encode("utf-8"),
        headers={"Content-Type": "text/xml; charset=UTF-8", "SOAPAction": "login"},
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            xml = r.read()
    except urllib.error.HTTPError as e:
        xml = e.read()
    except urllib.error.URLError as e:
        raise ApiError(502, f"Cannot reach {domain}: {e.reason}")

    try:
        root = ET.fromstring(xml)
    except ET.ParseError:
        raise ApiError(502, "Unexpected response from Salesforce.")

    def find(tag):
        for el in root.iter():
            if el.tag.split("}")[-1] == tag:
                return el.text
        return None

    fault = find("faultstring")
    if fault:
        raise ApiError(401, fault)
    sid, server_url = find("sessionId"), find("serverUrl")
    if not sid or not server_url:
        raise ApiError(502, "Login response did not contain a session.")
    u = urllib.parse.urlparse(server_url)
    return {
        "sid": sid,
        "instance": f"{u.scheme}://{u.netloc}",
        "name": find("userFullName") or username,
        "email": find("userEmail") or "",
        "username": username,
        "created": time.time(),
    }


_SF_TLS = threading.local()          # one persistent HTTPS connection per worker thread and Salesforce host (saves a TLS handshake on every request)
_USE_POOL = not urllib.request.getproxies().get("https")      # behind a proxy the plain urllib path is used


def _sf_raw(sess, path):
    """-> (status, body bytes). Reuses the thread's connection; one transparent retry when a kept-alive connection has gone stale."""
    host = urllib.parse.urlparse(sess["instance"]).netloc
    hdr = {"Authorization": "Bearer " + sess["sid"], "Accept": "application/json", "Accept-Encoding": "gzip",
           "Sforce-Query-Options": "batchSize=2000", "Connection": "keep-alive"}
    pool = _SF_TLS.__dict__.setdefault("c", {})
    for attempt in (0, 1):
        conn = pool.get(host)
        fresh = conn is None
        if fresh:
            conn = pool[host] = http.client.HTTPSConnection(host, timeout=90)
        try:
            conn.request("GET", path, headers=hdr)
            r = conn.getresponse()
            data = r.read()
            if r.headers.get("Content-Encoding") == "gzip":
                data = gzip.decompress(data)
            if r.headers.get("Connection", "").lower() == "close":
                pool.pop(host, None)
                conn.close()
            return r.status, data
        except (http.client.HTTPException, OSError):
            pool.pop(host, None)
            try:
                conn.close()
            except Exception:
                pass
            if fresh or attempt:
                raise


def sf_get(sess, path):
    if _USE_POOL:
        try:
            status, data = _sf_raw(sess, path)
        except (http.client.HTTPException, OSError) as e:
            raise ApiError(502, f"Cannot reach Salesforce: {e}")
        if status >= 400:
            if status == 401:
                raise ApiError(401, "Salesforce session expired. Please log in again.")
            try:
                j = json.loads(data)
                msg = j[0].get("message") if isinstance(j, list) else str(j)
            except Exception:
                msg = f"Salesforce returned HTTP {status}"
            raise ApiError(status, msg)
        return json.loads(data)
    req = urllib.request.Request(
        sess["instance"] + path,
        headers={
            "Authorization": "Bearer " + sess["sid"],
            "Accept": "application/json",
            "Accept-Encoding": "gzip",
            "Sforce-Query-Options": "batchSize=2000",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=90) as r:
            data = r.read()
            if r.headers.get("Content-Encoding") == "gzip":
                data = gzip.decompress(data)
            return json.loads(data)
    except urllib.error.HTTPError as e:
        if e.code == 401:
            raise ApiError(401, "Salesforce session expired. Please log in again.")
        try:
            j = json.loads(e.read())
            msg = j[0].get("message") if isinstance(j, list) else str(j)
        except Exception:
            msg = f"Salesforce returned HTTP {e.code}"
        raise ApiError(e.code, msg)
    except urllib.error.URLError as e:
        raise ApiError(502, f"Cannot reach Salesforce: {e.reason}")


def _parse_dt(value):
    try:
        d = datetime.fromisoformat(re.sub(r"([+-]\d\d)(\d\d)$", r"\1:\2", value.replace("Z", "+00:00")))
    except (ValueError, AttributeError):
        raise ApiError(400, "Invalid date or time.")
    if d.tzinfo is None:
        d = d.replace(tzinfo=timezone.utc)
    return d.astimezone(timezone.utc)


def sf_datetime(value, plus_days=0):
    """Validate an ISO timestamp from the browser and format it as a SOQL datetime literal (UTC)."""
    d = _parse_dt(value) + timedelta(days=plus_days)
    return d.strftime("%Y-%m-%dT%H:%M:%SZ")


def survey_range(dfrom, dto, all_time):
    """Date condition on the survey record's CreatedDate (= the survey date)."""
    return "" if all_time else f"CreatedDate >= {sf_datetime(dfrom)} AND CreatedDate <= {sf_datetime(dto)}"


def case_where(field, dfrom, dto, all_time, prefix="", survey=None):
    """Date filter (see _case_where) plus: Cancelled and Merged cases are always left out."""
    if field == "survey":       # cases that received a survey response in the range
        obj, link = survey
        rng = survey_range(dfrom, dto, all_time)
        idf = "CaseId" if prefix else "Id"      # prefix is only set when filtering CaseMilestone rows
        base = f"WHERE {idf} IN (SELECT {link} FROM {obj}" + (f" WHERE {rng}" if rng else f" WHERE {link} != null") + ") "
    else:
        base = _case_where(field, dfrom, dto, all_time, prefix)
    ex = ", ".join("'" + x + "'" for x in EXCLUDED_STATUSES)
    cond = f"{prefix}Status NOT IN ({ex}) "
    return f"WHERE ({base[len('WHERE '):].strip()}) AND {cond}" if base else f"WHERE {cond}"


def _case_where(field, dfrom, dto, all_time, prefix=""):
    """WHERE clause selecting cases by created date or by RESOLVED date. A resolved case is one that is in a
    resolved status (not yet auto-closed) or Closed. Auto-closure happens AUTO_CLOSE_DAYS after resolution, so
    the Closed-date window is widened by that many days; exact resolution time is filtered afterwards."""
    if field == "open":     # Group Insights: every unresolved case, whatever its created date
        sts = ", ".join("'" + x.replace("'", "\\'") + "'" for x in RESOLVED_STATUSES)
        return f"WHERE {prefix}IsClosed = false AND {prefix}Status NOT IN ({sts}) "
    if field != "resolved":
        if all_time:
            return ""
        c = prefix + "CreatedDate"
        return f"WHERE {c} >= {sf_datetime(dfrom)} AND {c} <= {sf_datetime(dto)} "
    closed, mod, st = prefix + "ClosedDate", prefix + "LastModifiedDate", prefix + "Status"
    sts = ", ".join("'" + x.replace("'", "\\'") + "'" for x in RESOLVED_STATUSES)
    if all_time:
        return f"WHERE {closed} != null OR {st} IN ({sts}) "
    a, b, bw = sf_datetime(dfrom), sf_datetime(dto), sf_datetime(dto, AUTO_CLOSE_DAYS + 1)
    return (f"WHERE ({closed} >= {a} AND {closed} <= {bw}) "
            f"OR ({st} IN ({sts}) AND {mod} >= {a} AND {mod} <= {b}) ")


def fetch_resolution_times(sess, where, ids=None):
    """CaseId -> latest time the Status became a resolved status (from Case history). {} if unavailable.
    With ids, cases are looked up in batches (needed when the case filter already contains a semi-join)."""
    wanted = {x.lower() for x in RESOLVED_STATUSES}
    base = "SELECT CaseId, NewValue, CreatedDate FROM CaseHistory WHERE Field = 'Status' AND CaseId IN "
    sts = ", ".join("'" + x.replace("'", "\\'") + "'" for x in RESOLVED_STATUSES)
    # only resolved / closed cases can have a resolution time, so open cases are not read from history at all
    queries = ([base + "(" + ", ".join("'" + x + "'" for x in ids[i:i + 300]) + ")" for i in range(0, len(ids), 300)]
               if ids is not None else [base + f"(SELECT Id FROM Case {where}AND (IsClosed = true OR Status IN ({sts})))"])

    def pull(soql):
        part = {}
        res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql))
        while True:
            for r in res.get("records", []):
                if str(r.get("NewValue") or "").lower() in wanted:
                    t = _parse_dt(r["CreatedDate"])
                    if r["CaseId"] not in part or t > part[r["CaseId"]]:
                        part[r["CaseId"]] = t
            if res.get("done") or not res.get("nextRecordsUrl"):
                break
            res = sf_get(sess, res["nextRecordsUrl"])
        return part
    out = {}
    try:
        for part in pmap(pull, queries):
            for k, t in part.items():
                if k not in out or t > out[k]:
                    out[k] = t
    except ApiError as e:
        if e.status == 401:
            raise
        return {}
    return out


def fetch_cases(sess, field, dfrom, dto, all_time=False, csat="", fb="", obj="", full=False):
    col = "ClosedDate" if field == "resolved" else "CreatedDate"
    survey = survey_spec(sess, obj) if field == "survey" else None
    where = case_where(field, dfrom, dto, all_time, "", survey)
    extra = resolve_extra_fields(sess)
    grp = resolve_group(sess)
    fgrp = resolve_first_group(sess)
    agrp = resolve_agent(sess)
    used = {e["path"] for e in extra if e["path"]}
    for g_ in (grp, fgrp, agrp):
        if g_["path"]:
            used.add(g_["path"])
    defs = case_field_defs(sess, used) if full else []     # every other Case field is only loaded on request (much slower)
    try:
        names = {f["name"] for f in _describe(sess, "Case")}
    except ApiError:
        names = set()
    sel_extra = [x for x in dict.fromkeys((csat, fb)) if x and not obj and FIELD_NAME_RE.match(x) and x in names]
    warnings = []

    def run(paths, limit=None):
        soql = (
            "SELECT Id, CaseNumber, Subject, Status, Priority, Origin, Type, Reason, IsClosed, IsEscalated, "
            "CreatedDate, ClosedDate, LastModifiedDate, Account.Name, OwnerId, Owner.Name, Owner.Type"
            + "".join(", " + p for p in dict.fromkeys(paths)) + f" FROM Case {where}ORDER BY {col} DESC" + (f" LIMIT {limit}" if limit else "")
        )
        return sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql))

    xp = [e["path"] for e in extra if e["path"]]
    gp = [grp["path"]] if grp["path"] else []
    fgp = [fgrp["path"]] if fgrp["path"] else []
    agp = [agrp["path"]] if agrp["path"] else []
    raw = [d["name"] for d in defs]
    rels = [d["rel"] for d in defs if d["rel"]]
    def usable(paths):
        """Keep every field the org will accept. One unreadable field must not blank the others, so on an
        error the list is split in halves until the bad fields are isolated."""
        paths = list(dict.fromkeys(paths))
        try:
            run(paths, 1)
            return paths
        except ApiError as e:
            if e.status == 401:
                raise
            if len(paths) <= 1:
                return []
        mid = len(paths) // 2
        return usable(paths[:mid]) + usable(paths[mid:])

    levels = [(xp + gp + fgp + agp + sel_extra + raw + rels, True, True, True),     # everything
              (xp + gp + fgp + agp + sel_extra + raw, True, True, False),           # without related-record names
              (xp + gp + fgp + agp + sel_extra, True, False, False),                # without the "all fields" block
              (sel_extra, False, False, False)]                               # core fields only
    f_rt = pfuture(fetch_resolution_times, sess, where, None) if not survey and field != "open" else None      # same filter as the main query: run together
    res = None
    for i, (paths, ex_ok, defs_ok, rel_ok) in enumerate(levels):
        try:
            res = run(paths)
            break
        except ApiError as e:
            if e.status == 401:
                raise
            last = e.message
            if i == 0:   # isolate the unreadable fields and keep all the others
                good = set(usable(paths))
                bad = [p for p in dict.fromkeys(paths) if p not in good]
                try:
                    res = run([p for p in paths if p in good])
                except ApiError as e2:
                    if e2.status == 401:
                        raise
                    continue
                if bad:
                    warnings.append("Not readable in this org (skipped): " + ", ".join(bad[:8]) + (" …" if len(bad) > 8 else ""))
                xp = [p for p in xp if p in good]
                gp = [p for p in gp if p in good]
                fgp = [p for p in fgp if p in good]
                agp = [p for p in agp if p in good]
                extra = [x if (x["path"] in good) else dict(x, path=None) for x in extra]
                defs = [d for d in defs if d["name"] in good]
                defs = [d if (not d["rel"] or d["rel"] in good) else dict(d, rel=None) for d in defs]
                ex_ok = defs_ok = rel_ok = True
                last = None
                break
            if i == len(levels) - 1:
                raise
    if i > 0 and last:
        warnings.append("Some fields could not be loaded (" + last + "); showing a reduced set.")
    if not ex_ok:
        extra = [{"label": x["label"], "path": None} for x in extra]
        gp = []
        fgp = []
        agp = []
    if not defs_ok:
        defs = []
    if not rel_ok:
        defs = [dict(d, rel=None) for d in defs]
    rows = list(res.get("records", []))
    while not res.get("done") and len(rows) < MAX_ROWS:
        res = sf_get(sess, res["nextRecordsUrl"])
        rows += res.get("records", [])
    f_q = None if gp else pfuture(queue_membership, sess)
    res_times = f_rt.result() if f_rt else ({} if field == "open" else fetch_resolution_times(sess, where, [c["Id"] for c in rows]))
    qmap = {} if gp else f_q.result()
    resolved_set = {x.lower() for x in RESOLVED_STATUSES}
    lo = _parse_dt(dfrom) if (field == "resolved" and not all_time) else None
    hi = _parse_dt(dto) if lo else None
    out = []
    for c in rows:
        # Resolved = in a resolved status, or Closed (auto-closed after AUTO_CLOSE_DAYS days).
        is_resolved = bool(c.get("IsClosed")) or str(c.get("Status") or "").lower() in resolved_set
        rdt = None
        if is_resolved:
            rdt = res_times.get(c["Id"])
            cd = _parse_dt(c["ClosedDate"]) if c.get("ClosedDate") else None
            if rdt is None:     # no history: Closed -> its closed date, otherwise the last modification
                rdt = cd or (_parse_dt(c["LastModifiedDate"]) if c.get("LastModifiedDate") else None)
            elif cd and rdt > cd:
                rdt = cd
        if lo and not (rdt and lo <= rdt <= hi):
            continue
        owner = c.get("Owner") or {}
        otype, oname, oid = owner.get("Type"), owner.get("Name") or "—", c.get("OwnerId") or ""
        # Agent = the user who owns the case. Group = the Case's group field if the org has one,
        # otherwise the queue that owns it, otherwise the queue(s) the owning agent belongs to.
        agent = oname if otype == "User" else "Unassigned"
        av = _dig(c, agp[0]) if agp else None          # the Case's own "Agent" field wins over the owner
        if av not in (None, ""):
            agent = str(plain(av))
        elif agp:
            agent = "Unassigned"
        gv = _dig(c, gp[0]) if gp else None
        if gv not in (None, ""):
            group = str(plain(gv))
        elif otype == "Queue":
            group = oname
        elif otype == "User" and qmap.get(oid):
            group = " / ".join(qmap[oid])
        else:
            group = "No group"
        fv = _dig(c, fgp[0]) if fgp else None
        row = {
            "Id": c["Id"], "CaseNumber": c["CaseNumber"], "Subject": c.get("Subject") or "",
            "Status": c.get("Status") or "—", "Priority": c.get("Priority") or "—",
            "Origin": c.get("Origin") or "—", "Type": c.get("Type") or "—", "Reason": c.get("Reason") or "—",
            "IsClosed": bool(c.get("IsClosed")), "IsEscalated": bool(c.get("IsEscalated")),
            "CreatedDate": c.get("CreatedDate"), "ClosedDate": c.get("ClosedDate"),
            "IsResolved": is_resolved,
            "ResolvedDate": rdt.strftime("%Y-%m-%dT%H:%M:%S.000+0000") if rdt else None,
            "Account": (c.get("Account") or {}).get("Name") or "—",
            "Agent": agent, "Group": group,
            "FirstGroup": str(fv) if fv not in (None, "") else "No first group",
        }
        for e in extra:
            if e["path"]:
                v = plain(_dig(c, e["path"]))
                if isinstance(v, (dict, list)):
                    v = json.dumps(v, ensure_ascii=False)
                row["X:" + e["label"]] = (("Yes" if v else "No") if isinstance(v, bool)
                                         else ("—" if v in (None, "") else v))
        for d in defs:
            v = c.get(d["name"])
            if d["rel"]:
                rv = _dig(c, d["rel"])
                if rv not in (None, ""):
                    v = rv
            v = plain(v)
            if v is None or v == "":
                continue
            row[d["key"]] = ("Yes" if v else "No") if isinstance(v, bool) else v
        if csat in sel_extra:
            row["CSAT"] = c.get(csat)
        if fb in sel_extra:
            row["Feedback"] = plain(c.get(fb))
            if isinstance(row["Feedback"], (dict, list)):
                row["Feedback"] = json.dumps(row["Feedback"], ensure_ascii=False)
        out.append(row)
    if obj:     # survey / feedback kept in a separate custom object that points to the case
        sv = fetch_survey(sess, obj, csat, fb, where, [r["Id"] for r in out], warnings,
                         survey_range(dfrom, dto, all_time) if field == "survey" else None)
        for row in out:
            r = sv.get(row["Id"])
            if r:
                row["CSAT"], row["Feedback"] = r["csat"], r["comment"]
                row["CSATDate"], row["SurveyExtra"] = r["date"], r["extra"]
                if r.get("agent"):
                    row["CSATAgent"] = r["agent"]
    if gp:
        gsrc = f"Group = Case field “{grp['label']}”"
    else:
        gsrc = "Group = owning queue, or the queue the owning agent belongs to (no Group field found on Case; set one in field_map.json as {\"Group\": \"YourField__c\"})"
    return {"cases": out, "totalSize": len(out), "truncated": not res.get("done"),
            "columns": [{"key": "X:" + e["label"], "label": e["label"], "found": bool(e["path"]),
                         "type": e.get("type")} for e in extra],
            "firstGroupFound": bool(fgp),
            "fields": [{"key": d["key"], "label": d["label"], "type": d["type"]} for d in defs],
            "groupSource": gsrc, "warnings": warnings}


# ---------------------------------------------------------------- HTTP layer

# ---------------------------------------------------------------- Case audit & similar-issue search
ID_RE = re.compile(r"^[A-Za-z0-9]{15,18}$")
MAX_BODY = 20000
EMAIL_STATUS = {"0": "New", "1": "Read", "2": "Replied", "3": "Sent", "4": "Forwarded", "5": "Draft"}
FEED_SKIP = {"TrackedChange", "EmailMessageEvent", "CaseCommentEvent", "CreateRecordEvent", "ActivityEvent"}
QUOTE_CUT = re.compile(r"(?im)^\s*(on .{5,160}wrote:|-{2,}\s*original message\s*-{2,}|from:\s.+|_{5,}|sent from my .*|>.*)$")


def soql_str(v):
    return "'" + str(v).replace("\\", "\\\\").replace("'", "\\'") + "'"


def soql_all(sess, soql, cap=5000):
    res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql))
    rows = list(res.get("records", []))
    while not res.get("done") and res.get("nextRecordsUrl") and len(rows) < cap:
        res = sf_get(sess, res["nextRecordsUrl"])
        rows += res.get("records", [])
    return rows


def _norm_txt(v):
    v = html.unescape(_TAG_RE.sub(" ", v or "")) if isinstance(v, str) else ""
    return re.sub(r"[^a-z0-9]+", " ", v.lower().replace("\u2019", "'")).strip()


def is_holding_mail(body):
    """True when the newest message in an e-mail body (quoted history cut off) contains one of HOLDING_PHRASES."""
    full = body if isinstance(body, str) else ""
    top = reply_only(plain(full)) or full
    t = _norm_txt(top)
    return any(_norm_txt(p) in t for p in HOLDING_PHRASES if _norm_txt(p))


def ack_phrase(body):
    """The ACK_PHRASES entry that the newest message of an e-mail body contains (punctuation / case ignored), else ''."""
    full = body if isinstance(body, str) else ""
    t = _norm_txt(reply_only(plain(full)) or full)
    return next((p for p in ACK_PHRASES if _norm_txt(p) and _norm_txt(p) in t), "")


def trim(v, n=MAX_BODY):
    v = plain(v) if isinstance(v, str) else v
    v = "" if v is None else str(v)
    return v if len(v) <= n else v[:n] + " …[truncated]"


def reply_only(text):
    """Latest message of an e-mail thread: cut the quoted history below it."""
    text = text or ""
    m = QUOTE_CUT.search(text)
    head = text[:m.start()].strip() if m else text.strip()
    return head or text.strip()


def _hours(a, b):
    return (b - a).total_seconds() / 3600.0


# ---------------------------------------------------------------- Case audit > add a post / a tag to the case (the only places the app WRITES to Salesforce)
def sf_write(sess, method, path, body):
    """POST / PATCH JSON to Salesforce as the logged-in user (so the post / tag shows that person's name and follows his permissions)."""
    req = urllib.request.Request(sess["instance"] + path, data=json.dumps(body).encode("utf-8"), method=method,
                                 headers={"Authorization": "Bearer " + sess["sid"], "Content-Type": "application/json", "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            raw = r.read()
            return json.loads(raw) if raw else {}
    except urllib.error.HTTPError as e:
        if e.code == 401:
            raise ApiError(401, "Salesforce session expired. Please log in again.")
        try:
            j = json.loads(e.read())
            msg = "; ".join(str(x.get("message")) + (f" [{x.get('errorCode')}" + (f": {', '.join(x.get('fields'))}" if x.get("fields") else "") + "]" if x.get("errorCode") else "")
                            for x in j) if isinstance(j, list) else str(j)
        except Exception:
            msg = f"Salesforce returned HTTP {e.code}"
        raise ApiError(e.code if e.code in (400, 403, 404) else 502, "Salesforce did not accept it: " + msg)
    except urllib.error.URLError as e:
        raise ApiError(502, f"Cannot reach Salesforce: {e.reason}")


def _case_id_ok(case_id):
    cid = str(case_id or "").strip()
    if not (ID_RE.match(cid) and cid.startswith("500")):
        raise ApiError(400, "Invalid case Id.")
    return cid


def audit_tag_options(sess):
    """-> {mode, label, tags: [{id, name, color}], freeText}: every tag the person can pick from for the 'Add tag' drop-down."""
    spec = find_tags(sess)
    tags, free = [], False
    if spec["mode"] == "object" and spec.get("mobj"):
        npath = (spec["name"] or "Name").split(".")[-1]
        cpath = (spec.get("color") or "").split(".")[-1]
        cols = ["Id", npath] + ([cpath] if cpath and cpath != npath else [])
        rows = soql_all(sess, f"SELECT {', '.join(cols)} FROM {spec['mobj']} ORDER BY {npath} LIMIT 2000")
        tags = [{"id": r["Id"], "name": str(r.get(npath) or "(no name)"), "color": (r.get(cpath) if cpath else None) or ""} for r in rows]
    elif spec["mode"] == "object":
        npath = spec["name"] or "Name"
        rows = soql_all(sess, f"SELECT {npath} FROM {spec['obj']} WHERE {npath} != null ORDER BY CreatedDate DESC LIMIT 2000")
        seen = sorted({str(r.get(npath)).strip() for r in rows if r.get(npath)}, key=str.lower)
        tags, free = [{"id": "", "name": n, "color": ""} for n in seen], True
    else:
        fld = next((f for f in sf_get(sess, f"/services/data/v{API}/sobjects/Case/describe").get("fields", []) if f["name"] == spec["field"]), {})
        vals = [p["value"] for p in (fld.get("picklistValues") or []) if p.get("active", True)]
        tags, free = [{"id": "", "name": v, "color": ""} for v in vals], not vals
    return {"mode": spec["mode"], "label": spec.get("label"), "tags": tags, "freeText": free}


def audit_users(sess):
    """Every active Salesforce user (agents), for the @mention list in a post."""
    if "_users" not in sess:
        rows = soql_all(sess, "SELECT Id, Name FROM User WHERE IsActive = true AND UserType = 'Standard' ORDER BY Name LIMIT 5000")
        sess["_users"] = [{"id": r["Id"], "name": r["Name"]} for r in rows if r.get("Name")]
    return sess["_users"]


def audit_add_post(sess, case_id, text, mentions=None):
    cid = _case_id_ok(case_id)
    text = str(text or "").strip()
    if not text:
        raise ApiError(400, "Write the post first.")
    if len(text) > 10000:
        raise ApiError(400, "The post is too long (10,000 characters at most).")
    ment = {}
    for m in (mentions or [])[:25]:
        uid, nm = str((m or {}).get("id") or ""), str((m or {}).get("name") or "").strip()
        if nm and ID_RE.match(uid) and uid.startswith("005") and ("@" + nm) in text:
            ment[nm] = uid
    if not ment:
        r = sf_write(sess, "POST", f"/services/data/v{API}/sobjects/FeedItem", {"ParentId": cid, "Body": text})
        return {"ok": True, "id": r.get("id"), "message": "Post added to the case."}
    # @mentions need the Chatter API: the text is cut into Text / Mention segments
    rx = re.compile("(" + "|".join(re.escape("@" + n) for n in sorted(ment, key=len, reverse=True)) + ")")
    segs = []
    for part in rx.split(text):
        if not part:
            continue
        if part.startswith("@") and part[1:] in ment:
            segs.append({"type": "Mention", "id": ment[part[1:]]})
        else:
            segs.append({"type": "Text", "text": part})
    r = sf_write(sess, "POST", f"/services/data/v{API}/chatter/feed-elements",
                 {"feedElementType": "FeedItem", "subjectId": cid, "body": {"messageSegments": segs}})
    return {"ok": True, "id": r.get("id"), "message": f"Post added to the case ({len(ment)} @mention(s))."}


def audit_add_tag(sess, case_id, tag_id, tag_name):
    cid = _case_id_ok(case_id)
    spec = find_tags(sess)
    tag_id, tag_name = str(tag_id or "").strip(), str(tag_name or "").strip()
    if spec["mode"] == "object":
        obj, flds = spec["obj"], None
        if spec.get("mobj"):
            if not ID_RE.match(tag_id):
                raise ApiError(400, "Select a tag from the list.")
            flds = _describe(sess, obj)
            mf = next((f for f in flds if f.get("relationshipName") == spec["mrel"]), None)
            if not mf:
                raise ApiError(404, "The tag lookup field could not be found on " + obj + ".")
            dup = soql_all(sess, f"SELECT Id FROM {obj} WHERE {spec['caseField']} = {soql_str(cid)} AND {mf['name']} = {soql_str(tag_id)} LIMIT 1")
            if dup:
                raise ApiError(400, "This tag is already on the case.")
            body = {spec["caseField"]: cid, mf["name"]: tag_id}
        else:
            if not tag_name:
                raise ApiError(400, "Select or type a tag.")
            npath = spec["name"] or "Name"
            dup = soql_all(sess, f"SELECT Id FROM {obj} WHERE {spec['caseField']} = {soql_str(cid)} AND {npath} = {soql_str(tag_name)} LIMIT 1")
            if dup:
                raise ApiError(400, "This tag is already on the case.")
            body = {spec["caseField"]: cid, npath: tag_name}
        # many orgs also keep the tagged record on the tag-assignment as plain text ("Record Id", "Object Name" ...): fill those too
        flds = flds or _describe(sess, obj)
        for f in flds:
            n = f["name"]
            lab = _norm(f.get("label")) + " " + _norm(n.replace("__c", ""))
            if n in body or n in TAG_SYS or not f.get("createable") or f.get("type") not in ("string", "textarea"):
                continue
            if re.search(r"(record|related|parent|case|tagged|object|what|source)\s*(record)?\s*(id|identifier)\b|recordid|relatedid|parentid|caseid|whatid", lab) \
                    and "name" not in lab:
                body[n] = cid
            elif re.search(r"(object|sobject)\s*(api)?\s*(name|type)|objectname|objecttype|relatedto|parenttype", lab):
                body[n] = "Case"
        try:
            r = sf_write(sess, "POST", f"/services/data/v{API}/sobjects/{obj}", body)
        except ApiError as e:
            raise ApiError(e.status, f"{e.message}  (object {obj}, fields sent: {', '.join(f'{k}={str(v)[:18]}' for k, v in body.items())})")
        return {"ok": True, "id": r.get("id"), "message": "Tag added to the case."}
    if not tag_name:
        raise ApiError(400, "Select or type a tag.")
    fld = spec["field"]
    cur = str((soql_all(sess, f"SELECT {fld} FROM Case WHERE Id = {soql_str(cid)} LIMIT 1") or [{}])[0].get(fld) or "").strip()
    have = [t.strip().lower() for t in re.split(r"[;,]", cur) if t.strip()]
    if tag_name.lower() in have:
        raise ApiError(400, "This tag is already on the case.")
    ftype = next((f.get("type") for f in _describe(sess, "Case") if f["name"] == fld), "string")
    sep = ";" if (ftype == "multipicklist" or ";" in cur) else ", "
    new = tag_name if ftype == "picklist" else (cur + sep + tag_name if cur else tag_name)
    sf_write(sess, "PATCH", f"/services/data/v{API}/sobjects/Case/{cid}", {fld: new})
    return {"ok": True, "message": "Tag added to the case."}


# ---------------------------------------------------------------- Case audit > attachments (files on posts, e-mails and the case) with a preview link
PREVIEW_EXT = {"pdf": "application/pdf", "png": "image/png", "jpg": "image/jpeg", "jpeg": "image/jpeg", "gif": "image/gif",
               "webp": "image/webp", "txt": "text/plain", "csv": "text/plain", "log": "text/plain"}
FILE_MAX = 30_000_000


def attach_files(sess, cid, ev, notes):
    """Puts e["files"] = [{kind: 'cv' (Salesforce File) | 'att' (old Attachment), id, name, ext, docId, size}] on the e-mail / post events that have files."""
    by_id = {e["id"]: e for e in ev if e.get("id")}
    post_ids = [i for i, e in by_id.items() if e["kind"] == "Post"]
    mail_ids = [i for i, e in by_id.items() if e["kind"] == "Email"]
    found = []          # (entity id, kind, file id, name, ext, docId)

    def run(label, ids, tmpl, fn):
        for k in range(0, len(ids), 150):
            q = tmpl.format(ids=", ".join(soql_str(i) for i in ids[k:k + 150]))
            try:
                for r in soql_all(sess, q):
                    fn(r)
            except ApiError as e:
                if e.status == 401:
                    raise
                notes.append(f"{label} could not be read ({e.message[:120]}).")
                break

    run("Post attachments", post_ids, "SELECT FeedEntityId, RecordId, Title FROM FeedAttachment WHERE FeedEntityId IN ({ids})",
        lambda r: found.append((r["FeedEntityId"], "cv", r["RecordId"], r.get("Title") or "", "", "")) if str(r.get("RecordId") or "").startswith("068") else None)
    run("Files", mail_ids + [cid], "SELECT LinkedEntityId, ContentDocumentId, ContentDocument.Title, ContentDocument.FileExtension, ContentDocument.LatestPublishedVersionId "
        "FROM ContentDocumentLink WHERE LinkedEntityId IN ({ids})",
        lambda r: found.append((r["LinkedEntityId"], "cv", (r.get("ContentDocument") or {}).get("LatestPublishedVersionId"),
                                (r.get("ContentDocument") or {}).get("Title") or "", (r.get("ContentDocument") or {}).get("FileExtension") or "", r.get("ContentDocumentId") or "")))
    run("E-mail attachments", mail_ids + [cid], "SELECT Id, ParentId, Name FROM Attachment WHERE ParentId IN ({ids})",
        lambda r: found.append((r["ParentId"], "att", r["Id"], r.get("Name") or "", (r.get("Name") or "").rsplit(".", 1)[-1] if "." in (r.get("Name") or "") else "", "")))
    if not found:
        return
    meta = {}
    cv_ids = sorted({f[2] for f in found if f[1] == "cv" and f[2]})
    run("File details", cv_ids, "SELECT Id, ContentDocumentId, Title, FileExtension, ContentSize FROM ContentVersion WHERE Id IN ({ids})",
        lambda r: meta.__setitem__(r["Id"], r))
    on_events = {f[2] for f in found if f[0] != cid}            # a file already shown on a post / e-mail is not repeated at case level
    first_case = next((e for e in ev if e["kind"] == "Case"), None)
    for ent, kind, fid, name, ext, doc in found:
        if not fid:
            continue
        e = first_case if ent == cid else by_id.get(ent)
        if e is None or (ent == cid and fid in on_events):
            continue
        m = meta.get(fid) or {}
        name, ext, doc = m.get("Title") or name, (m.get("FileExtension") or ext or "").lower(), m.get("ContentDocumentId") or doc
        full = name if (not ext or name.lower().endswith("." + ext)) else f"{name}.{ext}"
        if not any(x["id"] == fid for x in e["files"]):
            e["files"].append({"kind": kind, "id": fid, "name": full or "(file)", "ext": ext, "docId": doc, "size": m.get("ContentSize")})


def audit_file(sess, kind, fid):
    """-> (bytes, file name, content type, inline?) of one attachment, fetched with the person's own Salesforce session."""
    fid = str(fid or "").strip()
    if not ID_RE.match(fid) or not ((kind == "cv" and fid.startswith("068")) or (kind == "att" and fid.startswith("00P"))):
        raise ApiError(400, "Invalid file.")
    if kind == "cv":
        row = (soql_all(sess, f"SELECT Title, FileExtension, ContentSize FROM ContentVersion WHERE Id = {soql_str(fid)}") or [None])[0]
        path = f"/services/data/v{API}/sobjects/ContentVersion/{fid}/VersionData"
        name, ext, size = (row or {}).get("Title") or "file", ((row or {}).get("FileExtension") or "").lower(), (row or {}).get("ContentSize") or 0
    else:
        row = (soql_all(sess, f"SELECT Name, BodyLength FROM Attachment WHERE Id = {soql_str(fid)}") or [None])[0]
        path = f"/services/data/v{API}/sobjects/Attachment/{fid}/Body"
        name, size = (row or {}).get("Name") or "file", (row or {}).get("BodyLength") or 0
        ext = name.rsplit(".", 1)[-1].lower() if "." in name else ""
    if not row:
        raise ApiError(404, "The file was not found (or you do not have access to it).")
    if size and size > FILE_MAX:
        raise ApiError(413, "This file is too large to open here (over 30 MB). Open it in Salesforce.")
    req = urllib.request.Request(sess["instance"] + path, headers={"Authorization": "Bearer " + sess["sid"]})
    try:
        with urllib.request.urlopen(req, timeout=120) as r:
            data = r.read(FILE_MAX + 1)
    except urllib.error.HTTPError as e:
        raise ApiError(401 if e.code == 401 else 502, "Salesforce session expired. Please log in again." if e.code == 401 else f"Salesforce could not give the file (HTTP {e.code}).")
    except urllib.error.URLError as e:
        raise ApiError(502, f"Cannot reach Salesforce: {e.reason}")
    if len(data) > FILE_MAX:
        raise ApiError(413, "This file is too large to open here (over 30 MB). Open it in Salesforce.")
    full = name if (not ext or name.lower().endswith("." + ext)) else f"{name}.{ext}"
    return data, full, PREVIEW_EXT.get(ext, "application/octet-stream"), ext in PREVIEW_EXT


def find_case(sess, term):
    term = (term or "").strip()
    if ID_RE.match(term) and term.startswith("500"):
        cond = "Id = " + soql_str(term)
    elif re.match(r"^[0-9]{1,10}$", term):
        cond = "CaseNumber IN (" + soql_str(term) + ", " + soql_str(term.zfill(8)) + ")"
    else:
        raise ApiError(400, "Enter a case number (for example 00166097) or a 15/18-character case Id.")
    rows = soql_all(sess, "SELECT Id, CaseNumber, Subject, Description, Status, Priority, Origin, Type, Reason, IsClosed, "
                          "IsEscalated, CreatedDate, ClosedDate, LastModifiedDate, SuppliedEmail, Account.Name, Contact.Name, "
                          "Owner.Name, CreatedBy.Name FROM Case WHERE " + cond + " LIMIT 1")
    if not rows:
        raise ApiError(404, f"Case {term} was not found in Salesforce (or you do not have access to it).")
    return rows[0]


# Fields shown under "Case analysis" in Case audit, in this order: (label, other accepted labels). Looked up by label on the Case object
# (then on the Account); a field that cannot be found shows as "—". Override a label with its API name in field_map.json if needed.
AUDIT_FIELDS = [
    ("Application", []), ("Application Module", []), ("Type", []), ("Type - Module", []), ("Type - SubModule", []),
    ("Helpdesk Focus Area", []), ("Helpdesk Focus Area - Module", []), ("Resolution Type", []), ("Size", ["Case Size"]),
    ("Total Hours", ["Total Hrs", "Total Hours Spent"]), ("Subject (Internal)", ["Internal Subject"]),
    ("Support Expiry", ["Support Expiry Date", "Support Expiration Date", "Support Expiration"]),
]


def audit_fields(sess, c):
    """-> ([{label, value, found}], [notes]) for the Case-audit field panel."""
    notes, found = [], []
    try:
        case_f = _describe(sess, "Case")
    except ApiError as e:
        if e.status == 401:
            raise
        case_f = []
    try:
        acct_f = _describe(sess, "Account")
    except ApiError as e:
        if e.status == 401:
            raise
        acct_f = []
    ci = {}
    for f in case_f:
        ci.setdefault(_norm(f.get("label")), f)
    ai = {}
    for f in acct_f:
        ai.setdefault(_norm(f.get("label")), f)
    ov = _overrides()
    for label, alts in AUDIT_FIELDS:
        if label == "Type":
            found.append({"label": label, "path": "Type", "std": True})
            continue
        path = ov.get(label)
        if not path:
            keys = [_norm(x) for x in [label] + alts]
            f = next((ci[k] for k in keys if k in ci), None)
            if f:
                path = _select_path("", f)
            else:
                f = next((ai[k] for k in keys if k in ai), None)
                if f:
                    path = _select_path("Account.", f)
        found.append({"label": label, "path": path})
    vals = {}
    paths = [x["path"] for x in found if x["path"] and not x.get("std") and FIELD_NAME_RE.match(x["path"].replace(".", "_"))]
    if paths:
        try:
            rows = soql_all(sess, f"SELECT {', '.join(dict.fromkeys(paths))} FROM Case WHERE Id = {soql_str(c['Id'])}")
            rec = rows[0] if rows else {}
            for p in paths:
                vals[p] = _dig(rec, p)
        except ApiError as e:
            if e.status == 401:
                raise
            for p in paths:         # one unreadable field (no access) must not hide the others
                try:
                    rows = soql_all(sess, f"SELECT {p} FROM Case WHERE Id = {soql_str(c['Id'])}")
                    vals[p] = _dig(rows[0], p) if rows else None
                except ApiError as e2:
                    if e2.status == 401:
                        raise
                    notes.append(f"{p} could not be read ({e2.message[:80]}).")
    out = []
    for x in found:
        v = c.get("Type") if x.get("std") else (vals.get(x["path"]) if x["path"] else None)
        out.append({"label": x["label"], "value": "" if v is None else (("Yes" if v else "No") if isinstance(v, bool) else str(v)),
                    "found": bool(x["path"])})
    missing = [o["label"] for o in out if not o["found"]]
    if missing:
        notes.append("Not found on the Case / Account object: " + ", ".join(missing) + " (add their API names to field_map.json to show them).")
    return out, notes


def audit_case(sess, term, paused_txt=""):
    c = find_case(sess, term)
    cid, ev, notes = c["Id"], [], []

    def add(kind, time, title, who="", direction="", body="", meta=None, holding=False, rid="", ack=""):
        if time:
            ev.append({"time": time, "kind": kind, "title": title, "who": who or "", "direction": direction,
                       "body": trim(body), "meta": meta or {}, "holding": bool(holding), "ack": ack or "", "id": rid or "", "files": []})

    def src(name, queries, fn):
        last = None
        for q in queries:
            try:
                for r in soql_all(sess, q):
                    fn(r)
                return
            except ApiError as e:
                if e.status == 401:
                    raise
                last = e
        notes.append(f"{name} could not be read ({last.message[:160]}).")

    add("Case", c.get("CreatedDate"), "Case created: " + (c.get("Subject") or ""), (c.get("CreatedBy") or {}).get("Name"),
        body=c.get("Description"), meta={"Origin": c.get("Origin"), "Priority": c.get("Priority"), "Type": c.get("Type")})

    def email(r):
        body = r.get("TextBody") or r.get("HtmlBody") or ""
        inc = bool(r.get("Incoming"))
        add("Email", r.get("MessageDate"), r.get("Subject") or "(no subject)", r.get("FromName") or r.get("FromAddress"),
            "Inbound" if inc else "Outbound", body,
            {"From": r.get("FromAddress"), "To": r.get("ToAddress"), "Cc": r.get("CcAddress"), "Bcc": r.get("BccAddress"),
             "Status": EMAIL_STATUS.get(str(r.get("Status")), r.get("Status")), "Attachment": "Yes" if r.get("HasAttachment") else ""},
            holding=(not inc) and is_holding_mail(body), rid=r.get("Id"), ack=("" if inc else ack_phrase(body)))
    src("E-mails", [
        "SELECT Id, Subject, FromAddress, FromName, ToAddress, CcAddress, BccAddress, MessageDate, Incoming, Status, HasAttachment, "
        f"TextBody, HtmlBody FROM EmailMessage WHERE ParentId = {soql_str(cid)} ORDER BY MessageDate ASC",
        f"SELECT Id, Subject, FromAddress, FromName, ToAddress, MessageDate, Incoming, TextBody FROM EmailMessage WHERE ParentId = {soql_str(cid)}"], email)

    def post(r):
        if r.get("Type") in FEED_SKIP:
            return
        add("Post", r.get("CreatedDate"), r.get("Title") or "Post (" + str(r.get("Type")) + ")", (r.get("CreatedBy") or {}).get("Name"),
            body=rich_text(r.get("Body")), meta={"Type": r.get("Type"), "Visibility": r.get("Visibility")}, rid=r.get("Id"))
    src("Posts", [f"SELECT Id, Type, Body, Title, CreatedDate, Visibility, CreatedBy.Name FROM CaseFeed WHERE ParentId = {soql_str(cid)} ORDER BY CreatedDate ASC"], post)
    src("Post comments", [f"SELECT Id, CommentBody, CreatedDate, CreatedBy.Name FROM FeedComment WHERE ParentId = {soql_str(cid)} ORDER BY CreatedDate ASC"],
        lambda r: add("Post", r.get("CreatedDate"), "Comment on a post", (r.get("CreatedBy") or {}).get("Name"), body=rich_text(r.get("CommentBody")),
                      meta={"Type": "FeedComment"}))
    src("Case comments", [f"SELECT Id, CommentBody, IsPublished, CreatedDate, CreatedBy.Name FROM CaseComment WHERE ParentId = {soql_str(cid)} ORDER BY CreatedDate ASC"],
        lambda r: add("Comment", r.get("CreatedDate"), "Case comment (" + ("public" if r.get("IsPublished") else "internal") + ")",
                      (r.get("CreatedBy") or {}).get("Name"), body=r.get("CommentBody"), meta={"Visibility": "Public" if r.get("IsPublished") else "Internal"}))

    def task(r):
        add("Activity", r.get("CreatedDate"), "Task: " + (r.get("Subject") or ""), (r.get("Owner") or {}).get("Name"), body=r.get("Description"),
            meta={"Status": r.get("Status"), "Priority": r.get("Priority"), "Subtype": r.get("TaskSubtype") or r.get("Type"), "Due": r.get("ActivityDate")})
    src("Tasks", [f"SELECT Id, Subject, Status, Priority, TaskSubtype, Type, ActivityDate, CreatedDate, Description, Owner.Name FROM Task WHERE WhatId = {soql_str(cid)} ORDER BY CreatedDate ASC",
                  f"SELECT Id, Subject, Status, Priority, ActivityDate, CreatedDate, Description, Owner.Name FROM Task WHERE WhatId = {soql_str(cid)}"], task)
    src("Events", [f"SELECT Id, Subject, StartDateTime, EndDateTime, Location, Description, CreatedDate, Owner.Name FROM Event WHERE WhatId = {soql_str(cid)} ORDER BY StartDateTime ASC"],
        lambda r: add("Activity", r.get("StartDateTime") or r.get("CreatedDate"), "Event: " + (r.get("Subject") or ""), (r.get("Owner") or {}).get("Name"),
                      body=r.get("Description"), meta={"Subtype": "Event", "Ends": r.get("EndDateTime"), "Location": r.get("Location")}))

    hist = []

    def history(r):
        hist.append(r)
        fld = r.get("Field")
        if fld == "created":
            return
        ov, nv = r.get("OldValue"), r.get("NewValue")
        if isinstance(ov, str) and ID_RE.match(ov) and isinstance(nv, str) and ID_RE.match(nv):
            return          # raw Id pair (duplicate of the readable owner row)
        add("History", r.get("CreatedDate"), f"{fld} changed", (r.get("CreatedBy") or {}).get("Name"),
            body=f"{'' if ov in (None, '') else ov}  →  {'' if nv in (None, '') else nv}", meta={"Field": fld, "From": ov, "To": nv})
    src("Field history", [f"SELECT Field, OldValue, NewValue, CreatedDate, CreatedById, CreatedBy.Name FROM CaseHistory WHERE CaseId = {soql_str(cid)} ORDER BY CreatedDate ASC",
                          f"SELECT Field, OldValue, NewValue, CreatedDate, CreatedBy.Name FROM CaseHistory WHERE CaseId = {soql_str(cid)} ORDER BY CreatedDate ASC"], history)
    # who made each status change: customer (portal / site / community / guest user) or agent - looked up on the User record itself
    uids = sorted({h.get("CreatedById") for h in hist if h.get("Field") == "Status" and h.get("CreatedById")})
    if uids:
        info = {}
        inlist = ", ".join(soql_str(u) for u in uids[:100])
        for q in (f"SELECT Id, UserType, Profile.Name, ContactId FROM User WHERE Id IN ({inlist})", f"SELECT Id, UserType FROM User WHERE Id IN ({inlist})"):
            try:
                info = {u["Id"]: u for u in soql_all(sess, q)}
                break
            except ApiError as e:
                if e.status == 401:
                    raise
        for h in hist:
            u = info.get(h.get("CreatedById"))
            if u:
                h["CreatedBy"] = {**(h.get("CreatedBy") or {}), "UserType": u.get("UserType"), "Profile": u.get("Profile"), "ContactId": u.get("ContactId")}

    if c.get("ClosedDate"):
        add("Case", c["ClosedDate"], "Case closed", body="Status: " + str(c.get("Status")))

    attach_files(sess, cid, ev, notes)
    ev.sort(key=lambda e: _parse_dt(e["time"]))
    analysis = analyse_case(c, ev, hist)
    gj = None
    try:
        if analysis["resolvedAt"]:
            end_dt, end_label = _parse_dt(analysis["resolvedAt"]), "resolution"
        else:
            end_dt, end_label = datetime.now(timezone.utc), "now (case still open)"
        gj, gnotes = group_journey(sess, c, end_dt, end_label)
        notes.extend(n for n in gnotes if n not in notes and "labelled" not in n)   # agent-field hint isn't relevant here
        if gj and len(gj["groups"]) > 1:
            top = max(gj["groups"], key=lambda g: g["hours"])
            analysis["observations"].append(
                f"Case moved through {len(gj['groups'])} groups ({' → '.join(x['group'] for x in gj['path'])}); "
                f"longest in {top['group']} ({top['hours'] / 24:.1f} days, {top['pct']:.0f}% of its age).")
    except ApiError as e:
        if e.status == 401:
            raise
        notes.append("Group-wise age could not be calculated: " + e.message[:160])
    gsegs = gj.pop("segments", None) if gj else None          # per-agent segments: used below, not sent to the browser
    analysis["groupAge"] = gj
    try:
        nr = no_response_check(sess, c, ev, hist, analysis, gsegs, paused_txt)
        analysis["noResponse"] = nr
        if nr:
            analysis["observations"].append(nr["summary"])
    except ApiError as e:
        if e.status == 401:
            raise
        notes.append("Agent-response check could not be completed: " + e.message[:160])
    try:
        extra, enotes = audit_fields(sess, c)
        notes.extend(enotes)
    except ApiError as e:
        if e.status == 401:
            raise
        extra = []
        notes.append("Case fields could not be read: " + e.message[:160])
    return {"fields": extra, "case": {k: (c.get(k) if k not in ("Account", "Contact", "Owner", "CreatedBy") else (c.get(k) or {}).get("Name"))
                     for k in ("Id", "CaseNumber", "Subject", "Description", "Status", "Priority", "Origin", "Type", "Reason", "IsClosed",
                               "IsEscalated", "CreatedDate", "ClosedDate", "LastModifiedDate", "SuppliedEmail", "Account", "Contact", "Owner", "CreatedBy")},
            "events": ev, "analysis": analysis, "notes": notes}


def _iso_z(dt):
    return dt.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def no_response_check(sess, c, ev, hist, analysis, segs, paused_txt=""):
    """Case audit > Case analysis: a case is on OUR side from creation until it is resolved / closed. Pending and Waiting on
    Third Party are NOT excluded - only the time after resolution is. However short or long that is (no minimum), list every day it
    was with us where the assigned agent was working (recorded activity on OTHER cases that day) but no outbound e-mail was
    sent on THIS case (comments, public or internal, do not count as a response). When the agent failed to respond on several
    days, ALL of those days are listed.
    -> None, or {holdDays, minDays, checked, paused, days: [...], flagged, flaggedDays, summary}."""
    created = _parse_dt(c["CreatedDate"])
    end = _parse_dt(analysis["resolvedAt"]) if analysis.get("resolvedAt") else datetime.now(timezone.utc)
    if end <= created:
        return None
    paused = []        # Pending / Waiting on Third Party are no longer left out here (paused_txt is ignored): only time after resolution is excluded
    skip = {x.lower() for x in RESOLVED_STATUSES} | {"closed"}
    srows = sorted(((_parse_dt(h["CreatedDate"]), h.get("OldValue"), h.get("NewValue")) for h in hist if h.get("Field") == "Status"),
                   key=lambda x: x[0])
    if srows:
        first = srows[0][1]
        cur = first if isinstance(first, str) and first else "New"
    else:
        cur = c.get("Status") or ""
    pts = [(created, cur)] + [(t, n if isinstance(n, str) else "") for t, _o, n in srows if created < t < end]
    ours, ours_st = [], []                                 # intervals where the case was on our side (and the status in each)
    for i, (t, st) in enumerate(pts):
        nxt = pts[i + 1][0] if i + 1 < len(pts) else end
        if nxt > t and st.strip().lower() not in skip:
            ours.append((t, nxt))
            ours_st.append((t, nxt, st.strip() or "Open"))      # the status the case had (Open / Pending / Waiting on Third Party ...)
    hold_h = sum(_hours(a, b) for a, b in ours)
    out = {"holdDays": hold_h / 24, "minDays": HOLD_DAYS_MIN, "checked": False, "paused": paused, "days": [], "flagged": 0}
    info = f"Case was on our side (creation until resolution, including Pending / Waiting on Third Party) for {hold_h / 24:.1f} days."
    out["checked"] = True          # every case is checked, however quickly it was resolved (no minimum number of days)

    def overlap(a, b, x, y):
        return max(0.0, (min(b, y) - max(a, x)).total_seconds() / 3600.0)
    if not segs:
        segs = [{"agent": (c.get("Owner") or {}).get("Name") or "Unassigned", "start": created.isoformat(), "end": end.isoformat()}]
    sg = [(_parse_dt(x["start"]), _parse_dt(x["end"]), x.get("agent") or "Unassigned") for x in segs]
    resp = [(_parse_dt(e["time"]), e.get("who") or "") for e in ev           # only outbound e-mails count as a response (no comments)
            if e["kind"] == "Email" and e["direction"] == "Outbound" and not e.get("holding")]      # ...and not a standard holding / acknowledgement mail
    held = [_parse_dt(e["time"]) for e in ev if e["kind"] == "Email" and e["direction"] == "Outbound" and e.get("holding")]
    d, last, days = created.astimezone().date(), end.astimezone().date(), []
    while d <= last:
        d0 = datetime.combine(d, datetime.min.time()).astimezone(timezone.utc)
        d1 = datetime.combine(d + timedelta(days=1), datetime.min.time()).astimezone(timezone.utc)
        oh = sum(overlap(a, b, d0, d1) for a, b in ours)
        if oh >= HOLD_DAY_MIN_HOURS:
            per = {}
            for a, b in ours:
                for x, y, ag in sg:
                    h = overlap(max(a, x), min(b, y), d0, d1)
                    if h > 0:
                        per[ag] = per.get(ag, 0.0) + h
            sth = {}
            for a, b, st in ours_st:
                h = overlap(a, b, d0, d1)
                if h > 0:
                    sth[st] = sth.get(st, 0.0) + h
            agents = sorted(per, key=lambda k: -per[k])
            real = [a for a in agents if a != "Unassigned"]
            got = [w for t, w in resp if d0 <= t < d1]
            days.append({"date": d.isoformat(), "label": f"{d:%a %d %b %Y}", "ourHours": round(oh, 1),
                         "agent": (real[0] if real and per[real[0]] >= per.get("Unassigned", 0) else "Unassigned"),
                         "status": max(sth, key=sth.get) if sth else "",
                         "agents": real, "responded": bool(got), "respondedBy": ", ".join(dict.fromkeys(w for w in got if w)),
                         "otherCases": 0, "verdict": "", "holdingMails": sum(1 for t in held if d0 <= t < d1)})
        d += timedelta(days=1)
    cand = [x for x in days if not x["responded"] and x["agent"] != "Unassigned"]
    activity, checked_src = {}, []
    if cand:
        names = sorted({a for x in cand for a in x["agents"]})
        id2name = {}
        for i in range(0, len(names), 100):
            try:
                for u in soql_all(sess, "SELECT Id, Name FROM User WHERE Name IN (" + ", ".join(soql_str(n) for n in names[i:i + 100]) + ")"):
                    id2name[u["Id"]] = u["Name"]
            except ApiError as e:
                if e.status == 401:
                    raise
        if id2name:
            lo = min(datetime.fromisoformat(x["date"]) for x in cand)
            hi = max(datetime.fromisoformat(x["date"]) for x in cand) + timedelta(days=1)
            lo, hi = _iso_z(lo.astimezone()), _iso_z(hi.astimezone())
            idq, cid = ", ".join(soql_str(i) for i in id2name), soql_str(c["Id"])
            for label, q, ck, tk in (
                    ("case history", f"SELECT CaseId, CreatedById, CreatedDate FROM CaseHistory WHERE CreatedById IN ({idq}) AND CreatedDate >= {lo} AND CreatedDate < {hi} AND CaseId != {cid}", "CaseId", "CreatedDate"),
                    ("case comments", f"SELECT ParentId, CreatedById, CreatedDate FROM CaseComment WHERE CreatedById IN ({idq}) AND CreatedDate >= {lo} AND CreatedDate < {hi} AND ParentId != {cid}", "ParentId", "CreatedDate"),
                    ("e-mails", f"SELECT ParentId, CreatedById, MessageDate FROM EmailMessage WHERE CreatedById IN ({idq}) AND MessageDate >= {lo} AND MessageDate < {hi} AND ParentId != {cid}", "ParentId", "MessageDate")):
                try:
                    for r in soql_all(sess, q, cap=30000):
                        k = r.get(ck)
                        if not k or not str(k).startswith("500") or not r.get(tk):
                            continue
                        activity.setdefault((id2name.get(r["CreatedById"]), _parse_dt(r[tk]).astimezone().date().isoformat()), set()).add(k)
                    checked_src.append(label)
                except ApiError as e:
                    if e.status == 401:
                        raise
    for x in days:
        if x["responded"]:
            x["verdict"] = "Responded to the customer"
            continue
        hm = " – only a standard acknowledgement e-mail was sent" if x.get("holdingMails") else ""
        if x["agent"] == "Unassigned":
            x["verdict"] = "No agent assigned" + hm
        else:
            n = len({k for a in x["agents"] for k in activity.get((a, x["date"]), ())})
            x["otherCases"] = n
            x["verdict"] = (f"NO RESPONSE – agent worked on {n} other case(s)" + hm if n else
                            ("No response – no agent activity recorded this day (leave / off?)" if checked_src else
                             "No response – agent activity could not be checked") + hm)
    flagged = [x for x in days if x["verdict"].startswith("NO RESPONSE")]
    out["days"], out["flagged"], out["sources"] = days, len(flagged), checked_src
    out["flaggedDays"] = [x["date"] for x in flagged]
    if flagged:
        shown = "; ".join(f"{x['label']} ({x['agent']}, {x['otherCases']} other case(s))" for x in flagged)      # every day, not a shortened list
        out["summary"] = (info + f" On {len(flagged)} of {len(days)} such days the assigned agent was working on other cases but sent no "
                          f"outbound e-mail on this case: {shown}.")
    else:
        out["summary"] = (info + f" On none of the {len(days)} days it was with us was there a day where the assigned agent was active on other cases "
                          "and yet sent no outbound e-mail here.")
    return out


def group_journey(sess, c, end_dt, end_label):
    """Time the case spent in each support group (a case can leave a group and come back), rebuilt from Owner / Group
    field history. -> {groups: [{group, hours, pct, visits}], path: [{group, start, end, hours, agents}], ...} or None."""
    gpath = (resolve_group(sess) or {}).get("path")
    cur_group = ""
    if gpath:
        try:
            rows = soql_all(sess, f"SELECT {gpath} FROM Case WHERE Id = {soql_str(c['Id'])}")
            cur_group = str(_dig(rows[0], gpath) or "") if rows else ""
        except ApiError as e:
            if e.status == 401:
                raise
    r = ownership_times(sess, [{"id": c["Id"], "agent": (c.get("Owner") or {}).get("Name") or "Unassigned",
                                "group": cur_group or "No group", "created": c["CreatedDate"],
                                "resolved": end_dt.isoformat()}], with_segments=True)
    one = (r["cases"] or {}).get(c["Id"])
    if not one:
        return None, r["notes"]
    stints = []
    for sg in one["segments"]:
        if stints and stints[-1]["group"] == sg["group"]:       # same group again straight away: one stay
            st = stints[-1]
            st["end"], st["hours"] = sg["end"], st["hours"] + sg["hours"]
            if sg["agent"] not in st["agents"]:
                st["agents"].append(sg["agent"])
        else:
            stints.append({"group": sg["group"], "start": sg["start"], "end": sg["end"], "hours": sg["hours"], "agents": [sg["agent"]]})
    total = sum(x["hours"] for x in stints) or 1.0
    groups = {}
    for st in stints:
        g = groups.setdefault(st["group"], {"group": st["group"], "hours": 0.0, "visits": 0})
        g["hours"] += st["hours"]
        g["visits"] += 1
    for g in groups.values():
        g["pct"] = g["hours"] / total * 100
    return {"endLabel": end_label, "totalHours": one["hours"], "groups": list(groups.values()), "path": stints,
            "groupHistory": r["groupHistory"], "segments": one["segments"]}, r["notes"]


def analyse_case(c, ev, hist):
    created = _parse_dt(c["CreatedDate"])
    closed = _parse_dt(c["ClosedDate"]) if c.get("ClosedDate") else None
    now = datetime.now(timezone.utc)
    kinds = {}
    for e in ev:
        kinds[e["kind"]] = kinds.get(e["kind"], 0) + 1
    inbound = [e for e in ev if e["kind"] == "Email" and e["direction"] == "Inbound"]
    outbound = [e for e in ev if e["kind"] == "Email" and e["direction"] == "Outbound"]
    public = [e for e in ev if e["kind"] == "Comment" and e["meta"].get("Visibility") == "Public"]
    real_out = [e for e in outbound if not e.get("holding")]       # standard acknowledgement mails are not a real response
    resp = sorted([e for e in real_out if _parse_dt(e["time"]) >= created], key=lambda e: _parse_dt(e["time"]))      # response = outbound e-mail only
    first_resp = _hours(created, _parse_dt(resp[0]["time"])) if resp else None
    wanted = {x.lower() for x in RESOLVED_STATUSES}
    status_rows = [h for h in hist if h.get("Field") == "Status"]
    res_rows = [h for h in status_rows if str(h.get("NewValue") or "").lower() in wanted]
    # Age rule: a case that is resolved / closed NOW ages from creation to its resolution time; any other case
    # (including one that was resolved earlier and then re-opened) ages from creation to the current time.
    is_resolved = bool(c.get("IsClosed")) or str(c.get("Status") or "").lower() in wanted
    resolved_at = None
    if is_resolved:
        resolved_at = _parse_dt(res_rows[-1]["CreatedDate"]) if res_rows else None
        if closed and (resolved_at is None or resolved_at > closed):
            resolved_at = closed                       # Closed = auto-closed after resolution; never later than the close
        if resolved_at is None and c.get("LastModifiedDate"):
            resolved_at = _parse_dt(c["LastModifiedDate"])
    resolved_by = None
    if is_resolved:      # who moved the case to Resolved (or, when it went straight to Closed, who closed it)
        by_rows = res_rows or [h for h in status_rows if str(h.get("NewValue") or "").lower() == "closed"]
        cb = (by_rows[-1].get("CreatedBy") or {}) if by_rows else {}
        resolved_by = cb.get("Name")
        utype, prof = str(cb.get("UserType") or ""), str((cb.get("Profile") or {}).get("Name") or "")
        contact = str((c.get("Contact") or {}).get("Name") or "").strip().lower()
        # a customer is a portal / site / guest user (not a Standard Salesforce user), or the case contact himself; anything else is an agent
        customer = bool(resolved_by) and ((utype not in ("", "Standard") or bool(cb.get("ContactId"))) or bool(re.search(r"customer|guest|portal|community|external|site", prof, re.I))
                                          or (contact and resolved_by.strip().lower() == contact))
        if customer:
            resolved_by = f"{resolved_by} (Customer)"
    reopened = sum(1 for h in status_rows if str(h.get("OldValue") or "").lower() in wanted | {"closed"}
                   and str(h.get("NewValue") or "").lower() not in wanted | {"closed"})
    owner_changes = sum(1 for h in hist if h.get("Field") == "Owner" and not ID_RE.match(str(h.get("NewValue") or "")))
    end = resolved_at                                  # None while the case is open: age runs to now
    t = [_parse_dt(e["time"]) for e in ev]
    tg = [x for x in t if resolved_at is None or x <= resolved_at]      # silence is measured up to the resolution only; later events (auto-close, customer reply) are not part of it
    gap = max(((_hours(a, b), a, b) for a, b in zip(tg, tg[1:])), default=None)
    obs = []
    obs.append("First agent response (outbound e-mail) came after "
               + (f"{first_resp:.1f} hours." if first_resp is not None else "— none was found."))
    if not outbound:
        obs.append("No outbound e-mail is recorded on this case.")
    elif len(real_out) < len(outbound):
        obs.append(f"{len(outbound) - len(real_out)} outbound e-mail(s) are only a standard acknowledgement (e.g. “We regret for the inconvenience caused”) and are not counted as a response.")
    if resolved_at:
        obs.append(f"Resolved {_hours(created, resolved_at) / 24:.1f} days after creation.")
        after = [e for e in inbound if _parse_dt(e["time"]) > resolved_at]
        if closed and abs(_hours(resolved_at, closed) - AUTO_CLOSE_DAYS * 24) < 24 and not after:
            obs.append(f"Closed automatically about {AUTO_CLOSE_DAYS} days after resolution (no customer reply).")
        elif after:
            obs.append(f"Customer replied {len(after)} time(s) after the case was resolved.")
    else:
        obs.append(f"Case is still open (age {_hours(created, now) / 24:.1f} days, counted up to now)"
                   + (" – it was re-opened after an earlier resolution." if reopened else "."))
    if reopened:
        obs.append(f"Re-opened {reopened} time(s) after being resolved / closed.")
    if owner_changes:
        obs.append(f"Owner changed {owner_changes} time(s).")
    # Response delays: every time the customer was waiting for an outbound e-mail for more than 1 calendar day (date difference) (from the case creation or from
    # a customer e-mail that came after the last reply, until the next real outbound e-mail - or until resolution / now when none came)
    resp_t = [(_parse_dt(e["time"]), e.get("who") or "") for e in resp]
    in_t = sorted(_parse_dt(e["time"]) for e in inbound)
    limit = resolved_at or now
    waits, cur = [], created
    while cur is not None and cur < limit:
        nxt = next(((rt, who) for rt, who in resp_t if rt > cur), None)
        stop = nxt[0] if nxt and nxt[0] <= limit else limit
        cal = (stop.astimezone().date() - cur.astimezone().date()).days          # calendar days between the two dates (not 24-hour periods)
        if cal > RESPONSE_DELAY_DAYS:
            waits.append({"from": cur.isoformat(), "to": stop.isoformat(), "days": cal, "answered": bool(nxt and nxt[0] <= limit),
                          "by": nxt[1] if nxt and nxt[0] <= limit else None})
        if not (nxt and nxt[0] <= limit):
            break
        cur = next((x for x in in_t if x > nxt[0]), None)         # the customer writes again after the reply
    if waits:
        obs.append(f"Agent did not respond for more than {RESPONSE_DELAY_DAYS} calendar day on {len(waits)} occasion(s):")
        for w in waits:
            a, b = _parse_dt(w["from"]), _parse_dt(w["to"])
            obs.append(f"• {w['days']} calendar days with no outbound e-mail ({a:%d %b %Y} → {b:%d %b %Y}) – "
                       + (f"answered by {w['by']}." if w["answered"] and w["by"] else "answered." if w["answered"]
                          else ("the case was resolved without a response." if resolved_at else "still waiting for a response.")))
    if gap and gap[0] >= 72:
        obs.append(f"Longest silence: {gap[0] / 24:.1f} days with no recorded activity ({gap[1]:%d %b %Y} → {gap[2]:%d %b %Y}).")
    days = {}
    for e, ts in zip(ev, t):
        days[f"{ts:%Y-%m-%d}"] = days.get(f"{ts:%Y-%m-%d}", 0) + 1
    return {"counts": kinds, "inbound": len(inbound), "outbound": len(outbound), "firstResponseHours": first_resp,
            "ageDays": _hours(created, end or now) / 24, "isResolved": is_resolved, "resolvedAt": resolved_at.isoformat() if resolved_at else None, "resolvedBy": resolved_by,
            "reopened": reopened, "ownerChanges": owner_changes, "activeDays": len(days),
            "longestGapDays": gap[0] / 24 if gap else None, "responseDelays": waits, "observations": obs,
            "statusFlow": [{"time": h["CreatedDate"], "from": h.get("OldValue"), "to": h.get("NewValue"),
                            "by": (h.get("CreatedBy") or {}).get("Name")} for h in status_rows]}


# ---- similar issues
STOP = set("the a an and or of to in on for with is are was were be been this that it as at by from we i you our my me have has had "
           "not but can could would should will please issue problem facing getting error again same earlier before currently now "
           "when what which how why who also any some very just still".split())


def sosl_term(words, op):
    esc = lambda w: re.sub(r'([\\?&|!{}\[\]()^~*:"\'+\-])', r"\\\1", w)
    return f" {op} ".join(esc(w) for w in words)


def snippet(text, words, n=260):
    text = re.sub(r"\s+", " ", plain(text) or "").strip()
    if not text:
        return ""
    low, pos = text.lower(), -1
    for w in words:
        pos = low.find(w.lower())
        if pos >= 0:
            break
    a = max(0, pos - n // 3) if pos >= 0 else 0
    out = text[a:a + n]
    return ("…" if a else "") + out + ("…" if a + n < len(text) else "")


def find_similar(sess, query, exclude="", limit=10, sort="recent"):
    query = (query or "").strip()
    words = [w for w in dict.fromkeys(re.findall(r"[A-Za-z0-9_.@-]{3,}", query)) if w.lower() not in STOP][:8]
    if not words:
        raise ApiError(400, "Enter a few keywords that describe the issue (at least one word of 3+ letters).")
    limit = max(1, min(int(limit or 10), 25))
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    def build(order):
        o = " ORDER BY CreatedDate DESC" if order else ""
        c = f"Case(Id, CaseNumber WHERE Status NOT IN ({ex}){o} LIMIT 40)"
        em, fi, cc = f"EmailMessage(Id, ParentId{o} LIMIT 60)", f"FeedItem(Id, ParentId WHERE Type IN ('TextPost','ContentPost','LinkPost','QuestionPost'){o} LIMIT 60)", f"CaseComment(Id, ParentId{o} LIMIT 60)"
        return [f"{c}, {em}, {fi}, {cc}", f"{c}, {em}, {cc}", f"{c}, {em}", c]
    # newest records first inside Salesforce, so the 40/60-row caps keep recent cases; plain versions are the fallback
    attempts = build(True) + build(False)
    hits = []
    for op in ("AND", "OR") if len(words) > 1 else ("AND",):
        got = []
        for ret in attempts:
            try:
                res = sf_get(sess, f"/services/data/v{API}/search?q=" + urllib.parse.quote(
                    f"FIND {{{sosl_term(words, op)}}} IN ALL FIELDS RETURNING {ret}"))
                got = res.get("searchRecords", [])
                break
            except ApiError as e:
                if e.status == 401:
                    raise
        hits += got
        # enough candidates that contain every keyword? then skip the broader "any keyword" search
        if op == "AND" and len({(h.get("Id") if (h.get("attributes") or {}).get("type") == "Case" else h.get("ParentId")) for h in got}) >= max(limit * 3, 30):
            break
    score, why = {}, {}
    for h in hits:
        typ = (h.get("attributes") or {}).get("type")
        cid = h.get("Id") if typ == "Case" else h.get("ParentId")
        if not cid or not str(cid).startswith("500"):
            continue
        score[cid] = score.get(cid, 0) + (3 if typ == "Case" else 1)
        why.setdefault(cid, set()).add({"Case": "Subject / description", "EmailMessage": "E-mail", "FeedItem": "Post", "CaseComment": "Case comment"}.get(typ, typ))
    if not score:
        return {"words": words, "operator": "AND", "total": 0, "results": []}
    ids = sorted(score, key=lambda k: -score[k])[:120]
    idlist = ", ".join(soql_str(i) for i in ids)
    cases = soql_all(sess, "SELECT Id, CaseNumber, Subject, Description, Status, Priority, Type, IsClosed, CreatedDate, ClosedDate, Account.Name, Owner.Name "
                           f"FROM Case WHERE Id IN ({idlist}) AND Status NOT IN ({ex})")
    cases = [x for x in cases if x["CaseNumber"] != (exclude or "").strip().zfill(8) and x["CaseNumber"] != (exclude or "").strip()]
    wanted = {x.lower() for x in RESOLVED_STATUSES}
    keep = ", ".join(soql_str(x["Id"]) for x in cases) or "''"
    by_case = {x["Id"]: {"emails": [], "posts": [], "comments": []} for x in cases}
    lw = [w.lower() for w in words]
    seen = {x["Id"]: {w for w in lw if w in ((x.get("Subject") or "") + " " + (x.get("Description") or "")).lower()} for x in cases}
    notes = []
    for key, soql, fn, rawfn in (
        ("emails", f"SELECT ParentId, Subject, FromName, FromAddress, ToAddress, MessageDate, Incoming, TextBody FROM EmailMessage WHERE ParentId IN ({keep}) ORDER BY MessageDate ASC",
         lambda r: {"time": r.get("MessageDate"), "direction": "Inbound" if r.get("Incoming") else "Outbound", "who": r.get("FromName") or r.get("FromAddress"),
                    "title": r.get("Subject") or "", "text": trim(reply_only(r.get("TextBody")), 1500)},
         lambda r: (r.get("Subject") or "") + " " + (r.get("TextBody") or "")),
        ("posts", f"SELECT ParentId, Body, Type, CreatedDate, CreatedBy.Name FROM CaseFeed WHERE ParentId IN ({keep}) ORDER BY CreatedDate ASC",
         lambda r: None if r.get("Type") in FEED_SKIP else {"time": r.get("CreatedDate"), "who": (r.get("CreatedBy") or {}).get("Name"), "title": "", "text": trim(r.get("Body"), 1200)},
         lambda r: r.get("Body") or ""),
        ("comments", f"SELECT ParentId, CommentBody, IsPublished, CreatedDate, CreatedBy.Name FROM CaseComment WHERE ParentId IN ({keep}) ORDER BY CreatedDate ASC",
         lambda r: {"time": r.get("CreatedDate"), "who": (r.get("CreatedBy") or {}).get("Name"), "title": "Public" if r.get("IsPublished") else "Internal",
                    "text": trim(r.get("CommentBody"), 1200)},
         lambda r: r.get("CommentBody") or ""),
    ):
        try:
            for r in soql_all(sess, soql, cap=3000):
                pid = r.get("ParentId")
                if pid in seen:                 # count every keyword found anywhere on the case (full text)
                    low = plain(rawfn(r)).lower() if rawfn(r) else ""
                    seen[pid].update(w for w in lw if w in low)
                item = fn(r)
                if item and item["text"]:
                    by_case.get(pid, {}).get(key, []).append(item)
        except ApiError as e:
            if e.status == 401:
                raise
            notes.append(f"{key} could not be read ({e.message[:120]}).")
    # recent cases on top by default; sort=match switches to most-keywords-first
    best = max((len(seen[x["Id"]]) for x in cases), default=0)
    cases.sort(key=lambda x: x["CreatedDate"], reverse=True)          # newest created first (default)
    if sort == "match":                                                # optional: most keywords first, newest within ties
        cases.sort(key=lambda x: -len(seen[x["Id"]]))
    total = len(cases)
    cases = cases[:limit]
    out = []
    for x in cases:
        b = by_case[x["Id"]]
        out_mail = [m for m in b["emails"] if m["direction"] == "Outbound"]
        sol = None      # the solution that was given: last agent e-mail, else last public comment, else last post
        if out_mail:
            m = out_mail[-1]
            sol = {"source": "E-mail", "time": m["time"], "who": m["who"], "text": m["text"]}
        elif [k for k in b["comments"] if k["title"] == "Public"]:
            m = [k for k in b["comments"] if k["title"] == "Public"][-1]
            sol = {"source": "Case comment", "time": m["time"], "who": m["who"], "text": m["text"]}
        elif b["posts"]:
            m = b["posts"][-1]
            sol = {"source": "Post", "time": m["time"], "who": m["who"], "text": m["text"]}
        has = lambda t: any(w.lower() in (t or "").lower() for w in words)
        found = snippet(x.get("Description"), words) if has(x.get("Description")) else ""
        if not found:
            for grp in ("emails", "posts", "comments"):
                m = next((m for m in b[grp] if has(m["text"])), None)
                if m:
                    found = snippet(m["text"], words)
                    break
        found = found or snippet(x.get("Description") or x.get("Subject"), words)
        out.append({"id": x["Id"], "caseNumber": x["CaseNumber"], "subject": x.get("Subject") or "", "status": x.get("Status"),
                    "priority": x.get("Priority"), "type": x.get("Type"), "account": (x.get("Account") or {}).get("Name"),
                    "owner": (x.get("Owner") or {}).get("Name"), "created": x.get("CreatedDate"), "closed": x.get("ClosedDate"),
                    "isResolved": bool(x.get("IsClosed")) or str(x.get("Status") or "").lower() in wanted,
                    "matchedIn": sorted(why.get(x["Id"], [])), "matchText": found, "solution": sol,
                    "matchCount": len(seen[x["Id"]]), "wordCount": len(words),
                    "matchedWords": [w for w, l in zip(words, lw) if l in seen[x["Id"]]],
                    "emails": b["emails"][-6:], "posts": b["posts"][-6:], "comments": b["comments"][-6:]})
    all_match = bool(out) and best == len(words)
    return {"words": words, "operator": "AND" if all_match else "OR", "total": total, "results": out, "notes": notes}


# ---------------------------------------------------------------- recurrence: posts of recent cases vs older cases
# Reads the Chatter posts / post comments of the cases created in a date range, extracts the "Observation" and
# "Resolution" details written in them (or the whole post when no such label is used), turns them into weighted
# keywords and finds older cases (created before the range) that talk about the same thing, best match first.
RC_LABEL = re.compile(r"(?i)\b(observ\w*|resolution(?:\s+details?)?|root\s*cause|solution|action\s+taken|findings?)\s*(?:details?)?\s*[:\-–=]")
RC_RES = re.compile(r"(?i)resolution|solution|action|root")
_RC_EXTRA = set("observation observations resolution resolutions details detail solution case cases ticket tickets customer client "
                "user users team update updated regards thanks thank hello dear kindly noted informed shared sent attached "
                "screenshot mail email checked found done need needs needed using used use after before showing shows "
                "action taken finding findings root cause done fixed".split())


def _rc_norm(w):
    w = w.lower().strip(".-_")
    if len(w) > 4 and w.endswith("s") and not w.endswith("ss"):
        w = w[:-1]
    return w


_RC_STOP = {_rc_norm(w) for w in (STOP | _RC_EXTRA)}


def rc_tokens(text):
    """[(normalised, original)] for every word of 3+ letters that starts with a letter (ids and plain numbers are ignored)."""
    out = []
    for w in re.findall(r"[A-Za-z][A-Za-z0-9_.-]{2,29}", text or ""):
        n = _rc_norm(w)
        if len(n) >= 3 and n not in _RC_STOP:
            out.append((n, w.lower().strip(".-_")))
    return out


def rc_parts(text):
    """Labelled parts of one post: [(label, text)] for Observation / Resolution / Root cause ... details."""
    t = plain(text) if isinstance(text, str) else ""
    t = (t or "").replace("\r", "")
    ms = list(RC_LABEL.finditer(t))
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        seg = re.sub(r"\s+", " ", t[m.end():min(end, m.end() + 900)]).strip()
        if seg:
            out.append((re.sub(r"\s+", " ", m.group(1)).strip().capitalize(), seg))
    return out


def find_recurrence(sess, dfrom, dto, limit=10, max_src=100, lookback=6, scope="all"):
    """Do the tickets created in [dfrom, dto] repeat issues seen in the `lookback` months before dfrom?
    Every ticket (or only those with an Observation / Resolution post when scope='labelled') is turned into weighted keywords,
    older tickets inside the look-back window are searched and scored, and for each new ticket the old tickets are
    returned best keyword match first."""
    limit = max(1, min(int(limit or 10), 25))
    max_src = max(5, min(int(max_src or 100), 400))
    lookback = max(0, min(int(lookback or 0), 60))
    scope = "labelled" if scope == "labelled" else "all"
    start_dt = _parse_dt(dfrom)
    cut = sf_datetime(dfrom)
    lo_dt = start_dt - timedelta(days=round(lookback * 30.4375)) if lookback else None
    lo = lo_dt.strftime("%Y-%m-%dT%H:%M:%SZ") if lo_dt else ""
    win = f"CreatedDate < {cut}" + (f" AND CreatedDate >= {lo}" if lo else "")
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    notes = []
    where = case_where("created", dfrom, dto, False)
    src_cases = soql_all(sess, "SELECT Id, CaseNumber, Subject, Description, Status, Priority, CreatedDate, Account.Name, Owner.Name FROM Case "
                               + where + "ORDER BY CreatedDate DESC LIMIT 5000", cap=5000)
    base = {"scanned": len(src_cases), "withPosts": 0, "analysed": 0, "recurred": 0, "results": [], "total": 0, "sources": [],
            "bySource": [], "lookback": lookback, "lookbackFrom": lo_dt.isoformat() if lo_dt else None, "scope": scope, "notes": notes}
    if not src_cases:
        notes.append("No cases were created in the selected dates.")
        return base

    # ---- 1) posts and post comments of the selected cases
    def read(chunk):
        ids = ", ".join(soql_str(x["Id"]) for x in chunk)
        rows = []
        for name, soql, mk in (
            ("posts", f"SELECT ParentId, Body, Type, CreatedDate FROM CaseFeed WHERE ParentId IN ({ids}) ORDER BY CreatedDate ASC",
             lambda r: None if r.get("Type") in FEED_SKIP else (r["ParentId"], r.get("Body"))),
            ("post comments", f"SELECT ParentId, CommentBody, CreatedDate FROM FeedComment WHERE ParentId IN ({ids}) ORDER BY CreatedDate ASC",
             lambda r: (r["ParentId"], r.get("CommentBody"))),
        ):
            try:
                for r in soql_all(sess, soql, cap=50000):
                    x = mk(r)
                    if x and x[1]:
                        rows.append(x)
            except ApiError as e:
                if e.status == 401:
                    raise
                notes.append(f"{name} could not be read ({e.message[:120]}).")
        return rows
    posts = {}
    for part in pmap(read, [src_cases[i:i + 300] for i in range(0, len(src_cases), 300)]):
        for cid, body in part:
            posts.setdefault(cid, []).append(body)
    srcs, nolabel = [], 0
    for c in src_cases:
        bodies = posts.get(c["Id"]) or []
        parts = [p for b in bodies for p in rc_parts(b)]
        if parts:
            base["withPosts"] += 1
            srcs.append({"c": c, "signal": " | ".join(f"{l}: {t}" for l, t in parts), "labelled": True})
            continue
        if scope == "labelled":
            continue
        nolabel += 1
        txt = " | ".join(re.sub(r"\s+", " ", plain(b) or "").strip()[:600] for b in bodies[:3])
        txt = txt or re.sub(r"\s+", " ", plain(c.get("Description")) or "").strip()[:900]
        srcs.append({"c": c, "signal": txt, "labelled": False})
    srcs = [s for s in srcs if s["signal"] or s["c"].get("Subject")]
    if not srcs:
        notes.append(f"{len(src_cases)} cases were checked but none has usable text" + (" (scope is limited to cases with an Observation / Resolution label)." if scope == "labelled" else "."))
        return base
    srcs.sort(key=lambda s: not s["labelled"])          # labelled posts first (stable: newest first inside each group)
    if len(srcs) > max_src:
        notes.append(f"{len(srcs)} cases qualify; {max_src} were analysed (cases with Observation / Resolution posts first, then the newest). Raise “Cases to analyse” to include more.")
        srcs = srcs[:max_src]
    if nolabel:
        notes.append(f"{sum(1 for s in srcs if not s['labelled'])} analysed case(s) have no Observation / Resolution label, so their subject, description and posts were used instead.")
    base["analysed"] = len(srcs)

    # ---- 2) weighted keywords per case (rare words count more than words that appear in many cases)
    import math
    df = {}
    for s in srcs:
        for n in {n for n, _ in rc_tokens(s["signal"] + " " + (s["c"].get("Subject") or ""))}:
            df[n] = df.get(n, 0) + 1
    N = len(srcs)
    for s in srcs:
        tf, orig = {}, {}
        for text, w in ((s["signal"], 2), (s["c"].get("Subject") or "", 2)):
            for n, o in rc_tokens(text):
                tf[n] = tf.get(n, 0) + w
                orig.setdefault(n, o)
        cand = [n for n in tf if not (N >= 8 and df.get(n, 1) / N > 0.5)]
        idf = {n: math.log((N + 1) / (df.get(n, 1) + 1)) + 1 for n in cand}
        top = sorted(cand, key=lambda n: -tf[n] * idf[n])[:10]
        s["kw"] = top
        s["orig"] = {n: orig[n] for n in top}
        s["idf"] = {n: idf[n] for n in top}
        s["tot"] = sum(idf[n] for n in top) or 1.0

    # ---- 3) candidate older cases inside the look-back window: one Salesforce search per case, then everything is scored here
    typ_ok = "'TextPost','ContentPost','LinkPost','QuestionPost'"
    src_ids = {c["Id"] for c in src_cases}

    def retrieve(s):
        words = [s["orig"][n] for n in s["kw"][:8]]
        if not words:
            return []
        c_ = f"Case(Id WHERE {win} AND Status NOT IN ({ex}) LIMIT 100)"
        for ret in (f"{c_}, FeedItem(ParentId WHERE Type IN ({typ_ok}) LIMIT 80), CaseComment(ParentId LIMIT 60), EmailMessage(ParentId LIMIT 60)",
                    f"{c_}, CaseComment(ParentId LIMIT 60), EmailMessage(ParentId LIMIT 60)", c_):
            try:
                res = sf_get(sess, f"/services/data/v{API}/search?q=" + urllib.parse.quote(
                    f"FIND {{{sosl_term(words, 'OR')}}} IN ALL FIELDS RETURNING {ret}"))
                return res.get("searchRecords", [])
            except ApiError as e:
                if e.status == 401:
                    raise
        return []
    hits = {}
    for recs in pmap(retrieve, srcs):
        for h in recs:
            typ = (h.get("attributes") or {}).get("type")
            cid = h.get("Id") if typ == "Case" else h.get("ParentId")
            if cid and str(cid).startswith("500") and cid not in src_ids:
                hits[cid] = hits.get(cid, 0) + (3 if typ == "Case" else 1)
    if not hits:
        notes.append("No older case in the look-back window shares keywords with the selected cases.")
        return base
    cand_ids = sorted(hits, key=lambda k: -hits[k])[:600]

    # ---- 4) text of the candidate cases
    def read_c(chunk):
        ids = ", ".join(soql_str(i) for i in chunk)
        got = {"cases": [], "feed": [], "cc": [], "em": []}
        try:
            got["cases"] = soql_all(sess, "SELECT Id, CaseNumber, Subject, Description, Status, Priority, IsClosed, CreatedDate, ClosedDate, Account.Name, Owner.Name "
                                          f"FROM Case WHERE Id IN ({ids}) AND {win} AND Status NOT IN ({ex})", cap=5000)
        except ApiError as e:
            if e.status == 401:
                raise
            notes.append("Older cases could not be read: " + e.message[:120])
            return got
        for key, soql in (("feed", f"SELECT ParentId, Body, Type, CreatedDate, CreatedBy.Name FROM CaseFeed WHERE ParentId IN ({ids}) ORDER BY CreatedDate ASC"),
                          ("cc", f"SELECT ParentId, CommentBody, IsPublished, CreatedDate, CreatedBy.Name FROM CaseComment WHERE ParentId IN ({ids}) ORDER BY CreatedDate ASC"),
                          ("em", f"SELECT ParentId, Subject, FromName, TextBody, Incoming, MessageDate FROM EmailMessage WHERE ParentId IN ({ids}) ORDER BY MessageDate ASC")):
            try:
                got[key] = soql_all(sess, soql, cap=20000)
            except ApiError as e:
                if e.status == 401:
                    raise
                notes.append(f"{key} of older cases could not be read ({e.message[:100]}).")
        return got
    cs, feed, cc, em = {}, {}, {}, {}
    for g in pmap(read_c, [cand_ids[i:i + 150] for i in range(0, len(cand_ids), 150)]):
        for r in g["cases"]:
            cs[r["Id"]] = r
        for r in g["feed"]:
            if r.get("Type") not in FEED_SKIP and r.get("Body"):
                feed.setdefault(r["ParentId"], []).append(r)
        for r in g["cc"]:
            cc.setdefault(r["ParentId"], []).append(r)
        for r in g["em"]:
            em.setdefault(r["ParentId"], []).append(r)
    wanted = {x.lower() for x in RESOLVED_STATUSES}
    cands = []
    for cid, c in cs.items():
        all_text = [c.get("Subject") or "", c.get("Description") or ""]
        sig_text, res_parts, obs_parts = [], [], []
        for r in feed.get(cid, []):
            all_text.append(r.get("Body") or "")
            for lab, seg in rc_parts(r.get("Body")):
                sig_text.append(seg)
                (res_parts if RC_RES.search(lab) else obs_parts).append(f"{lab}: {seg}")
        for r in cc.get(cid, []):
            all_text.append(r.get("CommentBody") or "")
        out_mail = []
        for r in em.get(cid, []):
            all_text.append((r.get("Subject") or "") + " " + (r.get("TextBody") or "")[:6000])
            if not r.get("Incoming") and r.get("TextBody"):
                out_mail.append(r)
        sol = None
        if res_parts:
            sol = {"source": "Post (resolution details)", "who": "", "time": None, "text": trim(res_parts[-1], 1200)}
        elif out_mail:
            m = out_mail[-1]
            sol = {"source": "E-mail", "who": m.get("FromName") or "", "time": m.get("MessageDate"), "text": trim(reply_only(m.get("TextBody")), 1200)}
        elif [k for k in cc.get(cid, []) if k.get("IsPublished")]:
            m = [k for k in cc[cid] if k.get("IsPublished")][-1]
            sol = {"source": "Case comment", "who": (m.get("CreatedBy") or {}).get("Name") or "", "time": m.get("CreatedDate"), "text": trim(m.get("CommentBody"), 1200)}
        elif feed.get(cid):
            m = feed[cid][-1]
            sol = {"source": "Post", "who": (m.get("CreatedBy") or {}).get("Name") or "", "time": m.get("CreatedDate"), "text": trim(m.get("Body"), 1200)}
        # the subject counts double (people write it for this reason), so it is also part of the "signal" words
        cands.append({"c": c, "all": {n for n, _ in rc_tokens(" ".join(all_text))},
                      "sig": {n for n, _ in rc_tokens(" ".join(sig_text + [c.get("Subject") or ""]))},
                      "obs": " | ".join(obs_parts)[:600], "sol": sol})

    # ---- 5) score every analysed case against every older case
    per_src = {s["c"]["Id"]: [] for s in srcs}
    ranked = []
    for cd in cands:
        matches = []
        for s in srcs:
            hit = [n for n in s["kw"] if n in cd["all"]]
            need = min(2, len(s["kw"]))
            if len(hit) < need or not hit:
                continue
            ratio = sum(s["idf"][n] for n in hit) / s["tot"]
            if ratio < 0.3:
                continue
            sh = sum(s["idf"][n] for n in s["kw"] if n in cd["sig"]) / s["tot"]
            m = {"s": s, "hit": hit, "score": ratio + 0.5 * sh}
            matches.append(m)
            per_src[s["c"]["Id"]].append((cd, m))
        if not matches:
            continue
        matches.sort(key=lambda m: (-m["score"], -len(m["hit"])))
        ranked.append((cd, matches))
    ranked.sort(key=lambda x: (-x[1][0]["score"], -len(x[1][0]["hit"]), x[0]["c"]["CreatedDate"]))
    base["total"] = len(ranked)
    pct = lambda sc: min(100, round(sc / 1.5 * 100))

    def old_info(cd, m):
        c = cd["c"]
        return {"id": c["Id"], "caseNumber": c["CaseNumber"], "subject": c.get("Subject") or "", "status": c.get("Status"), "priority": c.get("Priority"),
                "account": (c.get("Account") or {}).get("Name"), "owner": (c.get("Owner") or {}).get("Name"), "created": c.get("CreatedDate"), "closed": c.get("ClosedDate"),
                "isResolved": bool(c.get("IsClosed")) or str(c.get("Status") or "").lower() in wanted,
                "score": pct(m["score"]), "matchCount": len(m["hit"]), "wordCount": len(m["s"]["kw"]),
                "matchedWords": [m["s"]["orig"][n] for n in m["hit"]], "observation": cd["obs"], "solution": cd["sol"]}

    # (a) by old ticket: the old tickets that repeat most strongly, best match first
    results = []
    for cd, ms in ranked[:limit * 3]:
        r = old_info(cd, ms[0])
        r["recurrence"] = len(ms)
        r["sources"] = [{"id": m["s"]["c"]["Id"], "caseNumber": m["s"]["c"]["CaseNumber"], "subject": m["s"]["c"].get("Subject") or "",
                         "created": m["s"]["c"].get("CreatedDate"), "score": pct(m["score"]),
                         "matchedWords": [m["s"]["orig"][n] for n in m["hit"]], "text": snippet(m["s"]["signal"], [m["s"]["orig"][n] for n in m["hit"]], 320)}
                        for m in ms[:5]]
        results.append(r)
    base["results"] = results

    # (b) by new ticket: for every analysed ticket, did it recur? old tickets best keyword match first
    rows = []
    for s in srcs:
        pairs = list(per_src[s["c"]["Id"]])
        # best keyword match first; for equal scores the more recent old ticket comes first
        pairs.sort(key=lambda p: (-p[1]["score"], -len(p[1]["hit"]), -(_parse_dt(p[0]["c"]["CreatedDate"]).timestamp())))
        c = s["c"]
        rows.append({"id": c["Id"], "caseNumber": c["CaseNumber"], "subject": c.get("Subject") or "", "created": c.get("CreatedDate"),
                     "status": c.get("Status"), "priority": c.get("Priority"), "account": (c.get("Account") or {}).get("Name"),
                     "labelled": s["labelled"], "keywords": [s["orig"][n] for n in s["kw"]], "text": s["signal"][:400],
                     "matches": len(pairs), "best": pct(pairs[0][1]["score"]) if pairs else 0,
                     "old": [old_info(cd, m) for cd, m in pairs[:limit]]})
    rows.sort(key=lambda r: (-r["best"], -r["matches"]))          # most clearly recurring tickets first
    base["bySource"] = rows
    base["recurred"] = sum(1 for r in rows if r["matches"])
    base["sources"] = [{k: r[k] for k in ("id", "caseNumber", "subject", "created", "labelled", "keywords", "text", "matches")} for r in rows]
    return base


# ---------------------------------------------------------------- actual time held per group / agent
def _history_group_field(sess, resolver=None):
    """API name of the Case field behind 'Group' (or 'Agent' via resolver) so its CaseHistory rows can be read, or ''."""
    path = ((resolver or resolve_group)(sess) or {}).get("path")
    if not path:
        return ""
    try:
        for f in _describe(sess, "Case"):
            if f["name"] == path or _select_path("", f) == path:
                return f["name"] if FIELD_NAME_RE.match(f["name"]) else ""
    except ApiError as e:
        if e.status == 401:
            raise
    return ""


def _queue_names(sess):
    c = sess.get("_qnames")
    if c is None:
        try:
            c = {r["Name"] for r in soql_all(sess, "SELECT Name FROM Group WHERE Type = 'Queue'")}
        except ApiError as e:
            if e.status == 401:
                raise
            c = set()
        sess["_qnames"] = c
    return c


def status_timelines(sess, items):
    """Status history per case, so the browser can leave out time spent in paused statuses (Pending, Waiting on Third Party...).
    items = [{id}] -> {id: {"init": status before the first change, "ch": [[iso time, new status], ...]}}. Cases without any Status history are left out."""
    ids = [str(i.get("id", "")) for i in items if isinstance(i, dict)]
    ids = [x for x in ids if ID_RE.match(x)][:20000]
    out = {}

    def rows(chunk):
        q = ", ".join(soql_str(x) for x in chunk)
        return soql_all(sess, f"SELECT CaseId, OldValue, NewValue, CreatedDate FROM CaseHistory "
                              f"WHERE CaseId IN ({q}) AND Field = 'Status' ORDER BY CreatedDate ASC", cap=200000)
    for part in pmap(rows, [ids[i:i + 300] for i in range(0, len(ids), 300)]):
        for r in part:
            e = out.setdefault(r["CaseId"], {"init": None, "ch": []})
            if e["init"] is None and not e["ch"]:
                e["init"] = r.get("OldValue") if isinstance(r.get("OldValue"), str) else ""
            e["ch"].append([r["CreatedDate"], r.get("NewValue") if isinstance(r.get("NewValue"), str) else ""])
    return {"cases": out}


def csat_owners(sess, items):
    """Who resolved each ticket that got CSAT feedback: the agent and group holding the case just before it was last
    resolved (at or before the survey date), so later reopening / reassignment does not move the feedback.
    items = [{id, agent, group, created, surveyed}] -> {"cases": {id: {agent, group, resolved}}, "notes": [...]}"""
    items = [i for i in items if isinstance(i, dict) and ID_RE.match(str(i.get("id", "")))][:5000]
    wanted = {x.lower() for x in RESOLVED_STATUSES} | {"closed"}
    ids = [i["id"] for i in items]

    def rows(chunk):
        q = ", ".join(soql_str(x) for x in chunk)
        return soql_all(sess, f"SELECT CaseId, OldValue, NewValue, CreatedDate FROM CaseHistory "
                              f"WHERE CaseId IN ({q}) AND Field = 'Status' ORDER BY CreatedDate ASC", cap=200000)
    hist = {}
    for part in pmap(rows, [ids[i:i + 300] for i in range(0, len(ids), 300)]):
        for r in part:
            hist.setdefault(r["CaseId"], []).append(r)
    jobs = []
    for it in items:
        try:
            created = _parse_dt(it["created"])
            limit = _parse_dt(it["surveyed"]) if it.get("surveyed") else None
        except (ApiError, KeyError):
            continue
        res_t = closed_t = None      # resolution time = last move into a Resolved status; Closed is only a fallback
        for r in hist.get(it["id"], []):
            nv = str(r.get("NewValue") or "").lower()
            if nv not in wanted:
                continue
            t = _parse_dt(r["CreatedDate"])
            if limit is not None and t > limit:
                break
            if nv == "closed":
                if closed_t is None:
                    closed_t = t
            else:
                res_t = t
        if res_t is None:
            res_t = closed_t
        fa = str(it.get("fbAgent") or "").strip()
        end_t = res_t
        if fa and limit is not None:        # survey names its own agent: look at the case up to the survey time
            end_t = limit if limit > created else res_t
        if end_t is None or end_t <= created:
            continue
        jobs.append({"id": it["id"], "agent": it.get("agent"), "group": it.get("group"),
                     "created": it["created"], "resolved": end_t.isoformat(), "fa": fa})
    r = ownership_times(sess, jobs, with_segments=True) if jobs else {"cases": {}, "notes": []}
    when = {j["id"]: j["resolved"] for j in jobs}
    fas = {j["id"]: j["fa"] for j in jobs}
    out = {}
    for k, v in r["cases"].items():
        agent, group = v["lastAgent"], v["lastGroup"]
        if fas[k]:                          # credit the survey's agent, in the group that agent held the case in
            agent = fas[k]
            seg = [x for x in v.get("segments", []) if str(x["agent"]).strip().lower() == fas[k].lower()]
            if seg:
                group = seg[-1]["group"]
        out[k] = {"agent": agent, "group": group, "resolved": when[k]}
    return {"cases": out, "notes": r.get("notes", [])}


def reopen_info(sess, items):
    """Reopened tickets. A reopen is a move from Resolved / Closed back to an open status (Resolved -> Closed is the
    automatic close, not a reopen). Each reopen is credited to the agent (and group) who held the case when it was
    resolved just before the reopening, whoever finally resolved it again.
    items = [{id, agent, group, created}] -> {"cases": {id: [{agent, group, resolved}]}, "notes": [...]}"""
    items = [i for i in items if isinstance(i, dict) and ID_RE.match(str(i.get("id", "")))][:5000]
    wanted = {x.lower() for x in RESOLVED_STATUSES} | {"closed"}
    ids = [i["id"] for i in items]

    def rows(chunk):
        q = ", ".join(soql_str(x) for x in chunk)
        return soql_all(sess, f"SELECT CaseId, OldValue, NewValue, CreatedDate, CreatedById, CreatedBy.Name FROM CaseHistory "
                              f"WHERE CaseId IN ({q}) AND Field = 'Status' ORDER BY CreatedDate ASC", cap=200000)
    hist = {}
    for part in pmap(rows, [ids[i:i + 300] for i in range(0, len(ids), 300)]):
        for r in part:
            hist.setdefault(r["CaseId"], []).append(r)
    uname = {}                          # user Id -> name, for history rows whose CreatedBy.Name did not come back
    miss = sorted({r.get("CreatedById") for rs in hist.values() for r in rs
                   if r.get("CreatedById") and not (r.get("CreatedBy") or {}).get("Name")})
    for k0 in range(0, len(miss), 300):
        try:
            for u in soql_all(sess, "SELECT Id, Name FROM User WHERE Id IN (" + ", ".join(soql_str(x) for x in miss[k0:k0 + 300]) + ")"):
                uname[u["Id"]] = u["Name"]
        except ApiError as e:
            if e.status == 401:
                raise
            break
    events, created, meta = {}, {}, {}
    for it in items:
        try:
            created[it["id"]] = _parse_dt(it["created"])
        except (ApiError, KeyError):
            continue
        last_res, evs, who = None, [], []
        for r in hist.get(it["id"], []):
            nv = str(r.get("NewValue") or "").lower()
            t = _parse_dt(r["CreatedDate"])
            if nv in wanted:
                if last_res is None:
                    last_res = t                # first entry of a resolved / closed run
            elif last_res is not None:
                evs.append(last_res)            # left the resolved state: that resolution was reopened
                who.append((((r.get("CreatedBy") or {}).get("Name")) or uname.get(r.get("CreatedById") or "", ""), t.isoformat()))      # who reopened it, and when
                last_res = None
        if evs:
            events[it["id"]] = evs[:5]
            meta[it["id"]] = who[:5]
    out, notes = {}, []
    byid = {i["id"]: i for i in items}
    for k in range(5):
        jobs = [{"id": cid, "agent": byid[cid].get("agent"), "group": byid[cid].get("group"),
                 "created": byid[cid]["created"], "resolved": evs[k].isoformat()}
                for cid, evs in events.items() if len(evs) > k and evs[k] > created[cid]]
        if not jobs:
            continue
        r = ownership_times(sess, jobs)
        for n in r.get("notes", []):
            if n not in notes:
                notes.append(n)
        for cid, v in r["cases"].items():
            mk = meta.get(cid, [])
            out.setdefault(cid, []).append({"agent": v["lastAgent"], "group": v["lastGroup"],
                                            "resolved": next(j["resolved"] for j in jobs if j["id"] == cid),
                                            "reopenedBy": mk[k][0] if len(mk) > k else "",
                                            "reopenedOn": mk[k][1] if len(mk) > k else ""})
    return {"cases": out, "notes": notes}


def ownership_times(sess, items, with_segments=False):
    """For resolved cases: hours each agent / group actually held the case between creation and resolution,
    rebuilt from Owner and Group field history. items = [{id, agent, group, created, resolved}]."""
    items = [i for i in items if isinstance(i, dict) and ID_RE.match(str(i.get("id", "")))][:20000]
    gf = _history_group_field(sess)
    af = _history_group_field(sess, resolve_agent)      # Case "Agent" field; '' -> fall back to the Owner
    ofield = af or "Owner"
    queues = _queue_names(sess)
    fields = f"'{ofield}'" + (f", '{gf}'" if gf else "")
    hist, notes = {}, []

    def hist_rows(chunk):
        ids = ", ".join(soql_str(x["id"]) for x in chunk)
        return soql_all(sess, f"SELECT CaseId, Field, OldValue, NewValue, CreatedDate FROM CaseHistory "
                              f"WHERE CaseId IN ({ids}) AND Field IN ({fields}) ORDER BY CreatedDate ASC", cap=200000)
    try:
        batches = pmap(hist_rows, [items[i:i + 300] for i in range(0, len(items), 300)])
    except ApiError as e:
        if e.status == 401:
            raise
        notes.append("Agent / group history could not be read: " + e.message[:160])
        return {"cases": {}, "notes": notes, "groupHistory": bool(gf)}
    for rows in batches:
        for r in rows:
            ov, nv = r.get("OldValue"), r.get("NewValue")
            idlike = any(isinstance(v, str) and ID_RE.match(v) for v in (ov, nv))
            if idlike and not (af and r["Field"] == af):
                continue                        # raw Id rows duplicate the readable ones (Owner / Group)
            hist.setdefault(r["CaseId"], []).append(r)
    if af:                                      # a lookup to User stores user Ids in history: turn them into names
        uids = sorted({v for rs in hist.values() for r in rs if r["Field"] == af
                       for v in (r.get("OldValue"), r.get("NewValue")) if isinstance(v, str) and v.startswith("005") and ID_RE.match(v)})
        names = {}
        for i in range(0, len(uids), 300):
            try:
                for u in soql_all(sess, "SELECT Id, Name FROM User WHERE Id IN (" + ", ".join(soql_str(x) for x in uids[i:i + 300]) + ")"):
                    names[u["Id"]] = u["Name"]
            except ApiError as e:
                if e.status == 401:
                    raise
                notes.append("Some agent names could not be resolved: " + e.message[:120])
                break
        for rs in hist.values():
            for r in rs:
                if r["Field"] == af:
                    for k in ("OldValue", "NewValue"):
                        if r.get(k) in names:
                            r[k] = names[r[k]]
    else:
        notes.append("No Case field labelled “Agent” was found, so agent time follows the case Owner "
                     "(map it in field_map.json as {\"Agent\": \"YourField__c\"}).")
    out = {}
    for it in items:
        try:
            start, end = _parse_dt(it["created"]), _parse_dt(it["resolved"])
        except ApiError:
            continue
        if end <= start:
            continue
        h = hist.get(it["id"], [])
        oc = [(_parse_dt(r["CreatedDate"]), r.get("OldValue"), r.get("NewValue")) for r in h if r["Field"] == ofield]
        gc = [(_parse_dt(r["CreatedDate"]), r.get("OldValue"), r.get("NewValue")) for r in h if gf and r["Field"] == gf]
        cur_agent, cur_group = it.get("agent") or "Unassigned", it.get("group") or "No group"

        def owner_at(t):
            if not oc:
                return None
            cur = oc[0][1]
            for ts, _o, n in oc:
                if ts <= t:
                    cur = n
            # History exists: an empty value really means "nobody was assigned yet" (None would mean "no history at all",
            # which falls back to the current agent and wrongly credits a late assignment to earlier groups).
            return "" if cur is None else cur

        def group_at(t, owner):
            if gc:
                cur = gc[0][1]
                for ts, _o, n in gc:
                    if ts <= t:
                        cur = n
                if cur not in (None, ""):
                    return str(cur)
                return "No group"       # history exists: before the first assignment the case really had no group
            if not gf and owner in queues:      # no Group field on Case: the owning queue is the group
                return owner
            return cur_group

        cuts = sorted({t for t, _, _ in oc + gc if start < t < end})
        bounds = [start] + cuts + [end]
        agents, groups, last_a, last_g, segs = {}, {}, cur_agent, cur_group, []
        for a, b in zip(bounds, bounds[1:]):
            raw = owner_at(a)
            if raw is None:
                agent = cur_agent
                owner_name = None if cur_agent == "Unassigned" else cur_agent
            else:
                owner_name = raw
                agent = "Unassigned" if ((raw in queues and not af) or raw in (None, "")) else str(raw)
            group = group_at(a, owner_name)
            hrs = _hours(a, b)
            agents[agent] = agents.get(agent, 0) + hrs
            groups[group] = groups.get(group, 0) + hrs
            last_a, last_g = agent, group
            segs.append({"group": group, "agent": agent, "start": a.isoformat(), "end": b.isoformat(), "hours": hrs})
        out[it["id"]] = {"agents": agents, "groups": groups, "lastAgent": last_a, "lastGroup": last_g,
                         "hours": _hours(start, end)}
        if with_segments:
            out[it["id"]]["segments"] = segs
    if not gf:
        notes.append("No Group field with history was found on Case, so group time follows the owning queue "
                     "(or the case's current group when an agent owned it).")
    return {"cases": out, "notes": notes, "groupHistory": bool(gf)}


def _group_history_names(sess):
    """Every name the Case Group field can appear under in CaseHistory.Field: API name, label, plus 'Group'."""
    names = set()
    try:
        gf = _history_group_field(sess)
        if gf:
            names.add(gf)
        for f in _describe(sess, "Case"):
            if _norm(f.get("label")) in ("group", "supportgroup", "assignmentgroup", "casegroup", "assignedgroup") \
                    and FIELD_NAME_RE.match(f["name"]):
                names.add(f["name"])
    except ApiError as e:
        if e.status == 401:
            raise
    names.add("Group")
    return sorted(names)


def group_forwards(sess, items):
    """Group-to-group transfers per case, read straight from the Case History rows of the Group field.
    Every row that changes Group from X to Y is one move X -> Y, so A -> C -> B gives A->C and C->B (never A->B).
    A first assignment (blank -> A) or a cleared group is not a forward.
    items = [{id, group, created}] -> {cases: {id: {"i": first group, "e": [[iso time, from, to], ...]}}}."""
    ids = []
    for i in items:
        if isinstance(i, dict) and ID_RE.match(str(i.get("id", ""))):
            ids.append(i["id"])
    ids = ids[:20000]
    names = _group_history_names(sess)
    fields = ", ".join(soql_str(n) for n in names)
    notes = []

    def rows(chunk):
        q = ", ".join(soql_str(x) for x in chunk)
        return soql_all(sess, f"SELECT CaseId, Field, OldValue, NewValue, CreatedDate FROM CaseHistory "
                              f"WHERE CaseId IN ({q}) AND Field IN ({fields}) ORDER BY CreatedDate ASC", cap=200000)
    try:
        parts = pmap(rows, [ids[i:i + 300] for i in range(0, len(ids), 300)])
    except ApiError as e:
        if e.status == 401:
            raise
        return {"cases": {}, "notes": ["Group history could not be read: " + e.message[:160]], "failed": True}
    hist, total = {}, 0
    for part in parts:
        for r in part:
            total += 1
            hist.setdefault(r["CaseId"], []).append(r)
    if not total and ids:
        # No Group field history at all (the group is the owning queue in this org): a queue -> queue Owner change is a group move.
        queues = _queue_names(sess)
        if queues:
            def orows(chunk):
                q = ", ".join(soql_str(x) for x in chunk)
                return soql_all(sess, f"SELECT CaseId, Field, OldValue, NewValue, CreatedDate FROM CaseHistory "
                                      f"WHERE CaseId IN ({q}) AND Field = 'Owner' ORDER BY CreatedDate ASC", cap=200000)
            try:
                oparts = pmap(orows, [ids[i:i + 300] for i in range(0, len(ids), 300)])
            except ApiError as e:
                if e.status == 401:
                    raise
                oparts = []
                notes.append("Owner history could not be read: " + e.message[:160])
            for part in oparts:
                for r in part:
                    ov, nv = r.get("OldValue"), r.get("NewValue")
                    if isinstance(ov, str) and isinstance(nv, str) and ov in queues and nv in queues and ov != nv:
                        hist.setdefault(r["CaseId"], []).append(r)
                        total += 1
            if total:
                notes.append("No Group field history exists, so queue-to-queue Owner changes are used as group moves.")
    # some orgs store a lookup Group as record Ids: turn those into names
    want = sorted({v for rs in hist.values() for r in rs for v in (r.get("OldValue"), r.get("NewValue"))
                   if isinstance(v, str) and ID_RE.match(v) and v[:3] in ("00G", "005")})
    idname = {}
    for k in range(0, len(want), 300):
        part = want[k:k + 300]
        for obj in ("Group", "User"):
            sub = [x for x in part if x.startswith("00G" if obj == "Group" else "005")]
            if sub:
                try:
                    for u in soql_all(sess, f"SELECT Id, Name FROM {obj} WHERE Id IN (" + ", ".join(soql_str(x) for x in sub) + ")"):
                        idname[u["Id"]] = u["Name"]
                except ApiError as e:
                    if e.status == 401:
                        raise
    out = {}
    for cid, rs in hist.items():
        seen, ev, first = set(), [], None
        for r in rs:                               # already ordered by CreatedDate
            ov, nv = r.get("OldValue"), r.get("NewValue")
            ov, nv = idname.get(ov, ov), idname.get(nv, nv)
            if not (isinstance(ov, str) or isinstance(nv, str)):
                continue
            ov, nv = (ov or "").strip(), (nv or "").strip()
            if (ID_RE.match(ov) or ID_RE.match(nv)):          # raw Id row that duplicates a readable one
                continue
            key = (r["CreatedDate"], ov, nv)
            if key in seen:
                continue
            seen.add(key)
            if first is None:
                first = ov or nv
            if ov and nv and ov != nv:
                ev.append([_parse_dt(r["CreatedDate"]).isoformat(), ov, nv])
        if ev:
            out[cid] = {"i": ev[0][1], "e": ev}
    notes.append(f"Group field read as: {', '.join(names)}. {total} Group history rows found for {len(ids)} cases; "
                 f"{len(out)} cases had a group-to-group transfer.")
    if not total and ids:
        notes.append("No Group history rows came back. Check that field history tracking is enabled for the Case Group field in Salesforce, "
                     "and that this login can see Case History.")
    return {"cases": out, "notes": notes, "groupHistory": True, "failed": False}


# ---------------------------------------------------------------- Time Logs (custom object related to Case)
# The object is found automatically (custom object whose name / label looks like "Time Log" and that has a lookup to Case).
# To force it, add to field_map.json, for example:
#   {"Time Log Object": "Time_Log__c", "Time Log Agent": "Agent__c", "Time Log HH:MM": "HH_MM__c",
#    "Time Log Billable": "Billable__c", "Time Log On": "On__c", "Time Log Note": "Note__c", "Time Log Unit": "minutes"}
TIMELOG_RE = re.compile(r"time\s*_?\s*(log|sheet|entry|entries)", re.I)
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
TL_SYS = {"Id", "IsDeleted", "CreatedById", "LastModifiedById", "SystemModstamp", "LastModifiedDate",
          "LastViewedDate", "LastReferencedDate", "CurrencyIsoCode", "RecordTypeId"}
TL_ROLES = {
    "agent":    ("Time Log Agent",    ["agent", "loggedby", "user", "employee", "resource", "engineer", "assignedto"]),
    "hhmm":     ("Time Log HH:MM",    ["hhmm", "hours", "duration", "timespent", "timelogged", "time", "effort"]),
    "minutes":  ("Time Log Minutes",  ["timeinminute", "timeinminutes", "timeinmin", "minutes", "totalminutes", "loggedminutes"]),
    "billable": ("Time Log Billable", ["billable", "isbillable"]),
    "on":       ("Time Log On",       ["on", "date", "logdate", "timelogdate", "workdate", "loggedon", "logon"]),
    "note":     ("Time Log Note",     ["note", "notes", "comment", "comments", "remarks", "description"]),
}
TL_TYPES = {
    "agent": None,
    "hhmm": {"string", "textarea", "double", "int", "percent", "long", "time", "picklist", "currency"},
    "minutes": {"double", "int", "long", "percent", "currency"},
    "billable": {"boolean"},
    "on": {"date", "datetime"},
    "note": {"string", "textarea", "richtext"},
}


def find_timelog(sess):
    if "_tlog" in sess:
        return sess["_tlog"]
    ov = _overrides()
    want = str(ov.get("Time Log Object") or "").strip()
    g = sf_get(sess, f"/services/data/v{API}/sobjects")
    cands = []
    for o in g.get("sobjects", []):
        if not o.get("queryable"):
            continue
        if want:
            if o["name"].lower() != want.lower():
                continue
        elif not (o.get("custom") and TIMELOG_RE.search(o["name"] + " " + (o.get("label") or ""))):
            continue
        cands.append(o)
    cands.sort(key=lambda o: 0 if re.search(r"time\s*_?\s*log", o["name"] + " " + (o.get("label") or ""), re.I) else 1)
    for o in cands:
        try:
            flds = _describe(sess, o["name"])
        except ApiError as e:
            if e.status == 401:
                raise
            continue
        link = _case_link(flds)
        if not link or not link.get("relationshipName"):
            continue
        by_name = {f["name"]: f for f in flds}

        def pick(role):
            ov_name = ov.get(TL_ROLES[role][0])
            if ov_name and ov_name in by_name and not (role == "agent" and re.search(r"group", (by_name[ov_name].get("label") or "") + ov_name, re.I)):
                return by_name[ov_name]
            types = TL_TYPES[role]
            for lab in TL_ROLES[role][1]:
                for f in flds:
                    if f["name"] in TL_SYS or f["name"] == link["name"] or f.get("type") in SKIP_TYPES:
                        continue
                    if types and f.get("type") not in types:
                        continue
                    if role == "agent" and f.get("type") in ("date", "datetime", "boolean"):
                        continue
                    if _norm(f.get("label")) == lab or _norm(f["name"].replace("__c", "")) == lab:
                        return f
            return None

        def pick_agent():
            a = pick("agent")
            if a:
                return a
            def usable(f):
                return (f["name"] not in TL_SYS and f["name"] != link["name"] and f.get("type") not in SKIP_TYPES
                        and not re.search(r"group", (f.get("label") or "") + f["name"], re.I))
            # 1) a text / lookup field whose label or name contains "agent" (e.g. "Time Log Agent", "Agent Name")
            for f in flds:
                if usable(f) and f.get("type") not in ("date", "datetime", "boolean", "textarea", "double", "int") \
                        and re.search(r"agent", (f.get("label") or "") + " " + f["name"], re.I):
                    return f
            # 2) a custom lookup to User (who logged the time)
            for f in flds:
                if usable(f) and f["name"].endswith("__c") and f.get("type") == "reference" and "User" in (f.get("referenceTo") or []):
                    return f
            # 3) the standard owner / creator of the time log record
            return by_name.get("OwnerId") or by_name.get("CreatedById")
        agent = pick_agent()
        on = pick("on") or next((f for f in flds if f["name"].endswith("__c") and f.get("type") in ("date", "datetime")), None) or by_name.get("CreatedDate")
        spec = {"name": o["name"], "label": o.get("label") or o["name"], "caseField": link["name"],
                "caseRel": link["relationshipName"], "flds": flds,
                "all": [{"name": f["name"], "label": f.get("label") or f["name"], "type": f.get("type")}
                        for f in flds if (f["name"] not in TL_SYS or f["name"] in ("CreatedById", "LastModifiedById")) and f.get("type") not in SKIP_TYPES],
                "fields": {"agent": agent, "hhmm": pick("hhmm"), "minutes": pick("minutes"), "billable": pick("billable"), "on": on, "note": pick("note")}}
        sess["_tlog"] = spec
        return spec
    raise ApiError(404, "No Time Log object was found in this org (a custom object with a lookup to Case and a name like “Time Log”). "
                        "Set it in field_map.json, for example {\"Time Log Object\": \"Time_Log__c\"}.")


def tl_minutes(v, unit):
    if v in (None, "") or isinstance(v, bool):
        return None
    mult = 60 if unit == "hours" else 1
    if isinstance(v, (int, float)):
        return float(v) * mult
    s = str(v).strip()
    m = re.match(r"^(\d+):(\d{1,2})(?::(\d{1,2}))?(?:\.\d+)?Z?$", s)
    if m:
        return int(m.group(1)) * 60 + int(m.group(2))
    m = re.match(r"^(?:(\d+)\s*h\w*)?\s*(?:(\d+)\s*m\w*)?$", s, re.I)
    if m and (m.group(1) or m.group(2)):
        return int(m.group(1) or 0) * 60 + int(m.group(2) or 0)
    try:
        return float(s) * mult
    except ValueError:
        return None


TL_HIDE = {"IsDeleted", "SystemModstamp", "LastViewedDate", "LastReferencedDate"}


def fetch_timelogs(sess, dfrom, dto, tf, tt, all_time=False, full=False):
    spec = find_timelog(sess)
    obj, link, rel, F = spec["name"], spec["caseField"], spec["caseRel"], spec["fields"]
    on, warnings = F["on"], []
    if F["agent"]:
        warnings.append(f"Agent is read from the Time Log field “{F['agent'].get('label')}” ({F['agent']['name']}).")
    if not F["hhmm"] and not F["minutes"]:
        warnings.append("No HH:MM / minutes field was found on the Time Log object; choose it in the “Time Log fields” panel.")
    paths = {role: _select_path("", f) for role, f in F.items() if f}
    unit = str(_overrides().get("Time Log Unit") or "").lower()
    if unit not in ("hours", "minutes"):
        h = F["hhmm"]
        unit = "hours" if h and re.search(r"hour", (h.get("label") or "") + h["name"], re.I) else "minutes"
    if not F["minutes"] and F["hhmm"] and F["hhmm"].get("type") in ("double", "int", "percent", "long", "currency"):
        warnings.append(f"The HH:MM field is a number, so values are read as {unit} (override with {{\"Time Log Unit\": \"hours\"}} in field_map.json).")
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    conds = [f"{rel}.Status NOT IN ({ex})"]
    if not all_time:
        if on.get("type") == "date":
            if not (DATE_RE.match(tf or "") and DATE_RE.match(tt or "")):
                raise ApiError(400, "Choose both From and To dates.")
            conds.append(f"{on['name']} >= {tf} AND {on['name']} <= {tt}")
        elif on.get("type") == "datetime":
            conds.append(f"{on['name']} >= {sf_datetime(dfrom)} AND {on['name']} <= {sf_datetime(dto)}")
        else:
            warnings.append(f"The “{on.get('label')}” field is {on.get('type')}, not a date, so Salesforce cannot filter on it: all entries are downloaded and the dates are filtered in the app.")
    ordf = on["name"] if on.get("type") in ("date", "datetime") else "CreatedDate"
    where = " AND ".join(conds)

    # ---- every Time Log field (Info) and the Case details
    tdefs = []
    for f in spec["flds"]:
        n, t = f["name"], f.get("type")
        if n in TL_HIDE or n == link or t in SKIP_TYPES:
            continue
        if t == "reference":
            refs = f.get("referenceTo") or []
            if not f.get("relationshipName") or not refs or not all(r in SAFE_REFS or r.endswith("__c") for r in refs):
                continue
            path, t = _select_path("", f), "string"
        else:
            path = n
        tdefs.append({"key": "T:" + n, "label": f.get("label") or n, "type": t, "path": path, "name": n})
    extra_cfg = resolve_extra_fields(sess)
    gp = (resolve_group(sess) or {}).get("path")
    fgp = (resolve_first_group(sess) or {}).get("path")
    agp = (resolve_agent(sess) or {}).get("path")
    cdefs = []

    def addc(key, label, typ, path):
        cdefs.append({"key": key, "label": "Case: " + label, "type": typ or "string", "path": path})
    for n, l, t in (("Origin", "Origin", "string"), ("Type", "Type", "string"), ("Reason", "Reason", "string"),
                    ("CreatedDate", "Created on", "datetime"), ("ClosedDate", "Closed date", "datetime"),
                    ("IsClosed", "Closed", "boolean"), ("IsEscalated", "Escalated", "boolean")):
        addc("C:" + n, l, t, n)
    for e in extra_cfg:
        if e["path"]:
            addc("X:" + e["label"], e["label"], e.get("type") if e.get("type") in ("date", "datetime", "double", "int", "currency", "percent") else "string", e["path"])
    if agp:
        addc("C:Agent", "Agent", "string", agp)
    if full:
        used = {e["path"] for e in extra_cfg if e["path"]} | {p for p in (gp, fgp, agp) if p}
        for d in case_field_defs(sess, used):
            addc(d["key"], d["label"], d["type"], d["name"])
    base = ["Id", "CreatedDate", link] + list(paths.values()) + [f"{rel}.CaseNumber", f"{rel}.Subject", f"{rel}.Status", f"{rel}.Priority"]
    acct = [f"{rel}.Account.Name", f"{rel}.Owner.Name"]
    groups = [f"{rel}.{p}" for p in (gp, fgp) if p]
    want = list(dict.fromkeys(acct + groups + [t["path"] for t in tdefs] + [f"{rel}.{c['path']}" for c in cdefs]))

    def run(extra, limit=None):
        soql = (f"SELECT {', '.join(dict.fromkeys(base + extra))} FROM {obj} WHERE {where} "
                f"ORDER BY {ordf} DESC, CreatedDate DESC" + (f" LIMIT {limit}" if limit else ""))
        res = sf_get(sess, f"/services/data/v{API}/query?q=" + urllib.parse.quote(soql))
        rows = list(res.get("records", []))
        while not limit and not res.get("done") and res.get("nextRecordsUrl") and len(rows) < MAX_ROWS:
            res = sf_get(sess, res["nextRecordsUrl"])
            rows += res.get("records", [])
        return rows, not res.get("done")

    def usable(ps):
        ps = list(dict.fromkeys(ps))
        if not ps:
            return []
        try:
            run(ps, 1)
            return ps
        except ApiError as e:
            if e.status == 401:
                raise
            if len(ps) == 1:
                return []
        mid = len(ps) // 2
        return usable(ps[:mid]) + usable(ps[mid:])

    good = set(want)
    try:
        rows, truncated = run(want)
    except ApiError as e:
        if e.status == 401:
            raise
        run([], 1)                      # the essential fields must work; otherwise this raises its own error
        good = set(usable(want))
        bad = [p for p in want if p not in good]
        try:
            rows, truncated = run([p for p in want if p in good])
        except ApiError as e2:
            if e2.status == 401:
                raise
            good = set()
            rows, truncated = run([])
            bad = want
        warnings.append("Not readable in this org (skipped): " + ", ".join(bad[:8]) + (" …" if len(bad) > 8 else ""))
    tdefs = [t for t in tdefs if t["path"] in good]
    cdefs = [c for c in cdefs if f"{rel}.{c['path']}" in good]
    used_groups = bool(groups) and all(g in good for g in groups)

    def val(rec, path):
        x = plain(_dig(rec, path))
        if isinstance(x, (dict, list)):
            x = json.dumps(x, ensure_ascii=False)
        return None if x in (None, "") else x

    out = []
    for r in rows:
        c = r.get(rel) or {}
        mins = None
        if "minutes" in paths:
            try:
                mv = plain(_dig(r, paths["minutes"]))
                mins = float(mv) if mv not in (None, "") else None
            except (TypeError, ValueError):
                mins = None
        if mins is None and "hhmm" in paths:
            mins = tl_minutes(plain(_dig(r, paths["hhmm"])), unit)
        h = None if mins is None else divmod(int(round(mins)), 60)
        av = plain(_dig(r, paths["agent"])) if "agent" in paths else None
        row = {
            "Id": r["Id"], "CaseId": r.get(link), "CaseNumber": c.get("CaseNumber") or "", "Subject": c.get("Subject") or "",
            "Status": c.get("Status") or "—", "Priority": c.get("Priority") or "—",
            "Account": (c.get("Account") or {}).get("Name") or "—", "CaseOwner": (c.get("Owner") or {}).get("Name") or "—",
            "Group": str(plain(_dig(c, gp))) if used_groups and gp and _dig(c, gp) not in (None, "") else "—",
            "FirstGroup": str(plain(_dig(c, fgp))) if used_groups and fgp and _dig(c, fgp) not in (None, "") else "—",
            "Agent": str(av) if av not in (None, "") else "—",
            "Minutes": mins, "HHMM": None if h is None else f"{h[0]:02d}:{h[1]:02d}",
            "Billable": bool(_dig(r, paths["billable"])) if "billable" in paths else None,
            "On": _dig(r, paths["on"]) if "on" in paths else None,
            "Note": str(plain(_dig(r, paths["note"])) or "") if "note" in paths else "",
            "Created": r.get("CreatedDate"),
        }
        for t in tdefs:
            x = val(r, t["path"])
            if x is not None:
                row[t["key"]] = x
        for d in cdefs:
            x = val(r, f"{rel}.{d['path']}")
            if x is not None:
                row[d["key"]] = x
        out.append(row)
    if not out:
        try:
            agg = soql_all(sess, f"SELECT COUNT(Id) c, MIN({on['name']}) mn, MAX({on['name']}) mx FROM {obj}")
            a = agg[0] if agg else {}
            warnings.append(f"No entries matched. Object {spec['label']} ({obj}) holds {a.get('c', 0)} records in total, with “{on.get('label')}” "
                            f"from {a.get('mn')} to {a.get('mx')}; the filter used was: {where}. Fields used: "
                            + ", ".join(f"{k}={f['name']}" for k, f in F.items() if f) + ".")
        except ApiError as e:
            if e.status == 401:
                raise
            warnings.append("No entries matched, and the object could not be summarised: " + e.message[:160])

    # ---- column list for the table: a sensible default set first, then everything else
    role_names = {f["name"] for f in F.values() if f}
    grp_t = next((t for t in tdefs if _norm(t["label"]) == "group"), None)
    tmap = {t["name"]: t for t in tdefs}
    cols, seen = [], set()

    def addcol(key, label, typ, g, d):
        if key not in seen:
            seen.add(key)
            cols.append({"key": key, "label": label, "type": typ, "g": g, "d": 1 if d else 0})
    addcol("CaseNumber", "Case #", "string", "Case", True)
    addcol("Subject", "Case: Subject", "string", "Case", True)
    for role in ("agent",):
        if F[role] and F[role]["name"] in tmap:
            t = tmap[F[role]["name"]]; addcol(t["key"], t["label"], t["type"], "Time Log", True)
    if grp_t:
        addcol(grp_t["key"], grp_t["label"], grp_t["type"], "Time Log", True)
    for role in ("hhmm", "minutes", "billable", "on", "note"):
        if F[role] and F[role]["name"] in tmap:
            t = tmap[F[role]["name"]]; addcol(t["key"], t["label"], t["type"], "Time Log", True)
    for k, l in (("Status", "Case: Status"), ("Priority", "Case: Priority"), ("Account", "Case: Account"), ("CaseOwner", "Case: Owner"), ("Group", "Case: Group")):
        addcol(k, l, "string", "Case", True)
    addcol("FirstGroup", "Case: First assigned group", "string", "Case", False)
    for t in tdefs:
        addcol(t["key"], t["label"], t["type"], "Time Log", False)
    for d in cdefs:
        addcol(d["key"], d["label"], d["type"], "Case", False)
    return {"rows": out, "object": {"name": obj, "label": spec["label"]}, "truncated": truncated, "columns": cols,
            "fields": {role: (f.get("label") if f else None) for role, f in F.items()},
            "fieldInfo": {role: ({"name": f["name"], "label": f.get("label"), "type": f.get("type")} if f else None) for role, f in F.items()},
            "logGroup": ({"name": grp_t["name"], "label": grp_t["label"], "type": grp_t["type"]} if grp_t else None),
            "allFields": spec["all"], "warnings": warnings}



def fetch_case_history(sess, dfrom, dto, all_time=False):
    """Group changes from Case History: Field = Group, Original Value = from group, New Value = to group.
    Every row that changes Group from X to Y is one move X -> Y (A -> C -> B gives A->C and C->B).
    A first assignment (blank -> A) or a cleared group is not a forward and is left out."""
    names = _group_history_names(sess)
    try:
        for f in _describe(sess, "Case"):
            if _norm(f.get("label")) in ("group", "supportgroup", "assignmentgroup", "casegroup", "assignedgroup"):
                lab = f.get("label")
                if lab and lab not in names:
                    names.append(lab)
    except ApiError as e:
        if e.status == 401:
            raise
    ex = ", ".join(soql_str(x) for x in EXCLUDED_STATUSES)
    rng = "" if all_time else f" AND CreatedDate >= {sf_datetime(dfrom)} AND CreatedDate <= {sf_datetime(dto)}"
    notes = []

    def pull(cond):
        sel = ("SELECT CaseId, Case.CaseNumber, Case.Subject, Case.Status, Case.Priority, Case.Account.Name, "
               "Field, OldValue, NewValue, CreatedDate, CreatedBy.Name FROM CaseHistory ")
        tail = f"WHERE {cond}{rng} AND Case.Status NOT IN ({ex}) ORDER BY CreatedDate ASC"
        try:
            return soql_all(sess, sel + tail, cap=MAX_ROWS)
        except ApiError as e:
            if e.status == 401:
                raise
            return soql_all(sess, sel.replace("Case.Account.Name, ", "") + tail, cap=MAX_ROWS)

    fields = ", ".join(soql_str(n) for n in names)
    recs = pull(f"Field IN ({fields})")
    if not recs:
        # no Group field history: a queue -> queue Owner change is a group move
        queues = _queue_names(sess)
        if queues:
            recs = [r for r in pull("Field = 'Owner'")
                    if isinstance(r.get("OldValue"), str) and isinstance(r.get("NewValue"), str)
                    and r["OldValue"] in queues and r["NewValue"] in queues]
            if recs:
                notes.append("No Group field history exists, so queue-to-queue Owner changes are used as group moves.")
    # a lookup Group stores record Ids: turn them into names
    want = sorted({v for r in recs for v in (r.get("OldValue"), r.get("NewValue"))
                   if isinstance(v, str) and ID_RE.match(v) and v[:3] in ("00G", "005")})
    idname = {}
    for obj, pre in (("Group", "00G"), ("User", "005")):
        sub = [x for x in want if x.startswith(pre)]
        for i in range(0, len(sub), 300):
            try:
                for u in soql_all(sess, f"SELECT Id, Name FROM {obj} WHERE Id IN (" + ", ".join(soql_str(x) for x in sub[i:i + 300]) + ")"):
                    idname[u["Id"]] = u["Name"]
            except ApiError as e:
                if e.status == 401:
                    raise
    out, seen, skipped = [], set(), 0
    for r in recs:
        ov, nv = r.get("OldValue"), r.get("NewValue")
        ov, nv = idname.get(ov, ov), idname.get(nv, nv)
        if not (isinstance(ov, str) or isinstance(nv, str)):
            continue
        ov, nv = (ov or "").strip(), (nv or "").strip()
        if ID_RE.match(ov) or ID_RE.match(nv):      # raw Id row that duplicates a readable one
            continue
        key = (r["CaseId"], r["CreatedDate"], ov, nv)
        if key in seen:
            continue
        seen.add(key)
        if not (nv and ov != nv):      # keep real moves and the first assignment (blank -> group)
            skipped += 1
            continue
        c = r.get("Case") or {}
        out.append({"CaseId": r["CaseId"], "CaseNumber": c.get("CaseNumber") or "", "Subject": c.get("Subject") or "",
                    "Status": c.get("Status") or "—", "Priority": c.get("Priority") or "—",
                    "Account": (c.get("Account") or {}).get("Name") or "—",
                    "Date": _parse_dt(r["CreatedDate"]).isoformat(), "From": ov, "To": nv,
                    "By": (r.get("CreatedBy") or {}).get("Name") or "—"})
    notes.append(f"Group field read as: {', '.join(names)}. {len(recs)} Group history rows found; {len(out)} are group-to-group transfers "
                 f"({skipped} first assignments / cleared groups left out).")
    if not recs:
        notes.append("No Group history rows came back. Check that field history tracking is enabled for the Case Group field in Salesforce, "
                     "and that this login can see Case History.")
    return {"rows": out, "truncated": len(recs) >= MAX_ROWS, "notes": notes}


class QuietServer(ThreadingHTTPServer):
    daemon_threads = True

    def handle_error(self, request, client_address):      # dropped browser connections are normal: stay silent about them
        import sys
        if isinstance(sys.exc_info()[1], (ConnectionError, BrokenPipeError, TimeoutError)):
            return
        super().handle_error(request, client_address)


class Handler(BaseHTTPRequestHandler):
    server_version = "CSTAnalytics"
    protocol_version = "HTTP/1.1"      # keep-alive: the browser reuses one connection, and so does this handler thread's Salesforce connection
    timeout = 300                      # drop idle keep-alive connections after 5 minutes

    def log_message(self, *args):   # never log request details (could contain credentials)
        pass

    # -- helpers
    def _local_host(self):
        if SHARE:
            return True                   # --share: reached through this PC's name / IP address as well
        return self.headers.get("Host", "").split(":")[0].lower() in ("localhost", "127.0.0.1")

    def _is_owner(self):
        """True when the request comes from this PC itself (not from another machine on the network)."""
        return self.client_address[0] in ("127.0.0.1", "::1", "::ffff:127.0.0.1")

    def _send(self, code, body, ctype="application/json", extra=None):
        data = body if isinstance(body, bytes) else json.dumps(body).encode("utf-8")
        gz = False
        if len(data) > 1400 and not self._is_owner() and "gzip" in self.headers.get("Accept-Encoding", ""):
            data = gzip.compress(data, 4)       # people on the network get the page and the data ~5-10x smaller (this PC itself needs no compression)
            gz = True
        try:
            self.send_response(code)
            if gz:
                self.send_header("Content-Encoding", "gzip")
                self.send_header("Vary", "Accept-Encoding")
            if self.command == "POST":
                self.send_header("Connection", "close")      # request bodies are not always read to the end: never reuse the connection after a POST
                self.close_connection = True
            self.send_header("Content-Type", ctype + ("; charset=utf-8" if ctype.startswith("text") or "json" in ctype else ""))
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            for k, v in (extra or []):
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(data)
        except (ConnectionError, BrokenPipeError, TimeoutError):
            # the browser closed / cancelled the request (page refreshed, tab changed, auto-refresh restarted) before the
            # answer was delivered - nobody is waiting for it any more, so this is not an error
            self.close_connection = True

    def _session(self):
        now = time.time()
        for k in [k for k, v in SESSIONS.items() if now - v["created"] > SESSION_TTL]:
            SESSIONS.pop(k, None)
        c = SimpleCookie(self.headers.get("Cookie", ""))
        tok = c["sid"].value if "sid" in c else None
        s = SESSIONS.get(tok)
        if s:                                   # re-checked on every request: a user removed from the list is out at once, a changed role applies at once
            a = access_for(s, self._is_owner())
            if a is None:
                SESSIONS.pop(tok, None)
                return tok, None
            s["role"], s["tabs"], s["owner"], s["admin"], s["dl"], s["master"] = a["role"], a["tabs"], self._is_owner(), a["admin"], a["dl"], a["master"]
        return tok, s

    def _who(self, s):
        return {**{k: s[k] for k in ("name", "email", "username", "instance")}, "role": s.get("role", ""), "tabs": s.get("tabs", ["*"]), "owner": bool(s.get("owner")), "admin": bool(s.get("admin")), "dl": s.get("dl", True) is not False, "master": s.get("master", True) is not False}

    def _guard(self):
        if not self._local_host():
            self._send(403, {"error": "Forbidden"})
            return False
        origin = self.headers.get("Origin")
        if origin and urllib.parse.urlparse(origin).hostname not in ("localhost", "127.0.0.1") \
                and not (SHARE and urllib.parse.urlparse(origin).netloc == self.headers.get("Host", "")):
            self._send(403, {"error": "Forbidden"})
            return False
        return True

    DL_PATHS = {"/api/cases", "/api/timelogs", "/api/casehistory", "/api/caseflow", "/api/milestones", "/api/tags", "/api/ownership", "/api/forwards", "/api/csatowner"}

    def _dl_ok(self, path):
        """Master-filter downloads (and the history reads that follow them) need the Download permission of the role."""
        if path in self.DL_PATHS:
            _, s = self._session()
            if s and not s.get("dl", True):
                self._send(403, {"error": "Downloading data from Salesforce is limited to roles with the Download permission. Ask an administrator."})
                return False
        return True

    def _run(self, fn):
        try:
            fn()
        except ApiError as e:
            self._send(e.status, {"error": e.message})
        except (ConnectionError, BrokenPipeError, TimeoutError):
            self.close_connection = True      # browser went away - nothing to reply to
        except Exception as e:  # noqa
            self._send(500, {"error": f"Server error: {e}"})

    # -- routes
    def do_GET(self):
        if not self._guard():
            return
        url = urllib.parse.urlparse(self.path)
        if not self._dl_ok(url.path):
            return
        if url.path == "/api/version":
            info = {"build": BUILD, "pid": os.getpid()}
            if self._is_owner():
                info["file"] = str(Path(__file__).resolve())
            return self._send(200, info)
        if url.path.startswith("/vendor/"):      # chart / PowerPoint libraries: served from the vendor folder, so the app needs no internet (falls back to the CDN if the file is missing)
            name = url.path[len("/vendor/"):]
            if name not in VENDOR_LIBS:
                return self._send(404, {"error": "Not found"})
            p = HERE / "vendor" / name
            if p.is_file():
                return self._send(200, p.read_bytes(), "application/javascript")
            return self._send(302, b"", "text/plain", [("Location", VENDOR_LIBS[name])])
        elif url.path.rstrip("/") in ("/live", "/group"):      # short links: /live -> /?view=live, /group -> /?view=group
            self._send(302, b"", "text/plain", [("Location", "/?view=" + url.path.strip("/"))])
        elif url.path in ("/", "/index.html"):
            page = (HERE / "index.html").read_bytes()
            prefs = json.dumps(load_prefs()).replace("<", "\\u003c").encode("utf-8")      # settings kept in the app folder
            page = page.replace(b"</head>", b"<script>window.__PREFS__=" + prefs + b";</script></head>", 1)
            self._send(200, page, "text/html")
        elif url.path == "/api/store":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            def get():
                p = store_path(urllib.parse.parse_qs(url.query).get("key", [""])[0])
                if not p.exists():
                    return self._send(404, {"error": "No local data"})
                self._send(200, p.read_bytes(), "application/json")
            self._run(get)
        elif url.path == "/api/diagcase":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            self._run(lambda: self._send(200, diag_case(s, urllib.parse.parse_qs(url.query).get("number", [""])[0])))
        elif url.path == "/api/me":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            self._send(200, self._who(s))
        elif url.path == "/api/access":      # settings: only on the PC that runs the server
            _, s = self._session()
            if not (s and s.get("admin")):
                return self._send(403, {"error": "Only users with the Admin role can open the access settings."})
            self._send(200, load_access())
        elif url.path == "/api/saved":      # never returns the password or token themselves
            sv = load_saved() if self._is_owner() else None      # the owner's saved login is never offered to other machines
            if not sv:
                return self._send(200, {"saved": False})
            self._send(200, {"saved": True, "env": sv.get("env", "production"), "domain": sv.get("domain", ""),
                             "username": sv["username"], "hasPassword": bool(sv.get("password")),
                             "hasToken": bool(sv.get("token"))})
        elif url.path == "/api/cases":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            field = q.get("field", ["created"])[0]
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            all_time = q.get("all", [""])[0] == "1"
            if field not in ("created", "resolved", "survey", "open") or (not all_time and (not dfrom or not dto)):
                return self._send(400, {"error": "Choose the date field and a From / To range."})
            csat = q.get("csat", [""])[0]
            fb = q.get("fb", [""])[0]
            obj = q.get("obj", [""])[0]
            full = q.get("full", [""])[0] == "1"
            if field == "open":      # Group Insights: standard + mapped fields only (never the slow "all fields" block), kept 5 minutes per login
                if q.get("refresh", [""])[0] == "1":
                    s.get("_ttl", {}).pop("open_cases", None)
                self._run(lambda: self._send(200, cached(s, "open_cases", 300, lambda: pfuture(fetch_cases, s, "open", "", "", True).result())))
                return
            self._run(lambda: self._send(200, fetch_cases(s, field, dfrom, dto, all_time, csat, fb, obj, full)))
        elif url.path == "/api/tags":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            try:
                days = max(0, min(int(q.get("days", ["0"])[0] or 0), 3650))
            except ValueError:
                days = 0
            cols = [x for x in q.get("cols", [""])[0].split(",") if re.fullmatch(r"[TRCGX]:[A-Za-z0-9_ .()/&+\-]{1,80}", x)][:60]
            try:
                cap = max(1000, min(int(q.get("cap", ["5000"])[0] or 5000), 50000))
            except ValueError:
                cap = 5000
            all_time = q.get("all", [""])[0] == "1"
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            if not all_time and bool(dfrom) != bool(dto):
                return self._send(400, {"error": "Choose both From and To."})
            self._run(lambda: self._send(200, fetch_tags(s, days, q.get("open", [""])[0] == "1", cols, cap,
                                                         dfrom or None, dto or None, all_time)))
        elif url.path == "/api/auditreport":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            all_time = q.get("all", [""])[0] == "1"
            if not all_time and (not dfrom or not dto):
                return self._send(400, {"error": "Choose a From / To range."})
            lst = lambda k: [x for x in q.get(k, [""])[0].split("|") if x.strip()]
            self._run(lambda: self._send(200, fetch_audit_tags(s, dfrom, dto, all_time, lst("tags"), lst("groups"))))
        elif url.path == "/api/tagdetail":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            rid = urllib.parse.parse_qs(url.query).get("id", [""])[0]
            self._run(lambda: self._send(200, fetch_tag_detail(s, rid)))
        elif url.path == "/api/unresolved":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            grp = urllib.parse.parse_qs(url.query).get("group", [""])[0].strip()
            self._run(lambda: self._send(200, count_unresolved(s, grp or None)))
        elif url.path == "/api/groups":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            self._run(lambda: self._send(200, cached(s, "groups", 120, lambda: list_groups(s))))
        elif url.path == "/api/groupday":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            try:
                dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
                sf_datetime(dfrom), sf_datetime(dto)
            except Exception:
                return self._send(400, {"error": "Bad date range."})
            self._run(lambda: self._send(200, group_day(s, q.get("group", [""])[0], dfrom, dto)))
        elif url.path == "/api/audit":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            qs = urllib.parse.parse_qs(url.query)
            term = qs.get("case", [""])[0]
            paused = qs.get("paused", [""])[0]
            self._run(lambda: self._send(200, audit_case(s, term, paused)))
        elif url.path == "/api/audit/file":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            qs = urllib.parse.parse_qs(url.query)
            def serve():
                data, name, ctype, inline = audit_file(s, qs.get("kind", [""])[0], qs.get("id", [""])[0])
                if qs.get("dl", [""])[0]:
                    inline = False
                disp = ("inline" if inline else "attachment") + "; filename*=UTF-8''" + urllib.parse.quote(name)
                self._send(200, data, ctype, extra=[("Content-Disposition", disp)])
            self._run(serve)
        elif url.path == "/api/audit/users":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            self._run(lambda: self._send(200, {"users": audit_users(s)}))
        elif url.path == "/api/audit/tags":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            self._run(lambda: self._send(200, audit_tag_options(s)))
        elif url.path == "/api/similar":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            self._run(lambda: self._send(200, find_similar(s, q.get("q", [""])[0], q.get("exclude", [""])[0], q.get("limit", ["10"])[0], q.get("sort", ["recent"])[0])))
        elif url.path == "/api/recurrence":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            if not dfrom or not dto:
                return self._send(400, {"error": "Choose a From / To range."})
            self._run(lambda: self._send(200, find_recurrence(s, dfrom, dto, q.get("limit", ["10"])[0], q.get("max", ["100"])[0], q.get("lookback", ["6"])[0], q.get("scope", ["all"])[0])))
        elif url.path == "/api/timelogs":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            all_time = q.get("all", [""])[0] == "1"
            if not all_time and (not dfrom or not dto):
                return self._send(400, {"error": "Choose a From / To range."})
            self._run(lambda: self._send(200, fetch_timelogs(s, dfrom, dto, q.get("tf", [""])[0], q.get("tt", [""])[0], all_time, q.get("full", [""])[0] == "1")))
        elif url.path == "/api/casehistory":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            all_time = q.get("all", [""])[0] == "1"
            if not all_time and (not dfrom or not dto):
                return self._send(400, {"error": "Choose a From / To range."})
            self._run(lambda: self._send(200, fetch_case_history(s, dfrom, dto, all_time)))
        elif url.path == "/api/meta":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            self._run(lambda: self._send(200, cached(s, "meta", 600, lambda: build_meta(s))))
        elif url.path == "/api/milestones":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            q = urllib.parse.parse_qs(url.query)
            field = q.get("field", ["created"])[0]
            dfrom, dto = q.get("from", [""])[0], q.get("to", [""])[0]
            all_time = q.get("all", [""])[0] == "1"
            if field == "open":      # Group Insights: milestones of every unresolved case, kept 5 minutes per login
                if q.get("refresh", [""])[0] == "1":
                    s.get("_ttl", {}).pop("open_milestones", None)
                self._run(lambda: self._send(200, cached(s, "open_milestones", 300, lambda: fetch_milestones(s, "open", "", "", True))))
                return
            if field not in ("created", "resolved", "survey") or (not all_time and (not dfrom or not dto)):
                return self._send(400, {"error": "Choose the date field and a From / To range."})
            self._run(lambda: self._send(200, fetch_milestones(s, field, dfrom, dto, all_time, q.get("obj", [""])[0])))
        else:
            self._send(404, {"error": "Not found"})

    def do_POST(self):
        if not self._guard():
            return
        path = urllib.parse.urlparse(self.path).path
        if not self._dl_ok(path):
            return
        if path == "/api/login":
            self._run(self._login)
        elif path == "/api/logout":
            tok, s = self._session()
            if s:
                try:   # end the Salesforce session too
                    urllib.request.urlopen(urllib.request.Request(
                        s["instance"] + "/services/oauth2/revoke",
                        data=urllib.parse.urlencode({"token": s["sid"]}).encode()), timeout=15)
                except Exception:
                    pass
            SESSIONS.pop(tok, None)
            self._send(200, {"ok": True}, extra=[("Set-Cookie", "sid=; Max-Age=0; Path=/; HttpOnly; SameSite=Strict")])
        elif path == "/api/access":
            _, s = self._session()
            if not (s and s.get("admin")):
                return self._send(403, {"error": "Only users with the Admin role can change the access settings."})
            def save_access():
                n = int(self.headers.get("Content-Length", 0))
                if n > 400_000:
                    raise ApiError(413, "Request too large")
                cfg = clean_access(json.loads(self.rfile.read(n) or b"{}"))
                atomic_write(ACCESS_FILE, json.dumps(cfg, indent=1).encode("utf-8"))
                self._send(200, cfg)
            self._run(save_access)
        elif path in ("/api/audit/post", "/api/audit/tag"):
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 60_000:
                return self._send(413, {"error": "Request too large"})
            def write():
                b = json.loads(self.rfile.read(n) or b"{}")
                if path == "/api/audit/post":
                    self._send(200, audit_add_post(s, b.get("caseId"), b.get("text"), b.get("mentions")))
                else:
                    self._send(200, audit_add_tag(s, b.get("caseId"), b.get("tagId"), b.get("tagName")))
            self._run(write)
        elif path == "/api/ownership":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 8_000_000:
                return self._send(413, {"error": "Request too large"})
            body = json.loads(self.rfile.read(n) or b"{}")
            self._run(lambda: self._send(200, ownership_times(s, body.get("cases") or [])))
        elif path == "/api/caseflow":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 8_000_000:
                return self._send(413, {"error": "Request too large"})
            body = json.loads(self.rfile.read(n) or b"{}")
            # who (agent) and which group held each case, moment by moment, from the Owner / Agent and Group field history
            self._run(lambda: self._send(200, ownership_times(s, body.get("cases") or [], with_segments=True)))
        elif path == "/api/forwards":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 8_000_000:
                return self._send(413, {"error": "Request too large"})
            body = json.loads(self.rfile.read(n) or b"{}")
            self._run(lambda: self._send(200, group_forwards(s, body.get("cases") or [])))
        elif path == "/api/csatowner":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 8_000_000:
                return self._send(413, {"error": "Request too large"})
            body = json.loads(self.rfile.read(n) or b"{}")
            self._run(lambda: self._send(200, csat_owners(s, body.get("cases") or [])))
        elif path == "/api/reopens":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 8_000_000:
                return self._send(413, {"error": "Request too large"})
            body = json.loads(self.rfile.read(n) or b"{}")
            self._run(lambda: self._send(200, reopen_info(s, body.get("cases") or [])))
        elif path == "/api/statuslog":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            if n > 8_000_000:
                return self._send(413, {"error": "Request too large"})
            body = json.loads(self.rfile.read(n) or b"{}")
            self._run(lambda: self._send(200, status_timelines(s, body.get("cases") or [])))
        elif path == "/api/store":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            body = self.rfile.read(n)
            def put():
                p = store_path(urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("key", [""])[0])
                if not body.lstrip()[:1] in (b"{", b"["):      # cheap check instead of parsing a multi-MB body again
                    raise ApiError(400, "Invalid data.")
                atomic_write(p, body)
                self._send(200, {"ok": True})
            self._run(put)
        elif path == "/api/prefs":
            n = int(self.headers.get("Content-Length", 0))
            if n > 1_000_000:
                return self._send(413, {"error": "Request too large"})
            def put():
                d = json.loads(self.rfile.read(n) or b"{}")
                if not isinstance(d, dict):
                    raise ApiError(400, "Invalid settings.")
                atomic_write(PREFS_FILE, json.dumps(d).encode("utf-8"))
                self._send(200, {"ok": True})
            self._run(put)
        elif path == "/api/timelog-map":
            _, s = self._session()
            if not s:
                return self._send(401, {"error": "Not logged in"})
            n = int(self.headers.get("Content-Length", 0))
            body = json.loads(self.rfile.read(n) or b"{}")
            def put():
                data = _overrides()
                for role, val in (body or {}).items():
                    if role in TL_ROLES:
                        if val and FIELD_NAME_RE.match(str(val)):
                            data[TL_ROLES[role][0]] = str(val)
                        else:
                            data.pop(TL_ROLES[role][0], None)
                FIELD_MAP_FILE.write_text(json.dumps(data, indent=2), "utf-8")
                s.pop("_tlog", None)
                self._send(200, {"ok": True})
            self._run(put)
        elif path == "/api/forget":
            clear_saved()
            self._send(200, {"ok": True})
        else:
            self._send(404, {"error": "Not found"})

    def do_DELETE(self):
        if not self._guard():
            return
        url = urllib.parse.urlparse(self.path)
        _, s = self._session()
        if url.path != "/api/store":
            return self._send(404, {"error": "Not found"})
        if not s:
            return self._send(401, {"error": "Not logged in"})
        if not s.get("dl", True):
            return self._send(403, {"error": "Deleting the saved data is limited to roles with the Download permission."})
        def rm():
            try:
                store_path(urllib.parse.parse_qs(url.query).get("key", [""])[0]).unlink()
            except FileNotFoundError:
                pass
            self._send(200, {"ok": True})
        self._run(rm)

    def _login(self):
        n = int(self.headers.get("Content-Length", 0))
        if n > 10_000:
            raise ApiError(413, "Request too large")
        d = json.loads(self.rfile.read(n) or b"{}")
        saved = {}                                 # the server keeps NO saved logins: "Remember my login" lives in each person's own browser
        auto = bool(d.get("auto"))
        if auto:                                   # log in with the saved credentials
            if not saved:
                raise ApiError(400, "No saved login.")
            d = dict(saved)
        else:
            same = saved and saved.get("username", "").lower() == d.get("username", "").strip().lower()
            if same and not d.get("password"):     # blank = keep the saved password
                d["password"] = saved.get("password", "")
            if same and not d.get("token") and d.get("keepToken"):
                d["token"] = saved.get("token", "")
        remember = bool(d.get("remember"))
        username, password, token = d.get("username", "").strip(), d.get("password", ""), d.get("token", "").strip()
        if not username or not password:
            raise ApiError(400, "Enter your Salesforce username and password.")
        env = d.get("env", "production")
        if env == "production":
            domain = "login.salesforce.com"
        elif env == "sandbox":
            domain = "test.salesforce.com"
        else:
            raw = d.get("domain", "").strip()
            domain = urllib.parse.urlparse(raw if "//" in raw else "//" + raw).hostname or ""
            if not ALLOWED_HOST.match(domain):
                raise ApiError(400, "Domain must be a Salesforce address (e.g. yourcompany.my.salesforce.com).")
        sess = soap_login(domain, username, password, token)
        acc = access_for(sess, self._is_owner())
        if acc is None:
            raise ApiError(403, f"Access denied: {sess.get('email') or username} is not on the list of allowed users, or has been blocked. Ask the administrator to add your Salesforce email in Settings > Access.")
        sess["role"], sess["tabs"], sess["owner"], sess["admin"], sess["dl"], sess["master"] = acc["role"], acc["tabs"], self._is_owner(), acc["admin"], acc["dl"], acc["master"]
        tok = secrets.token_urlsafe(32)
        SESSIONS[tok] = sess
        self._send(200, self._who(sess),
                   extra=[("Set-Cookie", f"sid={tok}; Path=/; HttpOnly; SameSite=Strict")])


if __name__ == "__main__":
    DATA_DIR.mkdir(exist_ok=True)
    try:
        clear_saved()                          # remove any login an older version stored on the server (it could be somebody else's)
    except Exception:
        pass
    if BACKGROUND or sys.stdout is None or sys.stderr is None:      # no console (pythonw): keep print() working and keep a log
        try:
            _lf = open(Path(__file__).resolve().parent / "server.log", "w", encoding="utf-8", buffering=1)
            sys.stdout = sys.stderr = _lf
        except Exception:
            sys.stdout = sys.stderr = open(os.devnull, "w")
    print(f"Local data folder: {DATA_DIR}")
    srv = QuietServer(("0.0.0.0" if SHARE else "127.0.0.1", PORT), Handler)   # localhost only unless --share
    url = f"http://localhost:{PORT}"
    print(f"CST Analytics running at {url}  (press Ctrl+C to stop)")
    if SHARE:
        def _share_info():      # name lookups can be slow without a network: never hold up the start for them
            import socket
            try:
                ips = sorted({i[4][0] for i in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET)})
            except Exception:
                ips = []
            print("SHARING ON - others on your network can open:")
            for h in [socket.gethostname()] + ips:
                print(f"   http://{h}:{PORT}/live    http://{h}:{PORT}/group")
            print("They log in with their OWN Salesforce login; your saved login is never offered to them.")
        threading.Thread(target=_share_info, daemon=True).start()
    print("Build: group forwarding (/api/forwards) included")
    if not BACKGROUND:
        try:
            webbrowser.open(url)
        except Exception:
            pass
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")
