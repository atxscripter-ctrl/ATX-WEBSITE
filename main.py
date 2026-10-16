"""
ATXxKEEM HUB v2 — full stack, no external HTTP deps required.
Adds: 2FA (TOTP), multi-HWID, trial keys, kill switch, maintenance,
announcement, referral UI, bulk gen, CSV export, watermark, multi-stage loader,
HMAC loader, AES-at-rest payloads, IP velocity, concurrent validation, HWID
clustering, SSE live dashboard, status page, Turnstile, subscription keys,
license API, burn-after-read, paste versions, /metrics, webhooks, backup CLI,
Redis-optional rate limiting, Postgres-optional DB.
"""

import os
import sys
import json
import time
import random
import string
import sqlite3
import secrets
import threading
import traceback
import hmac
import hashlib
import base64
import io
import csv
import zipfile
import shutil
import argparse
from datetime import datetime, timezone
from functools import wraps
from collections import defaultdict, deque
from urllib.request import Request, urlopen
from urllib.parse import urlencode, urlparse, parse_qs
from urllib.error import URLError, HTTPError

from flask import (
    Flask, render_template, request, jsonify, session, g,
    redirect, abort, Response, send_file
)
from werkzeug.security import generate_password_hash, check_password_hash
from itsdangerous import URLSafeTimedSerializer, BadSignature, SignatureExpired

try:
    import pyotp
except ImportError:
    pyotp = None

try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives import hashes as _hashes
    HAVE_CRYPTO = True
except ImportError:
    HAVE_CRYPTO = False

try:
    import redis as redis_lib
    HAVE_REDIS = True
except ImportError:
    redis_lib = None
    HAVE_REDIS = False

try:
    import psycopg
    HAVE_PG = True
except ImportError:
    psycopg = None
    HAVE_PG = False


# ============================================================
# APP / CONFIG
# ============================================================
app = Flask(__name__)
app.secret_key = os.getenv("ATX_SECRET", secrets.token_hex(32))
app.permanent_session_lifetime = 60 * 60 * 24 * 30
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.getenv("ATX_HTTPS", "0") == "1",
    MAX_CONTENT_LENGTH=2 * 1024 * 1024,
)

DATA_DIR = os.getenv("DATA_DIR", "/data")
KEYS_FILE      = os.path.join(DATA_DIR, "keys.json")
SCRIPTS_FILE   = os.path.join(DATA_DIR, "scripts.json")
PASTES_FILE    = os.path.join(DATA_DIR, "pastes.json")
CONFIG_FILE    = os.path.join(DATA_DIR, "config.json")
BLACKLIST_FILE = os.path.join(DATA_DIR, "blacklist.json")
AUDIT_FILE     = os.path.join(DATA_DIR, "audit.json")
STATS_FILE     = os.path.join(DATA_DIR, "stats.json")
USERS_DB       = os.path.join(DATA_DIR, "users.db")
PAYLOAD_STORE  = os.path.join(DATA_DIR, "payloads")

TELEGRAM_CHANNEL   = os.getenv("TG_CHANNEL", "https://t.me/+_eEH_XgASVFhNmNl")
TELEGRAM_PREMIUM   = os.getenv("TG_PREMIUM", "https://t.me/AntraxdevZ")
TELEGRAM_BOT_TOKEN = os.getenv("TG_BOT_TOKEN", "").strip()
TELEGRAM_ADMIN_IDS = set(x.strip() for x in os.getenv("TG_ADMIN_IDS", "").split(",") if x.strip())
TELEGRAM_NOTIFY_CHAT = os.getenv("TG_NOTIFY_CHAT", "").strip()

DEFAULT_PAYLOAD_URL = os.getenv("SCRIPT_PAYLOAD_URL", "https://pastebin.com/raw/V4jrqcQz")

ADMIN_USERNAME = os.getenv("ATX_ADMIN_USER", "antrax")
ADMIN_PASSWORD = os.getenv("ATX_ADMIN_PASS", "antraxdevzagodz")

KEY_VALID_HOURS = 12
TASK_COOLDOWN_SECONDS = 30
PASTE_MAX_LENGTH = 100000
ORIGIN_ALLOWLIST = set(x.strip() for x in os.getenv("ATX_ORIGINS", "").split(",") if x.strip())

TURNSTILE_SITE   = os.getenv("TURNSTILE_SITE", "").strip()
TURNSTILE_SECRET = os.getenv("TURNSTILE_SECRET", "").strip()

HMAC_SECRET = os.getenv("ATX_HMAC_SECRET", "").strip() or app.secret_key

PAYLOAD_KEY_ENV = os.getenv("ATX_PAYLOAD_KEY", "").strip()

WEBHOOK_URL    = os.getenv("WEBHOOK_URL", "").strip()
WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "").strip()

ATX_DB_URL = os.getenv("ATX_DB_URL", "").strip()
ATX_REDIS_URL = os.getenv("ATX_REDIS_URL", "").strip()

signer = URLSafeTimedSerializer(app.secret_key, salt="atx-ttl")
twofa_signer = URLSafeTimedSerializer(app.secret_key, salt="atx-2fa")

_redis = None
if HAVE_REDIS and ATX_REDIS_URL:
    try:
        _redis = redis_lib.from_url(ATX_REDIS_URL, decode_responses=True)
        _redis.ping()
    except Exception:
        _redis = None


# ============================================================
# HTTP (stdlib)
# ============================================================
def http_post_json(url, payload, timeout=35, headers=None):
    try:
        data = json.dumps(payload).encode("utf-8")
        h = {"Content-Type": "application/json", "User-Agent": "atx-hub/2.0"}
        if headers: h.update(headers)
        req = Request(url, data=data, headers=h)
        with urlopen(req, timeout=timeout) as r:
            body = r.read().decode("utf-8", errors="replace")
            return json.loads(body) if body else {}
    except (URLError, HTTPError, ValueError, TimeoutError) as e:
        print(f"[http_post_json] {url} -> {e}")
        return None


def http_get_json(url, params=None, timeout=40):
    try:
        if params:
            url = url + ("&" if "?" in url else "?") + urlencode(params)
        req = Request(url, headers={"User-Agent": "atx-hub/2.0"})
        with urlopen(req, timeout=timeout) as r:
            body = r.read().decode("utf-8", errors="replace")
            return json.loads(body) if body else {}
    except (URLError, HTTPError, ValueError, TimeoutError) as e:
        print(f"[http_get_json] {url} -> {e}")
        return None


def http_get_text(url, timeout=10):
    try:
        req = Request(url, headers={"User-Agent": "atx-hub/2.0"})
        with urlopen(req, timeout=timeout) as r:
            return r.read().decode("utf-8", errors="replace")
    except (URLError, HTTPError, TimeoutError) as e:
        print(f"[http_get_text] {url} -> {e}")
        return None


def http_post_form(url, form, timeout=10):
    try:
        data = urlencode(form).encode()
        req = Request(url, data=data, headers={
            "Content-Type": "application/x-www-form-urlencoded",
            "User-Agent": "atx-hub/2.0",
        })
        with urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8", errors="replace"))
    except Exception as e:
        print(f"[http_post_form] {url} -> {e}")
        return None


# ============================================================
# STORAGE
# ============================================================
def ensure_storage():
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(PAYLOAD_STORE, exist_ok=True)
    for f, default in [
        (KEYS_FILE, {}),
        (SCRIPTS_FILE, {}),
        (PASTES_FILE, {}),
        (BLACKLIST_FILE, {"keys": [], "hwids": []}),
        (AUDIT_FILE, []),
        (STATS_FILE, {"daily": {}, "totals": {}}),
    ]:
        if not os.path.exists(f):
            with open(f, "w") as fp:
                json.dump(default, fp, indent=2)
    if not os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, "w") as fp:
            json.dump({
                "payloads": {
                    "free":    DEFAULT_PAYLOAD_URL,
                    "premium": DEFAULT_PAYLOAD_URL,
                    "vip":     DEFAULT_PAYLOAD_URL,
                },
                "key_durations_hours": {"free": 12, "premium": 24 * 7, "vip": 24 * 30},
                "hwid_slots": {"free": 1, "premium": 3, "vip": 5, "trial": 1},
                "killswitch": {"on": False, "message": "Service temporarily disabled."},
                "maintenance": {"on": False, "message": "Under maintenance. Back soon."},
                "announcement": "",
                "webhooks": {"events": []},
                "subscription_interval_hours": 24,
            }, fp, indent=2)
    init_db()


def _load(path):
    ensure_storage()
    try:
        with open(path, "r") as f:
            return json.load(f)
    except (json.JSONDecodeError, IOError):
        return {}


def _save(path, data):
    ensure_storage()
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp, path)


def load_keys():       return _load(KEYS_FILE)
def save_keys(d):      _save(KEYS_FILE, d)
def load_scripts():    return _load(SCRIPTS_FILE)
def save_scripts(d):   _save(SCRIPTS_FILE, d)
def load_pastes():     return _load(PASTES_FILE)
def save_pastes(d):    _save(PASTES_FILE, d)
def load_blacklist():  return _load(BLACKLIST_FILE)
def save_blacklist(d): _save(BLACKLIST_FILE, d)
def load_audit():      return _load(AUDIT_FILE) or []
def save_audit(d):     _save(AUDIT_FILE, d[-5000:])
def load_stats():      return _load(STATS_FILE)
def save_stats(d):     _save(STATS_FILE, d)
def load_config():     return _load(CONFIG_FILE)
def save_config(d):    _save(CONFIG_FILE, d)


# ============================================================
# PAYLOAD ENCRYPTION (AES-GCM at rest)
# ============================================================
def _payload_key():
    if PAYLOAD_KEY_ENV:
        raw = bytes.fromhex(PAYLOAD_KEY_ENV)
        if len(raw) >= 32: return raw[:32]
    return hashlib.sha256(app.secret_key.encode()).digest()


def encrypt_blob(plaintext: str) -> bytes:
    if not HAVE_CRYPTO:
        return plaintext.encode("utf-8")
    aes = AESGCM(_payload_key())
    nonce = os.urandom(12)
    ct = aes.encrypt(nonce, plaintext.encode("utf-8"), b"atx-payload")
    return b"ATXAES1" + nonce + ct


def decrypt_blob(blob: bytes) -> str:
    if not HAVE_CRYPTO or not blob.startswith(b"ATXAES1"):
        return blob.decode("utf-8", errors="replace")
    aes = AESGCM(_payload_key())
    nonce = blob[7:19]
    ct = blob[19:]
    return aes.decrypt(nonce, ct, b"atx-payload").decode("utf-8", errors="replace")


# ============================================================
# STATS
# ============================================================
def _today_key():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def stat_incr(name, amount=1):
    if _redis:
        try:
            _redis.hincrby(f"atx:stats:daily:{_today_key()}", name, amount)
            _redis.hincrby("atx:stats:totals", name, amount)
            return
        except Exception:
            pass
    s = load_stats()
    day = _today_key()
    s.setdefault("daily", {}).setdefault(day, {})
    s["daily"][day][name] = s["daily"][day].get(name, 0) + amount
    s.setdefault("totals", {})
    s["totals"][name] = s["totals"].get(name, 0) + amount
    save_stats(s)


def stats_snapshot(days=14):
    if _redis:
        try:
            totals = {k: int(v) for k, v in _redis.hgetall("atx:stats:totals").items()}
            labels = sorted((_redis.keys("atx:stats:daily:*")))
            labels = [k.split(":")[-1] for k in labels][-days:]
            series = {"labels": labels, "keys_generated": [], "validations": [],
                      "pastes_created": [], "registrations": [], "paste_views": []}
            for lbl in labels:
                row = _redis.hgetall(f"atx:stats:daily:{lbl}")
                for k in series:
                    if k == "labels": continue
                    series[k].append(int(row.get(k, 0)))
            return {"totals": totals, "series": series}
        except Exception:
            pass
    s = load_stats()
    daily = s.get("daily", {})
    keys = sorted(daily.keys())[-days:]
    series = {
        "labels": keys,
        "keys_generated": [daily[k].get("keys_generated", 0) for k in keys],
        "validations":    [daily[k].get("validations", 0) for k in keys],
        "pastes_created": [daily[k].get("pastes_created", 0) for k in keys],
        "registrations":  [daily[k].get("registrations", 0) for k in keys],
        "paste_views":    [daily[k].get("paste_views", 0) for k in keys],
    }
    return {"totals": s.get("totals", {}), "series": series}


# ============================================================
# AUDIT + WEBHOOKS
# ============================================================
def audit(action, actor=None, detail=None, ip=None):
    entry = {
        "ts": int(time.time()),
        "action": action,
        "actor": actor,
        "detail": detail or {},
        "ip": ip or (request.remote_addr if request else None),
    }
    log = load_audit()
    log.append(entry)
    save_audit(log)
    _maybe_webhook(action, entry)


def _maybe_webhook(action, entry):
    if not WEBHOOK_URL: return
    cfg = load_config()
    events = (cfg.get("webhooks") or {}).get("events") or []
    if not events: return
    if action not in events and "*" not in events: return
    def _send():
        headers = {}
        if WEBHOOK_SECRET:
            sig = hmac.new(WEBHOOK_SECRET.encode(), json.dumps(entry).encode(), hashlib.sha256).hexdigest()
            headers["X-ATX-Signature"] = sig
        http_post_json(WEBHOOK_URL, entry, timeout=10, headers=headers)
    threading.Thread(target=_send, daemon=True).start()


# ============================================================
# DB
# ============================================================
def get_db():
    if "db" not in g:
        if ATX_DB_URL and HAVE_PG:
            g.db = psycopg.connect(ATX_DB_URL, row_factory=psycopg.rows.dict_row)
            g.db_kind = "pg"
        else:
            g.db = sqlite3.connect(USERS_DB)
            g.db.row_factory = sqlite3.Row
            g.db_kind = "sqlite"
    return g.db


def db_kind():
    return g.get("db_kind", "sqlite")


def _q(sql):
    # SQLite uses ?, Postgres uses %s — normalize
    if db_kind() == "pg":
        return sql.replace("?", "%s")
    return sql


def db_exec(sql, params=(), commit=True, fetch=None):
    db = get_db()
    cur = db.cursor()
    cur.execute(_q(sql), params)
    result = None
    if fetch == "one":
        result = cur.fetchone()
    elif fetch == "all":
        result = cur.fetchall()
    if commit:
        db.commit()
    try:
        cur.close()
    except Exception:
        pass
    return result


@app.teardown_appcontext
def close_db(_exc):
    db = g.pop("db", None)
    if db is not None:
        try: db.close()
        except Exception: pass


def _row_val(row, key, default=None):
    if row is None: return default
    try:
        return row[key]
    except (KeyError, IndexError, TypeError):
        return default


def init_db():
    os.makedirs(DATA_DIR, exist_ok=True)
    if ATX_DB_URL and HAVE_PG:
        with psycopg.connect(ATX_DB_URL, row_factory=psycopg.rows.dict_row) as conn:
            cur = conn.cursor()
            cur.execute("""
                CREATE TABLE IF NOT EXISTS users (
                    id SERIAL PRIMARY KEY,
                    username TEXT UNIQUE NOT NULL,
                    password_hash TEXT NOT NULL,
                    created BIGINT NOT NULL,
                    paste_count INTEGER NOT NULL DEFAULT 0,
                    is_admin INTEGER NOT NULL DEFAULT 0,
                    is_banned INTEGER NOT NULL DEFAULT 0,
                    api_token TEXT,
                    referral_code TEXT UNIQUE,
                    referred_by INTEGER,
                    bonus_hours INTEGER NOT NULL DEFAULT 0,
                    totp_secret TEXT,
                    session_version INTEGER NOT NULL DEFAULT 1
                )
            """)
            for ddl in [
                "ALTER TABLE users ADD COLUMN IF NOT EXISTS totp_secret TEXT",
                "ALTER TABLE users ADD COLUMN IF NOT EXISTS session_version INTEGER NOT NULL DEFAULT 1",
                "ALTER TABLE users ADD COLUMN IF NOT EXISTS bonus_hours INTEGER NOT NULL DEFAULT 0",
            ]:
                try: cur.execute(ddl)
                except Exception: pass
            conn.commit()
            cur.close()
    else:
        conn = sqlite3.connect(USERS_DB)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE NOT NULL,
                password_hash TEXT NOT NULL,
                created INTEGER NOT NULL,
                paste_count INTEGER NOT NULL DEFAULT 0,
                is_admin INTEGER NOT NULL DEFAULT 0,
                is_banned INTEGER NOT NULL DEFAULT 0,
                api_token TEXT,
                referral_code TEXT UNIQUE,
                referred_by INTEGER,
                bonus_hours INTEGER NOT NULL DEFAULT 0
            )
        """)
        for ddl in [
            "ALTER TABLE users ADD COLUMN is_admin INTEGER NOT NULL DEFAULT 0",
            "ALTER TABLE users ADD COLUMN is_banned INTEGER NOT NULL DEFAULT 0",
            "ALTER TABLE users ADD COLUMN api_token TEXT",
            "ALTER TABLE users ADD COLUMN referral_code TEXT",
            "ALTER TABLE users ADD COLUMN referred_by INTEGER",
            "ALTER TABLE users ADD COLUMN bonus_hours INTEGER NOT NULL DEFAULT 0",
            "ALTER TABLE users ADD COLUMN totp_secret TEXT",
            "ALTER TABLE users ADD COLUMN session_version INTEGER NOT NULL DEFAULT 1",
        ]:
            try: conn.execute(ddl)
            except sqlite3.OperationalError: pass
        conn.commit()
        conn.close()
    seed_admin()


def seed_admin():
    # runs outside app context — use direct connection
    now = int(time.time())
    if ATX_DB_URL and HAVE_PG:
        with psycopg.connect(ATX_DB_URL, row_factory=psycopg.rows.dict_row) as conn:
            cur = conn.cursor()
            cur.execute("SELECT * FROM users WHERE username = %s", (ADMIN_USERNAME,))
            row = cur.fetchone()
            if row is None:
                cur.execute(
                    "INSERT INTO users (username, password_hash, created, is_admin, referral_code) VALUES (%s, %s, %s, 1, %s)",
                    (ADMIN_USERNAME, generate_password_hash(ADMIN_PASSWORD), now, gen_referral_code()),
                )
            else:
                cur.execute(
                    "UPDATE users SET password_hash = %s, is_admin = 1, is_banned = 0 WHERE username = %s",
                    (generate_password_hash(ADMIN_PASSWORD), ADMIN_USERNAME),
                )
            conn.commit()
            cur.close()
    else:
        conn = sqlite3.connect(USERS_DB)
        conn.row_factory = sqlite3.Row
        row = conn.execute("SELECT * FROM users WHERE username = ?", (ADMIN_USERNAME,)).fetchone()
        if row is None:
            conn.execute(
                "INSERT INTO users (username, password_hash, created, paste_count, is_admin, referral_code) VALUES (?, ?, ?, 0, 1, ?)",
                (ADMIN_USERNAME, generate_password_hash(ADMIN_PASSWORD), now, gen_referral_code()),
            )
        else:
            conn.execute(
                "UPDATE users SET password_hash = ?, is_admin = 1, is_banned = 0 WHERE username = ?",
                (generate_password_hash(ADMIN_PASSWORD), ADMIN_USERNAME),
            )
            if not row["referral_code"]:
                conn.execute("UPDATE users SET referral_code = ? WHERE id = ?",
                             (gen_referral_code(), row["id"]))
        conn.commit()
        conn.close()


def find_user_by_username(u):
    return db_exec("SELECT * FROM users WHERE username = ?", (u,), commit=False, fetch="one")


def find_user_by_id(uid):
    return db_exec("SELECT * FROM users WHERE id = ?", (uid,), commit=False, fetch="one")


def find_user_by_token(tok):
    return db_exec("SELECT * FROM users WHERE api_token = ?", (tok,), commit=False, fetch="one")


def create_user(username, password, referred_by_code=None):
    ref_id = None
    if referred_by_code:
        r = db_exec("SELECT id FROM users WHERE referral_code = ?", (referred_by_code,), commit=False, fetch="one")
        if r:
            ref_id = _row_val(r, "id")
    code = gen_referral_code()
    for _ in range(10):
        if not db_exec("SELECT 1 FROM users WHERE referral_code = ?", (code,), commit=False, fetch="one"):
            break
        code = gen_referral_code()
    db_exec(
        "INSERT INTO users (username, password_hash, created, referral_code, referred_by) VALUES (?, ?, ?, ?, ?)",
        (username, generate_password_hash(password), int(time.time()), code, ref_id),
    )
    if ref_id:
        db_exec("UPDATE users SET bonus_hours = bonus_hours + 2 WHERE id = ?", (ref_id,))
    return find_user_by_username(username)


def bump_paste_count(uid):
    db_exec("UPDATE users SET paste_count = paste_count + 1 WHERE id = ?", (uid,))


def bump_session_version(uid):
    db_exec("UPDATE users SET session_version = session_version + 1 WHERE id = ?", (uid,))


# ============================================================
# AUTH
# ============================================================
def _session_binding_ok():
    if not session.get("user_id"): return True
    ip = _client_ip()
    ua_hash = hashlib.sha256((request.headers.get("User-Agent") or "").encode()).hexdigest()[:16]
    if session.get("bind_ip") and session["bind_ip"] != ip:
        return False
    if session.get("bind_ua") and session["bind_ua"] != ua_hash:
        return False
    return True


def current_user():
    uid = session.get("user_id")
    if not uid:
        auth = request.headers.get("Authorization", "")
        if auth.startswith("Bearer "):
            u = find_user_by_token(auth[7:].strip())
            if u:
                return u
        return None
    if not _session_binding_ok():
        session.clear()
        return None
    u = find_user_by_id(uid)
    if not u: return None
    if session.get("sv") is not None and _row_val(u, "session_version", 1) != session["sv"]:
        session.clear()
        return None
    return u


def login_required(fn):
    @wraps(fn)
    def w(*a, **kw):
        u = current_user()
        if not u:
            return jsonify({"success": False, "error": "Login required"}), 401
        if _row_val(u, "is_banned", 0):
            return jsonify({"success": False, "error": "Account banned"}), 403
        return fn(*a, **kw)
    return w


def admin_required(fn):
    @wraps(fn)
    def w(*a, **kw):
        u = current_user()
        if not u:
            return jsonify({"success": False, "error": "Login required"}), 401
        if not _row_val(u, "is_admin", 0):
            return jsonify({"success": False, "error": "Admin only"}), 403
        if _row_val(u, "is_banned", 0):
            return jsonify({"success": False, "error": "Account banned"}), 403
        return fn(*a, **kw)
    return w


def valid_username(u):
    return 3 <= len(u) <= 20 and all(c.isalnum() or c == "_" for c in u)


COMMON_PASSWORDS = {
    "password","123456","12345678","qwerty","111111","abc123","password1",
    "letmein","welcome","admin","admin123","root","toor","pass123",
}


def password_ok(p):
    if len(p) < 8: return False, "Password must be at least 8 characters"
    if p.lower() in COMMON_PASSWORDS: return False, "Password too common"
    return True, ""


def user_public(u):
    if not u: return None
    return {
        "id": _row_val(u, "id"),
        "username": _row_val(u, "username"),
        "created": _row_val(u, "created"),
        "paste_count": _row_val(u, "paste_count", 0),
        "is_admin": bool(_row_val(u, "is_admin", 0)),
        "is_banned": bool(_row_val(u, "is_banned", 0)),
        "referral_code": _row_val(u, "referral_code"),
        "bonus_hours": _row_val(u, "bonus_hours", 0),
        "totp_enabled": bool(_row_val(u, "totp_secret")),
    }


# ============================================================
# IDS
# ============================================================
def gen_key(tier="free"):
    return f"ATX-{tier[:3].upper()}-" + "-".join(secrets.token_hex(2).upper() for _ in range(3))


def gen_script_id():
    return "SC-" + secrets.token_hex(4).upper()


def gen_paste_id(length=8):
    alphabet = string.ascii_letters + string.digits
    return "".join(secrets.choice(alphabet) for _ in range(length))


def gen_referral_code():
    return "REF" + secrets.token_hex(3).upper()


def gen_api_token():
    return "atx_" + secrets.token_urlsafe(32)


# ============================================================
# CAPTCHA
# ============================================================
def gen_math_challenge():
    op_sym = random.choice(["+", "-", "x"])
    if op_sym == "x":
        a, b = random.randint(2, 12), random.randint(2, 12)
        ans = a * b
    else:
        a = random.randint(10, 50); b = random.randint(5, 30)
        if op_sym == "-" and b > a: a, b = b, a
        ans = a + b if op_sym == "+" else a - b
    return {"question": f"What is {a} {op_sym} {b}?", "answer": str(ans)}


def gen_text_challenge():
    chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    code = "".join(random.choices(chars, k=5))
    return {"question": f"Type this code: {code}", "answer": code}


def gen_sequence_challenge():
    start = random.randint(1, 5); step = random.randint(2, 4)
    seq = [start + step * i for i in range(4)]
    return {"question": f"What comes next? {', '.join(map(str, seq))}, ?",
            "answer": str(start + step * 4)}


def gen_challenge():
    return random.choice([gen_math_challenge, gen_text_challenge, gen_sequence_challenge])()


def turnstile_verify(token, ip):
    if not TURNSTILE_SECRET:
        return True
    if not token:
        return False
    r = http_post_form(
        "https://challenges.cloudflare.com/turnstile/v0/siteverify",
        {"secret": TURNSTILE_SECRET, "response": token, "remoteip": ip},
    )
    return bool(r and r.get("success"))


# ============================================================
# RATE LIMIT + IP VELOCITY
# ============================================================
_rate_store = defaultdict(list)
_ip_velocity = defaultdict(deque)
_rate_lock = threading.Lock()
VELOCITY_WINDOW = 600
VELOCITY_MAX = 240


def _client_ip():
    fwd = request.headers.get("X-Forwarded-For", "")
    if fwd: return fwd.split(",")[0].strip()
    return request.remote_addr or "0.0.0.0"


def _velocity_trip(ip):
    now = time.time()
    with _rate_lock:
        dq = _ip_velocity[ip]
        while dq and now - dq[0] > VELOCITY_WINDOW:
            dq.popleft()
        dq.append(now)
        if len(dq) > VELOCITY_MAX:
            return True
    return False


def rate_limit(name, limit, window):
    def deco(fn):
        @wraps(fn)
        def w(*a, **kw):
            ip = _client_ip()
            if _velocity_trip(ip):
                audit("rate.velocity", actor="?", detail={"ip": ip, "endpoint": name})
                resp = jsonify({"success": False, "error": "Too many requests"})
                resp.status_code = 429
                resp.headers["Retry-After"] = "300"
                return resp
            key = (name, ip)
            now = time.time()
            if _redis:
                try:
                    rk = f"atx:rl:{name}:{ip}"
                    p = _redis.pipeline()
                    p.zremrangebyscore(rk, 0, now - window)
                    p.zcard(rk)
                    p.zadd(rk, {str(now): now})
                    p.expire(rk, window + 5)
                    _, cnt, *_ = p.execute()
                    if cnt >= limit:
                        resp = jsonify({"success": False, "error": f"Rate limited"})
                        resp.status_code = 429
                        resp.headers["Retry-After"] = str(window)
                        return resp
                    return fn(*a, **kw)
                except Exception:
                    pass
            with _rate_lock:
                bucket = _rate_store[key]
                bucket[:] = [t for t in bucket if now - t < window]
                if len(bucket) >= limit:
                    retry = int(window - (now - bucket[0])) + 1
                    resp = jsonify({"success": False, "error": f"Rate limited. Retry in {retry}s"})
                    resp.status_code = 429
                    resp.headers["Retry-After"] = str(retry)
                    return resp
                bucket.append(now)
            return fn(*a, **kw)
        return w
    return deco


def _rate_cleanup():
    while True:
        time.sleep(120)
        now = time.time()
        with _rate_lock:
            for k in list(_rate_store.keys()):
                _rate_store[k][:] = [t for t in _rate_store[k] if now - t < 600]
                if not _rate_store[k]:
                    del _rate_store[k]
            for k in list(_ip_velocity.keys()):
                dq = _ip_velocity[k]
                while dq and now - dq[0] > VELOCITY_WINDOW:
                    dq.popleft()
                if not dq:
                    del _ip_velocity[k]


threading.Thread(target=_rate_cleanup, daemon=True).start()


# ============================================================
# CSRF / ORIGIN / MAINTENANCE
# ============================================================
def _origin_ok():
    origin = request.headers.get("Origin") or request.headers.get("Referer") or ""
    if not origin: return True
    if not ORIGIN_ALLOWLIST: return True
    return any(origin.startswith(o) for o in ORIGIN_ALLOWLIST)


@app.before_request
def _csrf_and_origin():
    p = request.path or ""
    if p.startswith("/static/") or p in ("/health", "/status", "/metrics", "/status-page"):
        return None
    cfg = load_config()
    if (cfg.get("maintenance") or {}).get("on"):
        if p not in ("/health", "/status", "/metrics", "/status-page") and not p.startswith("/api/admin"):
            if p.startswith("/api/"):
                return jsonify({"success": False, "error": "Maintenance"}), 503
            return Response(_maintenance_page(cfg), mimetype="text/html")
    if request.method in ("POST", "PUT", "DELETE", "PATCH"):
        if request.headers.get("Authorization", "").startswith("Bearer "):
            return None
        if not _origin_ok():
            return jsonify({"success": False, "error": "Origin not allowed"}), 403
        if session.get("user_id"):
            token = request.headers.get("X-CSRF-Token") or (request.get_json(silent=True) or {}).get("_csrf")
            expected = session.get("csrf_token")
            if expected and token != expected:
                return jsonify({"success": False, "error": "CSRF token invalid"}), 403
    return None


def _maintenance_page(cfg):
    msg = (cfg.get("maintenance") or {}).get("message", "Under maintenance.")
    return f"""<!doctype html><html><head><meta charset=utf-8><title>ATX</title>
<style>body{{background:#000;color:#fff;font-family:sans-serif;display:flex;align-items:center;justify-content:center;height:100vh;margin:0}}
.box{{text-align:center;padding:40px;border:1px solid #222;border-radius:12px;max-width:420px}}
h1{{font-size:20px;margin:0 0 12px}}p{{color:#888;font-size:14px;line-height:1.6}}</style></head>
<body><div class=box><h1>ATX</h1><p>{msg}</p></div></body></html>"""


def _ensure_csrf():
    if "csrf_token" not in session:
        session["csrf_token"] = secrets.token_urlsafe(24)
    return session["csrf_token"]


# ============================================================
# PAYLOADS + HMAC
# ============================================================
def _config():
    return load_config()


def get_payload_url(tier="free"):
    cfg = load_config()
    payloads = cfg.get("payloads") or {}
    url = (payloads.get(tier) or "").strip()
    if not url:
        url = (payloads.get("free") or "").strip() or DEFAULT_PAYLOAD_URL
    return url


def get_key_duration(tier="free"):
    cfg = load_config()
    durs = cfg.get("key_durations_hours") or {}
    return int(durs.get(tier, KEY_VALID_HOURS))


def get_hwid_slots(tier="free"):
    cfg = load_config()
    slots = cfg.get("hwid_slots") or {}
    return int(slots.get(tier, 1))


def sign_loader(token):
    return hmac.new(HMAC_SECRET.encode(), token.encode(), hashlib.sha256).hexdigest()[:32]


def verify_loader_sig(token, sig):
    return hmac.compare_digest(sign_loader(token), sig or "")


def watermark(payload, key=None, hwid=None, tier=None):
    tag = f"--[atx ts={int(time.time())}"
    if key: tag += f" key={key}"
    if hwid: tag += f" hwid={hwid[:16]}"
    if tier: tag += f" tier={tier}"
    tag += "]"
    lines = payload.splitlines()
    if lines and lines[0].startswith("--[atx"):
        lines[0] = tag
    else:
        lines = [tag] + lines
    return "\n".join(lines)


def build_script_payload(tier="free", ttl_seconds=86400, hwid_required=False, key=None):
    url = get_payload_url(tier)
    token = signer.dumps({"tier": tier, "u": url, "hwid_required": hwid_required})
    base = request.host_url.rstrip("/") if request else ""
    sig = sign_loader(token)
    short = f"{base}/t/{token}?sig={sig}"
    if hwid_required:
        return (
            'local hwid = game:GetService("RbxAnalyticsService"):GetClientId()\n'
            f'loadstring(game:HttpGet("{short}&hwid=" .. hwid))()'
        )
    return f'loadstring(game:HttpGet("{short}"))()'


def build_multistage_stub(key, base):
    """Lua stub: hits /api/stage1 with key+hwid, then loads the returned payload url."""
    return (
        f'local KEY = "{key}"\n'
        'local BASE = "' + base + '"\n'
        'local hwid = game:GetService("RbxAnalyticsService"):GetClientId()\n'
        'local ok, res = pcall(function()\n'
        '  return game:HttpGet(BASE .. "/api/stage1?key=" .. KEY .. "&hwid=" .. hwid)\n'
        'end)\n'
        'if not ok then return end\n'
        'local data = game:GetService("HttpService"):JSONDecode(res)\n'
        'if not data.valid then return end\n'
        'loadstring(game:HttpGet(data.payload_url))()'
    )


# ============================================================
# KEY LOGIC
# ============================================================
def key_is_blacklisted(key):
    return key in (load_blacklist().get("keys") or [])


def hwid_is_blacklisted(hwid):
    if not hwid: return False
    return hwid in (load_blacklist().get("hwids") or [])


def _key_hwids(entry):
    if not entry: return []
    if isinstance(entry.get("hwids"), list):
        return entry["hwids"]
    if entry.get("hwid"):
        return [entry["hwid"]]
    return []


def validate_key_entry(key, hwid=None, client_ip=None):
    if key_is_blacklisted(key): return False, None, "Key blacklisted"
    if hwid_is_blacklisted(hwid): return False, None, "HWID blacklisted"
    keys = load_keys()
    entry = keys.get(key)
    if not entry: return False, None, "Invalid key"
    if entry.get("expires", 0) < time.time(): return False, None, "Key expired"

    hwids = _key_hwids(entry)
    slot_limit = get_hwid_slots(entry.get("tier", "free"))

    if hwid:
        if hwid in hwids:
            pass  # already bound
        elif len(hwids) < slot_limit:
            hwids.append(hwid)
            entry["hwids"] = hwids
            entry.pop("hwid", None)
        else:
            return False, None, "All HWID slots in use"

    # concurrent validation check
    now = int(time.time())
    last_hwid = entry.get("last_hwid")
    last_ts = entry.get("last_validate_ts", 0)
    if hwid and last_hwid and last_hwid != hwid and now - last_ts < 60:
        entry["flagged_concurrent"] = True
        entry["flagged_ts"] = now
        audit("key.concurrent", actor="system",
              detail={"key": key, "prev": last_hwid[:16], "now": hwid[:16]})
    entry["last_hwid"] = hwid
    entry["last_validate_ts"] = now
    if client_ip: entry["last_ip"] = client_ip

    # trial: consume on first successful validate
    if entry.get("trial"):
        if entry.get("consumed"):
            return False, None, "Trial already used"
        entry["consumed"] = True
        bl = load_blacklist()
        bl.setdefault("keys", [])
        if key not in bl["keys"]:
            bl["keys"].append(key)
        save_blacklist(bl)

    keys[key] = entry
    save_keys(keys)
    return True, entry, None


# ============================================================
# PASTE HELPERS
# ============================================================
def paste_is_expired(p):
    exp = p.get("expires")
    return bool(exp) and exp < time.time()


def _purge_expired_pastes():
    while True:
        try:
            pastes = load_pastes()
            now = time.time()
            changed = False
            for pid in list(pastes.keys()):
                if pastes[pid].get("expires") and pastes[pid]["expires"] < now:
                    del pastes[pid]
                    changed = True
            if changed:
                save_pastes(pastes)
        except Exception:
            traceback.print_exc()
        time.sleep(600)


threading.Thread(target=_purge_expired_pastes, daemon=True).start()


# ============================================================
# SUBSCRIPTION REISSUE
# ============================================================
def _subscription_loop():
    while True:
        time.sleep(120)
        try:
            cfg = load_config()
            interval = int(cfg.get("subscription_interval_hours", 24))
            keys = load_keys()
            changed = False
            now = int(time.time())
            for k, v in keys.items():
                if not v.get("subscription"): continue
                if not v.get("sub_active", True): continue
                next_reissue = v.get("sub_next_reissue", 0)
                if now >= next_reissue:
                    v["expires"] = now + interval * 3600
                    v["sub_next_reissue"] = now + interval * 3600
                    v["sub_last_reissue"] = now
                    changed = True
                    audit("key.sub.reissue", actor="system", detail={"key": k})
            if changed:
                save_keys(keys)
        except Exception:
            traceback.print_exc()


threading.Thread(target=_subscription_loop, daemon=True).start()


# ============================================================
# LIVE EVENTS (SSE)
# ============================================================
_event_bus = deque(maxlen=200)
_event_id = 0
_event_lock = threading.Lock()


def push_event(kind, payload):
    global _event_id
    with _event_lock:
        _event_id += 1
        _event_bus.append({"id": _event_id, "ts": int(time.time()), "kind": kind, "payload": payload})
    if _redis:
        try:
            _redis.publish("atx:events", json.dumps({"kind": kind, "payload": payload}))
        except Exception:
            pass


# ============================================================
# TELEGRAM BOT
# ============================================================
_tg_offset = 0


def tg_api(method, payload=None):
    if not TELEGRAM_BOT_TOKEN: return None
    return http_post_json(
        f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/{method}",
        payload or {}, timeout=35,
    )


def tg_notify(text):
    if TELEGRAM_NOTIFY_CHAT:
        tg_api("sendMessage", {"chat_id": TELEGRAM_NOTIFY_CHAT, "text": text, "parse_mode": "HTML"})


def _tg_send_doc(chat_id, filename, content):
    # multipart via urllib is painful — send as text chunks or via sendMessage with monospace
    tg_api("sendMessage", {"chat_id": chat_id, "text": f"`{content[:3900]}`", "parse_mode": "MarkdownV2"})


def _tg_handle(update):
    msg = update.get("message") or update.get("edited_message")
    if not msg: return
    chat_id = msg.get("chat", {}).get("id")
    from_id = str(msg.get("from", {}).get("id", ""))
    text = (msg.get("text") or "").strip()
    if not text.startswith("/"): return
    if TELEGRAM_ADMIN_IDS and from_id not in TELEGRAM_ADMIN_IDS:
        tg_api("sendMessage", {"chat_id": chat_id, "text": "Not authorized."})
        return
    parts = text.split()
    cmd = parts[0].lower()

    if cmd == "/start":
        tg_api("sendMessage", {"chat_id": chat_id,
            "text": "ATX bot v2.\n/seturl <tier> <url>\n/urls\n/genkey <tier>\n"
                    "/bulkgen <tier> <count>\n/user <username>\n/stats\n/killswitch on|off\n"
                    "/maint on|off\n/announce <text>"})
    elif cmd == "/seturl" and len(parts) >= 3:
        tier, url = parts[1].lower(), parts[2]
        if tier not in ("free", "premium", "vip"):
            tg_api("sendMessage", {"chat_id": chat_id, "text": "tier must be free/premium/vip"}); return
        if not (url.startswith("http://") or url.startswith("https://")):
            tg_api("sendMessage", {"chat_id": chat_id, "text": "url must be http(s)"}); return
        cfg = load_config()
        cfg.setdefault("payloads", {})[tier] = url
        save_config(cfg)
        audit("tg.seturl", actor=f"tg:{from_id}", detail={"tier": tier, "url": url})
        tg_api("sendMessage", {"chat_id": chat_id, "text": f"[{tier}] -> {url}"})
    elif cmd == "/urls":
        cfg = load_config()
        lines = [f"{k}: {v}" for k, v in (cfg.get("payloads") or {}).items()]
        tg_api("sendMessage", {"chat_id": chat_id, "text": "\n".join(lines) or "none"})
    elif cmd == "/genkey" and len(parts) >= 2:
        tier = parts[1].lower()
        if tier not in ("free", "premium", "vip", "trial"):
            tg_api("sendMessage", {"chat_id": chat_id, "text": "invalid tier"}); return
        k = _create_key(tier)
        tg_api("sendMessage", {"chat_id": chat_id, "text": f"{k} ({tier})"})
    elif cmd == "/bulkgen" and len(parts) >= 3:
        tier = parts[1].lower()
        try: n = int(parts[2])
        except: tg_api("sendMessage", {"chat_id": chat_id, "text": "count must be int"}); return
        n = min(max(n, 1), 200)
        keys_out = [_create_key(tier) for _ in range(n)]
        tg_api("sendMessage", {"chat_id": chat_id, "text": "\n".join(keys_out)})
    elif cmd == "/user" and len(parts) >= 2:
        u = find_user_by_username(parts[1])
        if not u:
            tg_api("sendMessage", {"chat_id": chat_id, "text": "not found"}); return
        txt = (f"id={_row_val(u,'id')}\nuser={_row_val(u,'username')}\n"
               f"admin={bool(_row_val(u,'is_admin',0))}\nbanned={bool(_row_val(u,'is_banned',0))}\n"
               f"pastes={_row_val(u,'paste_count',0)}\nbonus={_row_val(u,'bonus_hours',0)}h")
        tg_api("sendMessage", {"chat_id": chat_id, "text": txt})
    elif cmd == "/stats":
        snap = stats_snapshot()
        t = snap["totals"]
        txt = "\n".join(f"{k}: {v}" for k, v in t.items()) or "no data"
        tg_api("sendMessage", {"chat_id": chat_id, "text": txt})
    elif cmd == "/killswitch" and len(parts) >= 2:
        state = parts[1].lower() == "on"
        cfg = load_config()
        cfg.setdefault("killswitch", {})["on"] = state
        save_config(cfg)
        audit("tg.killswitch", actor=f"tg:{from_id}", detail={"on": state})
        tg_api("sendMessage", {"chat_id": chat_id, "text": f"killswitch: {state}"})
    elif cmd == "/maint" and len(parts) >= 2:
        state = parts[1].lower() == "on"
        cfg = load_config()
        cfg.setdefault("maintenance", {})["on"] = state
        save_config(cfg)
        audit("tg.maint", actor=f"tg:{from_id}", detail={"on": state})
        tg_api("sendMessage", {"chat_id": chat_id, "text": f"maintenance: {state}"})
    elif cmd == "/announce":
        msg = text[len("/announce"):].strip()
        cfg = load_config()
        cfg["announcement"] = msg
        save_config(cfg)
        tg_api("sendMessage", {"chat_id": chat_id, "text": "ok"})


def _create_key(tier="free"):
    keys = load_keys()
    k = gen_key(tier)
    now = int(time.time())
    entry = {"created": now, "expires": now + get_key_duration(tier) * 3600, "tier": tier, "hwids": []}
    if tier == "trial":
        entry["expires"] = now + 3600
        entry["trial"] = True
    keys[k] = entry
    save_keys(keys)
    stat_incr("keys_generated")
    push_event("key.created", {"key": k, "tier": tier})
    return k


def _tg_poll():
    global _tg_offset
    if not TELEGRAM_BOT_TOKEN: return
    print("[tg] polling started")
    while True:
        try:
            data = http_get_json(
                f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates",
                params={"offset": _tg_offset + 1, "timeout": 30}, timeout=40,
            )
            if not data:
                time.sleep(3); continue
            for u in data.get("result", []):
                _tg_offset = max(_tg_offset, u["update_id"])
                try: _tg_handle(u)
                except Exception: traceback.print_exc()
        except Exception:
            traceback.print_exc()
            time.sleep(5)


def start_tg_thread():
    if TELEGRAM_BOT_TOKEN:
        threading.Thread(target=_tg_poll, daemon=True).start()


# ============================================================
# ROUTES — ROOT
# ============================================================
@app.route("/")
def index():
    cfg = load_config()
    return render_template(
        "index.html",
        telegram_channel=TELEGRAM_CHANNEL,
        telegram_premium=TELEGRAM_PREMIUM,
        csrf_token=_ensure_csrf(),
        announcement=cfg.get("announcement", ""),
        turnstile_site=TURNSTILE_SITE,
    )


@app.route("/status")
def status():
    keys = load_keys()
    now = time.time()
    active = sum(1 for v in keys.values() if v.get("expires", 0) > now)
    cfg = load_config()
    return jsonify({
        "status": "ok",
        "time": int(now),
        "active_keys": active,
        "total_keys": len(keys),
        "total_pastes": len(load_pastes()),
        "killswitch": bool((cfg.get("killswitch") or {}).get("on")),
        "maintenance": bool((cfg.get("maintenance") or {}).get("on")),
    })


@app.route("/health")
def health():
    return jsonify({"status": "ok", "time": int(time.time())})


@app.route("/status-page")
def status_page():
    keys = load_keys()
    now = time.time()
    active = sum(1 for v in keys.values() if v.get("expires", 0) > now)
    pastes = len(load_pastes())
    snap = stats_snapshot(1)
    valid_24h = snap["series"]["validations"][-1] if snap["series"]["validations"] else 0
    cfg = load_config()
    return Response(f"""<!doctype html><html><head><meta charset=utf-8><title>ATX status</title>
<style>body{{background:#000;color:#fff;font-family:sans-serif;padding:40px;max-width:640px;margin:0 auto}}
h1{{margin:0 0 4px}}.sub{{color:#888;font-size:13px;margin-bottom:24px}}
.row{{display:flex;justify-content:space-between;padding:14px;border-bottom:1px solid #1a1a1a;font-size:14px}}
.k{{color:#888}}.v{{font-weight:700}}a{{color:#8af;text-decoration:none}}</style></head>
<body><h1>ATX Status</h1><div class=sub>live service status</div>
<div class=row><span class=k>Service</span><span class=v>{"MAINTENANCE" if (cfg.get('maintenance') or {}).get('on') else ("DISABLED" if (cfg.get('killswitch') or {}).get('on') else "ONLINE")}</span></div>
<div class=row><span class=k>Active keys</span><span class=v>{active}</span></div>
<div class=row><span class=k>Total keys</span><span class=v>{len(keys)}</span></div>
<div class=row><span class=k>Pastes</span><span class=v>{pastes}</span></div>
<div class=row><span class=k>Validations (24h)</span><span class=v>{valid_24h}</span></div>
<div class=row><span class=k>Server time (UTC)</span><span class=v>{datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')}</span></div>
<p style="margin-top:24px"><a href="/">← back to hub</a></p></body></html>""", mimetype="text/html")


@app.route("/metrics")
def metrics():
    keys = load_keys()
    now = time.time()
    active = sum(1 for v in keys.values() if v.get("expires", 0) > now)
    pastes = load_pastes()
    snap = stats_snapshot(30)
    lines = [
        "# HELP atx_active_keys Active (unexpired) keys",
        "# TYPE atx_active_keys gauge",
        f"atx_active_keys {active}",
        "# HELP atx_total_keys Total keys",
        "# TYPE atx_total_keys gauge",
        f"atx_total_keys {len(keys)}",
        "# HELP atx_total_pastes Total pastes",
        "# TYPE atx_total_pastes gauge",
        f"atx_total_pastes {len(pastes)}",
    ]
    for k, v in (snap.get("totals") or {}).items():
        safe = k.replace("-", "_")
        lines.append(f"atx_total_{safe} {v}")
    return Response("\n".join(lines) + "\n", mimetype="text/plain")


# ============================================================
# CONFIG / PUBLIC
# ============================================================
@app.route("/api/config", methods=["GET"])
def api_config():
    cfg = load_config()
    return jsonify({
        "success": True,
        "announcement": cfg.get("announcement", ""),
        "killswitch": bool((cfg.get("killswitch") or {}).get("on")),
        "maintenance": bool((cfg.get("maintenance") or {}).get("on")),
        "turnstile_site": TURNSTILE_SITE,
    })


# ============================================================
# AUTH
# ============================================================
def _do_login(u):
    session.permanent = True
    session["user_id"] = _row_val(u, "id")
    session["bind_ip"] = _client_ip()
    session["bind_ua"] = hashlib.sha256((request.headers.get("User-Agent") or "").encode()).hexdigest()[:16]
    session["sv"] = _row_val(u, "session_version", 1)
    _ensure_csrf()


@app.route("/api/auth/register", methods=["POST"])
@rate_limit("register", 5, 600)
def auth_register():
    data = request.get_json() or {}
    username = (data.get("username") or "").strip()
    password = (data.get("password") or "").strip()
    ref = (data.get("ref") or "").strip() or None
    if TURNSTILE_SECRET:
        if not turnstile_verify(data.get("turnstile_token"), _client_ip()):
            return jsonify({"success": False, "error": "Captcha failed"}), 400
    if not valid_username(username):
        return jsonify({"success": False, "error": "Username 3-20 chars, alnum/underscore"}), 400
    ok, msg = password_ok(password)
    if not ok: return jsonify({"success": False, "error": msg}), 400
    if find_user_by_username(username):
        return jsonify({"success": False, "error": "Username taken"}), 409
    u = create_user(username, password, ref)
    _do_login(u)
    stat_incr("registrations")
    audit("auth.register", actor=username)
    push_event("user.registered", {"username": username})
    return jsonify({"success": True, "user": user_public(u), "csrf_token": session["csrf_token"]})


@app.route("/api/auth/login", methods=["POST"])
@rate_limit("login", 8, 300)
def auth_login():
    data = request.get_json() or {}
    username = (data.get("username") or "").strip()
    password = (data.get("password") or "").strip()
    code = (data.get("code") or "").strip()
    if TURNSTILE_SECRET and not code:
        if not turnstile_verify(data.get("turnstile_token"), _client_ip()):
            return jsonify({"success": False, "error": "Captcha failed"}), 400
    if not username or not password:
        return jsonify({"success": False, "error": "Missing fields"}), 400
    u = find_user_by_username(username)
    if not u or not check_password_hash(_row_val(u, "password_hash"), password):
        return jsonify({"success": False, "error": "Invalid credentials"}), 401
    if _row_val(u, "is_banned", 0):
        return jsonify({"success": False, "error": "Account banned"}), 403
    secret = _row_val(u, "totp_secret")
    if secret and pyotp:
        if not code:
            return jsonify({"success": True, "requires_2fa": True}), 200
        totp = pyotp.TOTP(secret)
        if not totp.verify(code, valid_window=1):
            return jsonify({"success": False, "error": "Invalid 2FA code"}), 401
    _do_login(u)
    audit("auth.login", actor=username)
    return jsonify({"success": True, "user": user_public(u), "csrf_token": session["csrf_token"]})


@app.route("/api/auth/logout", methods=["POST"])
def auth_logout():
    session.clear()
    return jsonify({"success": True})


@app.route("/api/auth/me", methods=["GET"])
def auth_me():
    u = current_user()
    return jsonify({"success": True, "user": user_public(u), "csrf_token": _ensure_csrf()})


@app.route("/api/auth/apitoken", methods=["POST"])
@login_required
def auth_apitoken():
    u = current_user()
    if not _row_val(u, "api_token"):
        tok = gen_api_token()
        db_exec("UPDATE users SET api_token = ? WHERE id = ?", (tok, _row_val(u, "id")))
        audit("user.apitoken.create", actor=_row_val(u, "username"))
    u = find_user_by_id(_row_val(u, "id"))
    return jsonify({"success": True, "api_token": _row_val(u, "api_token")})


@app.route("/api/auth/apitoken/revoke", methods=["POST"])
@login_required
def auth_apitoken_revoke():
    u = current_user()
    db_exec("UPDATE users SET api_token = NULL WHERE id = ?", (_row_val(u, "id"),))
    audit("user.apitoken.revoke", actor=_row_val(u, "username"))
    return jsonify({"success": True})


# 2FA
@app.route("/api/auth/2fa/setup", methods=["POST"])
@login_required
def twofa_setup():
    if not pyotp:
        return jsonify({"success": False, "error": "pyotp not installed"}), 500
    u = current_user()
    secret = pyotp.random_base32()
    uri = pyotp.TOTP(secret).provisioning_uri(name=_row_val(u, "username"), issuer_name="ATX")
    session["pending_2fa_secret"] = secret
    return jsonify({"success": True, "secret": secret, "uri": uri})


@app.route("/api/auth/2fa/enable", methods=["POST"])
@login_required
def twofa_enable():
    if not pyotp: return jsonify({"success": False, "error": "pyotp not installed"}), 500
    data = request.get_json() or {}
    code = (data.get("code") or "").strip()
    secret = session.get("pending_2fa_secret")
    if not secret: return jsonify({"success": False, "error": "Run setup first"}), 400
    if not pyotp.TOTP(secret).verify(code, valid_window=1):
        return jsonify({"success": False, "error": "Invalid code"}), 400
    u = current_user()
    db_exec("UPDATE users SET totp_secret = ? WHERE id = ?", (secret, _row_val(u, "id")))
    session.pop("pending_2fa_secret", None)
    audit("user.2fa.enable", actor=_row_val(u, "username"))
    return jsonify({"success": True})


@app.route("/api/auth/2fa/disable", methods=["POST"])
@login_required
def twofa_disable():
    u = current_user()
    db_exec("UPDATE users SET totp_secret = NULL WHERE id = ?", (_row_val(u, "id"),))
    audit("user.2fa.disable", actor=_row_val(u, "username"))
    return jsonify({"success": True})


# session invalidate (used after password change etc.)
@app.route("/api/auth/invalidate", methods=["POST"])
@login_required
def auth_invalidate():
    u = current_user()
    bump_session_version(_row_val(u, "id"))
    session.clear()
    return jsonify({"success": True})


# ============================================================
# CAPTCHA
# ============================================================
@app.route("/api/get-challenge", methods=["POST"])
@rate_limit("challenge", 20, 60)
def get_challenge():
    c = gen_challenge()
    session["captcha_answer"] = c["answer"].upper()
    session["captcha_time"] = time.time()
    session["captcha_solved"] = False
    return jsonify({"success": True, "question": c["question"]})


@app.route("/api/verify-human", methods=["POST"])
@rate_limit("verify", 30, 60)
def verify_human():
    data = request.get_json() or {}
    answer = (data.get("answer") or "").strip().upper()
    expected = session.get("captcha_answer", "")
    ts = session.get("captcha_time", 0)
    if not expected: return jsonify({"success": False, "error": "No challenge"}), 400
    if time.time() - ts > 300: return jsonify({"success": False, "error": "Expired"}), 410
    if answer != expected:
        session.pop("captcha_answer", None)
        return jsonify({"success": False, "error": "Wrong answer"}), 400
    session["captcha_solved"] = True
    session["captcha_solved_time"] = time.time()
    session.pop("captcha_answer", None)
    return jsonify({"success": True})


# ============================================================
# KEY GENERATION
# ============================================================
@app.route("/api/generate-key", methods=["POST"])
@rate_limit("genkey", 5, 3600)
def generate_key():
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return jsonify({"success": False, "error": "Service disabled"}), 503
    if not session.get("captcha_solved"):
        return jsonify({"success": False, "error": "Complete verification first"}), 403
    elapsed = time.time() - session.get("captcha_solved_time", 0)
    if elapsed < TASK_COOLDOWN_SECONDS:
        return jsonify({"success": False, "error": f"Wait {int(TASK_COOLDOWN_SECONDS - elapsed)}s"}), 429
    tier = "free"
    new_key = _create_key(tier)
    session.pop("captcha_solved", None)
    session.pop("captcha_solved_time", None)
    tg_notify(f"New key generated: <code>{new_key}</code> ({tier})")
    return jsonify({"success": True, "key": new_key, "expires_in_hours": get_key_duration(tier), "tier": tier})


@app.route("/api/validate-key", methods=["GET", "POST"])
@rate_limit("validate", 120, 60)
def validate_key():
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return jsonify({"valid": False, "error": "Service disabled"}), 503
    if request.method == "GET":
        key = (request.args.get("key") or "").strip()
        hwid = (request.args.get("hwid") or "").strip() or None
    else:
        d = request.get_json(silent=True) or {}
        key = (d.get("key") or "").strip()
        hwid = (d.get("hwid") or "").strip() or None
    if not key: return jsonify({"valid": False, "error": "No key"}), 400
    ok, entry, err = validate_key_entry(key, hwid, _client_ip())
    stat_incr("validations")
    if not ok: return jsonify({"valid": False, "error": err}), 403
    keys = load_keys()
    if key in keys:
        keys[key]["last_used"] = int(time.time())
        save_keys(keys)
    return jsonify({
        "valid": True,
        "tier": entry.get("tier", "free"),
        "expires": entry.get("expires"),
        "hwids": _key_hwids(entry),
        "slots": get_hwid_slots(entry.get("tier", "free")),
    })


# trial
@app.route("/api/trial-key", methods=["POST"])
@rate_limit("trial", 3, 86400)
def trial_key():
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return jsonify({"success": False, "error": "Service disabled"}), 503
    if not session.get("captcha_solved"):
        return jsonify({"success": False, "error": "Complete verification first"}), 403
    elapsed = time.time() - session.get("captcha_solved_time", 0)
    if elapsed < TASK_COOLDOWN_SECONDS:
        return jsonify({"success": False, "error": f"Wait {int(TASK_COOLDOWN_SECONDS - elapsed)}s"}), 429
    k = _create_key("trial")
    session.pop("captcha_solved", None)
    session.pop("captcha_solved_time", None)
    audit("key.trial", actor="?", detail={"key": k})
    return jsonify({"success": True, "key": k, "expires_in_hours": 1, "tier": "trial"})


# ============================================================
# SCRIPT / STAGE1 / TTL LOADER / SHORT LOADER
# ============================================================
@app.route("/api/generate-script", methods=["POST"])
@rate_limit("genscript", 10, 3600)
def generate_script():
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return jsonify({"success": False, "error": "Service disabled"}), 503
    if not session.get("captcha_solved"):
        return jsonify({"success": False, "error": "Complete verification first"}), 403
    elapsed = time.time() - session.get("captcha_solved_time", 0)
    if elapsed < TASK_COOLDOWN_SECONDS:
        return jsonify({"success": False, "error": f"Wait {int(TASK_COOLDOWN_SECONDS - elapsed)}s"}), 429
    scripts = load_scripts()
    sid = gen_script_id()
    scripts[sid] = {"created": int(time.time())}
    save_scripts(scripts)
    base = request.host_url.rstrip("/")
    # multi-stage stub — user supplies their key
    payload = build_multistage_stub("ATX-FRE-XXXX-XXXX-XXXX", base)
    session.pop("captcha_solved", None)
    session.pop("captcha_solved_time", None)
    stat_incr("scripts_delivered")
    return jsonify({"success": True, "script_id": sid, "payload": payload})


@app.route("/api/stage1", methods=["GET"])
@rate_limit("stage1", 200, 60)
def stage1():
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return jsonify({"valid": False, "error": "Service disabled"}), 503
    key = (request.args.get("key") or "").strip()
    hwid = (request.args.get("hwid") or "").strip() or None
    if not key:
        return jsonify({"valid": False, "error": "No key"}), 400
    ok, entry, err = validate_key_entry(key, hwid, _client_ip())
    stat_incr("validations")
    if not ok:
        return jsonify({"valid": False, "error": err}), 403
    tier = entry.get("tier", "free")
    url = get_payload_url(tier)
    token = signer.dumps({"tier": tier, "u": url, "hwid_required": False, "key": key, "hwid": hwid})
    sig = sign_loader(token)
    base = request.host_url.rstrip("/")
    payload_url = f"{base}/t/{token}?sig={sig}&key={key}&hwid={hwid or ''}"
    return jsonify({"valid": True, "payload_url": payload_url, "tier": tier})


@app.route("/t/<token>", methods=["GET"])
def ttl_loader(token):
    sig = request.args.get("sig") or ""
    if sig and not verify_loader_sig(token, sig):
        return "Invalid signature", 403
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return "Service disabled", 503
    try:
        data = signer.loads(token, max_age=60 * 60 * 24 * 7)
    except SignatureExpired:
        return "Token expired", 410
    except BadSignature:
        return "Invalid token", 400
    url = data.get("u")
    if not url: return "Bad token", 400
    text = http_get_text(url, timeout=10)
    if text is None: return "Upstream error", 502
    key = request.args.get("key") or data.get("key")
    hwid = request.args.get("hwid") or data.get("hwid")
    tier = data.get("tier")
    watermarked = watermark(text, key=key, hwid=hwid, tier=tier)
    return Response(watermarked, mimetype="text/plain")


@app.route("/r/<pid>", methods=["GET"])
def short_loader(pid):
    cfg = load_config()
    if (cfg.get("killswitch") or {}).get("on"):
        return "-- disabled", 503
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry or paste_is_expired(entry):
        return "Not found", 404
    hwid = request.args.get("hwid")
    if hwid and hwid_is_blacklisted(hwid):
        return "-- blocked", 403
    return Response(entry.get("content", ""), mimetype="text/plain")


# ============================================================
# LICENSE SERVER
# ============================================================
@app.route("/api/license/check", methods=["POST", "GET"])
@rate_limit("license", 300, 60)
def license_check():
    if request.method == "GET":
        key = (request.args.get("key") or "").strip()
        hwid = (request.args.get("hwid") or "").strip() or None
    else:
        d = request.get_json(silent=True) or {}
        key = (d.get("key") or "").strip()
        hwid = (d.get("hwid") or "").strip() or None
    if not key:
        return jsonify({"valid": False, "error": "No key"}), 400
    ok, entry, err = validate_key_entry(key, hwid, _client_ip())
    if not ok:
        return jsonify({"valid": False, "error": err}), 403
    return jsonify({
        "valid": True,
        "tier": entry.get("tier", "free"),
        "expires": entry.get("expires"),
        "tier_features": _tier_features(entry.get("tier", "free")),
    })


def _tier_features(tier):
    return {
        "free": {"max_sessions": 1, "features": ["basic"]},
        "premium": {"max_sessions": 3, "features": ["basic", "advanced"]},
        "vip": {"max_sessions": 5, "features": ["basic", "advanced", "priority"]},
        "trial": {"max_sessions": 1, "features": ["basic"]},
    }.get(tier, {"max_sessions": 1, "features": []})


# ============================================================
# ADMIN
# ============================================================
@app.route("/api/admin/config", methods=["GET"])
@admin_required
def admin_get_config():
    return jsonify({"success": True, "config": load_config()})


@app.route("/api/admin/config", methods=["POST"])
@admin_required
def admin_set_config():
    data = request.get_json() or {}
    cfg = load_config()
    if "announcement" in data:
        cfg["announcement"] = str(data["announcement"])[:500]
    if "killswitch" in data:
        cfg.setdefault("killswitch", {})["on"] = bool(data["killswitch"].get("on"))
        if "message" in data["killswitch"]:
            cfg["killswitch"]["message"] = str(data["killswitch"]["message"])[:300]
    if "maintenance" in data:
        cfg.setdefault("maintenance", {})["on"] = bool(data["maintenance"].get("on"))
        if "message" in data["maintenance"]:
            cfg["maintenance"]["message"] = str(data["maintenance"]["message"])[:300]
    if "webhooks" in data:
        cfg.setdefault("webhooks", {})
        if "events" in data["webhooks"]:
            cfg["webhooks"]["events"] = [str(e) for e in data["webhooks"]["events"]][:50]
    save_config(cfg)
    audit("admin.config.set", actor=_row_val(current_user(), "username"), detail=data)
    return jsonify({"success": True, "config": cfg})


@app.route("/api/admin/payloads", methods=["GET"])
@admin_required
def admin_get_payloads():
    cfg = load_config()
    return jsonify({
        "success": True,
        "payloads": cfg.get("payloads", {}),
        "durations": cfg.get("key_durations_hours", {}),
        "hwid_slots": cfg.get("hwid_slots", {}),
    })


@app.route("/api/admin/payloads", methods=["POST"])
@admin_required
def admin_set_payloads():
    data = request.get_json() or {}
    tier = (data.get("tier") or "").lower()
    url = (data.get("url") or "").strip()
    if tier not in ("free", "premium", "vip"):
        return jsonify({"success": False, "error": "tier must be free/premium/vip"}), 400
    if not (url.startswith("http://") or url.startswith("https://")):
        return jsonify({"success": False, "error": "URL must be http(s)"}), 400
    cfg = load_config()
    cfg.setdefault("payloads", {})[tier] = url
    save_config(cfg)
    audit("admin.payload.set", actor=_row_val(current_user(), "username"), detail={"tier": tier, "url": url})
    return jsonify({"success": True, "payloads": cfg["payloads"]})


@app.route("/api/admin/durations", methods=["POST"])
@admin_required
def admin_set_durations():
    data = request.get_json() or {}
    tier = (data.get("tier") or "").lower()
    try: hours = int(data.get("hours", 0))
    except (TypeError, ValueError): return jsonify({"success": False, "error": "hours must be int"}), 400
    if tier not in ("free", "premium", "vip", "trial"):
        return jsonify({"success": False, "error": "invalid tier"}), 400
    if hours < 1 or hours > 24 * 365:
        return jsonify({"success": False, "error": "hours must be 1..8760"}), 400
    cfg = load_config()
    cfg.setdefault("key_durations_hours", {})[tier] = hours
    save_config(cfg)
    audit("admin.duration.set", actor=_row_val(current_user(), "username"), detail={"tier": tier, "hours": hours})
    return jsonify({"success": True, "durations": cfg["key_durations_hours"]})


@app.route("/api/admin/hwid_slots", methods=["POST"])
@admin_required
def admin_set_hwid_slots():
    data = request.get_json() or {}
    tier = (data.get("tier") or "").lower()
    try: slots = int(data.get("slots", 1))
    except (TypeError, ValueError): return jsonify({"success": False, "error": "slots int"}), 400
    if tier not in ("free", "premium", "vip", "trial"):
        return jsonify({"success": False, "error": "invalid tier"}), 400
    if slots < 1 or slots > 50:
        return jsonify({"success": False, "error": "slots 1..50"}), 400
    cfg = load_config()
    cfg.setdefault("hwid_slots", {})[tier] = slots
    save_config(cfg)
    audit("admin.hwid_slots.set", actor=_row_val(current_user(), "username"), detail={"tier": tier, "slots": slots})
    return jsonify({"success": True, "hwid_slots": cfg["hwid_slots"]})


@app.route("/api/admin/keys", methods=["GET"])
@admin_required
def admin_list_keys():
    keys = load_keys()
    now = time.time()
    items = [{
        "key": k,
        "tier": v.get("tier", "free"),
        "created": v.get("created"),
        "expires": v.get("expires"),
        "hwids": _key_hwids(v),
        "last_used": v.get("last_used"),
        "active": v.get("expires", 0) > now,
        "blacklisted": key_is_blacklisted(k),
        "flagged": bool(v.get("flagged_concurrent")),
    } for k, v in keys.items()]
    items.sort(key=lambda x: x.get("created", 0), reverse=True)
    return jsonify({"success": True, "keys": items})


@app.route("/api/admin/keys/revoke", methods=["POST"])
@admin_required
def admin_revoke_key():
    data = request.get_json() or {}
    key = (data.get("key") or "").strip()
    if not key: return jsonify({"success": False, "error": "key required"}), 400
    keys = load_keys()
    keys.pop(key, None)
    save_keys(keys)
    bl = load_blacklist()
    bl.setdefault("keys", [])
    if key not in bl["keys"]:
        bl["keys"].append(key)
    save_blacklist(bl)
    audit("admin.key.revoke", actor=_row_val(current_user(), "username"), detail={"key": key})
    return jsonify({"success": True})


@app.route("/api/admin/keys/unrevoke", methods=["POST"])
@admin_required
def admin_unrevoke_key():
    data = request.get_json() or {}
    key = (data.get("key") or "").strip()
    bl = load_blacklist()
    if key in (bl.get("keys") or []):
        bl["keys"].remove(key)
        save_blacklist(bl)
    audit("admin.key.unrevoke", actor=_row_val(current_user(), "username"), detail={"key": key})
    return jsonify({"success": True})


@app.route("/api/admin/keys/gen", methods=["POST"])
@admin_required
def admin_gen_key():
    data = request.get_json() or {}
    tier = (data.get("tier") or "free").lower()
    count = int(data.get("count") or 1)
    count = max(1, min(count, 500))
    if tier not in ("free", "premium", "vip", "trial"):
        return jsonify({"success": False, "error": "invalid tier"}), 400
    made = [_create_key(tier) for _ in range(count)]
    audit("admin.key.gen", actor=_row_val(current_user(), "username"),
          detail={"tier": tier, "count": count})
    return jsonify({"success": True, "keys": made, "tier": tier})


@app.route("/api/admin/keys/export", methods=["GET"])
@admin_required
def admin_export_keys():
    keys = load_keys()
    now = time.time()
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["key", "tier", "created", "expires", "active", "hwids", "last_used", "blacklisted"])
    for k, v in keys.items():
        w.writerow([
            k, v.get("tier", "free"),
            datetime.fromtimestamp(v.get("created", 0), timezone.utc).isoformat() if v.get("created") else "",
            datetime.fromtimestamp(v.get("expires", 0), timezone.utc).isoformat() if v.get("expires") else "",
            "yes" if v.get("expires", 0) > now else "no",
            ";".join(_key_hwids(v)),
            v.get("last_used", ""),
            "yes" if key_is_blacklisted(k) else "no",
        ])
    data = buf.getvalue().encode("utf-8")
    return Response(data, mimetype="text/csv",
                    headers={"Content-Disposition": "attachment; filename=atx_keys.csv"})


@app.route("/api/admin/hwid/clusters", methods=["GET"])
@admin_required
def admin_hwid_clusters():
    keys = load_keys()
    hwid_to_keys = defaultdict(list)
    for k, v in keys.items():
        for h in _key_hwids(v):
            hwid_to_keys[h].append(k)
    clusters = [{"hwid": h, "keys": ks} for h, ks in hwid_to_keys.items() if len(ks) >= 3]
    clusters.sort(key=lambda x: -len(x["keys"]))
    return jsonify({"success": True, "clusters": clusters})


@app.route("/api/admin/hwid/blacklist_cluster", methods=["POST"])
@admin_required
def admin_blacklist_cluster():
    data = request.get_json() or {}
    hwid = (data.get("hwid") or "").strip()
    if not hwid: return jsonify({"success": False, "error": "hwid required"}), 400
    bl = load_blacklist()
    bl.setdefault("hwids", [])
    if hwid not in bl["hwids"]:
        bl["hwids"].append(hwid)
    keys = load_keys()
    revoked = []
    for k, v in list(keys.items()):
        if hwid in _key_hwids(v):
            keys.pop(k, None)
            bl.setdefault("keys", [])
            if k not in bl["keys"]:
                bl["keys"].append(k)
            revoked.append(k)
    save_keys(keys); save_blacklist(bl)
    audit("admin.hwid.blacklist_cluster", actor=_row_val(current_user(), "username"),
          detail={"hwid": hwid[:16], "revoked": len(revoked)})
    return jsonify({"success": True, "revoked": len(revoked)})


@app.route("/api/admin/blacklist", methods=["GET"])
@admin_required
def admin_list_blacklist():
    return jsonify({"success": True, **load_blacklist()})


@app.route("/api/admin/blacklist/add", methods=["POST"])
@admin_required
def admin_bl_add():
    data = request.get_json() or {}
    kind = (data.get("kind") or "").strip()
    value = (data.get("value") or "").strip()
    if kind not in ("keys", "hwids") or not value:
        return jsonify({"success": False, "error": "kind keys|hwids + value"}), 400
    bl = load_blacklist()
    bl.setdefault(kind, [])
    if value not in bl[kind]:
        bl[kind].append(value)
    save_blacklist(bl)
    audit("admin.blacklist.add", actor=_row_val(current_user(), "username"), detail={"kind": kind, "value": value})
    return jsonify({"success": True})


@app.route("/api/admin/blacklist/remove", methods=["POST"])
@admin_required
def admin_bl_remove():
    data = request.get_json() or {}
    kind = (data.get("kind") or "").strip()
    value = (data.get("value") or "").strip()
    bl = load_blacklist()
    if kind in bl and value in bl[kind]:
        bl[kind].remove(value)
        save_blacklist(bl)
    audit("admin.blacklist.remove", actor=_row_val(current_user(), "username"), detail={"kind": kind, "value": value})
    return jsonify({"success": True})


@app.route("/api/admin/users", methods=["GET"])
@admin_required
def admin_list_users():
    rows = db_exec("SELECT * FROM users ORDER BY created DESC LIMIT 500", commit=False, fetch="all") or []
    out = []
    for r in rows:
        out.append({
            "id": _row_val(r, "id"),
            "username": _row_val(r, "username"),
            "created": _row_val(r, "created"),
            "paste_count": _row_val(r, "paste_count", 0),
            "is_admin": bool(_row_val(r, "is_admin", 0)),
            "is_banned": bool(_row_val(r, "is_banned", 0)),
            "bonus_hours": _row_val(r, "bonus_hours", 0),
            "totp_enabled": bool(_row_val(r, "totp_secret")),
        })
    return jsonify({"success": True, "users": out})


@app.route("/api/admin/users/<int:uid>/ban", methods=["POST"])
@admin_required
def admin_ban_user(uid):
    db_exec("UPDATE users SET is_banned = 1, session_version = session_version + 1 WHERE id = ?", (uid,))
    audit("admin.user.ban", actor=_row_val(current_user(), "username"), detail={"uid": uid})
    return jsonify({"success": True})


@app.route("/api/admin/users/<int:uid>/unban", methods=["POST"])
@admin_required
def admin_unban_user(uid):
    db_exec("UPDATE users SET is_banned = 0 WHERE id = ?", (uid,))
    audit("admin.user.unban", actor=_row_val(current_user(), "username"), detail={"uid": uid})
    return jsonify({"success": True})


@app.route("/api/admin/users/<int:uid>/promote", methods=["POST"])
@admin_required
def admin_promote(uid):
    db_exec("UPDATE users SET is_admin = 1 WHERE id = ?", (uid,))
    audit("admin.user.promote", actor=_row_val(current_user(), "username"), detail={"uid": uid})
    return jsonify({"success": True})


@app.route("/api/admin/users/<int:uid>/demote", methods=["POST"])
@admin_required
def admin_demote(uid):
    if uid == _row_val(current_user(), "id"):
        return jsonify({"success": False, "error": "Cannot demote yourself"}), 400
    db_exec("UPDATE users SET is_admin = 0 WHERE id = ?", (uid,))
    audit("admin.user.demote", actor=_row_val(current_user(), "username"), detail={"uid": uid})
    return jsonify({"success": True})


@app.route("/api/admin/users/<int:uid>/delete", methods=["POST"])
@admin_required
def admin_delete_user(uid):
    if uid == _row_val(current_user(), "id"):
        return jsonify({"success": False, "error": "Cannot delete yourself"}), 400
    db_exec("DELETE FROM users WHERE id = ?", (uid,))
    audit("admin.user.delete", actor=_row_val(current_user(), "username"), detail={"uid": uid})
    return jsonify({"success": True})


@app.route("/api/admin/users/<int:uid>/reset_password", methods=["POST"])
@admin_required
def admin_reset_pw(uid):
    data = request.get_json() or {}
    new_pw = (data.get("password") or "").strip()
    ok, msg = password_ok(new_pw)
    if not ok: return jsonify({"success": False, "error": msg}), 400
    db_exec("UPDATE users SET password_hash = ?, session_version = session_version + 1 WHERE id = ?",
            (generate_password_hash(new_pw), uid))
    audit("admin.user.resetpw", actor=_row_val(current_user(), "username"), detail={"uid": uid})
    return jsonify({"success": True})


@app.route("/api/admin/stats", methods=["GET"])
@admin_required
def admin_stats():
    return jsonify({"success": True, **stats_snapshot()})


@app.route("/api/admin/audit", methods=["GET"])
@admin_required
def admin_audit():
    return jsonify({"success": True, "entries": list(reversed(load_audit()))[:300]})


@app.route("/api/admin/live/stream", methods=["GET"])
@admin_required
def admin_live_stream():
    def gen():
        last = 0
        yield "retry: 3000\n\n"
        while True:
            with _event_lock:
                snapshot = list(_event_bus)
            for ev in snapshot:
                if ev["id"] > last:
                    last = ev["id"]
                    data = json.dumps(ev)
                    yield f"event: {ev['kind']}\ndata: {data}\n\n"
            time.sleep(1)
    return Response(gen(), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


# ============================================================
# PASTEBIN
# ============================================================
@app.route("/api/paste/create", methods=["POST"])
@login_required
@rate_limit("paste_create", 20, 3600)
def paste_create():
    data = request.get_json() or {}
    content = (data.get("content") or "").strip()
    title = (data.get("title") or "").strip()[:120]
    syntax = (data.get("syntax") or "text").strip()[:24]
    expiry = (data.get("expiry") or "never").strip()
    password = (data.get("password") or "").strip()
    burn = int(data.get("burn") or 0)
    if not content: return jsonify({"success": False, "error": "Content required"}), 400
    if len(content) > PASTE_MAX_LENGTH:
        return jsonify({"success": False, "error": f"Max {PASTE_MAX_LENGTH}"}), 413
    expires_at = None
    map_secs = {"1h": 3600, "1d": 86400, "7d": 86400 * 7, "30d": 86400 * 30}
    if expiry in map_secs:
        expires_at = int(time.time()) + map_secs[expiry]
    pastes = load_pastes()
    pid = gen_paste_id()
    while pid in pastes:
        pid = gen_paste_id()
    u = current_user()
    entry = {
        "title": title,
        "content": content,
        "syntax": syntax,
        "created": int(time.time()),
        "views": 0,
        "unique_views": [],
        "user_id": _row_val(u, "id"),
        "username": _row_val(u, "username"),
        "ip": request.remote_addr,
        "expires": expires_at,
        "versions": [],
        "burn_after_views": max(0, burn),
        "burn_views": 0,
    }
    if password:
        entry["password_hash"] = generate_password_hash(password)
    pastes[pid] = entry
    save_pastes(pastes)
    bump_paste_count(_row_val(u, "id"))
    stat_incr("pastes_created")
    audit("paste.create", actor=_row_val(u, "username"), detail={"id": pid})
    push_event("paste.created", {"id": pid, "username": entry["username"], "title": title})
    return jsonify({
        "success": True, "id": pid,
        "url": f"/paste/{pid}", "raw_url": f"/raw/{pid}", "short_url": f"/r/{pid}",
    })


@app.route("/api/paste/mine", methods=["GET"])
@login_required
def paste_mine():
    uid = _row_val(current_user(), "id")
    pastes = load_pastes()
    mine = [{
        "id": pid, "title": v.get("title", ""), "syntax": v.get("syntax", "text"),
        "created": v.get("created"), "views": v.get("views", 0),
        "expires": v.get("expires"), "has_password": bool(v.get("password_hash")),
        "burn_after_views": v.get("burn_after_views", 0),
    } for pid, v in pastes.items() if v.get("user_id") == uid and not paste_is_expired(v)]
    mine.sort(key=lambda x: x.get("created", 0), reverse=True)
    return jsonify({"success": True, "pastes": mine})


@app.route("/api/paste/recent", methods=["GET"])
def paste_recent():
    pastes = load_pastes()
    live = [{
        "id": pid, "title": v.get("title", ""), "username": v.get("username", "anon"),
        "created": v.get("created"), "views": v.get("views", 0),
        "has_password": bool(v.get("password_hash")),
    } for pid, v in pastes.items() if not paste_is_expired(v)]
    live.sort(key=lambda x: x.get("created", 0), reverse=True)
    return jsonify({"success": True, "pastes": live[:50]})


@app.route("/api/paste/search", methods=["GET"])
def paste_search():
    q = (request.args.get("q") or "").strip().lower()
    if not q: return jsonify({"success": True, "pastes": []})
    pastes = load_pastes()
    hits = []
    for pid, v in pastes.items():
        if paste_is_expired(v): continue
        if q in (v.get("title", "").lower()) or q in (v.get("content", "").lower()):
            hits.append({
                "id": pid, "title": v.get("title", ""),
                "username": v.get("username", "anon"),
                "created": v.get("created"), "views": v.get("views", 0),
            })
    hits.sort(key=lambda x: x.get("created", 0), reverse=True)
    return jsonify({"success": True, "pastes": hits[:50]})


@app.route("/api/paste/get/<pid>", methods=["GET"])
def paste_get(pid):
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry or paste_is_expired(entry):
        return jsonify({"success": False, "error": "Not found"}), 404
    if entry.get("password_hash"):
        pw = request.args.get("pw") or ""
        if not pw or not check_password_hash(entry["password_hash"], pw):
            return jsonify({"success": False, "error": "Password required", "locked": True}), 401
    entry["views"] = entry.get("views", 0) + 1
    ip = _client_ip()
    uniq = entry.setdefault("unique_views", [])
    if ip not in uniq:
        uniq.append(ip)
        if len(uniq) > 5000: uniq.pop(0)
    pastes[pid] = entry
    save_pastes(pastes)
    stat_incr("paste_views")
    # burn after read
    bav = entry.get("burn_after_views", 0)
    if bav:
        entry["burn_views"] = entry.get("burn_views", 0) + 1
        pastes[pid] = entry
        if entry["burn_views"] >= bav:
            del pastes[pid]
        save_pastes(pastes)
    return jsonify({
        "success": True, "id": pid,
        "title": entry.get("title", ""),
        "content": entry.get("content", ""),
        "syntax": entry.get("syntax", "text"),
        "created": entry.get("created"),
        "updated": entry.get("updated"),
        "views": entry["views"],
        "unique_views": len(uniq),
        "username": entry.get("username", "anon"),
        "expires": entry.get("expires"),
        "has_password": bool(entry.get("password_hash")),
        "raw_url": f"/raw/{pid}",
        "versions": len(entry.get("versions", [])),
    })


@app.route("/api/paste/versions/<pid>", methods=["GET"])
@login_required
def paste_versions(pid):
    uid = _row_val(current_user(), "id")
    u = current_user()
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry: return jsonify({"success": False, "error": "Not found"}), 404
    if entry.get("user_id") != uid and not _row_val(u, "is_admin", 0):
        return jsonify({"success": False, "error": "Not yours"}), 403
    return jsonify({"success": True, "versions": entry.get("versions", [])})


@app.route("/api/paste/restore/<pid>/<int:idx>", methods=["POST"])
@login_required
def paste_restore(pid, idx):
    uid = _row_val(current_user(), "id")
    u = current_user()
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry: return jsonify({"success": False, "error": "Not found"}), 404
    if entry.get("user_id") != uid and not _row_val(u, "is_admin", 0):
        return jsonify({"success": False, "error": "Not yours"}), 403
    versions = entry.get("versions", [])
    if idx < 0 or idx >= len(versions):
        return jsonify({"success": False, "error": "No such version"}), 404
    versions.append({
        "ts": int(time.time()),
        "title": entry.get("title", ""),
        "content": entry.get("content", ""),
        "syntax": entry.get("syntax", "text"),
        "reason": "pre-restore",
    })
    v = versions[idx]
    entry["title"] = v.get("title", entry.get("title", ""))
    entry["content"] = v.get("content", entry.get("content", ""))
    entry["syntax"] = v.get("syntax", entry.get("syntax", "text"))
    entry["updated"] = int(time.time())
    entry["versions"] = versions[-20:]
    pastes[pid] = entry
    save_pastes(pastes)
    audit("paste.restore", actor=_row_val(u, "username"), detail={"id": pid, "idx": idx})
    return jsonify({"success": True})


@app.route("/api/paste/edit/<pid>", methods=["POST"])
@login_required
def paste_edit(pid):
    uid = _row_val(current_user(), "id")
    u = current_user()
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry or paste_is_expired(entry):
        return jsonify({"success": False, "error": "Not found"}), 404
    if entry.get("user_id") != uid and not _row_val(u, "is_admin", 0):
        return jsonify({"success": False, "error": "Not yours"}), 403
    data = request.get_json() or {}
    versions = entry.get("versions", [])
    versions.append({
        "ts": int(time.time()),
        "title": entry.get("title", ""),
        "content": entry.get("content", ""),
        "syntax": entry.get("syntax", "text"),
    })
    if "title" in data:
        entry["title"] = (data["title"] or "").strip()[:120]
    if "content" in data:
        c = (data["content"] or "").strip()
        if not c: return jsonify({"success": False, "error": "Content empty"}), 400
        if len(c) > PASTE_MAX_LENGTH: return jsonify({"success": False, "error": "Too long"}), 413
        entry["content"] = c
    if "syntax" in data:
        entry["syntax"] = (data["syntax"] or "text").strip()[:24]
    if "password" in data:
        pw = (data["password"] or "").strip()
        if pw: entry["password_hash"] = generate_password_hash(pw)
        else: entry.pop("password_hash", None)
    entry["updated"] = int(time.time())
    entry["versions"] = versions[-20:]
    pastes[pid] = entry
    save_pastes(pastes)
    audit("paste.edit", actor=_row_val(u, "username"), detail={"id": pid})
    return jsonify({"success": True})


@app.route("/api/paste/delete/<pid>", methods=["POST", "DELETE"])
@login_required
def paste_delete(pid):
    uid = _row_val(current_user(), "id")
    u = current_user()
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry: return jsonify({"success": False, "error": "Not found"}), 404
    if entry.get("user_id") != uid and not _row_val(u, "is_admin", 0):
        return jsonify({"success": False, "error": "Not yours"}), 403
    del pastes[pid]
    save_pastes(pastes)
    audit("paste.delete", actor=_row_val(u, "username"), detail={"id": pid})
    return jsonify({"success": True})


@app.route("/api/paste/fork/<pid>", methods=["POST"])
@login_required
def paste_fork(pid):
    pastes = load_pastes()
    src = pastes.get(pid)
    if not src or paste_is_expired(src):
        return jsonify({"success": False, "error": "Not found"}), 404
    if src.get("password_hash"):
        return jsonify({"success": False, "error": "Cannot fork password-protected paste"}), 403
    new_id = gen_paste_id()
    while new_id in pastes:
        new_id = gen_paste_id()
    u = current_user()
    pastes[new_id] = {
        "title": (src.get("title", "") + " (fork)")[:120],
        "content": src.get("content", ""),
        "syntax": src.get("syntax", "text"),
        "created": int(time.time()),
        "views": 0, "unique_views": [],
        "user_id": _row_val(u, "id"), "username": _row_val(u, "username"),
        "ip": request.remote_addr, "expires": None, "forked_from": pid,
        "versions": [],
    }
    save_pastes(pastes)
    bump_paste_count(_row_val(u, "id"))
    stat_incr("pastes_created")
    audit("paste.fork", actor=_row_val(u, "username"), detail={"from": pid, "to": new_id})
    return jsonify({"success": True, "id": new_id, "url": f"/paste/{new_id}", "raw_url": f"/raw/{new_id}"})


# ============================================================
# RAW / PASTE VIEW
# ============================================================
def _content_type_for(syntax):
    return {
        "lua": "text/x-lua; charset=utf-8",
        "javascript": "application/javascript; charset=utf-8",
        "python": "text/x-python; charset=utf-8",
        "html": "text/html; charset=utf-8",
        "css": "text/css; charset=utf-8",
        "json": "application/json; charset=utf-8",
        "cpp": "text/x-c++src; charset=utf-8",
        "csharp": "text/x-csharp; charset=utf-8",
        "bash": "text/x-shellscript; charset=utf-8",
    }.get(syntax, "text/plain; charset=utf-8")


@app.route("/api/paste/raw/<pid>", methods=["GET"])
@app.route("/raw/<pid>", methods=["GET"])
def paste_raw(pid):
    pastes = load_pastes()
    entry = pastes.get(pid)
    if not entry or paste_is_expired(entry):
        return "Not found", 404
    if entry.get("password_hash"):
        pw = request.args.get("pw") or ""
        if not pw or not check_password_hash(entry["password_hash"], pw):
            return "Password required", 401
    syntax = request.args.get("syntax") or entry.get("syntax", "text")
    ct = _content_type_for(syntax)
    return Response(entry.get("content", ""), content_type=ct)


@app.route("/paste/<pid>")
def paste_view(pid):
    cfg = load_config()
    return render_template(
        "index.html",
        telegram_channel=TELEGRAM_CHANNEL,
        telegram_premium=TELEGRAM_PREMIUM,
        csrf_token=_ensure_csrf(),
        paste_id=pid,
        announcement=cfg.get("announcement", ""),
        turnstile_site=TURNSTILE_SITE,
    )


# ============================================================
# REFERRAL
# ============================================================
@app.route("/api/referral/me", methods=["GET"])
@login_required
def referral_me():
    u = current_user()
    uid = _row_val(u, "id")
    rows = db_exec("SELECT id, username, created FROM users WHERE referred_by = ?", (uid,), commit=False, fetch="all") or []
    return jsonify({
        "success": True,
        "code": _row_val(u, "referral_code"),
        "bonus_hours": _row_val(u, "bonus_hours", 0),
        "referred": [{"id": _row_val(r, "id"), "username": _row_val(r, "username"),
                      "created": _row_val(r, "created")} for r in rows],
    })


# ============================================================
# BACKUP CLI
# ============================================================
def _backup_cmd(out_path=None):
    ts = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
    out_path = out_path or f"atx-backup-{ts}.zip"
    with zipfile.ZipFile(out_path, "w", zipfile.ZIP_DEFLATED) as zf:
        if os.path.isdir(DATA_DIR):
            for root, _, files in os.walk(DATA_DIR):
                for f in files:
                    p = os.path.join(root, f)
                    arc = os.path.relpath(p, DATA_DIR)
                    zf.write(p, arc)
    print(f"backup -> {out_path}")


def _restore_cmd(zip_path):
    if not os.path.exists(zip_path):
        print("not found:", zip_path); sys.exit(1)
    if os.path.exists(DATA_DIR):
        shutil.rmtree(DATA_DIR, ignore_errors=True)
    os.makedirs(DATA_DIR, exist_ok=True)
    with zipfile.ZipFile(zip_path) as zf:
        zf.extractall(DATA_DIR)
    print(f"restored -> {DATA_DIR}")


# ============================================================
# BOOT
# ============================================================
ensure_storage()
start_tg_thread()

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", nargs="?", default="serve")
    ap.add_argument("arg", nargs="?")
    args = ap.parse_args()
    if args.cmd == "backup":
        _backup_cmd(args.arg); sys.exit(0)
    if args.cmd == "restore":
        _restore_cmd(args.arg); sys.exit(0)
    port = int(os.getenv("PORT", 8080))
    app.run(host="0.0.0.0", port=port, threaded=True)