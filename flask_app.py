from flask import Flask, render_template, request, redirect, url_for, session, jsonify, flash
from urllib.parse import urlparse
import sqlite3
import requests
import os
import re
import json
import time
import secrets
import random
import threading
from datetime import date, datetime, timedelta

def _load_dotenv(path='.env'):
    try:
        with open(path, encoding='utf-8') as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith('#') or '=' not in line:
                    continue
                key, _, val = line.partition('=')
                key = key.strip()
                val = val.strip()
                if (val.startswith('"') and val.endswith('"')) or (val.startswith("'") and val.endswith("'")):
                    val = val[1:-1]
                os.environ.setdefault(key, val)
    except FileNotFoundError:
        pass

def _require_env(name):
    val = (os.environ.get(name) or '').strip()
    if not val:
        raise RuntimeError(
            f"Missing required environment variable: {name}. Copy .env.example to .env and fill in the values."
        )
    return val

_load_dotenv()

app = Flask(__name__)
app.secret_key = _require_env('SECRET_KEY')
app.permanent_session_lifetime = timedelta(days=30)
app.config['MAX_CONTENT_LENGTH'] = 6 * 1024 * 1024

ADMINS = [x.strip() for x in os.environ.get('ADMINS', '').split(',') if x.strip()]
ADMINS_LOWER = [a.lower() for a in ADMINS]
FOUNDER_USERNAME = os.environ.get('FOUNDER_USERNAME', '').strip().lower()
DEVELOPER_USERNAME = os.environ.get('DEVELOPER_USERNAME', '').strip().lower()
HOST_USERNAME = os.environ.get('HOST_USERNAME', '').strip().lower()
SITE_AUTHOR = os.environ.get('SITE_AUTHOR', '').strip()
SITE_CO_AUTHOR = os.environ.get('SITE_CO_AUTHOR', '').strip()
SITE_HOST = os.environ.get('SITE_HOST', '').strip()
HOME_CREATOR_A = os.environ.get('HOME_CREATOR_A', '').strip()
HOME_CREATOR_B = os.environ.get('HOME_CREATOR_B', '').strip()

def is_admin(username):
    return (username or '').lower() in ADMINS_LOWER

def is_founder(username):
    return bool(FOUNDER_USERNAME) and (username or '').lower() == FOUNDER_USERNAME
_loc_cache = {'count': None, 'ts': 0}
_steam_cache = {'ts': 0, 'owned': {}, 'playtimes': {}, 'no_steam': []}
_steam_cache_loaded = False
_steam_refreshing = False
_steam_refresh_lock = threading.Lock()
_steam_fail_ts = 0
_recent_games_cache = {}
_steam_name_cache = {}
_started_at = time.time()
STEAM_CACHE_TTL = 300
STEAM_RECENT_TTL = 420
STEAM_NAME_TTL = 600
STEAM_FAIL_TTL = 60
STEAM_CACHE_KEY = 'steam_own_cache'
STEAM_HTTP_TIMEOUT = (2, 3)
DISCORD_HTTP_TIMEOUT = 8
LOC_CACHE_TTL = 21600
APP_ROOT = os.path.abspath(os.path.dirname(__file__))
DB_PATH = os.path.join(APP_ROOT, 'database.db')
I18N_LANGS = ('en', 'de', 'pl', 'cs', 'hr', 'fr', 'ja')
I18N_DIR = os.path.join(APP_ROOT, 'static', 'i18n')
_i18n_catalogs = {}
_i18n_mtimes = {}
UPLOAD_ROOT = os.path.join(APP_ROOT, 'static', 'uploads')
ARMORY_UPLOAD_DIR = os.path.join(UPLOAD_ROOT, 'armory')
ARMORY_PHOTO_MAX = 3 * 1024 * 1024
BOUNTY_CRATE_MIN = 40
BOUNTY_CRATE_MAX = 80
CLIP_OF_WEEK_OC = 100

STEAM_API_KEY = _require_env('STEAM_API_KEY')
DISCORD_CLIENT_ID = _require_env('DISCORD_CLIENT_ID')
DISCORD_CLIENT_SECRET = _require_env('DISCORD_CLIENT_SECRET')
DISCORD_REDIRECT_URI = (os.environ.get('DISCORD_REDIRECT_URI') or '').strip() or 'http://localhost:5000/callback'
DISCORD_AUTH_URL = "https://discord.com/oauth2/authorize"
DISCORD_TOKEN_URL = "https://discord.com/api/oauth2/token"
DISCORD_API_URL = "https://discord.com/api/users/@me"
DISCORD_WEBHOOK_URL = (os.environ.get('DISCORD_WEBHOOK_URL') or '').strip()
DISCORD_PING_ROLE_ID = (os.environ.get('DISCORD_PING_ROLE_ID') or '').strip()
CRON_SECRET = (os.environ.get("CRON_SECRET") or "").strip()
_WEBHOOK_RE = re.compile(r'^https://(?:canary\.|ptb\.)?(?:discord|discordapp)\.com/api/webhooks/\d+/[\w-]+$', re.I)
_ROLE_ID_RE = re.compile(r'^\d{5,22}$')
_ping_lock = threading.Lock()
_ping_checked_ts = 0
_atmosphere_cache = {'ts': 0, 'art': '', 'winner': ''}
try:
    from zoneinfo import ZoneInfo
    BERLIN_TZ = ZoneInfo('Europe/Berlin')
except Exception:
    BERLIN_TZ = None
DEFAULT_AVATAR = "https://cdn.discordapp.com/embed/avatars/0.png"
HEX_RE = re.compile(r'^#[0-9A-Fa-f]{6}$')

def _raw_db():
    conn = sqlite3.connect(DB_PATH, timeout=5)
    conn.row_factory = sqlite3.Row
    conn.execute('PRAGMA journal_mode=WAL')
    conn.execute('PRAGMA busy_timeout=4000')
    return conn

def config_get(conn, key, default=''):
    row = conn.execute("SELECT value FROM config WHERE key = ?", (key,)).fetchone()
    if not row or row['value'] is None:
        return default
    return row['value']

def config_set(conn, key, value):
    conn.execute(
        "INSERT INTO config (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (key, value),
    )

def berlin_now():
    if BERLIN_TZ is not None:
        return datetime.now(BERLIN_TZ)
    return datetime.now()

def _valid_webhook(url):
    return bool(url and _WEBHOOK_RE.match(url.strip()))

def _discord_retry_after(res):
    try:
        data = res.json()
        ra = data.get('retry_after')
        if ra is not None:
            return float(ra)
    except Exception:
        pass
    try:
        ra = res.headers.get('Retry-After')
        if ra:
            return float(ra)
    except Exception:
        pass
    return None

def send_discord_webhook(url, payload):
    if not _valid_webhook(url):
        return False, 'Webhook URL missing or invalid'
    try:
        res = requests.post(url, json=payload, timeout=DISCORD_HTTP_TIMEOUT)
        if res.status_code == 429:
            wait = _discord_retry_after(res)
            if wait is not None and 0 <= wait <= 3:
                time.sleep(wait + 0.2)
                res = requests.post(url, json=payload, timeout=DISCORD_HTTP_TIMEOUT)
        if res.status_code in (200, 204):
            return True, 'Sent'
        if res.status_code == 429:
            wait = _discord_retry_after(res)
            secs = max(1, int(wait) + 1) if wait else 30
            return False, f'Discord 429 (rate limit — wait {secs}s and try again)'
        return False, f'Discord {res.status_code}'
    except Exception as exc:
        return False, str(exc)[:160]

def session_ping_payload(game_name, role_id):
    mention = f'<@&{role_id}>' if _ROLE_ID_RE.match(role_id or '') else '@Corporate Slave'
    raw = (game_name or '').strip()
    if not raw or raw.lower().startswith('tbd'):
        game_line = "Tonight's lineup is still TBD."
        embed_game = 'TBD'
    else:
        game_line = f"Tonight we're playing **{raw}**."
        embed_game = raw
    content = f"{mention} {game_line} Session starts in 15 minutes — get ready and gather up."
    payload = {
        'content': content,
        'allowed_mentions': {'parse': []},
        'embeds': [{
            'title': 'OreTime Saturday',
            'description': 'Get ready and gather up. We start at 20:00.',
            'color': 0xFFD700,
            'fields': [
                {'name': 'Tonight', 'value': embed_game, 'inline': True},
                {'name': 'Start', 'value': '20:00', 'inline': True},
            ],
        }],
    }
    if _ROLE_ID_RE.match(role_id or ''):
        payload['allowed_mentions'] = {'parse': [], 'roles': [role_id]}
    return payload

def try_send_session_ping(force=False, mark=True):
    now = berlin_now()
    today = now.date().isoformat()
    in_window = now.weekday() == 5 and (
        (now.hour == 19 and now.minute >= 45) or (now.hour == 20 and now.minute <= 10)
    )
    if not force and not in_window:
        return False, 'Outside Saturday 19:45–20:10 Berlin'
    conn = get_db()
    try:
        sent = (config_get(conn, 'session_ping_sent', '') or '').strip()
        if not _valid_webhook(DISCORD_WEBHOOK_URL):
            return False, 'Webhook URL missing or invalid'
        if not force and sent == today:
            return False, 'Already sent today'
        next_sat = get_next_two_saturdays()[0]
        winner = get_winner_for_date(next_sat, conn=conn)
        ok, msg = send_discord_webhook(
            DISCORD_WEBHOOK_URL,
            session_ping_payload(winner, DISCORD_PING_ROLE_ID),
        )
        if ok and mark:
            config_set(conn, 'session_ping_sent', today)
            conn.commit()
        return ok, msg
    finally:
        conn.close()

def maybe_session_ping():
    if not _ping_lock.acquire(blocking=False):
        return
    try:
        try_send_session_ping(force=False, mark=True)
    except Exception:
        pass
    finally:
        _ping_lock.release()

def kick_session_ping_if_due():
    global _ping_checked_ts
    now_ts = time.time()
    if now_ts - _ping_checked_ts < 60:
        return
    now = berlin_now()
    in_window = now.weekday() == 5 and (
        (now.hour == 19 and now.minute >= 45) or (now.hour == 20 and now.minute <= 10)
    )
    if not in_window:
        return
    _ping_checked_ts = now_ts
    threading.Thread(target=maybe_session_ping, daemon=True).start()

def weekly_atmosphere(game_appids, conn=None):
    now = time.time()
    if now - _atmosphere_cache['ts'] < 120:
        return _atmosphere_cache['art'], _atmosphere_cache['winner']
    winner = ''
    art = ''
    close = False
    try:
        if conn is None:
            conn = get_db()
            close = True
        next_sat = get_next_two_saturdays()[0]
        winner = get_winner_for_date(next_sat, conn=conn) or ''
        appid = str((game_appids or {}).get(winner) or '').strip()
        if appid and appid.lower() != 'non' and not (winner or '').lower().startswith('tbd'):
            art = f'https://shared.akamai.steamstatic.com/store_item_assets/steam/apps/{appid}/header.jpg'
    except Exception:
        winner, art = '', ''
    finally:
        if close and conn is not None:
            conn.close()
    _atmosphere_cache.update({'ts': now, 'art': art, 'winner': winner})
    return art, winner

def get_db():
    conn = _raw_db()
    try:
        conn.execute('SELECT 1 FROM users LIMIT 1')
    except sqlite3.OperationalError:
        conn.close()
        init_db()
        conn = _raw_db()
    return conn

def init_db():
    conn = _raw_db()
    conn.execute('''CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY, username TEXT UNIQUE, password TEXT, steam_id TEXT, theme TEXT DEFAULT 'pink')''')

    try: conn.execute('ALTER TABLE users ADD COLUMN owns_title INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN custom_title TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN avatar TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN discord_name TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN discord_id TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN banner TEXT DEFAULT "#1a1a1a"')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN ore_coins INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN discord_status TEXT DEFAULT "offline"')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN discord_activity TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN owns_mvp INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN active_border TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN borders TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    
    # NEU: Spalten für das Banner System
    try: conn.execute('ALTER TABLE users ADD COLUMN active_banner TEXT DEFAULT "default"')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN owned_banners TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN banner_config TEXT DEFAULT "{}"')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN last_claim_date TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN claim_streak INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN xp INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN season_xp INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN claimed_level_rewards TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN xp_date TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN xp_today INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN welkin_until TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN artifact_date TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE users ADD COLUMN artifact_runs INTEGER DEFAULT 0')
    except sqlite3.OperationalError: pass
    
    conn.execute('''CREATE TABLE IF NOT EXISTS votes (id INTEGER PRIMARY KEY, user_id INTEGER, target_date TEXT, game1 TEXT, game2 TEXT, game3 TEXT, UNIQUE(user_id, target_date))''')
    try: conn.execute('ALTER TABLE votes ADD COLUMN game1 TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE votes ADD COLUMN game2 TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE votes ADD COLUMN game3 TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE votes ADD COLUMN multiplier INTEGER DEFAULT 1')
    except sqlite3.OperationalError: pass

    conn.execute('''CREATE TABLE IF NOT EXISTS beacons (id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT, game TEXT, created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP)''')
    conn.execute('''CREATE TABLE IF NOT EXISTS wishlist (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, game_name TEXT, appid TEXT)''')
    try: conn.execute('ALTER TABLE wishlist ADD COLUMN kind TEXT DEFAULT "game"')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE wishlist ADD COLUMN created_at TEXT')
    except sqlite3.OperationalError: pass
    conn.execute('''CREATE TABLE IF NOT EXISTS radar (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, target_date TEXT, status TEXT, UNIQUE(user_id, target_date))''')
    conn.execute('''CREATE TABLE IF NOT EXISTS games (id INTEGER PRIMARY KEY, name TEXT UNIQUE, steam_appid TEXT)''')
    conn.execute('''CREATE TABLE IF NOT EXISTS config (key TEXT UNIQUE, value TEXT)''')
    conn.execute("INSERT OR IGNORE INTO config (key, value) VALUES ('voting_locked', 'false')")
    conn.execute("INSERT OR IGNORE INTO config (key, value) VALUES ('pit_ashes', '0')")
    conn.execute("INSERT OR IGNORE INTO config (key, value) VALUES ('looks_rev', '0')")
    conn.execute("INSERT OR IGNORE INTO config (key, value) VALUES ('session_ping_sent', '')")
    conn.execute('''CREATE TABLE IF NOT EXISTS coinflips (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        creator_id INTEGER NOT NULL,
        joiner_id INTEGER,
        stake INTEGER NOT NULL,
        creator_side TEXT NOT NULL,
        result_side TEXT,
        winner_id INTEGER,
        rake INTEGER DEFAULT 0,
        status TEXT DEFAULT 'open',
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        resolved_at TIMESTAMP
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS armory_likes (
        liker_id INTEGER NOT NULL,
        owner_id INTEGER NOT NULL,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (liker_id, owner_id)
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS market_listings (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        seller_id INTEGER NOT NULL,
        item_type TEXT NOT NULL,
        item_key TEXT NOT NULL,
        price INTEGER NOT NULL,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS armory (
        user_id TEXT PRIMARY KEY, username TEXT,
        cpu TEXT, gpu TEXT, mouse TEXT, sens TEXT, keyboard TEXT, photo TEXT, updated_at TEXT)''')
    try: conn.execute('ALTER TABLE armory ADD COLUMN keyboard TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE armory ADD COLUMN photo TEXT')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE armory ADD COLUMN updated_at TEXT')
    except sqlite3.OperationalError: pass
    conn.execute('''CREATE TABLE IF NOT EXISTS armory_ratings (
        rater_id INTEGER NOT NULL,
        owner_id INTEGER NOT NULL,
        stars INTEGER NOT NULL,
        PRIMARY KEY (rater_id, owner_id)
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS highlights (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        url TEXT NOT NULL,
        title TEXT DEFAULT '',
        platform TEXT DEFAULT 'other',
        embed_id TEXT DEFAULT '',
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS highlight_likes (
        user_id INTEGER NOT NULL,
        highlight_id INTEGER NOT NULL,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (user_id, highlight_id)
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS clip_of_week (
        week_id TEXT PRIMARY KEY,
        highlight_id INTEGER NOT NULL,
        creator_id INTEGER NOT NULL,
        paid INTEGER DEFAULT 0,
        awarded_at TIMESTAMP
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS quest_claims (
        user_id INTEGER NOT NULL,
        week_id TEXT NOT NULL,
        reward INTEGER,
        claimed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY (user_id, week_id)
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS notifications (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        kind TEXT DEFAULT '',
        title TEXT NOT NULL,
        body TEXT DEFAULT '',
        link TEXT DEFAULT '',
        is_read INTEGER DEFAULT 0,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS live_activity (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        kind TEXT DEFAULT '',
        icon TEXT DEFAULT '',
        text TEXT NOT NULL,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )''')
    try: conn.execute('ALTER TABLE live_activity ADD COLUMN meta TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    try: conn.execute('ALTER TABLE notifications ADD COLUMN meta TEXT DEFAULT ""')
    except sqlite3.OperationalError: pass
    conn.execute('''CREATE TABLE IF NOT EXISTS item_requests (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        user_id INTEGER NOT NULL,
        title TEXT NOT NULL,
        kind TEXT NOT NULL,
        color_notes TEXT DEFAULT '',
        details TEXT DEFAULT '',
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )''')

    if conn.execute("SELECT COUNT(*) FROM games").fetchone()[0] == 0:
        default_games = [("Big Walk", "1478500"), ("Codenames", "non"), ("Meccha", "4704690"), ("PEAK", "3527290"), ("R.E.P.O.", "3241660")]
        conn.executemany("INSERT INTO games (name, steam_appid) VALUES (?, ?)", default_games)
    conn.commit()
    conn.close()
    os.makedirs(ARMORY_UPLOAD_DIR, exist_ok=True)

init_db()

_SESSION_FREE_ENDPOINTS = frozenset({'static', 'index', 'login', 'callback', 'logout'})

def _session_uid():
    raw = session.get('user_id')
    if raw is None or raw == '':
        return None
    try:
        return int(raw)
    except (TypeError, ValueError):
        return None

def _names_match(a, b):
    return (a or '').strip().lower() == (b or '').strip().lower()

def _row_discord_id(row):
    if not row:
        return ''
    try:
        if 'discord_id' in row.keys():
            return (row['discord_id'] or '').strip()
    except Exception:
        pass
    return ''

def ensure_session_user(conn):
    """Bind this request to the logged-in person. Never reuse another account's id."""
    uid = _session_uid()
    uname = (session.get('username') or '').strip()
    discord_id = (session.get('discord_id') or '').strip()
    if uid is None and not uname and not discord_id:
        return None
    row = None
    if discord_id:
        try:
            row = conn.execute("SELECT * FROM users WHERE discord_id = ?", (discord_id,)).fetchone()
        except sqlite3.OperationalError:
            row = None
    if row is None and uid is not None:
        by_id = conn.execute("SELECT * FROM users WHERE id = ?", (uid,)).fetchone()
        if by_id:
            row_did = _row_discord_id(by_id)
            if discord_id and row_did and discord_id != row_did:
                by_id = None
            elif uname and not _names_match(by_id['username'], uname):
                by_id = None
        row = by_id
    if row is None and uname:
        by_name = conn.execute(
            "SELECT * FROM users WHERE username = ? COLLATE NOCASE",
            (uname,),
        ).fetchone()
        if by_name:
            row_did = _row_discord_id(by_name)
            if discord_id and row_did and discord_id != row_did:
                by_name = None
        row = by_name
    if not row:
        return None
    session['user_id'] = row['id']
    session['username'] = row['username']
    row_did = _row_discord_id(row)
    if row_did:
        session['discord_id'] = row_did
    session.modified = True
    return row

@app.before_request
def _repair_stale_session():
    if request.endpoint in _SESSION_FREE_ENDPOINTS:
        return
    if request.path.startswith('/static/'):
        return
    if not session.get('user_id') and not session.get('username'):
        return
    conn = get_db()
    try:
        row = ensure_session_user(conn)
    finally:
        conn.close()
    if row:
        return
    session.clear()
    if request.path.startswith('/api/'):
        return jsonify({'error': 'Please log in again.'}), 401
    return redirect(url_for('login'))


def sanitize_hex(val, default):
    if isinstance(val, str) and HEX_RE.fullmatch(val.strip()):
        return val.strip()
    return default

BANNER_CONFIG_DEFAULTS = {
    'bg_color': '#1a1a1a',
    'text_glow': '#ff0000',
    'u_bg1': '#ff0000',
    'u_bg2': '#000000',
    'u_bg3': '#0000ff',
    'u_txt': '#00ffff',
    'g_bg1': '#ff0000',
    'g_bg2': '#ffff00',
    'g_bg3': '#00ff00',
    'g_bg4': '#00ffff',
    'g_bg5': '#0000ff',
    'g_txt1': '#ffffff',
    'g_txt2': '#aaaaaa',
}

def banner_config_from_mapping(src):
    src = src or {}
    if isinstance(src, str):
        try:
            src = json.loads(src)
        except Exception:
            src = {}
    if not isinstance(src, dict):
        src = {}
    return {k: sanitize_hex(src.get(k), d) for k, d in BANNER_CONFIG_DEFAULTS.items()}

BORDER_WRAP_KEYS = frozenset((
    'cosmos', 'giga', 'cyan', 'protocol', 'orecore',
    'void', 'plasma', 'aurora', 'glitch', 'obsidian',
    'apex', 'eclipse',
))
BORDER_IMG_KEYS = frozenset(('hacker', 'gold', 'ember', 'frost'))

def border_wrap_class(active_border):
    key = (active_border or '').strip()
    return f'border-{key}-wrapper' if key in BORDER_WRAP_KEYS else ''

def border_img_class(active_border):
    key = (active_border or '').strip()
    return f'border-{key}' if key in BORDER_IMG_KEYS else ''

def _player_face(row):
    steam_id = ''
    border = ''
    try:
        if 'steam_id' in row.keys():
            steam_id = row['steam_id'] or ''
        if 'active_border' in row.keys():
            border = row['active_border'] or ''
    except Exception:
        pass
    return {
        'username': row['username'],
        'avatar': safe_avatar(row['avatar'] if 'avatar' in row.keys() else None),
        'steam_id': steam_id,
        'active_border': border or '',
    }

def safe_avatar(value):
    return value if value else DEFAULT_AVATAR

def vote_multiplier(row):
    if row is None:
        return 1
    try:
        if 'multiplier' in row.keys() and row['multiplier']:
            return max(1, int(row['multiplier']))
    except (TypeError, ValueError, IndexError):
        pass
    return 1

def apply_vote_scores(scores, row):
    mult = vote_multiplier(row)
    for game, points in ((row['game1'], 3), (row['game2'], 2), (row['game3'], 1)):
        if game in scores:
            scores[game] += points * mult

def _count_loc_sync():
    loc = 0
    skip_dirs = {'.venv', 'venv', 'env', '__pycache__', 'node_modules', '.git', 'uploads'}
    for root, dirs, files in os.walk(os.path.abspath(os.path.dirname(__file__))):
        dirs[:] = [d for d in dirs if d not in skip_dirs]
        for file in files:
            if file.endswith(('.py', '.html', '.css', '.js')):
                try:
                    with open(os.path.join(root, file), 'r', encoding='utf-8') as f:
                        loc += sum(1 for line in f)
                except Exception:
                    pass
    _loc_cache['count'] = loc
    _loc_cache['ts'] = time.time()


def get_total_loc():
    now = time.time()
    if _loc_cache['count'] is not None and now - _loc_cache['ts'] < LOC_CACHE_TTL:
        return _loc_cache['count']
    if _loc_cache['count'] is None:
        _loc_cache['count'] = 0
        threading.Thread(target=_count_loc_sync, daemon=True).start()
        return 0
    threading.Thread(target=_count_loc_sync, daemon=True).start()
    return _loc_cache['count']

def get_all_games():
    conn = get_db()
    games = conn.execute("SELECT * FROM games ORDER BY name").fetchall()
    conn.close()
    return games

SEASON_NAME = 'Season 1: Saturday Protocol'
SEASON_MAX_LEVEL = 20
SEASON_ENDS_AT = datetime(2026, 9, 23, 23, 59, 59)
_SEASON_END_MONTHS = ('Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec')


def season_end_payload():
    now = datetime.now()
    return {
        'season_ends_at': SEASON_ENDS_AT.isoformat(timespec='seconds'),
        'season_ends_ms': int(SEASON_ENDS_AT.timestamp() * 1000),
        'season_ends_label': f"{SEASON_ENDS_AT.day} {_SEASON_END_MONTHS[SEASON_ENDS_AT.month - 1]} {SEASON_ENDS_AT.year}",
        'server_now_ms': int(now.timestamp() * 1000),
    }


DAILY_XP_CAP = 80
WELKIN_COST = 150
WELKIN_DAYS = 30
WELKIN_DAILY_OC = 8
WELKIN_INSTANT_OC = 20
ARTIFACT_RUNS_PER_DAY = 4
ARTIFACT_COMMON = ('Vault Flower', 'Ore Plume', 'Protocol Sands', 'Saturday Goblet', 'Night Circlet')
ARTIFACT_FINE = ('Ember Wake Flower', 'Frostline Plume', 'Ion Drift Sands', 'Acid Vein Cup', 'Aurora Circlet')
ARTIFACT_RARE = ('Genesis Flower', 'Apex Plume', 'Eclipse Sands', 'OreCore Goblet', 'Satmax Circlet')
CRATE_COST = 75
CRATE_DUP_OC = 15
CRATE_COMMON_OC = 10
COINFLIP_TTL_MIN = 10
COINFLIP_RAKE_PCT = 5
CASINO_ALLOWED_STAKES = (5, 10, 20, 50, 100, 250, 500)

COSMETIC_LABELS = {
    'hacker': 'Hacker',
    'gold': 'Gold',
    'cosmos': 'Cosmos',
    'giga': 'GIGA',
    'cyan': 'Ocean (Pink)',
    'ember': 'Ember',
    'frost': 'Frost',
    'void': 'Void',
    'plasma': 'Plasma',
    'aurora': 'Aurora',
    'glitch': 'Glitch',
    'obsidian': 'Obsidian',
    'protocol': 'Protocol Ring',
    'orecore': 'OreCore',
    'apex': 'Apex Ring',
    'eclipse': 'Eclipse',
    'standard': 'OreTime Standard',
    'pro': 'OreTime Pro',
    'ultra': 'OreTime Ultra',
    'giga_banner': 'OreTime Giga',
    'carbon': 'Carbon',
    'ember_banner': 'Ember Wake',
    'frost_banner': 'Frostline',
    'ion': 'Ion Drift',
    'acid_vein': 'Acid Vein',
    'aurora_banner': 'Aurora Veil',
    'velvet': 'Velvet Static',
    'molten': 'Molten',
    'voidglitch': 'VOIDGLITCH',
    'nightbeacon': 'Night Beacon',
    'satmax': 'Saturday Protocol MAX',
    'dawnveil': 'Dawn Veil',
    'genesis': 'Genesis',
    'pioneer': 'Protocol Pioneer',
}
BORDER_KEYS = {
    'hacker', 'gold', 'cosmos', 'giga', 'cyan', 'ember', 'frost',
    'void', 'plasma', 'aurora', 'glitch', 'obsidian',
    'protocol', 'orecore', 'apex', 'eclipse',
}
BANNER_KEYS = {
    'standard', 'pro', 'ultra', 'giga_banner',
    'carbon', 'ember_banner', 'frost_banner', 'ion', 'acid_vein', 'aurora_banner', 'velvet', 'molten',
    'voidglitch', 'nightbeacon', 'satmax', 'dawnveil', 'genesis',
}
BANNER_EQUIPPED_TEXT = 'OreTime'
BANNER_STYLE_MAP = {
    'standard': {'class': '', 'text_class': 'banner-standard-text', 'shop_text': 'Standard'},
    'pro': {'class': '', 'text_class': 'banner-pro-text', 'shop_text': 'Pro'},
    'ultra': {'class': '', 'text_class': 'banner-ultra-text', 'shop_text': 'Ultra'},
    'giga_banner': {'class': 'giga-banner-bg', 'text_class': 'banner-giga-text', 'shop_text': 'Giga'},
    'voidglitch': {'class': 'voidglitch-banner', 'text_class': 'banner-void-text', 'shop_text': 'VOIDGLITCH'},
    'nightbeacon': {'class': 'nightbeacon-banner', 'text_class': 'banner-beacon-text', 'shop_text': 'Night Beacon'},
    'satmax': {'class': 'satmax-banner', 'text_class': 'banner-satmax-text', 'shop_text': 'Protocol MAX'},
    'carbon': {'class': 'carbon-banner', 'text_class': 'banner-carbon-text', 'shop_text': 'Carbon'},
    'ember_banner': {'class': 'emberwake-banner', 'text_class': 'banner-ember-text', 'shop_text': 'Ember Wake'},
    'frost_banner': {'class': 'frostline-banner', 'text_class': 'banner-frost-text', 'shop_text': 'Frostline'},
    'ion': {'class': 'ion-banner', 'text_class': 'banner-ion-text', 'shop_text': 'Ion Drift'},
    'acid_vein': {'class': 'acidvein-banner', 'text_class': 'banner-acid-text', 'shop_text': 'Acid Vein'},
    'aurora_banner': {'class': 'aurora-banner', 'text_class': 'banner-aurora-text', 'shop_text': 'Aurora Veil'},
    'velvet': {'class': 'velvet-banner', 'text_class': 'banner-velvet-text', 'shop_text': 'Velvet Static'},
    'molten': {'class': 'molten-banner', 'text_class': 'banner-molten-text', 'shop_text': 'Molten'},
    'dawnveil': {'class': 'dawnveil-banner', 'text_class': 'banner-dawn-text', 'shop_text': 'Dawn Veil'},
    'genesis': {'class': 'genesis-banner', 'text_class': 'banner-genesis-text', 'shop_text': 'Genesis'},
}
WISHLIST_KINDS = {
    'game': 'Game',
    'banner': 'Banner',
    'frame': 'Profile frame',
    'other': 'Other wishes',
}
WISHLIST_KIND_ALIASES = {
    'game': 'game',
    'games': 'game',
    'banner': 'banner',
    'banners': 'banner',
    'frame': 'frame',
    'profile frame': 'frame',
    'profile_frame': 'frame',
    'profileframe': 'frame',
    'border': 'frame',
    'borders': 'frame',
    'other': 'other',
    'other wish': 'other',
    'other wishes': 'other',
    'wish': 'other',
    'wishes': 'other',
    'general': 'other',
    'general wish': 'other',
    'general wishes': 'other',
}
TITLE_PRESETS = {
    'pioneer': 'Protocol Pioneer',
}
RARITY_META = {
    'common': {'label': 'Common', 'color': '#9aa0a6'},
    'uncommon': {'label': 'Uncommon', 'color': '#3fb950'},
    'rare': {'label': 'Rare', 'color': '#58a6ff'},
    'epic': {'label': 'Epic', 'color': '#bb86fc'},
    'legendary': {'label': 'Legendary', 'color': '#FFD700'},
    'secret': {'label': 'Secret', 'color': '#00ffc8'},
}
COSMETIC_KIND_LABELS = {
    'border': 'Border',
    'banner': 'Banner',
    'title': 'Title',
    'mvp': 'Boost',
    'oc': 'OreCoins',
    'xp': 'Season XP',
}
COSMETIC_DEFS = [
    {'key': 'hacker', 'type': 'border', 'rarity': 'uncommon', 'icon': '🟢', 'blurb': 'Green flicker ring'},
    {'key': 'gold', 'type': 'border', 'rarity': 'rare', 'icon': '🥇', 'blurb': 'Gold pulse ring'},
    {'key': 'cosmos', 'type': 'border', 'rarity': 'epic', 'icon': '🌌', 'blurb': 'Purple galaxy ring'},
    {'key': 'giga', 'type': 'border', 'rarity': 'legendary', 'icon': '🌈', 'blurb': 'RGB flow ring'},
    {'key': 'cyan', 'type': 'border', 'rarity': 'common', 'icon': '🌊', 'blurb': 'Animated pink ocean flow ring'},
    {'key': 'ember', 'type': 'border', 'rarity': 'uncommon', 'icon': '🔥', 'blurb': 'Ember flicker ring'},
    {'key': 'frost', 'type': 'border', 'rarity': 'uncommon', 'icon': '❄️', 'blurb': 'Ice pulse ring'},
    {'key': 'void', 'type': 'border', 'rarity': 'rare', 'icon': '🕳️', 'blurb': 'Deep void halo'},
    {'key': 'plasma', 'type': 'border', 'rarity': 'rare', 'icon': '⚡', 'blurb': 'Magenta-cyan plasma'},
    {'key': 'aurora', 'type': 'border', 'rarity': 'epic', 'icon': '🌈', 'blurb': 'Northern lights ring'},
    {'key': 'glitch', 'type': 'border', 'rarity': 'epic', 'icon': '👾', 'blurb': 'RGB glitch ring'},
    {'key': 'obsidian', 'type': 'border', 'rarity': 'legendary', 'icon': '🖤', 'blurb': 'Black-gold obsidian'},
    {'key': 'protocol', 'type': 'border', 'rarity': 'epic', 'icon': '📡', 'blurb': 'Pass Exclusive Protocol ring', 'exclusive': True},
    {'key': 'orecore', 'type': 'border', 'rarity': 'epic', 'icon': '💎', 'blurb': 'Pass Exclusive OreCore ring', 'exclusive': True},
    {'key': 'apex', 'type': 'border', 'rarity': 'legendary', 'icon': '👑', 'blurb': 'Pass Exclusive spinning Apex ring', 'exclusive': True},
    {'key': 'eclipse', 'type': 'border', 'rarity': 'legendary', 'icon': '🌑', 'blurb': 'Pass Exclusive Eclipse corona', 'exclusive': True},
    {'key': 'standard', 'type': 'banner', 'rarity': 'common', 'icon': '🏳️', 'blurb': 'Solid banner'},
    {'key': 'pro', 'type': 'banner', 'rarity': 'uncommon', 'icon': '💜', 'blurb': 'Glow text banner'},
    {'key': 'ultra', 'type': 'banner', 'rarity': 'rare', 'icon': '🌈', 'blurb': '3-color gradient'},
    {'key': 'giga_banner', 'type': 'banner', 'rarity': 'legendary', 'icon': '⭐', 'blurb': 'GIGA rainbow banner'},
    {'key': 'carbon', 'type': 'banner', 'rarity': 'common', 'icon': '⬛', 'blurb': 'Carbon weave banner'},
    {'key': 'ember_banner', 'type': 'banner', 'rarity': 'uncommon', 'icon': '🔥', 'blurb': 'Ember wake banner'},
    {'key': 'frost_banner', 'type': 'banner', 'rarity': 'uncommon', 'icon': '❄️', 'blurb': 'Frostline banner'},
    {'key': 'ion', 'type': 'banner', 'rarity': 'rare', 'icon': '⚡', 'blurb': 'Ion drift banner'},
    {'key': 'acid_vein', 'type': 'banner', 'rarity': 'rare', 'icon': '🧪', 'blurb': 'Acid vein banner'},
    {'key': 'aurora_banner', 'type': 'banner', 'rarity': 'epic', 'icon': '🌌', 'blurb': 'Aurora veil banner'},
    {'key': 'velvet', 'type': 'banner', 'rarity': 'epic', 'icon': '💗', 'blurb': 'Velvet static banner'},
    {'key': 'molten', 'type': 'banner', 'rarity': 'legendary', 'icon': '🌋', 'blurb': 'Molten flow banner'},
    {'key': 'voidglitch', 'type': 'banner', 'rarity': 'secret', 'icon': '👾', 'blurb': 'Crate-only glitch'},
    {'key': 'nightbeacon', 'type': 'banner', 'rarity': 'epic', 'icon': '🌙', 'blurb': 'Pass Exclusive Night Beacon', 'exclusive': True},
    {'key': 'satmax', 'type': 'banner', 'rarity': 'legendary', 'icon': '📡', 'blurb': 'Pass Exclusive MAX banner', 'exclusive': True},
    {'key': 'dawnveil', 'type': 'banner', 'rarity': 'rare', 'icon': '🌅', 'blurb': 'Pass Exclusive Dawn Veil', 'exclusive': True},
    {'key': 'genesis', 'type': 'banner', 'rarity': 'legendary', 'icon': '✨', 'blurb': 'Pass Exclusive Genesis banner', 'exclusive': True},
    {'key': 'title', 'type': 'title', 'rarity': 'uncommon', 'icon': '🔥', 'blurb': 'Custom player title'},
    {'key': 'mvp', 'type': 'mvp', 'rarity': 'rare', 'icon': '🌟', 'blurb': 'Use when voting to double that week'},
]
LIVE_ACTIVITY_KEEP = 40
NOTIFY_KEEP = 100
RARITY_SORT_ORDER = ('secret', 'legendary', 'epic', 'rare', 'uncommon', 'common')
LIGHT_BANNER_KEYS = {'frost_banner'}
TRADEABLE_BORDERS = BORDER_KEYS
TRADEABLE_BANNERS = BANNER_KEYS
CRATE_UNCOMMON_BORDERS = [
    'hacker', 'gold', 'cosmos', 'giga', 'cyan', 'ember', 'frost',
    'void', 'plasma', 'aurora', 'glitch', 'obsidian',
]
CRATE_RARE_BANNERS = [
    'pro', 'ultra', 'giga_banner', 'carbon', 'ember_banner', 'frost_banner',
    'ion', 'acid_vein', 'aurora_banner', 'velvet', 'molten',
]
SHOP_PRICES = {
    'title': 100,
    'mvp': 200,
    'hacker': 50,
    'gold': 100,
    'cosmos': 200,
    'giga': 250,
    'cyan': 25,
    'ember': 60,
    'frost': 75,
    'void': 120,
    'plasma': 140,
    'aurora': 180,
    'glitch': 210,
    'obsidian': 260,
    'standard': 0,
    'pro': 50,
    'ultra': 150,
    'giga_banner': 200,
    'carbon': 30,
    'ember_banner': 55,
    'frost_banner': 70,
    'ion': 110,
    'acid_vein': 90,
    'aurora_banner': 160,
    'velvet': 135,
    'molten': 190,
}
SHOP_BORDER_BUY = {
    'hacker', 'gold', 'cosmos', 'giga', 'cyan', 'ember', 'frost',
    'void', 'plasma', 'aurora', 'glitch', 'obsidian',
}
SHOP_BANNER_BUY = {
    'standard', 'pro', 'ultra', 'giga_banner',
    'carbon', 'ember_banner', 'frost_banner', 'ion', 'acid_vein', 'aurora_banner', 'velvet', 'molten',
}
SEASON_REWARDS = {
    1: ('oc', 10),
    2: ('oc', 15),
    3: ('banner', 'dawnveil'),
    4: ('oc', 25),
    5: ('border', 'protocol'),
    6: ('oc', 30),
    7: ('xp', 8),
    8: ('oc', 35),
    9: ('title', 'pioneer'),
    10: ('banner', 'nightbeacon'),
    11: ('oc', 40),
    12: ('xp', 10),
    13: ('oc', 45),
    14: ('oc', 50),
    15: ('border', 'orecore'),
    16: ('border', 'eclipse'),
    17: ('banner', 'genesis'),
    18: ('border', 'apex'),
    19: ('oc', 75),
    20: ('banner', 'satmax'),
}
SEASON_REWARD_PREVIEWS = {
    'protocol': {'kind': 'border', 'wrapper': 'border-protocol-wrapper'},
    'orecore': {'kind': 'border', 'wrapper': 'border-orecore-wrapper'},
    'apex': {'kind': 'border', 'wrapper': 'border-apex-wrapper'},
    'eclipse': {'kind': 'border', 'wrapper': 'border-eclipse-wrapper'},
    'nightbeacon': {'kind': 'banner', 'banner_class': 'nightbeacon-banner', 'text_class': 'banner-beacon-text', 'text': BANNER_EQUIPPED_TEXT},
    'satmax': {'kind': 'banner', 'banner_class': 'satmax-banner', 'text_class': 'banner-satmax-text', 'text': BANNER_EQUIPPED_TEXT},
    'dawnveil': {'kind': 'banner', 'banner_class': 'dawnveil-banner', 'text_class': 'banner-dawn-text', 'text': BANNER_EQUIPPED_TEXT},
    'genesis': {'kind': 'banner', 'banner_class': 'genesis-banner', 'text_class': 'banner-genesis-text', 'text': BANNER_EQUIPPED_TEXT},
}

def _csv_list(val):
    return [x.strip() for x in (val or '').split(',') if x and x.strip()]

def _csv_join(items):
    seen = []
    for item in items:
        if item and item not in seen:
            seen.append(item)
    return ','.join(seen)

def cosmetic_label(key):
    return COSMETIC_LABELS.get(key, (key or '').replace('_', ' ').title())

LIVE_SHOP_LABELS = {
    'hacker': 'Hacker border',
    'gold': 'Gold border',
    'cosmos': 'Cosmos border',
    'giga': 'GIGA border',
    'cyan': 'Ocean (Pink) border',
    'ember': 'Ember border',
    'frost': 'Frost border',
    'void': 'Void border',
    'plasma': 'Plasma border',
    'aurora': 'Aurora border',
    'glitch': 'Glitch border',
    'obsidian': 'Obsidian border',
    'protocol': 'Protocol Ring',
    'orecore': 'OreCore border',
    'apex': 'Apex Ring',
    'eclipse': 'Eclipse border',
    'standard': 'OreTime Standard Banner',
    'pro': 'OreTime Pro Banner',
    'ultra': 'OreTime Ultra Banner',
    'giga_banner': 'GIGA Banner',
    'carbon': 'Carbon Banner',
    'ember_banner': 'Ember Wake Banner',
    'frost_banner': 'Frostline Banner',
    'ion': 'Ion Drift Banner',
    'acid_vein': 'Acid Vein Banner',
    'aurora_banner': 'Aurora Veil Banner',
    'velvet': 'Velvet Static Banner',
    'molten': 'Molten Banner',
    'voidglitch': 'VOIDGLITCH Banner',
    'nightbeacon': 'Night Beacon Banner',
    'satmax': 'Saturday Protocol MAX Banner',
    'dawnveil': 'Dawn Veil Banner',
    'genesis': 'Genesis Banner',
    'pioneer': 'Protocol Pioneer Title',
    'title': 'Custom Title',
    'mvp': 'MVP Multiplier',
    'welkin': 'Welkin Blessing',
}
LIVE_SHOP_BUY_KEYS = SHOP_BORDER_BUY | (SHOP_BANNER_BUY - {'standard'})

def live_item_label(key):
    return LIVE_SHOP_LABELS.get(key) or cosmetic_label(key)

def _safe_name(name):
    text = re.sub(r'[\x00-\x1f\x7f<>]', '', str(name or '')).strip()
    return text[:32] or 'Someone'

def _hero_slug(winner):
    return re.sub(r'[^a-z0-9]+', '', (winner or '').lower())

def hero_video_rel(winner):
    slug = _hero_slug(winner)
    candidates = []
    if 'repo' in slug:
        candidates.append('video/hero-repo.mp4')
    if slug:
        candidates.append(f'video/hero-{slug}.mp4')
    candidates.append('video/hero.mp4')
    static_dir = os.path.join(APP_ROOT, 'static')
    seen = set()
    for rel in candidates:
        if rel in seen:
            continue
        seen.add(rel)
        path = os.path.join(static_dir, *rel.split('/'))
        if os.path.isfile(path):
            return rel
    return None

def _fetch_notifications(conn, user_id, limit):
    try:
        return conn.execute(
            "SELECT id, kind, title, body, link, is_read, created_at, meta FROM notifications WHERE user_id = ? ORDER BY id DESC LIMIT ?",
            (user_id, limit),
        ).fetchall()
    except sqlite3.OperationalError:
        return conn.execute(
            "SELECT id, kind, title, body, link, is_read, created_at FROM notifications WHERE user_id = ? ORDER BY id DESC LIMIT ?",
            (user_id, limit),
        ).fetchall()

def _activity_event_payload(row):
    keys = row.keys() if hasattr(row, 'keys') else []
    meta_raw = row['meta'] if 'meta' in keys else ''
    i18n_key, i18n_vars = _parse_activity_meta(meta_raw)
    return {
        'id': row['id'],
        'kind': row['kind'] or '',
        'icon': row['icon'] or '•',
        'text': row['text'] or '',
        'created_at': row['created_at'] or '',
        'i18n_key': i18n_key or '',
        'i18n_vars': i18n_vars or {},
    }

def _notification_payload(row):
    if not row:
        return None
    keys = row.keys() if hasattr(row, 'keys') else []
    meta_raw = row['meta'] if 'meta' in keys else ''
    i18n_key, i18n_vars = _parse_activity_meta(meta_raw)
    title = row['title'] or ''
    body = row['body'] or ''
    if i18n_key:
        title = t_ui(i18n_key, **{k: v for k, v in i18n_vars.items() if k != '_body_key'})
        body_key = i18n_vars.get('_body_key')
        if body_key:
            body_vars = {k: v for k, v in i18n_vars.items() if k != '_body_key'}
            body = t_ui(body_key, **body_vars)
    return {
        'id': row['id'],
        'kind': row['kind'] or '',
        'title': title,
        'body': body,
        'link': row['link'] or '',
        'read': bool(row['is_read']),
        'created_at': row['created_at'] or '',
        'i18n_key': i18n_key or '',
        'i18n_vars': i18n_vars or {},
    }

def _trim_user_notifications(conn, user_id):
    rows = conn.execute(
        "SELECT id FROM notifications WHERE user_id = ? ORDER BY id DESC LIMIT ?",
        (user_id, NOTIFY_KEEP),
    ).fetchall()
    if len(rows) >= NOTIFY_KEEP:
        conn.execute(
            "DELETE FROM notifications WHERE user_id = ? AND id < ?",
            (user_id, min(r['id'] for r in rows)),
        )

def push_notification(user_id, kind, title, body='', link='', conn=None, i18n_key=None, i18n_vars=None, body_key=None):
    if not user_id or not title:
        return
    close = False
    if conn is None:
        conn = get_db()
        close = True
    vars_ = dict(i18n_vars or {})
    if body_key:
        vars_['_body_key'] = body_key
    meta = _activity_meta(i18n_key, vars_)
    try:
        try:
            cur = conn.execute(
                "INSERT INTO notifications (user_id, kind, title, body, link, meta) VALUES (?, ?, ?, ?, ?, ?)",
                (int(user_id), kind or '', str(title)[:180], str(body or '')[:280], str(link or '')[:120], meta),
            )
        except sqlite3.OperationalError:
            cur = conn.execute(
                "INSERT INTO notifications (user_id, kind, title, body, link) VALUES (?, ?, ?, ?, ?)",
                (int(user_id), kind or '', str(title)[:180], str(body or '')[:280], str(link or '')[:120]),
            )
        nid = cur.lastrowid
        _trim_user_notifications(conn, int(user_id))
        if close:
            conn.commit()
    except Exception:
        pass
    finally:
        if close:
            conn.close()

def _activity_meta(i18n_key, i18n_vars):
    if not i18n_key:
        return ''
    try:
        return json.dumps({'key': i18n_key, 'vars': i18n_vars or {}}, ensure_ascii=False)
    except Exception:
        return ''

def _parse_activity_meta(raw):
    if not raw:
        return None, {}
    try:
        data = json.loads(raw) if isinstance(raw, str) else raw
        if not isinstance(data, dict):
            return None, {}
        key = data.get('key') or data.get('i18n_key')
        vars_ = data.get('vars') or data.get('i18n_vars') or {}
        if not isinstance(vars_, dict):
            vars_ = {}
        return (key if isinstance(key, str) else None), vars_
    except Exception:
        return None, {}

def push_activity(*args, **kwargs):
    return None

def emit_watchout_live(*args, **kwargs):
    return None

def emit_shop_live(*args, **kwargs):
    return None

def emit_profile_update(*args, **kwargs):
    return None

def bump_looks_rev(conn):
    try:
        conn.execute("INSERT OR IGNORE INTO config (key, value) VALUES ('looks_rev', '0')")
        row = conn.execute("SELECT value FROM config WHERE key = 'looks_rev'").fetchone()
        n = int((row['value'] if row else '0') or 0) + 1
        conn.execute("UPDATE config SET value = ? WHERE key = 'looks_rev'", (str(n),))
    except Exception:
        pass

def owned_inventory_items(user):
    if not user:
        return []
    owned_borders = set(_csv_list(user['borders'] if 'borders' in user.keys() else ''))
    owned_banners = set(_csv_list(user['owned_banners'] if 'owned_banners' in user.keys() else ''))
    active_border = user['active_border'] if 'active_border' in user.keys() else ''
    active_banner = user['active_banner'] if 'active_banner' in user.keys() else 'default'
    items = []
    for spec in COSMETIC_DEFS:
        owned = False
        equipped = False
        qty = 1
        mvp_qty = 0
        if spec['type'] == 'border':
            owned = spec['key'] in owned_borders
            equipped = (active_border or '') == spec['key']
        elif spec['type'] == 'banner':
            owned = spec['key'] in owned_banners
            equipped = (active_banner or '') == spec['key']
        elif spec['type'] == 'title':
            owned = bool(user['owns_title'] if 'owns_title' in user.keys() else 0)
        elif spec['type'] == 'mvp':
            mvp_qty = int(user['owns_mvp'] if 'owns_mvp' in user.keys() and user['owns_mvp'] else 0)
            owned = mvp_qty > 0
            qty = mvp_qty
        if not owned:
            continue
        rarity = spec['rarity']
        meta = RARITY_META.get(rarity) or RARITY_META['common']
        style = BANNER_STYLE_MAP.get(spec['key']) or {}
        items.append({
            'key': spec['key'],
            'type': spec['type'],
            'label': cosmetic_label(spec['key']) if spec['key'] in COSMETIC_LABELS else (
                'Custom Title' if spec['type'] == 'title' else 'MVP Multiplier'
            ),
            'rarity': rarity,
            'rarity_label': meta['label'],
            'rarity_color': meta['color'],
            'kind_label': COSMETIC_KIND_LABELS.get(spec['type'], spec['type']),
            'icon': spec['icon'],
            'blurb': spec['blurb'],
            'equipped': equipped,
            'exclusive': bool(spec.get('exclusive')),
            'qty': qty,
            'wrap': f'border-{spec["key"]}-wrapper' if spec['key'] in BORDER_WRAP_KEYS else '',
            'img_class': f'border-{spec["key"]}' if spec['key'] in BORDER_IMG_KEYS else '',
            'banner_class': style.get('class', ''),
            'text_class': style.get('text_class', ''),
            'preview_text': BANNER_EQUIPPED_TEXT,
        })
    return items


def group_inventory_by_rarity(items):
    buckets = {key: [] for key in RARITY_SORT_ORDER}
    for item in items:
        rarity = item.get('rarity') if item.get('rarity') in buckets else 'common'
        buckets[rarity].append(item)
    groups = []
    for key in RARITY_SORT_ORDER:
        if not buckets[key]:
            continue
        meta = RARITY_META.get(key) or RARITY_META['common']
        groups.append({
            'key': key,
            'label': meta['label'],
            'color': meta['color'],
            'items': buckets[key],
        })
    return groups


def _hex_luminance(hex_color):
    val = sanitize_hex(hex_color, '#1a1a1a')
    h = val[1:]
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    return (0.299 * r + 0.587 * g + 0.114 * b) / 255.0


def member_banner_look(active_banner, banner_config, banner_hex):
    cfg = banner_config_from_mapping(banner_config)
    banner = (active_banner or 'default').strip() or 'default'
    style = BANNER_STYLE_MAP.get(banner) or {}
    css_class = style.get('class', '')
    bg_style = ''
    probe_hex = sanitize_hex(banner_hex, '#1a1a1a')
    text_class = style.get('text_class') or 'banner-standard-text'
    text_style = ''

    if banner == 'standard':
        probe_hex = sanitize_hex(cfg.get('bg_color'), '#1a1a1a')
        bg_style = f'background:{probe_hex};'
        css_class = ''
        text_class = 'banner-standard-text'
    elif banner == 'pro':
        glow = sanitize_hex(cfg.get('text_glow'), '#ff0000')
        bg_style = 'background:#000000;'
        probe_hex = '#000000'
        css_class = ''
        text_class = 'banner-pro-text'
        text_style = f'color:{glow};filter:drop-shadow(0 0 8px {glow});'
    elif banner == 'ultra':
        u1 = sanitize_hex(cfg.get('u_bg1'), '#ff0000')
        u2 = sanitize_hex(cfg.get('u_bg2'), '#000000')
        u3 = sanitize_hex(cfg.get('u_bg3'), '#0000ff')
        ut = sanitize_hex(cfg.get('u_txt'), '#00ffff')
        bg_style = f'background:linear-gradient(90deg,{u1} 0%,{u1} 15%,{u2} 50%,{u3} 85%,{u3} 100%);'
        probe_hex = u2
        css_class = ''
        text_class = 'banner-ultra-text'
        text_style = f'color:{ut};filter:drop-shadow(0 0 10px {ut});'
    elif banner == 'giga_banner':
        g1 = sanitize_hex(cfg.get('g_bg1'), '#ff0000')
        g2 = sanitize_hex(cfg.get('g_bg2'), '#ffff00')
        g3 = sanitize_hex(cfg.get('g_bg3'), '#00ff00')
        g4 = sanitize_hex(cfg.get('g_bg4'), '#00ffff')
        g5 = sanitize_hex(cfg.get('g_bg5'), '#0000ff')
        t1 = sanitize_hex(cfg.get('g_txt1'), '#ffffff')
        t2 = sanitize_hex(cfg.get('g_txt2'), '#aaaaaa')
        css_class = 'giga-banner-bg'
        bg_style = (
            f'--giga-flow:linear-gradient(90deg,{g1},{g2},{g3},{g4},{g5},{g1});'
        )
        probe_hex = g2
        text_class = 'banner-giga-text'
        text_style = f'background-image:linear-gradient(90deg,{t1},{t2},{t1},{t2},{t1});'
    elif css_class:
        pass
    else:
        bg_style = f'background:{probe_hex};'
        text_class = 'banner-standard-text'

    if banner in LIGHT_BANNER_KEYS:
        text_mode = 'dark'
    elif banner == 'standard':
        text_mode = 'dark' if _hex_luminance(probe_hex) > 0.58 else 'light'
    elif banner in BANNER_KEYS:
        text_mode = 'light'
    else:
        text_mode = 'dark' if _hex_luminance(probe_hex) > 0.58 else 'light'

    return {
        'css_class': css_class,
        'bg_style': bg_style,
        'text_mode': text_mode,
        'text_class': text_class,
        'text_style': text_style,
        'overlay_text': BANNER_EQUIPPED_TEXT,
    }


def reset_user_economy(conn, user_id):
    conn.execute(
        """UPDATE users SET
            ore_coins = 0,
            owns_title = 0,
            custom_title = '',
            owns_mvp = 0,
            borders = '',
            active_border = '',
            owned_banners = '',
            active_banner = 'default',
            banner = '#1a1a1a',
            banner_config = '{}',
            season_xp = 0,
            claimed_level_rewards = '',
            xp = 0,
            xp_today = 0
        WHERE id = ?""",
        (user_id,),
    )
    conn.execute("DELETE FROM market_listings WHERE seller_id = ?", (user_id,))

def _debit_coins(conn, user_id, amount):
    if amount <= 0:
        return True
    cur = conn.execute(
        "UPDATE users SET ore_coins = COALESCE(ore_coins, 0) - ? WHERE id = ? AND COALESCE(ore_coins, 0) >= ?",
        (amount, user_id, amount),
    )
    return cur.rowcount >= 1

def _credit_coins(conn, user_id, amount):
    if amount > 0:
        conn.execute("UPDATE users SET ore_coins = COALESCE(ore_coins, 0) + ? WHERE id = ?", (amount, user_id))

def _grant_cosmetic(conn, user_id, item_type, item_key):
    user = conn.execute("SELECT borders, owned_banners FROM users WHERE id = ?", (user_id,)).fetchone()
    if not user:
        return False
    if item_type == 'border':
        owned = _csv_list(user['borders'])
        if item_key in owned:
            return False
        owned.append(item_key)
        conn.execute("UPDATE users SET borders = ? WHERE id = ?", (_csv_join(owned), user_id))
        return True
    owned = _csv_list(user['owned_banners'])
    if item_key in owned:
        return False
    owned.append(item_key)
    conn.execute("UPDATE users SET owned_banners = ? WHERE id = ?", (_csv_join(owned), user_id))
    return True

def _owns_cosmetic(user, item_type, item_key):
    if item_type == 'border':
        return item_key in _csv_list(user['borders'] if user else '')
    return item_key in _csv_list(user['owned_banners'] if user else '')

def _remove_cosmetic(conn, user_id, item_type, item_key):
    user = conn.execute("SELECT borders, owned_banners, active_border, active_banner FROM users WHERE id = ?", (user_id,)).fetchone()
    if not user or not _owns_cosmetic(user, item_type, item_key):
        return False
    if item_type == 'border':
        owned = [b for b in _csv_list(user['borders']) if b != item_key]
        if (user['active_border'] or '') == item_key:
            conn.execute("UPDATE users SET borders = ?, active_border = '' WHERE id = ?", (_csv_join(owned), user_id))
        else:
            conn.execute("UPDATE users SET borders = ? WHERE id = ?", (_csv_join(owned), user_id))
        return True
    owned = [b for b in _csv_list(user['owned_banners']) if b != item_key]
    if (user['active_banner'] or '') == item_key:
        conn.execute("UPDATE users SET owned_banners = ?, active_banner = 'default' WHERE id = ?", (_csv_join(owned), user_id))
    else:
        conn.execute("UPDATE users SET owned_banners = ? WHERE id = ?", (_csv_join(owned), user_id))
    return True

def season_xp_required(level):
    if level <= 1:
        return 0
    total = 0
    for lv in range(2, min(level, SEASON_MAX_LEVEL) + 1):
        total += 10 + (lv - 2) * 4
    return total

def season_level_from_xp(xp):
    xp = xp or 0
    level = 1
    for lv in range(2, SEASON_MAX_LEVEL + 1):
        if xp >= season_xp_required(lv):
            level = lv
        else:
            break
    return level

def season_progress_payload(season_xp):
    season_xp = season_xp or 0
    level = season_level_from_xp(season_xp)
    if level >= SEASON_MAX_LEVEL:
        return {
            'season_name': SEASON_NAME,
            'level': SEASON_MAX_LEVEL,
            'xp': season_xp,
            'xp_into_level': season_xp_required(SEASON_MAX_LEVEL),
            'xp_for_level': 0,
            'next_level_xp': season_xp_required(SEASON_MAX_LEVEL),
            'percent': 100,
            'maxed': True,
        }
    current_need = season_xp_required(level)
    next_need = season_xp_required(level + 1)
    into = season_xp - current_need
    span = max(1, next_need - current_need)
    return {
        'season_name': SEASON_NAME,
        'level': level,
        'xp': season_xp,
        'xp_into_level': into,
        'xp_for_level': span,
        'next_level_xp': next_need,
        'percent': min(100, int(round(100 * into / span))),
        'maxed': False,
    }

def _claimed_reward_levels(user):
    return set(x for x in _csv_list(user['claimed_level_rewards'] if user else '') if str(x).isdigit())

def _season_reward_entry(reward_level):
    item_type, item_key = SEASON_REWARDS[reward_level]
    if item_type == 'oc':
        amount = int(item_key)
        return {
            'level': reward_level,
            'type': 'oc',
            'item': 'oc',
            'label': f'{amount} OC',
            'amount': amount,
            'preview': {'kind': 'oc', 'text': f'{amount} OC'},
        }
    if item_type == 'xp':
        amount = int(item_key)
        return {
            'level': reward_level,
            'type': 'xp',
            'item': 'xp',
            'label': f'+{amount} Season XP',
            'amount': amount,
            'preview': {'kind': 'xp', 'text': f'+{amount} XP'},
        }
    if item_type == 'title':
        text = TITLE_PRESETS.get(item_key, cosmetic_label(item_key))
        return {
            'level': reward_level,
            'type': 'title',
            'item': item_key,
            'label': cosmetic_label(item_key),
            'preview': {'kind': 'title', 'text': text},
        }
    preview = dict(SEASON_REWARD_PREVIEWS.get(item_key) or {})
    if not preview:
        if item_type == 'border':
            if item_key in BORDER_WRAP_KEYS:
                preview = {'kind': 'border', 'wrapper': f'border-{item_key}-wrapper'}
            else:
                preview = {'kind': 'border', 'img_class': f'border-{item_key}'}
        else:
            style = BANNER_STYLE_MAP.get(item_key) or {}
            preview = {
                'kind': 'banner',
                'banner_class': style.get('class', ''),
                'text_class': style.get('text_class', ''),
                'text': BANNER_EQUIPPED_TEXT,
            }
    return {
        'level': reward_level,
        'type': item_type,
        'item': item_key,
        'label': cosmetic_label(item_key),
        'preview': preview,
    }

def _season_claimable_rewards(user):
    if not user:
        return []
    level = season_level_from_xp(user['season_xp'] or 0)
    claimed = _claimed_reward_levels(user)
    claimable = []
    for reward_level in SEASON_REWARDS:
        if level >= reward_level and str(reward_level) not in claimed:
            claimable.append(_season_reward_entry(reward_level))
    return claimable

def season_track_payload(user):
    progress = season_progress_payload(user['season_xp'] if user else 0)
    level = progress['level']
    claimed = _claimed_reward_levels(user)
    nodes = []
    claimable_count = 0
    for lv in range(1, SEASON_MAX_LEVEL + 1):
        node = {
            'level': lv,
            'xp_required': season_xp_required(lv),
            'reached': level >= lv,
            'current': level == lv,
            'reward': None,
            'status': 'reached' if level >= lv else 'locked',
        }
        if lv in SEASON_REWARDS:
            node['reward'] = _season_reward_entry(lv)
            if str(lv) in claimed:
                node['status'] = 'claimed'
            elif level >= lv:
                node['status'] = 'claimable'
                claimable_count += 1
            else:
                node['status'] = 'locked'
        nodes.append(node)
    progress['nodes'] = nodes
    progress['claimable_count'] = claimable_count
    progress['claimed_levels'] = sorted(int(x) for x in claimed)
    return progress

def _claim_season_reward(conn, user_id, reward_level):
    if reward_level not in SEASON_REWARDS:
        return {'ok': False, 'error': 'No reward at that level.', 'status': 400}
    user = conn.execute(
        "SELECT season_xp, claimed_level_rewards, borders, owned_banners, owns_title, custom_title FROM users WHERE id = ?",
        (user_id,),
    ).fetchone()
    if not user:
        resolved = ensure_session_user(conn)
        if resolved:
            user_id = resolved['id']
            user = conn.execute(
                "SELECT season_xp, claimed_level_rewards, borders, owned_banners, owns_title, custom_title FROM users WHERE id = ?",
                (user_id,),
            ).fetchone()
    if not user:
        return {'ok': False, 'error': 'User not found.', 'status': 404}
    level = season_level_from_xp(user['season_xp'] or 0)
    if level < reward_level:
        return {'ok': False, 'error': 'Level not reached yet.', 'status': 400}
    claimed = _claimed_reward_levels(user)
    key = str(reward_level)
    if key in claimed:
        return {'ok': False, 'error': 'Already claimed.', 'status': 400}
    item_type, item_key = SEASON_REWARDS[reward_level]
    if item_type == 'oc':
        _credit_coins(conn, user_id, int(item_key))
    elif item_type == 'xp':
        amount = int(item_key)
        conn.execute(
            "UPDATE users SET xp = COALESCE(xp, 0) + ?, season_xp = COALESCE(season_xp, 0) + ? WHERE id = ?",
            (amount, amount, user_id),
        )
    elif item_type == 'title':
        preset = TITLE_PRESETS.get(item_key, cosmetic_label(item_key))
        current = (user['custom_title'] or '').strip() if 'custom_title' in user.keys() else ''
        conn.execute(
            "UPDATE users SET owns_title = 1, custom_title = ? WHERE id = ?",
            ((current or preset)[:48], user_id),
        )
    else:
        _grant_cosmetic(conn, user_id, item_type, item_key)
    claimed.add(key)
    conn.execute(
        "UPDATE users SET claimed_level_rewards = ? WHERE id = ?",
        (_csv_join(sorted(claimed, key=lambda x: int(x))), user_id),
    )
    entry = _season_reward_entry(reward_level)
    return {'ok': True, 'reward': entry}

def grant_xp(conn, user_id, amount):
    empty = {'granted': 0, 'unlocked': [], 'claimable': []}
    if amount <= 0:
        return empty
    today = date.today().isoformat()
    user = conn.execute("SELECT xp, season_xp, xp_date, xp_today FROM users WHERE id = ?", (user_id,)).fetchone()
    if not user:
        return empty
    old_level = season_level_from_xp(user['season_xp'] or 0)
    xp_today = user['xp_today'] or 0
    if (user['xp_date'] or '') != today:
        xp_today = 0
    remaining = max(0, DAILY_XP_CAP - xp_today)
    given = min(amount, remaining)
    if given <= 0:
        return {'granted': 0, 'unlocked': [], 'claimable': [], 'capped': True}
    conn.execute(
        "UPDATE users SET xp = COALESCE(xp, 0) + ?, season_xp = COALESCE(season_xp, 0) + ?, xp_date = ?, xp_today = ? WHERE id = ?",
        (given, given, today, xp_today + given, user_id),
    )
    track_user = conn.execute(
        "SELECT season_xp, claimed_level_rewards, borders, owned_banners FROM users WHERE id = ?",
        (user_id,),
    ).fetchone()
    new_level = season_level_from_xp(track_user['season_xp'] if track_user else 0)
    if new_level > old_level:
        for lv in range(old_level + 1, new_level + 1):
            push_notification(
                user_id,
                'pass',
                f'You reached Battle Pass level {lv}!',
                'Saturday Protocol',
                '/pass',
                conn=conn,
                i18n_key='notify.passLevel',
                i18n_vars={'level': lv},
                body_key='notify.saturdayProtocol',
            )
    claimable = _season_claimable_rewards(track_user)
    return {'granted': given, 'unlocked': [], 'claimable': claimable, 'capped': False, 'level': new_level}

def fetch_steam_name(steam_id, live=True):
    if not steam_id:
        return ''
    now = time.time()
    cached = _steam_name_cache.get(steam_id)
    if cached and now - cached['ts'] < STEAM_NAME_TTL:
        return cached['name']
    if not live:
        return cached['name'] if cached else ''
    try:
        res = requests.get(
            f"https://api.steampowered.com/ISteamUser/GetPlayerSummaries/v0002/?key={STEAM_API_KEY}&steamids={steam_id}",
            timeout=STEAM_HTTP_TIMEOUT,
        ).json()
        name = ((res.get('response') or {}).get('players') or [{}])[0].get('personaname') or 'Connected'
        _steam_name_cache[steam_id] = {'ts': now, 'name': name}
        return name
    except Exception:
        return cached['name'] if cached else 'Connected'

def fetch_recent_steam_games(steam_id, limit=2, live=True):
    if not steam_id:
        return []
    now = time.time()
    cached = _recent_games_cache.get(steam_id)
    if cached and now - cached['ts'] < STEAM_RECENT_TTL:
        return cached['games'][:limit]
    if not live:
        return (cached['games'][:limit] if cached else [])
    try:
        res = requests.get(
            f"https://api.steampowered.com/IPlayerService/GetOwnedGames/v0001/?key={STEAM_API_KEY}&steamid={steam_id}&include_appinfo=1&include_played_free_games=1&format=json",
            timeout=STEAM_HTTP_TIMEOUT,
        ).json()
        games = res.get('response', {}).get('games') or []
        recent = [g for g in games if g.get('playtime_2weeks')]
        recent.sort(key=lambda g: g.get('playtime_2weeks', 0), reverse=True)
        compact = [{
            'name': g.get('name') or 'Unknown',
            'appid': g.get('appid'),
            'minutes_2w': int(g.get('playtime_2weeks') or 0),
            'minutes_total': int(g.get('playtime_forever') or 0),
        } for g in recent[:8]]
        total_2w = sum(int(g.get('playtime_2weeks') or 0) for g in games)
        total_forever = sum(int(g.get('playtime_forever') or 0) for g in games)
        _recent_games_cache[steam_id] = {'ts': now, 'games': compact, 'total_2w': total_2w, 'total_forever': total_forever}
        return compact[:limit]
    except Exception:
        return (cached['games'][:limit] if cached else [])

def steam_play_summary(steam_id):
    games = fetch_recent_steam_games(steam_id, limit=6)
    cached = _recent_games_cache.get(steam_id) or {}
    return {
        'games': games,
        'total_2w': cached.get('total_2w', sum(g.get('minutes_2w') or 0 for g in games)),
        'total_forever': cached.get('total_forever', 0),
    }

def hours_label(minutes):
    minutes = int(minutes or 0)
    if minutes < 60:
        return f"{minutes}m"
    hours = minutes / 60.0
    if hours < 10:
        return f"{hours:.1f}h"
    return f"{int(round(hours))}h"

def expire_stale_flips(conn):
    mins = int(COINFLIP_TTL_MIN)
    rows = conn.execute(
        f"SELECT id, creator_id, stake FROM coinflips WHERE status = 'open' AND created_at <= datetime('now', '-{mins} minutes')"
    ).fetchall()
    for row in rows:
        _credit_coins(conn, row['creator_id'], row['stake'])
        conn.execute("UPDATE coinflips SET status = 'expired' WHERE id = ?", (row['id'],))
    return len(rows)

def _add_pit_ashes(conn, amount):
    if amount <= 0:
        return
    row = conn.execute("SELECT value FROM config WHERE key = 'pit_ashes'").fetchone()
    current = int(row['value']) if row and str(row['value']).isdigit() else 0
    conn.execute(
        "INSERT INTO config (key, value) VALUES ('pit_ashes', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
        (str(current + amount),),
    )

def _user_public(row):
    return {
        'id': row['id'],
        'username': row['username'],
        'avatar': safe_avatar(row['avatar'] if 'avatar' in row.keys() else None),
    }

def _user_val(user, key, default=None):
    if not user:
        return default
    try:
        if key not in user.keys():
            return default
    except Exception:
        return default
    val = user[key]
    return default if val is None else val

def _parse_iso_date(val):
    raw = str(val or '').strip()[:10]
    if not raw:
        return None
    try:
        return date.fromisoformat(raw)
    except ValueError:
        return None

def welkin_until_date(user):
    return _parse_iso_date(_user_val(user, 'welkin_until', ''))

def welkin_active(user, today=None):
    today = today or date.today()
    until = welkin_until_date(user)
    return bool(until and until >= today)

def welkin_days_left(user, today=None):
    today = today or date.today()
    until = welkin_until_date(user)
    if not until or until < today:
        return 0
    return (until - today).days + 1

def welkin_extend_until(user, today=None):
    today = today or date.today()
    until = welkin_until_date(user)
    if until and until >= today:
        return until + timedelta(days=WELKIN_DAYS)
    return today + timedelta(days=WELKIN_DAYS - 1)

def artifact_runs_used(user, today=None):
    today = today or date.today()
    last = str(_user_val(user, 'artifact_date', '') or '')
    runs = int(_user_val(user, 'artifact_runs', 0) or 0)
    if last != today.isoformat():
        return 0
    return max(0, runs)

def artifact_runs_left(user, today=None):
    return max(0, ARTIFACT_RUNS_PER_DAY - artifact_runs_used(user, today))

def roll_artifact_drop():
    roll = random.random()
    if roll < 0.08:
        return {
            'name': random.choice(ARTIFACT_RARE),
            'rarity': 'rare',
            'oc': random.randint(12, 18),
            'xp': 4,
        }
    if roll < 0.35:
        return {
            'name': random.choice(ARTIFACT_FINE),
            'rarity': 'fine',
            'oc': random.randint(5, 9),
            'xp': 3,
        }
    return {
        'name': random.choice(ARTIFACT_COMMON),
        'rarity': 'common',
        'oc': random.randint(1, 4),
        'xp': 2,
    }

def endgame_chamber(level):
    level = max(0, int(level or 0))
    floor = min(12, 1 + level // 2)
    chamber = (level % 3) + 1
    return {
        'floor': floor,
        'chamber': chamber,
        'label': f'{floor}-{chamber}',
    }

def daily_claim_status(user):
    today = date.today()
    last = user['last_claim_date'] if user and 'last_claim_date' in user.keys() else None
    streak = user['claim_streak'] if user and 'claim_streak' in user.keys() else 0
    streak = streak or 0
    available = True
    if last == today.isoformat():
        available = False
    display_streak = streak if streak <= 7 else 7
    active = last in (today.isoformat(), (today - timedelta(days=1)).isoformat())
    welkin_on = welkin_active(user, today)
    return {
        'available': available,
        'streak': display_streak,
        'last_claim_date': last or '',
        'next_bonus_in': max(0, 7 - (display_streak if active else 0)),
        'welkin_active': welkin_on,
        'welkin_days': welkin_days_left(user, today),
        'welkin_bonus': WELKIN_DAILY_OC if welkin_on else 0,
    }

def iso_week_id(d=None):
    d = d or date.today()
    y, w, _ = d.isocalendar()
    return f"{y}-W{w:02d}"

def iso_week_start(d=None):
    d = d or date.today()
    return d - timedelta(days=d.isocalendar()[2] - 1)

def _steam_user_fields(user):
    if isinstance(user, dict):
        name, steam_id = user.get('username'), user.get('steam_id')
    else:
        name, steam_id = user['username'], user['steam_id']
    steam_id = (steam_id or '').strip()
    return name, steam_id or None

def _steam_appid_set(apps):
    out = set()
    for a in apps or []:
        try:
            out.add(int(a))
        except (TypeError, ValueError):
            continue
    return out

def _steam_owned_index(steam):
    index = {}
    for name, apps in (steam.get('owned') or {}).items():
        key = (name or '').strip().lower()
        if key:
            index[key] = _steam_appid_set(apps)
    return index

def _steam_nosteam_index(steam):
    return {(n or '').strip().lower() for n in (steam.get('no_steam') or []) if n}

def _steam_cache_covers(users_snap, steam):
    if not steam or not steam.get('ts'):
        return False
    owned = _steam_owned_index(steam)
    no_steam = _steam_nosteam_index(steam)
    for u in users_snap or []:
        name, steam_id = _steam_user_fields(u)
        key = (name or '').strip().lower()
        if not key:
            continue
        if steam_id:
            if key not in owned:
                return False
        elif key not in no_steam:
            return False
    return True

def _steam_missing_users(all_users, steam, appid_int):
    """Who does not own this app. Users not in the cache yet count as missing."""
    owned = _steam_owned_index(steam)
    no_steam = _steam_nosteam_index(steam)
    missing = []
    for u in all_users or []:
        name, steam_id = _steam_user_fields(u)
        if not name:
            continue
        key = name.strip().lower()
        if not steam_id or key in no_steam:
            missing.append(name)
            continue
        if appid_int not in owned.get(key, set()):
            missing.append(name)
    return missing

def _steam_users_snap(all_users):
    if all_users is None:
        conn = get_db()
        try:
            rows = conn.execute("SELECT username, steam_id FROM users").fetchall()
            return [{'username': r['username'], 'steam_id': r['steam_id']} for r in rows]
        finally:
            conn.close()
    snap = []
    for u in all_users:
        name, steam_id = _steam_user_fields(u)
        snap.append({'username': name, 'steam_id': steam_id})
    return snap

def _hydrate_steam_cache_from_db():
    global _steam_cache_loaded
    if _steam_cache_loaded:
        return
    _steam_cache_loaded = True
    if _steam_cache['ts'] > 0:
        return
    try:
        conn = get_db()
        row = conn.execute("SELECT value FROM config WHERE key = ?", (STEAM_CACHE_KEY,)).fetchone()
        conn.close()
        if not row or not row['value']:
            return
        data = json.loads(row['value'])
        owned = {}
        for name, apps in (data.get('owned') or {}).items():
            owned[name] = [int(a) for a in apps]
        playtimes = {}
        for name, times in (data.get('playtimes') or {}).items():
            playtimes[name] = {int(k): int(v) for k, v in (times or {}).items()}
        _steam_cache.update({
            'ts': float(data.get('ts') or 0),
            'owned': owned,
            'playtimes': playtimes,
            'no_steam': list(data.get('no_steam') or []),
        })
    except Exception:
        pass

def _persist_steam_cache():
    try:
        payload = json.dumps({
            'ts': _steam_cache['ts'],
            'owned': _steam_cache['owned'],
            'playtimes': _steam_cache['playtimes'],
            'no_steam': _steam_cache['no_steam'],
        })
        conn = get_db()
        conn.execute(
            "INSERT INTO config (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
            (STEAM_CACHE_KEY, payload),
        )
        conn.commit()
        conn.close()
    except Exception:
        pass

def _run_steam_ownership_fetch(users_snap):
    global _steam_fail_ts
    owned_games = {}
    playtimes = {}
    no_steam_users = []
    ok = 0
    prev_owned = {(k or '').strip().lower(): v for k, v in (_steam_cache.get('owned') or {}).items()}
    prev_play = {(k or '').strip().lower(): v for k, v in (_steam_cache.get('playtimes') or {}).items()}
    for u in users_snap:
        name, steam_id = _steam_user_fields(u)
        if not name:
            continue
        key = name.strip().lower()
        if steam_id:
            try:
                games = requests.get(
                    f"https://api.steampowered.com/IPlayerService/GetOwnedGames/v0001/?key={STEAM_API_KEY}&steamid={steam_id}&include_played_free_games=1&format=json",
                    timeout=STEAM_HTTP_TIMEOUT,
                ).json().get('response', {}).get('games', []) or []
                owned_games[name] = [int(g['appid']) for g in games if g.get('appid') is not None]
                playtimes[name] = {
                    int(g['appid']): int(g.get('playtime_forever') or 0)
                    for g in games if g.get('appid') is not None
                }
                ok += 1
            except Exception:
                owned_games[name] = list(prev_owned.get(key, []))
                playtimes[name] = dict(prev_play.get(key, {}))
        else:
            no_steam_users.append(name)
    if ok > 0 or _steam_cache['ts'] == 0:
        _steam_cache.update({
            'ts': time.time(),
            'owned': owned_games,
            'playtimes': playtimes,
            'no_steam': no_steam_users,
        })
        _persist_steam_cache()
    else:
        _steam_fail_ts = time.time()

def _schedule_steam_refresh(users_snap):
    global _steam_refreshing
    with _steam_refresh_lock:
        if _steam_refreshing:
            return
        _steam_refreshing = True
    def job():
        global _steam_refreshing, _steam_fail_ts
        try:
            _run_steam_ownership_fetch(users_snap)
        except Exception:
            _steam_fail_ts = time.time()
        finally:
            with _steam_refresh_lock:
                _steam_refreshing = False
    threading.Thread(target=job, daemon=True).start()

def refresh_steam_ownership(all_users=None, blocking=False):
    now = time.time()
    _hydrate_steam_cache_from_db()
    snap = _steam_users_snap(all_users)
    covers = _steam_cache_covers(snap, _steam_cache)
    if covers and _steam_cache['ts'] > 0 and now - _steam_cache['ts'] < STEAM_CACHE_TTL:
        return _steam_cache
    if covers and _steam_fail_ts and now - _steam_fail_ts < STEAM_FAIL_TTL and _steam_cache['ts'] > 0:
        return _steam_cache
    if blocking:
        _run_steam_ownership_fetch(snap)
        return _steam_cache
    _schedule_steam_refresh(snap)
    return _steam_cache

def parse_clip_url(raw):
    raw = (raw or '').strip()
    if not raw or len(raw) > 500:
        return None
    try:
        parsed = urlparse(raw)
    except Exception:
        return None
    if parsed.scheme not in ('http', 'https'):
        return None
    host = (parsed.netloc or '').lower()
    if host.startswith('www.'):
        host = host[4:]
    allowed = (
        host == 'youtube.com' or host.endswith('.youtube.com') or host == 'youtu.be'
        or host == 'twitch.tv' or host.endswith('.twitch.tv')
        or host == 'medal.tv' or host.endswith('.medal.tv')
    )
    if not allowed:
        return None
    yt = re.search(r'(?:youtube\.com/watch\?v=|youtu\.be/|youtube\.com/embed/|youtube\.com/shorts/)([A-Za-z0-9_-]{6,})', raw, re.I)
    if yt:
        return {'platform': 'youtube', 'embed_id': yt.group(1), 'url': raw}
    clip = re.search(r'(?:clips\.twitch\.tv/|twitch\.tv/[^/]+/clip/)([A-Za-z0-9_-]+)', raw, re.I)
    if clip:
        return {'platform': 'twitch_clip', 'embed_id': clip.group(1), 'url': raw}
    vod = re.search(r'twitch\.tv/videos/(\d+)', raw, re.I)
    if vod:
        return {'platform': 'twitch_vod', 'embed_id': vod.group(1), 'url': raw}
    if 'medal.tv' in host:
        return {'platform': 'medal', 'embed_id': '', 'url': raw}
    return {'platform': 'twitch', 'embed_id': '', 'url': raw}

def _sniff_image(header):
    if header.startswith(b'\xff\xd8\xff'):
        return 'jpg'
    if header.startswith(b'\x89PNG\r\n\x1a\n'):
        return 'png'
    if len(header) >= 12 and header[:4] == b'RIFF' and header[8:12] == b'WEBP':
        return 'webp'
    return None

def save_armory_photo(file_storage):
    if not file_storage or not getattr(file_storage, 'filename', None):
        return None, None
    stream = file_storage.stream
    stream.seek(0, os.SEEK_END)
    size = stream.tell()
    stream.seek(0)
    if size <= 0:
        return None, None
    if size > ARMORY_PHOTO_MAX:
        return None, 'Setup photo max is 3 MB.'
    header = stream.read(16)
    stream.seek(0)
    kind = _sniff_image(header)
    if not kind:
        return None, 'Only JPG, PNG or WEBP photos.'
    filename = f"{session.get('user_id')}_{secrets.token_hex(8)}.{kind}"
    dest = os.path.join(ARMORY_UPLOAD_DIR, filename)
    file_storage.save(dest)
    return filename, None

def delete_armory_photo(filename):
    base = os.path.basename(filename or '')
    if not base:
        return
    path = os.path.join(ARMORY_UPLOAD_DIR, base)
    if os.path.isfile(path):
        try:
            os.remove(path)
        except OSError:
            pass

def week_clip_leader(conn, when=None):
    start = iso_week_start(when)
    end = start + timedelta(days=7)
    return conn.execute(
        """SELECT h.id, h.user_id, h.url, h.title, h.platform, h.embed_id, h.created_at,
                  u.username, u.avatar, COUNT(l.user_id) AS likes
           FROM highlights h
           JOIN users u ON u.id = h.user_id
           LEFT JOIN highlight_likes l ON l.highlight_id = h.id
           WHERE datetime(h.created_at) >= datetime(?) AND datetime(h.created_at) < datetime(?)
           GROUP BY h.id
           ORDER BY likes DESC, h.created_at ASC
           LIMIT 1""",
        (start.isoformat() + ' 00:00:00', end.isoformat() + ' 00:00:00'),
    ).fetchone()

def settle_clip_of_week(conn):
    last_week_day = date.today() - timedelta(days=7)
    week_id = iso_week_id(last_week_day)
    existing = conn.execute("SELECT week_id FROM clip_of_week WHERE week_id = ?", (week_id,)).fetchone()
    if existing:
        return
    leader = week_clip_leader(conn, last_week_day)
    if not leader or int(leader['likes'] or 0) <= 0:
        conn.execute(
            "INSERT INTO clip_of_week (week_id, highlight_id, creator_id, paid, awarded_at) VALUES (?, 0, 0, 0, CURRENT_TIMESTAMP)",
            (week_id,),
        )
        return
    _credit_coins(conn, leader['user_id'], CLIP_OF_WEEK_OC)
    conn.execute(
        "INSERT INTO clip_of_week (week_id, highlight_id, creator_id, paid, awarded_at) VALUES (?, ?, ?, 1, CURRENT_TIMESTAMP)",
        (week_id, leader['id'], leader['user_id']),
    )

def quest_progress(conn, user_id, username):
    week_start = iso_week_start().isoformat()
    next_sat = get_next_two_saturdays()[0]
    voted = conn.execute(
        "SELECT id FROM votes WHERE user_id = ? AND target_date = ?",
        (user_id, next_sat),
    ).fetchone() is not None
    watchout = conn.execute(
        "SELECT id FROM beacons WHERE username = ? AND datetime(created_at) >= datetime(?)",
        (username, week_start + ' 00:00:00'),
    ).fetchone() is not None
    armory_row = conn.execute(
        "SELECT updated_at FROM armory WHERE user_id = ?",
        (str(user_id),),
    ).fetchone()
    armory_ok = bool(armory_row and (armory_row['updated_at'] or '') >= week_start)
    tasks = [
        {'key': 'vote', 'label': 'Vote this week', 'hint': 'Drop your Saturday ranking on Events.', 'done': voted},
        {'key': 'watchout', 'label': 'Start a WatchOut', 'hint': 'Ping the squad from Community → WatchOut.', 'done': watchout},
        {'key': 'armory', 'label': 'Update Armory', 'hint': 'Save your loadout (photo optional) this week.', 'done': armory_ok},
    ]
    done_count = sum(1 for t in tasks if t['done'])
    week_id = iso_week_id()
    claimed = conn.execute(
        "SELECT reward FROM quest_claims WHERE user_id = ? AND week_id = ?",
        (user_id, week_id),
    ).fetchone()
    return {
        'week_id': week_id,
        'tasks': tasks,
        'done_count': done_count,
        'total': 3,
        'complete': done_count == 3,
        'claimed': bool(claimed),
        'claimed_reward': claimed['reward'] if claimed else None,
    }


def load_i18n(lang):
    if lang not in I18N_LANGS:
        lang = 'en'
    path = os.path.join(I18N_DIR, f'{lang}.json')
    try:
        mtime = os.path.getmtime(path)
    except OSError:
        mtime = 0
    if lang not in _i18n_catalogs or _i18n_mtimes.get(lang) != mtime:
        try:
            with open(path, encoding='utf-8') as fh:
                _i18n_catalogs[lang] = json.load(fh)
            _i18n_mtimes[lang] = mtime
        except (OSError, json.JSONDecodeError, TypeError, ValueError):
            _i18n_catalogs[lang] = {}
            _i18n_mtimes[lang] = mtime
    return _i18n_catalogs[lang]


def get_ui_lang():
    raw = (request.cookies.get('ot_lang') or '').strip().lower()
    return raw if raw in I18N_LANGS else 'en'


def t_ui(key, lang=None, **vars):
    lang = lang or get_ui_lang()

    def lookup(catalog):
        cur = catalog
        for part in str(key).split('.'):
            if not isinstance(cur, dict) or part not in cur:
                return None
            cur = cur[part]
        return cur if isinstance(cur, str) else None

    val = lookup(load_i18n(lang))
    if val is None and lang != 'en':
        val = lookup(load_i18n('en'))
    if val is None:
        return key
    for k, v in vars.items():
        val = val.replace('{' + str(k) + '}', str(v))
    return val


@app.context_processor
def inject_global_data():
    theme, steam_id, avatar = 'pink', '', 'https://cdn.discordapp.com/embed/avatars/0.png'
    nav_ore_coins = 0
    nav_daily = {'available': False, 'streak': 0}
    nav_borders = []
    nav_owned_banners = []
    nav_active_border = ''
    nav_active_banner = 'default'
    nav_banner_config = dict(BANNER_CONFIG_DEFAULTS)
    nav_owns_title = False
    nav_custom_title = ''
    admin_user = is_admin(session.get('username'))
    conn = get_db()
    games = conn.execute("SELECT name, steam_appid FROM games").fetchall()
    game_appids = {g['name']: g['steam_appid'] for g in games}

    locked_row = conn.execute("SELECT value FROM config WHERE key = 'voting_locked'").fetchone()
    voting_locked = (locked_row['value'] == 'true') if locked_row else False

    if 'user_id' in session:
        if 'theme' in session: theme = session['theme']
        if 'steam_id' in session: steam_id = session['steam_id']
        if 'avatar' in session: avatar = session['avatar']

        user = conn.execute(
            "SELECT theme, steam_id, avatar, ore_coins, last_claim_date, claim_streak, borders, owned_banners, active_border, active_banner, banner_config, owns_title, custom_title, welkin_until FROM users WHERE id = ?",
            (session['user_id'],),
        ).fetchone()
        if user:
            if 'theme' not in session or 'steam_id' not in session or 'avatar' not in session:
                theme = user['theme'] if user['theme'] else 'pink'
                steam_id = user['steam_id'] if user['steam_id'] else ''
                avatar = safe_avatar(user['avatar'] if 'avatar' in user.keys() else None)
                session.update({'theme': theme, 'steam_id': steam_id, 'avatar': avatar})
            nav_ore_coins = user['ore_coins'] or 0
            nav_daily = daily_claim_status(user)
            nav_borders = _csv_list(user['borders'] if 'borders' in user.keys() else '')
            nav_owned_banners = _csv_list(user['owned_banners'] if 'owned_banners' in user.keys() else '')
            nav_active_border = (user['active_border'] or '') if 'active_border' in user.keys() else ''
            nav_active_banner = (user['active_banner'] or 'default') if 'active_banner' in user.keys() else 'default'
            if 'banner_config' in user.keys():
                nav_banner_config = banner_config_from_mapping(user['banner_config'])
            nav_owns_title = bool(user['owns_title']) if 'owns_title' in user.keys() else False
            nav_custom_title = (user['custom_title'] or '') if 'custom_title' in user.keys() else ''
    bg_art, bg_winner = weekly_atmosphere(game_appids, conn=conn)
    conn.close()
    kick_session_ping_if_due()
    return {
        'current_theme': theme,
        'user_steam_id': steam_id,
        'user_avatar': avatar or DEFAULT_AVATAR,
        'game_appids': game_appids,
        'bg_game_art': bg_art,
        'bg_game_name': bg_winner,
        'voting_locked': voting_locked,
        'total_loc': get_total_loc(),
        'default_avatar': DEFAULT_AVATAR,
        'nav_ore_coins': nav_ore_coins,
        'nav_daily': nav_daily,
        'nav_borders': nav_borders,
        'nav_owned_banners': nav_owned_banners,
        'nav_active_border': nav_active_border,
        'nav_active_banner': nav_active_banner,
        'nav_banner_config': nav_banner_config,
        'nav_owns_title': nav_owns_title,
        'nav_custom_title': nav_custom_title,
        'cosmetic_labels': COSMETIC_LABELS,
        'is_admin': admin_user,
        'founder_username': FOUNDER_USERNAME,
        'site_author': SITE_AUTHOR,
        'site_co_author': SITE_CO_AUTHOR,
        'site_host': SITE_HOST,
        'home_creator_a': HOME_CREATOR_A,
        'home_creator_b': HOME_CREATOR_B,
        'border_wrap_class': border_wrap_class,
        'border_img_class': border_img_class,
        'border_wrap_keys': sorted(BORDER_WRAP_KEYS),
        'border_img_keys': sorted(BORDER_IMG_KEYS),
        'banner_style_map': BANNER_STYLE_MAP,
        'banner_equipped_text': BANNER_EQUIPPED_TEXT,
        'ui_lang': get_ui_lang(),
        'ui_i18n': load_i18n(get_ui_lang()),
        't': t_ui,
        **season_end_payload(),
    }

def get_next_two_saturdays():
    today = date.today()
    saturday1 = today + timedelta((5 - today.weekday()) % 7)
    return [saturday1.strftime('%Y-%m-%d'), (saturday1 + timedelta(days=7)).strftime('%Y-%m-%d')]

def get_past_saturdays(n=5):
    now = datetime.now()
    today = now.date()
    days_since_saturday = (today.weekday() - 5) % 7
    if days_since_saturday == 0 and now.hour < 20:
        days_since_saturday = 7
    last_saturday = today - timedelta(days=days_since_saturday)
    return [(last_saturday - timedelta(weeks=i)).strftime('%Y-%m-%d') for i in range(n)]

def get_winner_for_date(target_date, conn=None):
    close = False
    if conn is None:
        conn = get_db()
        close = True
    try:
        rows = conn.execute('SELECT game1, game2, game3, multiplier FROM votes WHERE target_date = ?', (target_date,)).fetchall()
        if not rows:
            return "TBD (No votes yet)"
        games = conn.execute("SELECT name FROM games ORDER BY name").fetchall()
        scores = {g['name']: 0 for g in games}
        if not scores:
            return "TBD (No votes yet)"
        for row in rows:
            apply_vote_scores(scores, row)
        if all(v == 0 for v in scores.values()):
            return "TBD (No votes yet)"
        return max(scores, key=scores.get)
    finally:
        if close:
            conn.close()

def collect_live_status():
    conn = get_db()
    users_count = conn.execute("SELECT COUNT(*) FROM users").fetchone()[0]
    votes_count = conn.execute("SELECT COUNT(*) FROM votes").fetchone()[0]
    games_count = conn.execute("SELECT COUNT(*) FROM games").fetchone()[0]
    locked_row = conn.execute("SELECT value FROM config WHERE key = 'voting_locked'").fetchone()
    voting_locked = (locked_row['value'] == 'true') if locked_row else False
    next_sat = get_next_two_saturdays()[0]
    radar = {'yes': 0, 'maybe': 0, 'no': 0}
    for row in conn.execute(
        "SELECT status, COUNT(*) AS c FROM radar WHERE target_date = ? GROUP BY status",
        (next_sat,)
    ):
        if row['status'] in radar:
            radar[row['status']] = row['c']
    active_beacons = conn.execute(
        "SELECT COUNT(*) FROM beacons WHERE created_at >= datetime('now', '-2 hours')"
    ).fetchone()[0]
    conn.close()
    return {
        'users_count': users_count,
        'votes_count': votes_count,
        'games_count': games_count,
        'voting_locked': voting_locked,
        'next_sat': next_sat,
        'winner': get_winner_for_date(next_sat),
        'radar': radar,
        'active_beacons': active_beacons,
        'total_loc': get_total_loc(),
        'server_time': datetime.now().isoformat(timespec='seconds'),
        'uptime_seconds': int(time.time() - _started_at),
    }

@app.route('/')
def index():
    if 'user_id' in session: 
        return redirect(url_for('home'))
    return render_template('landing.html')

@app.route('/home')
def home():
    if 'user_id' not in session: return redirect(url_for('index'))
    
    conn = get_db()
    active_beacons = conn.execute("SELECT * FROM beacons WHERE created_at >= datetime('now', '-2 hours') ORDER BY created_at DESC").fetchall()
    next_sat = get_next_two_saturdays()[0]
    past_sat = get_past_saturdays(1)[0]
    
    radar_raw = conn.execute("SELECT users.username, users.avatar, users.steam_id, users.active_border, radar.status FROM radar JOIN users ON radar.user_id = users.id WHERE radar.target_date = ?", (next_sat,)).fetchall()
    radar_data = {'yes': [], 'no': [], 'maybe': []}
    user_status = None
    
    for r in radar_raw:
        if r['status'] not in radar_data:
            continue
        face = _player_face(r)
        radar_data[r['status']].append(face)
        if r['username'] == session.get('username'):
            user_status = r['status']
            
    me = conn.execute(
        "SELECT last_claim_date, claim_streak, season_xp, xp_today, xp_date, claimed_level_rewards, borders, owned_banners, steam_id FROM users WHERE id = ?",
        (session['user_id'],),
    ).fetchone()
    claim = daily_claim_status(me)
    season = season_track_payload(me)
    xp_today = me['xp_today'] or 0 if me else 0
    if me and (me['xp_date'] or '') != date.today().isoformat():
        xp_today = 0
    richest = []
    for r in conn.execute(
        "SELECT username, avatar, steam_id, active_border, COALESCE(ore_coins, 0) AS ore_coins FROM users ORDER BY COALESCE(ore_coins, 0) DESC, username COLLATE NOCASE ASC LIMIT 3"
    ).fetchall():
        face = _player_face(r)
        face['ore_coins'] = r['ore_coins'] or 0
        richest.append(face)
    conn.close()
    winner = get_winner_for_date(next_sat)
    last_winner = get_winner_for_date(past_sat)
    video_rel = hero_video_rel(winner)
    return render_template(
        'home.html',
        next_sat=next_sat,
        winner=winner,
        last_winner=last_winner,
        active_beacons=active_beacons,
        radar_data=radar_data,
        user_status=user_status,
        daily_claim=claim,
        season=season,
        xp_today=xp_today,
        daily_xp_cap=DAILY_XP_CAP,
        richest=richest,
        hero_video=url_for('static', filename=video_rel) if video_rel else '',
        hero_is_repo='repo' in _hero_slug(winner),
        needs_steam_link=not bool(me and (me['steam_id'] or '').strip()),
    )

@app.route('/set_radar', methods=['POST'])
def set_radar():
    if 'user_id' not in session: return redirect(url_for('index'))
    status = request.form.get('status')
    target_date = get_next_two_saturdays()[0]
    
    if status in ['yes', 'no', 'maybe']:
        conn = get_db()
        existing = conn.execute("SELECT id FROM radar WHERE user_id = ? AND target_date = ?", (session['user_id'], target_date)).fetchone()
        if existing:
            conn.execute("UPDATE radar SET status = ? WHERE id = ?", (status, existing['id']))
        else:
            conn.execute("INSERT INTO radar (user_id, target_date, status) VALUES (?, ?, ?)", (session['user_id'], target_date, status))
        conn.commit()
        conn.close()
    return redirect(url_for('home'))

@app.route('/login')
def login():
    return redirect(f"{DISCORD_AUTH_URL}?client_id={DISCORD_CLIENT_ID}&redirect_uri={DISCORD_REDIRECT_URI}&response_type=code&scope=identify")

@app.route('/callback')
def callback():
    code = request.args.get('code')
    if not code: 
        return redirect(url_for('index'))
        
    data = {'client_id': DISCORD_CLIENT_ID, 'client_secret': DISCORD_CLIENT_SECRET, 'grant_type': 'authorization_code', 'code': code, 'redirect_uri': DISCORD_REDIRECT_URI}
    try:
        token_res = requests.post(DISCORD_TOKEN_URL, data=data, headers={'Content-Type': 'application/x-www-form-urlencoded'}, timeout=DISCORD_HTTP_TIMEOUT).json()
        token = token_res.get('access_token')
        if not token:
            flash("Discord login failed. Please try again.", "error")
            return redirect(url_for('index'))
        user_data = requests.get(DISCORD_API_URL, headers={'Authorization': f'Bearer {token}'}, timeout=DISCORD_HTTP_TIMEOUT).json()
        if not user_data.get('id') or not user_data.get('username'):
            flash("Could not load your Discord profile. Please try again.", "error")
            return redirect(url_for('index'))
    except Exception:
        flash("Discord login failed. Please try again.", "error")
        return redirect(url_for('index'))

    avatar_url = f"https://cdn.discordapp.com/avatars/{user_data['id']}/{user_data['avatar']}.png" if user_data.get('avatar') else "https://cdn.discordapp.com/embed/avatars/0.png"
    discord_global_name = user_data.get('global_name') or user_data.get('username')
    discord_id = str(user_data['id'])
    discord_username = user_data['username']

    conn = get_db()
    user = None
    try:
        user = conn.execute("SELECT * FROM users WHERE discord_id = ?", (discord_id,)).fetchone()
    except sqlite3.OperationalError:
        user = None
    if not user:
        user = conn.execute(
            "SELECT * FROM users WHERE username = ? COLLATE NOCASE",
            (discord_username,),
        ).fetchone()
        if user and _row_discord_id(user) and _row_discord_id(user) != discord_id:
            user = None
    if not user:
        try:
            conn.execute(
                "INSERT INTO users (username, password, avatar, discord_name, discord_id) VALUES (?, ?, ?, ?, ?)",
                (discord_username, "discord_oauth", avatar_url, discord_global_name, discord_id),
            )
            conn.commit()
        except sqlite3.IntegrityError:
            conn.rollback()
            conn.execute(
                "UPDATE users SET avatar = ?, discord_name = ?, discord_id = ? WHERE username = ? COLLATE NOCASE AND (discord_id IS NULL OR discord_id = '')",
                (avatar_url, discord_global_name, discord_id, discord_username),
            )
            conn.commit()
        user = conn.execute("SELECT * FROM users WHERE discord_id = ?", (discord_id,)).fetchone()
        if not user:
            user = conn.execute(
                "SELECT * FROM users WHERE username = ? COLLATE NOCASE",
                (discord_username,),
            ).fetchone()
    else:
        try:
            conn.execute(
                "UPDATE users SET username = ?, avatar = ?, discord_name = ?, discord_id = ? WHERE id = ?",
                (discord_username, avatar_url, discord_global_name, discord_id, user['id']),
            )
            conn.commit()
        except sqlite3.IntegrityError:
            conn.rollback()
            conn.execute(
                "UPDATE users SET avatar = ?, discord_name = ?, discord_id = ? WHERE id = ?",
                (avatar_url, discord_global_name, discord_id, user['id']),
            )
            conn.commit()
        user = conn.execute("SELECT * FROM users WHERE id = ?", (user['id'],)).fetchone()
    if not user:
        conn.close()
        flash("Could not create your account. Please try again.", "error")
        return redirect(url_for('index'))

    session.clear()
    session.permanent = True
    session.update({
        'user_id': user['id'],
        'username': user['username'],
        'discord_id': discord_id,
        'theme': user['theme'] or 'pink',
        'steam_id': user['steam_id'] or '',
        'avatar': avatar_url,
        'discord_name': discord_global_name,
    })
    conn.close()
    return redirect(url_for('home'))

@app.route('/logout')
def logout():
    session.clear()
    return redirect(url_for('index'))

@app.route('/profile', methods=['POST'])
def profile():
    if 'user_id' not in session: return redirect(url_for('index'))
    theme = request.form.get('theme')
    steam_id = request.form.get('steam_id')
    discord_name = request.form.get('discord_name')
    custom_title = request.form.get('custom_title')
    
    active_border = request.form.get('active_border')
    active_banner = request.form.get('active_banner')
    
    b_conf = banner_config_from_mapping(request.form)
    
    conn = get_db()
    prev = conn.execute(
        "SELECT active_border, active_banner FROM users WHERE id = ?",
        (session['user_id'],),
    ).fetchone()
    if theme: conn.execute("UPDATE users SET theme = ? WHERE id = ?", (theme, session['user_id'])), session.update({'theme': theme})
    if steam_id is not None: conn.execute("UPDATE users SET steam_id = ? WHERE id = ?", (steam_id, session['user_id'])), session.update({'steam_id': steam_id})
    if discord_name is not None:
        conn.execute("UPDATE users SET discord_name = ? WHERE id = ?", (discord_name, session['user_id']))
        session['discord_name'] = discord_name
    if custom_title is not None: conn.execute("UPDATE users SET custom_title = ? WHERE id = ?", (custom_title, session['user_id']))
    
    if active_border is not None: conn.execute("UPDATE users SET active_border = ? WHERE id = ?", (active_border, session['user_id']))
    if active_banner is not None: conn.execute("UPDATE users SET active_banner = ? WHERE id = ?", (active_banner, session['user_id']))
    if any(k in request.form for k in ('bg_color', 'text_glow', 'u_bg1', 'g_bg1', 'active_banner')):
        conn.execute("UPDATE users SET banner_config = ? WHERE id = ?", (json.dumps(b_conf), session['user_id']))
    conn.commit()
    bump_looks_rev(conn)
    conn.commit()
    conn.close()
    final_border = active_border if active_border is not None else ((prev['active_border'] or '') if prev else '')
    final_banner = active_banner if active_banner is not None else ((prev['active_banner'] or 'default') if prev else 'default')
    try:
        emit_profile_update(
            session.get('username'),
            session.get('steam_id') or '',
            final_border,
            final_banner,
            b_conf if any(k in request.form for k in ('bg_color', 'text_glow', 'u_bg1', 'g_bg1', 'active_banner')) else None,
            custom_title if custom_title is not None else None,
        )
    except Exception:
        pass
    border_changed = active_border is not None and prev and (prev['active_border'] or '') != (active_border or '') and active_border
    banner_changed = active_banner is not None and prev and (prev['active_banner'] or 'default') != (active_banner or 'default') and active_banner and active_banner != 'default'
    try:
        if border_changed:
            emit_shop_live(session.get('username'), active_border, live_item_label(active_border), 'equip')
        if banner_changed:
            emit_shop_live(session.get('username'), active_banner, live_item_label(active_banner), 'equip')
    except Exception:
        pass
    return redirect(request.referrer or url_for('home'))

@app.route('/api/profile', methods=['POST', 'PATCH'])
def api_profile():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.get_json(silent=True)
    if not isinstance(data, dict):
        data = request.form.to_dict() if request.form else {}
    if not data:
        return jsonify({'error': 'Empty payload'}), 400

    conn = get_db()
    resolved = ensure_session_user(conn)
    user = None
    if resolved:
        user = conn.execute(
            "SELECT username, steam_id, avatar, owns_title, custom_title, borders, owned_banners, active_border, active_banner, banner_config FROM users WHERE id = ?",
            (resolved['id'],),
        ).fetchone()
    if not user:
        conn.close()
        return jsonify({'error': 'User not found'}), 404

    owned_borders = set(_csv_list(user['borders']))
    owned_banners = set(_csv_list(user['owned_banners']))
    prev_border = user['active_border'] or ''
    prev_banner = user['active_banner'] or 'default'
    updates = []
    params = []
    active_border = None
    active_banner = None

    if 'active_border' in data:
        active_border = (data.get('active_border') or '').strip()
        if active_border and active_border not in owned_borders:
            conn.close()
            return jsonify({'error': 'Border not owned'}), 400
        updates.append('active_border = ?')
        params.append(active_border)

    if 'active_banner' in data:
        active_banner = (data.get('active_banner') or 'default').strip() or 'default'
        if active_banner != 'default' and active_banner not in owned_banners:
            conn.close()
            return jsonify({'error': 'Banner not owned'}), 400
        updates.append('active_banner = ?')
        params.append(active_banner)

    if 'steam_id' in data:
        steam_id = str(data.get('steam_id') or '').strip()[:32]
        updates.append('steam_id = ?')
        params.append(steam_id)
        session['steam_id'] = steam_id

    if 'discord_name' in data:
        discord_name = str(data.get('discord_name') or '').strip()[:64]
        updates.append('discord_name = ?')
        params.append(discord_name)
        session['discord_name'] = discord_name

    if 'custom_title' in data and user['owns_title']:
        updates.append('custom_title = ?')
        params.append(str(data.get('custom_title') or '').strip()[:48])

    banner_src = data.get('banner_config') if isinstance(data.get('banner_config'), dict) else data
    has_banner_colors = any(k in data for k in BANNER_CONFIG_DEFAULTS) or isinstance(data.get('banner_config'), dict)
    if has_banner_colors:
        updates.append('banner_config = ?')
        params.append(json.dumps(banner_config_from_mapping(banner_src)))

    if not updates:
        conn.close()
        return jsonify({'success': True, 'unchanged': True})

    params.append(session['user_id'])
    conn.execute(f"UPDATE users SET {', '.join(updates)} WHERE id = ?", params)
    conn.commit()
    if (
        'active_border' in data
        or 'active_banner' in data
        or has_banner_colors
        or ('custom_title' in data and user['owns_title'])
    ):
        bump_looks_rev(conn)
        conn.commit()
    conn.close()

    final_border = active_border if active_border is not None else prev_border
    final_banner = active_banner if active_banner is not None else prev_banner
    final_config = banner_src if has_banner_colors else (user['banner_config'] or {})
    final_title = str(data.get('custom_title') or '').strip()[:48] if ('custom_title' in data and user['owns_title']) else (user['custom_title'] or '')
    final_steam = session.get('steam_id') or (user['steam_id'] or '')
    if isinstance(final_config, dict):
        cfg_out = json.dumps(final_config)
    else:
        cfg_out = final_config if isinstance(final_config, str) else '{}'
    try:
        if (
            'active_border' in data
            or 'active_banner' in data
            or has_banner_colors
            or ('custom_title' in data and user['owns_title'])
        ):
            emit_profile_update(
                session.get('username') or user['username'],
                final_steam,
                final_border,
                final_banner,
                final_config,
                final_title,
            )
        if active_border is not None and active_border and active_border != prev_border:
            emit_shop_live(session.get('username'), active_border, live_item_label(active_border), 'equip')
        if active_banner is not None and active_banner not in ('', 'default') and active_banner != prev_banner:
            emit_shop_live(session.get('username'), active_banner, live_item_label(active_banner), 'equip')
    except Exception:
        pass

    return jsonify({
        'success': True,
        'username': session.get('username') or user['username'],
        'steam_id': final_steam,
        'avatar': safe_avatar(user['avatar'] if 'avatar' in user.keys() else None),
        'owns_title': bool(user['owns_title']),
        'custom_title': final_title,
        'active_border': final_border,
        'active_banner': final_banner,
        'banner_config': cfg_out,
    })

@app.route('/api/looks')
def api_looks():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    conn = get_db()
    rev_row = conn.execute("SELECT value FROM config WHERE key = 'looks_rev'").fetchone()
    try:
        rev = int((rev_row['value'] if rev_row else '0') or 0)
    except (TypeError, ValueError):
        rev = 0
    since = request.args.get('rev', type=int)
    if since is not None and since == rev:
        conn.close()
        return jsonify({'rev': rev, 'unchanged': True})
    rows = conn.execute(
        "SELECT username, steam_id, avatar, active_border, active_banner, banner_config, custom_title, owns_title FROM users"
    ).fetchall()
    conn.close()
    looks = []
    for r in rows:
        looks.append({
            'username': r['username'],
            'steam_id': r['steam_id'] or '',
            'avatar': safe_avatar(r['avatar'] if 'avatar' in r.keys() else None),
            'active_border': r['active_border'] or '',
            'active_banner': r['active_banner'] or 'default',
            'banner_config': r['banner_config'] or '{}',
            'custom_title': (r['custom_title'] or '') if r['owns_title'] else '',
            'owns_title': bool(r['owns_title']),
        })
    return jsonify({'rev': rev, 'looks': looks})

@app.route('/api/me')
def api_me():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    return api_player(session.get('username') or '')

@app.route('/api/player/<username>')
def api_player(username):
    if 'user_id' not in session: return jsonify({'error': 'Unauthorized'}), 401
    lite = str(request.args.get('lite') or '').lower() in ('1', 'true', 'yes')
    want_steam = str(request.args.get('steam') or '').lower() in ('1', 'true', 'yes')
    conn = get_db()
    _PLAYER_COLS = "id, username, steam_id, avatar, discord_name, banner, ore_coins, discord_status, discord_activity, owns_title, custom_title, active_border, borders, active_banner, owned_banners, banner_config"
    user = None
    looking_at_self = (username or '').lower() == (session.get('username') or '').lower() or not (username or '').strip()
    if looking_at_self:
        resolved = ensure_session_user(conn)
        if resolved:
            user = conn.execute(f"SELECT {_PLAYER_COLS} FROM users WHERE id = ?", (resolved['id'],)).fetchone()
    if not user and username:
        user = conn.execute(f"SELECT {_PLAYER_COLS} FROM users WHERE username = ? COLLATE NOCASE", (username,)).fetchone()
    
    if not user:
        conn.close()
        return jsonify({'error': 'User not found'}), 404
        
    votes = conn.execute("SELECT COUNT(*) FROM votes WHERE user_id = ?", (user['id'],)).fetchone()[0]
    
    most_voted = conn.execute("SELECT game1, COUNT(game1) as count FROM votes WHERE user_id = ? AND game1 IS NOT NULL GROUP BY game1 ORDER BY count DESC LIMIT 1", (user['id'],)).fetchone()
    fav_game = most_voted['game1'] if most_voted else "None"
            
    display_coins = user['ore_coins'] or 0

    season_row = conn.execute("SELECT season_xp FROM users WHERE id = ?", (user['id'],)).fetchone()
    steam_id = user['steam_id']
    conn.close()

    season = season_progress_payload(season_row['season_xp'] if season_row else 0)
    steam_name = ''
    recent_games = []
    live_steam = want_steam
    if steam_id and (not lite or want_steam):
        steam_name = fetch_steam_name(steam_id, live=live_steam)
    if not lite and steam_id:
        recent_games = fetch_recent_steam_games(steam_id, limit=2, live=live_steam)
        for g in recent_games:
            g['hours_2w'] = hours_label(g.get('minutes_2w'))

    return jsonify({
        'username': user['username'],
        'steam_id': user['steam_id'],
        'avatar': safe_avatar(user['avatar']),
        'discord_name': user['discord_name'] or user['username'],
        'steam_name': steam_name,
        'votes': votes,
        'fav_game': fav_game,
        'ore_coins': display_coins,
        'discord_status': user['discord_status'] or 'offline',
        'discord_activity': user['discord_activity'] or '',
        'owns_title': bool(user['owns_title']),
        'custom_title': user['custom_title'] or '',
        'borders': user['borders'] or '',
        'active_border': user['active_border'] or '',
        'owned_banners': user['owned_banners'] or '',
        'active_banner': user['active_banner'] or 'default',
        'banner_config': user['banner_config'] or '{}',
        'banner': user['banner'] or '#1a1a1a',
        'season': season,
        'season_badge': f"S1 L{season['level']}",
        'recent_games': recent_games,
        'cosmetic_labels': COSMETIC_LABELS,
        'is_founder': is_founder(user['username']),
    })

@app.route('/events')
def events():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    saturdays, games_names = get_next_two_saturdays(), [g['name'] for g in get_all_games()]
    all_users = conn.execute("SELECT username, steam_id FROM users").fetchall()
    
    next_sat = saturdays[0]
    radar_raw = conn.execute("SELECT users.username, users.avatar, users.steam_id, users.active_border, radar.status FROM radar JOIN users ON radar.user_id = users.id WHERE radar.target_date = ?", (next_sat,)).fetchall()
    radar_data = {'yes': [], 'no': [], 'maybe': []}
    for r in radar_raw:
        if r['status'] in radar_data:
            radar_data[r['status']].append(_player_face(r))

    steam = refresh_steam_ownership(all_users)

    steam_stats = {}
    for game in get_all_games():
        try: appid_int = int(game['steam_appid'])
        except (TypeError, ValueError): appid_int = None
        if game['steam_appid'] == "non" or not appid_int:
            steam_stats[game['name']] = {"is_steam": False}
        else:
            missing_users = _steam_missing_users(all_users, steam, appid_int)
            steam_stats[game['name']] = {
                "missing_count": len(missing_users),
                "missing_users": missing_users,
                "total_users": len(all_users),
                "is_steam": True,
            }

    user_votes, saturday_stats = {}, {}
    mvp_row = conn.execute("SELECT owns_mvp FROM users WHERE id = ?", (session['user_id'],)).fetchone()
    mvp_stock = int(mvp_row['owns_mvp'] or 0) if mvp_row else 0
    for sat in saturdays:
        vote = conn.execute("SELECT game1, game2, game3, multiplier FROM votes WHERE user_id = ? AND target_date = ?", (session['user_id'], sat)).fetchone()
        user_votes[sat] = {
            'game1': vote['game1'],
            'game2': vote['game2'],
            'game3': vote['game3'],
            'multiplier': vote_multiplier(vote),
        } if vote else None
        scores = {g: 0 for g in games_names}
        for r in conn.execute("SELECT game1, game2, game3, multiplier FROM votes WHERE target_date = ?", (sat,)).fetchall():
            apply_vote_scores(scores, r)
        saturday_stats[sat] = dict(sorted(scores.items(), key=lambda i: i[1], reverse=True))
    conn.close()
    
    return render_template(
        'events.html',
        saturdays=saturdays,
        games=games_names,
        user_votes=user_votes,
        saturday_stats=saturday_stats,
        steam_stats=steam_stats,
        radar_data=radar_data,
        mvp_stock=mvp_stock,
    )

@app.route('/vote', methods=['POST'])
def vote():
    if 'user_id' not in session: return redirect(url_for('index'))
    
    target_date = request.form.get('target_date')
    game1 = request.form.get('game1') or None
    game2 = request.form.get('game2') or None
    game3 = request.form.get('game3') or None
    
    selected_games = [g for g in [game1, game2, game3] if g]
    if not selected_games:
        flash("Please pick at least one game.", "error")
        return redirect(url_for('events'))
    if len(selected_games) != len(set(selected_games)):
        flash("Each rank has to be a different game.", "error")
        return redirect(url_for('events'))
    if target_date not in get_next_two_saturdays():
        flash("Invalid voting date.", "error")
        return redirect(url_for('events'))
    
    conn = get_db()
    locked_row = conn.execute("SELECT value FROM config WHERE key = 'voting_locked'").fetchone()
    if locked_row and locked_row['value'] == 'true':
        conn.close()
        flash("Voting is currently locked.", "error")
        return redirect(url_for('events'))

    valid_games = {g['name'] for g in get_all_games()}
    if any(g not in valid_games for g in selected_games):
        conn.close()
        flash("One of the selected games is no longer available.", "error")
        return redirect(url_for('events'))

    existing = conn.execute("SELECT id, multiplier FROM votes WHERE user_id = ? AND target_date = ?", (session['user_id'], target_date)).fetchone()
    multiplier = vote_multiplier(existing)
    already_boosted = multiplier >= 2
    user_row = conn.execute("SELECT owns_mvp FROM users WHERE id = ?", (session['user_id'],)).fetchone()
    owns_mvp = int(user_row['owns_mvp'] or 0) if user_row else 0
    use_mvp = str(request.form.get('use_mvp') or '').strip().lower() in ('1', 'yes', 'on', 'true')
    consumed_mvp = False
    if use_mvp and owns_mvp > 0:
        multiplier = 2
        if not already_boosted:
            conn.execute(
                "UPDATE users SET owns_mvp = MAX(0, COALESCE(owns_mvp, 0) - 1) WHERE id = ?",
                (session['user_id'],),
            )
            consumed_mvp = True
    
    if existing:
        conn.execute("UPDATE votes SET game1 = ?, game2 = ?, game3 = ?, multiplier = ? WHERE user_id = ? AND target_date = ?", 
                     (game1, game2, game3, multiplier, session['user_id'], target_date))
    else:
        conn.execute("INSERT INTO votes (user_id, target_date, game1, game2, game3, multiplier) VALUES (?, ?, ?, ?, ?, ?)",
                     (session['user_id'], target_date, game1, game2, game3, multiplier))
        conn.execute("UPDATE users SET ore_coins = COALESCE(ore_coins, 0) + 10 WHERE id = ?", (session['user_id'],))
        grant_xp(conn, session['user_id'], 15)
    top_pick = game1 or selected_games[0]
    uname = _safe_name(session.get("username"))
    push_activity('vote', '⚔️', f'{uname} voted for {top_pick}.', conn=conn, i18n_key='live.voted', i18n_vars={'user': uname, 'game': top_pick})
        
    conn.commit()
    conn.close()
    if consumed_mvp:
        flash("Your votes have been saved — MVP Multiplier used for this week. 🚀", "success")
    else:
        flash("Your votes have been saved successfully! 🚀", "success")
    return redirect(url_for('events'))

@app.route('/oretimers')
def oretimers():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    users = conn.execute(
        "SELECT id, username, avatar, steam_id, active_border, active_banner, banner_config, banner FROM users"
    ).fetchall()
    vote_rows = conn.execute("SELECT user_id, COUNT(*) AS c FROM votes GROUP BY user_id").fetchall()
    vote_map = {r['user_id']: r['c'] for r in vote_rows}
    user_data = []
    for u in users:
        vote_count = vote_map.get(u['id'], 0)
        badges = []
        uname = (u['username'] or '').lower()
        if FOUNDER_USERNAME and uname == FOUNDER_USERNAME:
            badges.append({'icon': '👑', 'title': 'Founder & Admin'})
        elif DEVELOPER_USERNAME and uname == DEVELOPER_USERNAME:
            badges.append({'icon': '💻', 'title': 'Developer & Admin'})
        elif HOST_USERNAME and uname == HOST_USERNAME:
            badges.append({'icon': '🖥️', 'title': 'Server Host & Admin'})

        if u['steam_id']: badges.append({'icon': '🎮', 'title': 'Steam Connected'})
        if vote_count >= 5: badges.append({'icon': '🔥', 'title': 'Veteran Voter'})
        elif vote_count > 0: badges.append({'icon': '🗳️', 'title': 'Active Voter'})
        else: badges.append({'icon': '👻', 'title': 'Ghost (No Votes yet)'})
        face = _player_face(u)
        look = member_banner_look(
            u['active_banner'] if 'active_banner' in u.keys() else 'default',
            u['banner_config'] if 'banner_config' in u.keys() else '{}',
            u['banner'] if 'banner' in u.keys() else '#1a1a1a',
        )
        face.update({'badges': badges, 'vote_count': vote_count, 'banner_look': look})
        user_data.append(face)
    conn.close()
    return render_template('oretimers.html', users=user_data)

@app.route('/history')
def history():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    dates = conn.execute("SELECT DISTINCT target_date FROM votes WHERE target_date < date('now') ORDER BY target_date DESC").fetchall()
    
    all_votes = conn.execute("SELECT game1, game2, game3, multiplier FROM votes").fetchall()
    scores = {}
    for row in all_votes:
        mult = vote_multiplier(row)
        for g, points in [(row['game1'], 3), (row['game2'], 2), (row['game3'], 1)]:
            if g: scores[g] = scores.get(g, 0) + points * mult
    top_games = sorted(scores.items(), key=lambda x: x[1], reverse=True)[:3]
    
    mvp = conn.execute("SELECT users.username, users.avatar, users.steam_id, users.active_border, COUNT(votes.id) as vote_count FROM votes JOIN users ON votes.user_id = users.id GROUP BY users.id ORDER BY vote_count DESC LIMIT 1").fetchone()

    conn.close()
    return render_template('history.html', history_data=[{'date': r['target_date'], 'winner': get_winner_for_date(r['target_date'])} for r in dates], top_games=top_games, mvp=mvp)

@app.route('/inventory')
def inventory():
    if 'user_id' not in session:
        return redirect(url_for('index'))
    conn = get_db()
    user = conn.execute(
        "SELECT owns_title, owns_mvp, borders, owned_banners, active_border, active_banner FROM users WHERE id = ?",
        (session['user_id'],),
    ).fetchone()
    conn.close()
    items = owned_inventory_items(user)
    loot_groups = group_inventory_by_rarity(items)
    return render_template('inventory.html', items=items, loot_groups=loot_groups)

@app.route('/notifications')
def notifications_page():
    return redirect(url_for('home'))

@app.route('/api/roulette/spin', methods=['POST'])
def roulette_spin():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    games = [g['name'] for g in get_all_games()]
    if not games:
        return jsonify({'error': 'No games'}), 400
    pick = secrets.choice(games)
    uname = _safe_name(session.get("username"))
    push_activity(
        'roulette',
        '🎲',
        f'{uname} spun {pick} on Roulette.',
        i18n_key='live.spun',
        i18n_vars={'user': uname, 'game': pick},
    )
    return jsonify({'success': True, 'game': pick})

@app.route('/shop')
def shop():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    
    user = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()
    coins = user['ore_coins'] if user and user['ore_coins'] else 0
    conn.close()
    return render_template('shop.html', coins=coins)

def _shop_inventory_payload(conn, user_id, extra=None):
    row = conn.execute(
        "SELECT username, steam_id, avatar, ore_coins, owns_title, custom_title, borders, owned_banners, active_border, active_banner, banner_config FROM users WHERE id = ?",
        (user_id,),
    ).fetchone()
    payload = {
        'success': True,
        'new_balance': (row['ore_coins'] or 0) if row else 0,
        'username': row['username'] if row else '',
        'steam_id': (row['steam_id'] or '') if row else '',
        'avatar': safe_avatar(row['avatar'] if row else None),
        'owns_title': bool(row['owns_title']) if row else False,
        'custom_title': (row['custom_title'] or '') if row else '',
        'borders': _csv_list(row['borders'] if row else ''),
        'owned_banners': _csv_list(row['owned_banners'] if row else ''),
        'active_border': (row['active_border'] or '') if row else '',
        'active_banner': (row['active_banner'] or 'default') if row else 'default',
        'banner_config': (row['banner_config'] or '{}') if row else '{}',
    }
    kind = (extra or {}).get('kind')
    if kind in ('border', 'banner', 'title'):
        bump_looks_rev(conn)
        conn.commit()
    if extra:
        payload.update(extra)
    return payload

@app.route('/api/buy', methods=['POST'])
def buy_item():
    if 'user_id' not in session: return jsonify({'error': 'Unauthorized'}), 401
    data = request.get_json(silent=True) or {}
    item = data.get('item')
    
    conn = get_db()
    try:
        resolved = ensure_session_user(conn)
        user = None
        if resolved:
            user = conn.execute("SELECT ore_coins, owns_title, owns_mvp, borders, owned_banners, welkin_until FROM users WHERE id = ?", (resolved['id'],)).fetchone()
        if not user:
            return jsonify({'error': 'User not found'}), 404
        coins = user['ore_coins'] if user['ore_coins'] else 0
        
        owned_borders = [b for b in (user['borders'] or '').split(',') if b]
        owned_banners = [b for b in (user['owned_banners'] or '').split(',') if b]

        prices = SHOP_PRICES

        if item == 'welkin':
            if coins < WELKIN_COST:
                return jsonify({'error': 'Not enough OC'}), 400
            if not _debit_coins(conn, session['user_id'], WELKIN_COST):
                return jsonify({'error': 'Not enough OC'}), 400
            new_until = welkin_extend_until(user)
            _credit_coins(conn, session['user_id'], WELKIN_INSTANT_OC)
            conn.execute("UPDATE users SET welkin_until = ? WHERE id = ?", (new_until.isoformat(), session['user_id']))
            conn.commit()
            emit_shop_live(session.get('username'), 'welkin', live_item_label('welkin'), 'buy')
            days = (new_until - date.today()).days + 1
            return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                'item': 'welkin',
                'kind': 'welkin',
                'action': 'buy',
                'message': f'Welkin active · {days} days · +{WELKIN_INSTANT_OC} OC',
                'welkin_until': new_until.isoformat(),
                'welkin_days': days,
            }))

        if item not in prices:
            return jsonify({'error': 'Invalid item'}), 400

        cost = prices[item]

        if item == 'title':
            if user['owns_title']: return jsonify({'error': 'Already owned'}), 400
            if coins < cost: return jsonify({'error': 'Not enough OC'}), 400
            conn.execute("UPDATE users SET ore_coins = ore_coins - ?, owns_title = 1 WHERE id = ?", (cost, session['user_id']))
            conn.commit()
            emit_shop_live(session.get('username'), item, live_item_label(item), 'buy')
            return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                'item': item, 'kind': 'title', 'action': 'buy', 'message': 'Purchased!',
            }))

        elif item == 'mvp':
            if coins < cost: return jsonify({'error': 'Not enough OC'}), 400
            conn.execute(
                "UPDATE users SET ore_coins = ore_coins - ?, owns_mvp = COALESCE(owns_mvp, 0) + 1 WHERE id = ?",
                (cost, session['user_id']),
            )
            conn.commit()
            emit_shop_live(session.get('username'), item, live_item_label(item), 'buy')
            return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                'item': item, 'kind': 'mvp', 'action': 'buy', 'message': 'Purchased!',
            }))

        elif item in SHOP_BORDER_BUY:
            if item in owned_borders:
                conn.execute("UPDATE users SET active_border = ? WHERE id = ?", (item, session['user_id']))
                conn.commit()
                emit_shop_live(session.get('username'), item, live_item_label(item), 'equip')
                return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                    'item': item, 'kind': 'border', 'action': 'equip', 'message': 'Equipped!',
                }))
            if coins < cost: return jsonify({'error': 'Not enough OC'}), 400
            owned_borders.append(item)
            new_borders_string = ",".join(owned_borders)
            conn.execute("UPDATE users SET ore_coins = ore_coins - ?, borders = ?, active_border = ? WHERE id = ?", (cost, new_borders_string, item, session['user_id']))
            conn.commit()
            emit_shop_live(session.get('username'), item, live_item_label(item), 'buy')
            return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                'item': item, 'kind': 'border', 'action': 'buy', 'message': 'Purchased!',
            }))
                
        elif item in SHOP_BANNER_BUY:
            if item in owned_banners:
                conn.execute("UPDATE users SET active_banner = ? WHERE id = ?", (item, session['user_id']))
                conn.commit()
                emit_shop_live(session.get('username'), item, live_item_label(item), 'equip')
                return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                    'item': item, 'kind': 'banner', 'action': 'equip', 'message': 'Equipped!',
                }))
            if cost > 0 and coins < cost:
                return jsonify({'error': 'Not enough OC'}), 400
            owned_banners.append(item)
            new_banners_string = ",".join(owned_banners)
            conn.execute("UPDATE users SET ore_coins = COALESCE(ore_coins, 0) - ?, owned_banners = ?, active_banner = ? WHERE id = ?", (cost, new_banners_string, item, session['user_id']))
            conn.commit()
            emit_shop_live(session.get('username'), item, live_item_label(item), 'buy')
            return jsonify(_shop_inventory_payload(conn, session['user_id'], {
                'item': item, 'kind': 'banner', 'action': 'buy', 'message': 'Purchased!',
            }))

        return jsonify({'error': 'Invalid item'}), 400
    finally:
        conn.close()

def _flip_payload(conn, row, me_id):
    creator = conn.execute("SELECT id, username, avatar FROM users WHERE id = ?", (row['creator_id'],)).fetchone()
    joiner = None
    if row['joiner_id']:
        joiner = conn.execute("SELECT id, username, avatar FROM users WHERE id = ?", (row['joiner_id'],)).fetchone()
    winner_name = None
    if row['winner_id']:
        w = conn.execute("SELECT username FROM users WHERE id = ?", (row['winner_id'],)).fetchone()
        winner_name = w['username'] if w else None
    pot = row['stake'] * 2 if row['status'] == 'resolved' else row['stake'] * 2
    if row['status'] == 'open':
        pot = row['stake'] * 2
    return {
        'id': row['id'],
        'stake': row['stake'],
        'pot': row['stake'] * 2,
        'creator': _user_public(creator) if creator else None,
        'joiner': _user_public(joiner) if joiner else None,
        'creator_side': row['creator_side'],
        'joiner_side': 'tails' if row['creator_side'] == 'heads' else 'heads',
        'result_side': row['result_side'],
        'winner_id': row['winner_id'],
        'winner': winner_name,
        'rake': row['rake'] or 0,
        'payout': (row['stake'] * 2) - (row['rake'] or 0) if row['status'] == 'resolved' else 0,
        'status': row['status'],
        'created_at': row['created_at'],
        'is_mine': row['creator_id'] == me_id,
        'can_join': row['status'] == 'open' and row['creator_id'] != me_id,
        'can_cancel': row['status'] == 'open' and row['creator_id'] == me_id,
    }

@app.route('/api/casino/list')
def casino_list():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    conn = get_db()
    try:
        expire_stale_flips(conn)
        conn.commit()
        me = session['user_id']
        open_rows = conn.execute(
            "SELECT * FROM coinflips WHERE status = 'open' ORDER BY created_at DESC"
        ).fetchall()
        recent_rows = conn.execute(
            "SELECT * FROM coinflips WHERE status = 'resolved' ORDER BY resolved_at DESC, id DESC LIMIT 8"
        ).fetchall()
        ashes_row = conn.execute("SELECT value FROM config WHERE key = 'pit_ashes'").fetchone()
        my_open = conn.execute(
            "SELECT id FROM coinflips WHERE creator_id = ? AND status = 'open'", (me,)
        ).fetchone()
        return jsonify({
            'success': True,
            'open': [_flip_payload(conn, r, me) for r in open_rows],
            'recent': [_flip_payload(conn, r, me) for r in recent_rows],
            'stakes': list(CASINO_ALLOWED_STAKES),
            'pit_ashes': int(ashes_row['value']) if ashes_row and str(ashes_row['value']).isdigit() else 0,
            'my_open_id': my_open['id'] if my_open else None,
            'ttl_min': COINFLIP_TTL_MIN,
            'rake_pct': COINFLIP_RAKE_PCT,
        })
    finally:
        conn.close()

@app.route('/api/casino/create', methods=['POST'])
def casino_create():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        stake = int(data.get('stake'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid stake'}), 400
    side = (data.get('side') or '').strip().lower()
    if stake not in CASINO_ALLOWED_STAKES:
        return jsonify({'error': 'Stake not allowed'}), 400
    if side not in ('heads', 'tails'):
        return jsonify({'error': 'Pick heads or tails'}), 400

    conn = get_db()
    try:
        expire_stale_flips(conn)
        existing = conn.execute(
            "SELECT id FROM coinflips WHERE creator_id = ? AND status = 'open'",
            (session['user_id'],),
        ).fetchone()
        if existing:
            conn.commit()
            return jsonify({'error': 'You already have an open flip. Cancel it first.'}), 400
        if not _debit_coins(conn, session['user_id'], stake):
            conn.rollback()
            return jsonify({'error': 'Not enough OC'}), 400
        cur = conn.execute(
            "INSERT INTO coinflips (creator_id, stake, creator_side, status) VALUES (?, ?, ?, 'open')",
            (session['user_id'], stake, side),
        )
        grant_xp(conn, session['user_id'], 2)
        conn.commit()
        row = conn.execute("SELECT * FROM coinflips WHERE id = ?", (cur.lastrowid,)).fetchone()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        return jsonify({
            'success': True,
            'flip': _flip_payload(conn, row, session['user_id']),
            'new_balance': new_balance,
            'message': f'{stake} OC locked. Waiting for a rival...',
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Could not create flip'}), 500
    finally:
        conn.close()

@app.route('/api/casino/join', methods=['POST'])
def casino_join():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        flip_id = int(data.get('flip_id'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid flip'}), 400

    conn = get_db()
    try:
        expire_stale_flips(conn)
        row = conn.execute("SELECT * FROM coinflips WHERE id = ?", (flip_id,)).fetchone()
        if not row or row['status'] != 'open':
            conn.commit()
            return jsonify({'error': 'This flip is gone'}), 400
        if row['creator_id'] == session['user_id']:
            return jsonify({'error': "You can't join your own flip"}), 400
        stake = row['stake']
        if not _debit_coins(conn, session['user_id'], stake):
            conn.rollback()
            return jsonify({'error': 'Not enough OC'}), 400

        result_side = secrets.choice(['heads', 'tails'])
        winner_id = row['creator_id'] if result_side == row['creator_side'] else session['user_id']
        pot = stake * 2
        rake = max(1, (pot * COINFLIP_RAKE_PCT) // 100)
        payout = pot - rake
        locked = conn.execute(
            """UPDATE coinflips SET joiner_id = ?, result_side = ?, winner_id = ?, rake = ?,
               status = 'resolved', resolved_at = CURRENT_TIMESTAMP WHERE id = ? AND status = 'open'""",
            (session['user_id'], result_side, winner_id, rake, flip_id),
        )
        if locked.rowcount < 1:
            conn.rollback()
            return jsonify({'error': 'This flip is gone'}), 400
        _credit_coins(conn, winner_id, payout)
        _add_pit_ashes(conn, rake)
        grant_xp(conn, session['user_id'], 2)
        conn.commit()
        resolved = conn.execute("SELECT * FROM coinflips WHERE id = ?", (flip_id,)).fetchone()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        winner_name = conn.execute("SELECT username FROM users WHERE id = ?", (winner_id,)).fetchone()['username']
        i_won = winner_id == session['user_id']
        wname = _safe_name(winner_name)
        push_activity(
            'flip',
            '🎰',
            f'{wname} just won {payout} OC in the Flip Pit.',
            i18n_key='live.wonPit',
            i18n_vars={'user': wname, 'amount': payout},
        )
        return jsonify({
            'success': True,
            'flip': _flip_payload(conn, resolved, session['user_id']),
            'new_balance': new_balance,
            'result_side': result_side,
            'won': i_won,
            'message': f"{'You take' if i_won else winner_name + ' takes'} the pit. {payout} OC after {rake} ashes burned.",
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Flip failed'}), 500
    finally:
        conn.close()

@app.route('/api/casino/cancel', methods=['POST'])
def casino_cancel():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        flip_id = int(data.get('flip_id'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid flip'}), 400
    conn = get_db()
    try:
        expire_stale_flips(conn)
        row = conn.execute("SELECT * FROM coinflips WHERE id = ? AND creator_id = ? AND status = 'open'", (flip_id, session['user_id'])).fetchone()
        if not row:
            conn.commit()
            return jsonify({'error': 'Nothing to cancel'}), 400
        conn.execute("UPDATE coinflips SET status = 'expired' WHERE id = ?", (flip_id,))
        _credit_coins(conn, session['user_id'], row['stake'])
        conn.commit()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        return jsonify({'success': True, 'new_balance': new_balance, 'message': f'{row["stake"]} OC returned.'})
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Cancel failed'}), 500
    finally:
        conn.close()

def _roll_crate(user):
    owned_borders = _csv_list(user['borders'])
    owned_banners = _csv_list(user['owned_banners'])
    roll = secrets.SystemRandom().randrange(100)
    if roll < 1:
        rarity, kind, key = 'secret', 'banner', 'voidglitch'
    elif roll < 20:
        missing = [b for b in CRATE_RARE_BANNERS if b not in owned_banners]
        if missing:
            rarity, kind, key = 'rare', 'banner', secrets.choice(missing)
        else:
            return {'rarity': 'rare', 'kind': 'coins', 'key': None, 'amount': CRATE_DUP_OC, 'duplicate': True, 'label': f'{CRATE_DUP_OC} OC (duplicate banner)'}
    elif roll < 45:
        missing = [b for b in CRATE_UNCOMMON_BORDERS if b not in owned_borders]
        if missing:
            rarity, kind, key = 'uncommon', 'border', secrets.choice(missing)
        else:
            return {'rarity': 'uncommon', 'kind': 'coins', 'key': None, 'amount': CRATE_DUP_OC, 'duplicate': True, 'label': f'{CRATE_DUP_OC} OC (duplicate border)'}
    else:
        return {'rarity': 'common', 'kind': 'coins', 'key': None, 'amount': CRATE_COMMON_OC, 'duplicate': False, 'label': f'{CRATE_COMMON_OC} OC refund'}

    if kind == 'banner' and key in owned_banners:
        return {'rarity': rarity, 'kind': 'coins', 'key': key, 'amount': CRATE_DUP_OC, 'duplicate': True, 'label': f'{CRATE_DUP_OC} OC (you already own {cosmetic_label(key)})'}
    if kind == 'border' and key in owned_borders:
        return {'rarity': rarity, 'kind': 'coins', 'key': key, 'amount': CRATE_DUP_OC, 'duplicate': True, 'label': f'{CRATE_DUP_OC} OC (you already own {cosmetic_label(key)})'}
    return {
        'rarity': rarity,
        'kind': kind,
        'key': key,
        'amount': 0,
        'duplicate': False,
        'label': cosmetic_label(key),
    }

@app.route('/api/crate/open', methods=['POST'])
def crate_open():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    conn = get_db()
    try:
        resolved = ensure_session_user(conn)
        user = None
        if resolved:
            user = conn.execute("SELECT ore_coins, borders, owned_banners FROM users WHERE id = ?", (resolved['id'],)).fetchone()
        if not user:
            return jsonify({'error': 'User not found'}), 404
        if not _debit_coins(conn, session['user_id'], CRATE_COST):
            conn.rollback()
            return jsonify({'error': 'Not enough OC'}), 400
        drop = _roll_crate(user)
        if drop['kind'] == 'coins':
            _credit_coins(conn, session['user_id'], drop['amount'])
        else:
            _grant_cosmetic(conn, session['user_id'], drop['kind'], drop['key'])
        conn.commit()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        if drop.get('key') and not drop.get('duplicate') and drop.get('kind') in ('banner', 'border'):
            emit_shop_live(session.get('username'), drop['key'], live_item_label(drop['key']), 'crate')
        return jsonify({
            'success': True,
            'drop': drop,
            'new_balance': new_balance,
            'cost': CRATE_COST,
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Crate jammed'}), 500
    finally:
        conn.close()

@app.route('/api/daily/status')
def daily_status():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    conn = get_db()
    user = conn.execute("SELECT last_claim_date, claim_streak, season_xp, xp_today, xp_date, ore_coins, welkin_until FROM users WHERE id = ?", (session['user_id'],)).fetchone()
    conn.close()
    payload = daily_claim_status(user)
    xp_today = user['xp_today'] or 0 if user else 0
    if user and (user['xp_date'] or '') != date.today().isoformat():
        xp_today = 0
    payload.update({
        'success': True,
        'season': season_progress_payload(user['season_xp'] if user else 0),
        'xp_today': xp_today,
        'daily_xp_cap': DAILY_XP_CAP,
        'balance': user['ore_coins'] if user else 0,
    })
    return jsonify(payload)

@app.route('/api/daily/claim', methods=['POST'])
def daily_claim():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    today = date.today()
    yesterday = (today - timedelta(days=1)).isoformat()
    conn = get_db()
    try:
        resolved = ensure_session_user(conn)
        user = None
        if resolved:
            user = conn.execute("SELECT last_claim_date, claim_streak, welkin_until FROM users WHERE id = ?", (resolved['id'],)).fetchone()
        if not user:
            return jsonify({'error': 'User not found'}), 404
        last = user['last_claim_date'] or ''
        if last == today.isoformat():
            return jsonify({'error': 'Already claimed today. Come back tomorrow.'}), 400
        streak = user['claim_streak'] or 0
        if last == yesterday:
            streak = 1 if streak >= 7 else streak + 1
        else:
            streak = 1
        bonus = 20 if streak == 7 else 0
        moon = WELKIN_DAILY_OC if welkin_active(user, today) else 0
        payout = 2 + bonus + moon
        _credit_coins(conn, session['user_id'], payout)
        conn.execute(
            "UPDATE users SET last_claim_date = ?, claim_streak = ? WHERE id = ?",
            (today.isoformat(), streak, session['user_id']),
        )
        xp_info = grant_xp(conn, session['user_id'], 5)
        conn.commit()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        season_xp = conn.execute("SELECT season_xp FROM users WHERE id = ?", (session['user_id'],)).fetchone()['season_xp']
        msg = f'+{payout} OC'
        if moon:
            msg += f' · Welkin +{moon}'
        if bonus:
            msg += f' — {streak}-day Protocol bonus!'
        else:
            msg += f' · streak {streak}/7'
        return jsonify({
            'success': True,
            'payout': payout,
            'bonus': bonus,
            'welkin_bonus': moon,
            'streak': streak,
            'new_balance': new_balance,
            'season': season_progress_payload(season_xp),
            'unlocked': [],
            'claimable': xp_info.get('claimable') or [],
            'message': msg,
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Claim failed'}), 500
    finally:
        conn.close()

@app.route('/api/armory/like', methods=['POST'])
def armory_like():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        owner_id = int(data.get('owner_id'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid setup'}), 400
    if owner_id == session['user_id']:
        return jsonify({'error': 'You already know your rig slaps.'}), 400
    conn = get_db()
    try:
        owner = conn.execute("SELECT id, username FROM users WHERE id = ?", (owner_id,)).fetchone()
        if not owner:
            return jsonify({'error': 'User not found'}), 404
        existing = conn.execute(
            "SELECT liker_id FROM armory_likes WHERE liker_id = ? AND owner_id = ?",
            (session['user_id'], owner_id),
        ).fetchone()
        if existing:
            return jsonify({'error': 'You already stamped this setup.'}), 400
        conn.execute("INSERT INTO armory_likes (liker_id, owner_id) VALUES (?, ?)", (session['user_id'], owner_id))
        _credit_coins(conn, owner_id, 1)
        liker = conn.execute("SELECT username FROM users WHERE id = ?", (session['user_id'],)).fetchone()
        liker_name = _safe_name(liker['username'] if liker else session.get('username'))
        owner_name = _safe_name(owner['username'])
        push_notification(
            owner_id,
            'armory',
            'Someone liked your setup',
            f'{liker_name} stamped Nice Setup.',
            '/armory',
            conn=conn,
            i18n_key='notify.likedSetup',
            i18n_vars={'user': liker_name},
            body_key='notify.stampedNice',
        )
        push_activity(
            'armory',
            '🖥️',
            f"{liker_name} liked {owner_name}'s setup.",
            conn=conn,
            i18n_key='live.likedSetup',
            i18n_vars={'user': liker_name, 'owner': owner_name},
        )
        conn.commit()
        count = conn.execute("SELECT COUNT(*) FROM armory_likes WHERE owner_id = ?", (owner_id,)).fetchone()[0]
        return jsonify({'success': True, 'likes': count, 'message': f'Nice Setup stamped. {owner["username"]} gets +1 OC.'})
    except sqlite3.IntegrityError:
        conn.rollback()
        return jsonify({'error': 'You already stamped this setup.'}), 400
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Like failed'}), 500
    finally:
        conn.close()

def _market_item_ok(item_type, item_key):
    if item_type == 'border':
        return item_key in TRADEABLE_BORDERS
    if item_type == 'banner':
        return item_key in TRADEABLE_BANNERS
    return False

@app.route('/api/market/list')
def market_list():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    conn = get_db()
    try:
        listings = conn.execute(
            """SELECT m.id, m.seller_id, m.item_type, m.item_key, m.price, m.created_at,
                      u.username, u.avatar
               FROM market_listings m JOIN users u ON u.id = m.seller_id
               ORDER BY m.created_at DESC"""
        ).fetchall()
        me = conn.execute("SELECT borders, owned_banners FROM users WHERE id = ?", (session['user_id'],)).fetchone()
        listed_keys = {(r['item_type'], r['item_key']) for r in listings if r['seller_id'] == session['user_id']}
        inventory = []
        for key in _csv_list(me['borders'] if me else ''):
            if key in TRADEABLE_BORDERS:
                inventory.append({'type': 'border', 'key': key, 'label': cosmetic_label(key), 'listed': ('border', key) in listed_keys})
        for key in _csv_list(me['owned_banners'] if me else ''):
            if key in TRADEABLE_BANNERS:
                inventory.append({'type': 'banner', 'key': key, 'label': cosmetic_label(key), 'listed': ('banner', key) in listed_keys})
        return jsonify({
            'success': True,
            'listings': [{
                'id': r['id'],
                'seller_id': r['seller_id'],
                'seller': r['username'],
                'avatar': safe_avatar(r['avatar']),
                'item_type': r['item_type'],
                'item_key': r['item_key'],
                'label': cosmetic_label(r['item_key']),
                'price': r['price'],
                'is_mine': r['seller_id'] == session['user_id'],
            } for r in listings],
            'inventory': inventory,
        })
    finally:
        conn.close()

@app.route('/api/market/sell', methods=['POST'])
def market_sell():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    item_type = (data.get('item_type') or '').strip()
    item_key = (data.get('item_key') or '').strip()
    try:
        price = int(data.get('price'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid price'}), 400
    if price < 1 or price > 9999:
        return jsonify({'error': 'Price must be 1–9999 OC'}), 400
    if not _market_item_ok(item_type, item_key):
        return jsonify({'error': 'That item cannot be listed'}), 400
    conn = get_db()
    try:
        user = conn.execute("SELECT borders, owned_banners FROM users WHERE id = ?", (session['user_id'],)).fetchone()
        if not user or not _owns_cosmetic(user, item_type, item_key):
            return jsonify({'error': "You don't own that"}), 400
        dup = conn.execute(
            "SELECT id FROM market_listings WHERE seller_id = ? AND item_type = ? AND item_key = ?",
            (session['user_id'], item_type, item_key),
        ).fetchone()
        if dup:
            return jsonify({'error': 'Already listed'}), 400
        conn.execute(
            "INSERT INTO market_listings (seller_id, item_type, item_key, price) VALUES (?, ?, ?, ?)",
            (session['user_id'], item_type, item_key, price),
        )
        conn.commit()
        return jsonify({'success': True, 'message': f'{cosmetic_label(item_key)} listed for {price} OC.'})
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Listing failed'}), 500
    finally:
        conn.close()

@app.route('/api/market/buy', methods=['POST'])
def market_buy():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        listing_id = int(data.get('listing_id'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid listing'}), 400
    conn = get_db()
    try:
        listing = conn.execute("SELECT * FROM market_listings WHERE id = ?", (listing_id,)).fetchone()
        if not listing:
            return jsonify({'error': 'Listing gone'}), 400
        if listing['seller_id'] == session['user_id']:
            return jsonify({'error': "That's your own stall."}), 400
        seller = conn.execute("SELECT id, borders, owned_banners, active_border, active_banner FROM users WHERE id = ?", (listing['seller_id'],)).fetchone()
        if not seller or not _owns_cosmetic(seller, listing['item_type'], listing['item_key']):
            conn.execute("DELETE FROM market_listings WHERE id = ?", (listing_id,))
            conn.commit()
            return jsonify({'error': 'Seller no longer owns this'}), 400
        buyer = conn.execute("SELECT borders, owned_banners FROM users WHERE id = ?", (session['user_id'],)).fetchone()
        if buyer and _owns_cosmetic(buyer, listing['item_type'], listing['item_key']):
            return jsonify({'error': 'You already own this'}), 400
        if not _debit_coins(conn, session['user_id'], listing['price']):
            conn.rollback()
            return jsonify({'error': 'Not enough OC'}), 400
        if not _remove_cosmetic(conn, listing['seller_id'], listing['item_type'], listing['item_key']):
            conn.rollback()
            return jsonify({'error': 'Transfer failed'}), 400
        _grant_cosmetic(conn, session['user_id'], listing['item_type'], listing['item_key'])
        _credit_coins(conn, listing['seller_id'], listing['price'])
        conn.execute("DELETE FROM market_listings WHERE id = ?", (listing_id,))
        conn.execute(
            "DELETE FROM market_listings WHERE seller_id = ? AND item_type = ? AND item_key = ?",
            (listing['seller_id'], listing['item_type'], listing['item_key']),
        )
        conn.commit()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        emit_shop_live(session.get('username'), listing['item_key'], live_item_label(listing['item_key']), 'trade')
        return jsonify({
            'success': True,
            'new_balance': new_balance,
            'message': f'Bought {cosmetic_label(listing["item_key"])} for {listing["price"]} OC.',
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Trade failed'}), 500
    finally:
        conn.close()

@app.route('/api/market/cancel', methods=['POST'])
def market_cancel():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        listing_id = int(data.get('listing_id'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid listing'}), 400
    conn = get_db()
    try:
        listing = conn.execute("SELECT * FROM market_listings WHERE id = ? AND seller_id = ?", (listing_id, session['user_id'])).fetchone()
        if not listing:
            return jsonify({'error': 'Listing not found'}), 400
        conn.execute("DELETE FROM market_listings WHERE id = ?", (listing_id,))
        conn.commit()
        return jsonify({'success': True, 'message': 'Listing pulled.'})
    finally:
        conn.close()

@app.route('/api/discord_sync', methods=['POST'])
def discord_sync():
    data = request.get_json(silent=True) or {}
    discord_name = data.get('discord_name')
    status = data.get('status') 
    activity = data.get('activity') 
    
    if not discord_name: return jsonify({'error': 'No discord_name provided'}), 400
    
    conn = get_db()
    conn.execute("UPDATE users SET discord_status = ?, discord_activity = ? WHERE discord_name = ?", (status, activity, discord_name))
    conn.commit()
    conn.close()
    return jsonify({"success": True, "message": f"Updated {discord_name}"})

@app.route('/status')
def status():
    if 'user_id' not in session: return redirect(url_for('index'))
    snap = collect_live_status()
    return render_template('status.html', status_json=snap, **snap)

@app.route('/api/status')
def api_status():
    if 'user_id' not in session: return jsonify({'error': 'Unauthorized'}), 401
    return jsonify(collect_live_status())

@app.route('/watchout', methods=['GET', 'POST'])
def watchout():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    
    if request.method == 'POST':
        game = request.form.get('game')
        if game:
            username = session.get('username')
            existing_beacon = conn.execute(
                "SELECT id FROM beacons WHERE username = ? AND created_at >= datetime('now', '-2 hours')",
                (username,)
            ).fetchone()
            if existing_beacon:
                conn.execute(
                    "UPDATE beacons SET game = ?, created_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (game, existing_beacon['id'])
                )
            else:
                conn.execute("INSERT INTO beacons (username, game) VALUES (?, ?)", (username, game))
            grant_xp(conn, session['user_id'], 8)
            conn.commit()
            emit_watchout_live(username, game)
            push_notification(
                session['user_id'],
                'watchout',
                'Your WatchOut ping went through',
                f'Signal for {game} is out.',
                '/watchout',
                i18n_key='notify.watchoutOk',
                i18n_vars={'game': game},
                body_key='notify.signalOut',
            )
            uname = _safe_name(username)
            push_activity('watchout', '🚨', f'{uname} is looking for people for {game}.', i18n_key='live.looking', i18n_vars={'user': uname, 'game': game})
            
            if DISCORD_WEBHOOK_URL:
                try:
                    payload = {"content": f"🚨 **{username}** is looking for teammates for **{game}**!"}
                    requests.post(DISCORD_WEBHOOK_URL, json=payload, timeout=2)
                except Exception:
                    pass 
            
    active_beacons = conn.execute("SELECT * FROM beacons WHERE created_at >= datetime('now', '-2 hours') ORDER BY created_at DESC").fetchall()
    games = [row['name'] for row in conn.execute("SELECT name FROM games").fetchall()]
    conn.close()
    
    return render_template('watchout.html', active_beacons=active_beacons, games=games)

@app.route('/delete_watchout/<int:beacon_id>', methods=['POST'])
def delete_watchout(beacon_id):
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    conn.execute("DELETE FROM beacons WHERE id = ? AND username = ?", (beacon_id, session.get('username')))
    conn.commit()
    conn.close()
    return redirect(request.referrer or url_for('watchout'))

@app.route('/armory', methods=['GET', 'POST'])
def armory():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    conn.execute('''CREATE TABLE IF NOT EXISTS armory (
                    user_id TEXT PRIMARY KEY, username TEXT, 
                    cpu TEXT, gpu TEXT, mouse TEXT, sens TEXT)''')
    
    for col, spec in (('keyboard', 'TEXT'), ('photo', 'TEXT'), ('updated_at', 'TEXT')):
        try: conn.execute(f'ALTER TABLE armory ADD COLUMN {col} {spec}')
        except sqlite3.OperationalError: pass
    
    if request.method == 'POST':
        cpu = request.form.get('cpu', '').strip()
        gpu = request.form.get('gpu', '').strip()
        mouse = request.form.get('mouse', '').strip()
        keyboard = request.form.get('keyboard', '').strip()
        existing = conn.execute("SELECT photo FROM armory WHERE user_id = ?", (str(session['user_id']),)).fetchone()
        photo_name = existing['photo'] if existing else None
        new_photo, photo_err = save_armory_photo(request.files.get('setup_photo'))
        if photo_err:
            conn.close()
            flash(photo_err, 'error')
            return redirect(url_for('armory'))
        if new_photo:
            if photo_name and photo_name != new_photo:
                delete_armory_photo(photo_name)
            photo_name = new_photo
        today = date.today().isoformat()
        conn.execute('''INSERT INTO armory (user_id, username, cpu, gpu, mouse, keyboard, photo, updated_at) 
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                        ON CONFLICT(user_id) DO UPDATE SET
                            username=excluded.username,
                            cpu=excluded.cpu,
                            gpu=excluded.gpu,
                            mouse=excluded.mouse,
                            keyboard=excluded.keyboard,
                            photo=excluded.photo,
                            updated_at=excluded.updated_at''', 
                     (str(session['user_id']), session.get('username'), cpu, gpu, mouse, keyboard, photo_name, today))
        conn.commit()
        
    my_setup = conn.execute("SELECT * FROM armory WHERE user_id = ?", (str(session['user_id']),)).fetchone()
    setups = conn.execute("SELECT * FROM armory").fetchall()
    like_rows = conn.execute("SELECT owner_id, COUNT(*) AS c FROM armory_likes GROUP BY owner_id").fetchall()
    like_counts = {int(r['owner_id']): r['c'] for r in like_rows}
    liked_by_me = {int(r['owner_id']) for r in conn.execute(
        "SELECT owner_id FROM armory_likes WHERE liker_id = ?", (session['user_id'],)
    ).fetchall()}
    rating_rows = conn.execute(
        "SELECT owner_id, AVG(stars) AS avg_stars, COUNT(*) AS votes FROM armory_ratings GROUP BY owner_id"
    ).fetchall()
    rating_map = {int(r['owner_id']): {'avg': round(float(r['avg_stars'] or 0), 1), 'votes': r['votes']} for r in rating_rows}
    my_ratings = {int(r['owner_id']): r['stars'] for r in conn.execute(
        "SELECT owner_id, stars FROM armory_ratings WHERE rater_id = ?", (session['user_id'],)
    ).fetchall()}
    setup_cards = []
    gallery = []
    for s in setups:
        try:
            owner_id = int(s['user_id'])
        except (TypeError, ValueError):
            owner_id = None
        photo = s['photo'] if 'photo' in s.keys() else None
        card = {
            'owner_id': owner_id,
            'username': s['username'],
            'cpu': s['cpu'],
            'gpu': s['gpu'],
            'mouse': s['mouse'],
            'keyboard': s['keyboard'],
            'photo': photo,
            'likes': like_counts.get(owner_id, 0) if owner_id else 0,
            'liked': owner_id in liked_by_me if owner_id else False,
            'is_mine': owner_id == session['user_id'] if owner_id else s['username'] == session.get('username'),
            'avg_stars': rating_map.get(owner_id, {}).get('avg', 0) if owner_id else 0,
            'rating_votes': rating_map.get(owner_id, {}).get('votes', 0) if owner_id else 0,
            'my_stars': my_ratings.get(owner_id, 0) if owner_id else 0,
        }
        setup_cards.append(card)
        if photo:
            gallery.append(card)
    conn.close()
    return render_template('armory.html', setups=setup_cards, my_setup=my_setup, gallery=gallery)

@app.route('/roulette')
def roulette():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    games = [row['name'] for row in conn.execute("SELECT name FROM games").fetchall()]
    conn.close()
    return render_template('roulette.html', games=games)

def _row_get(row, key, default=''):
    try:
        if key in row.keys() and row[key] not in (None, ''):
            return row[key]
    except Exception:
        pass
    return default


def normalize_wishlist_kind(kind, default='game'):
    k = (kind or '').strip().lower()
    if not k:
        return default
    k = ' '.join(k.replace('_', ' ').replace('-', ' ').split())
    if k in WISHLIST_KIND_ALIASES:
        return WISHLIST_KIND_ALIASES[k]
    return 'other'


def wishlist_admin_bucket(kind):
    return normalize_wishlist_kind(kind, default='game')


def wishlist_kind_label(kind):
    return WISHLIST_KINDS.get(normalize_wishlist_kind(kind), WISHLIST_KINDS['other'])


def normalize_wishlist_kinds_in_db(conn):
    try:
        rows = conn.execute('SELECT id, kind FROM wishlist').fetchall()
    except sqlite3.OperationalError:
        return
    changed = False
    for r in rows:
        raw = _row_get(r, 'kind', 'game') or 'game'
        new = normalize_wishlist_kind(raw, default='game')
        if str(raw).strip() != new:
            conn.execute('UPDATE wishlist SET kind = ? WHERE id = ?', (new, r['id']))
            changed = True
    if changed:
        conn.commit()


def migrate_item_requests_into_wishlist(conn):
    try:
        rows = conn.execute('SELECT * FROM item_requests').fetchall()
    except sqlite3.OperationalError:
        return
    if not rows:
        return
    for r in rows:
        kind = normalize_wishlist_kind(_row_get(r, 'kind', 'other'), default='other')
        parts = []
        title = (_row_get(r, 'title') or '').strip()
        colors = (_row_get(r, 'color_notes') or '').strip()
        details = (_row_get(r, 'details') or '').strip()
        if title:
            parts.append(title)
        if colors:
            parts.append(colors)
        if details:
            parts.append(details)
        text = ' — '.join(parts)[:500] or 'Request'
        created = _row_get(r, 'created_at') or datetime.now().isoformat(timespec='seconds')
        conn.execute(
            'INSERT INTO wishlist (user_id, game_name, appid, kind, created_at) VALUES (?, ?, ?, ?, ?)',
            (r['user_id'], text, '', kind, created),
        )
        conn.execute('DELETE FROM item_requests WHERE id = ?', (r['id'],))
    conn.commit()


@app.route('/wishlist', methods=['GET', 'POST'])
def wishlist():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    migrate_item_requests_into_wishlist(conn)
    normalize_wishlist_kinds_in_db(conn)

    success = False
    if request.method == 'POST':
        kind = normalize_wishlist_kind(request.form.get('kind') or 'game', default='game')
        message = (request.form.get('message') or request.form.get('game_name') or '').strip()[:500]
        if message:
            conn.execute(
                "INSERT INTO wishlist (user_id, game_name, appid, kind, created_at) VALUES (?, ?, ?, ?, ?)",
                (session['user_id'], message, '', kind, datetime.now().isoformat(timespec='seconds')),
            )
            conn.commit()
            success = True
        else:
            flash('Write a short request first.', 'error')

    conn.close()
    return render_template('wishlist.html', success=success, wishlist_kinds=WISHLIST_KINDS)


@app.route('/requests', methods=['GET', 'POST'])
def item_requests():
    return redirect(url_for('wishlist'))

@app.route('/rivals')
def rivals():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    users = conn.execute(
        "SELECT id, username, avatar, steam_id FROM users WHERE steam_id IS NOT NULL AND TRIM(steam_id) != '' ORDER BY username COLLATE NOCASE"
    ).fetchall()
    conn.close()
    roster = [{'id': u['id'], 'username': u['username'], 'avatar': safe_avatar(u['avatar']), 'steam_id': u['steam_id']} for u in users]
    return render_template('rivals.html', steam_users=roster)

@app.route('/api/rivals/compare')
def rivals_compare():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    a_name = (request.args.get('a') or '').strip()
    b_name = (request.args.get('b') or '').strip()
    if not a_name or not b_name or a_name.lower() == b_name.lower():
        return jsonify({'error': 'Pick two different ORETIMERS'}), 400
    conn = get_db()
    def load(name):
        return conn.execute(
            "SELECT id, username, avatar, steam_id FROM users WHERE username = ? COLLATE NOCASE", (name,)
        ).fetchone()
    a = load(a_name)
    b = load(b_name)
    conn.close()
    if not a or not b:
        return jsonify({'error': 'User not found'}), 404
    if not a['steam_id'] or not b['steam_id']:
        return jsonify({'error': 'Both players need a Steam ID linked'}), 400
    a_sum = steam_play_summary(a['steam_id'])
    b_sum = steam_play_summary(b['steam_id'])
    a_games, b_games = a_sum['games'], b_sum['games']
    a_2w, b_2w = a_sum['total_2w'], b_sum['total_2w']
    winner = 'tie'
    roast = "Same hours. Same excuses. Rematch Saturday."
    if a_2w > b_2w:
        winner = 'a'
        roast = f"{a['username']} has been living in the mines. {b['username']} might still be in the menu."
    elif b_2w > a_2w:
        winner = 'b'
        roast = f"{b['username']} clocked more pain this week. {a['username']}, touch grass less — touch Steam more."
    def pack(user, games, total, forever):
        return {
            'username': user['username'],
            'avatar': safe_avatar(user['avatar']),
            'minutes_2w': total,
            'hours_label': hours_label(total),
            'hours_total': hours_label(forever),
            'top': [{**g, 'hours_2w': hours_label(g.get('minutes_2w')), 'hours_total': hours_label(g.get('minutes_total'))} for g in games[:2]],
        }
    return jsonify({
        'success': True,
        'a': pack(a, a_games, a_2w, a_sum['total_forever']),
        'b': pack(b, b_games, b_2w, b_sum['total_forever']),
        'winner': winner,
        'roast': roast,
    })

@app.route('/api/admin/analytics')
def admin_analytics():
    if not is_admin(session.get('username')):
        return jsonify({'error': 'Unauthorized'}), 403
    conn = get_db()
    try:
        weekday_names = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat']
        votes_map = {i: 0 for i in range(7)}
        for row in conn.execute("SELECT CAST(strftime('%w', target_date) AS INTEGER) AS dow, COUNT(*) AS c FROM votes GROUP BY dow"):
            if row['dow'] is not None:
                votes_map[int(row['dow'])] = row['c']
        oc_row = conn.execute("SELECT COALESCE(SUM(ore_coins), 0) AS total FROM users").fetchone()
        hour_map = {i: 0 for i in range(24)}
        for row in conn.execute("SELECT CAST(strftime('%H', created_at) AS INTEGER) AS h, COUNT(*) AS c FROM beacons GROUP BY h"):
            if row['h'] is not None:
                hour_map[int(row['h'])] = row['c']
        ashes_row = conn.execute("SELECT value FROM config WHERE key = 'pit_ashes'").fetchone()
        return jsonify({
            'success': True,
            'votes_weekday': {'labels': weekday_names, 'values': [votes_map[i] for i in range(7)]},
            'ore_coins_total': int(oc_row['total'] or 0),
            'beacons_hour': {'labels': [f'{h:02d}:00' for h in range(24)], 'values': [hour_map[h] for h in range(24)]},
            'pit_ashes': int(ashes_row['value']) if ashes_row and str(ashes_row['value']).isdigit() else 0,
        })
    finally:
        conn.close()

def _highlight_card(row, liked_ids, request_host):
    parent = (request_host or 'localhost').split(':')[0]
    platform = row['platform'] or 'other'
    embed_id = row['embed_id'] or ''
    embed_url = ''
    if platform == 'youtube' and re.fullmatch(r'[A-Za-z0-9_-]{6,}', embed_id):
        embed_url = f'https://www.youtube.com/embed/{embed_id}'
    elif platform == 'twitch_clip' and re.fullmatch(r'[A-Za-z0-9_-]+', embed_id):
        embed_url = f'https://clips.twitch.tv/embed?clip={embed_id}&parent={parent}'
    elif platform == 'twitch_vod' and embed_id.isdigit():
        embed_url = f'https://player.twitch.tv/?video={embed_id}&parent={parent}'
    return {
        'id': row['id'],
        'username': row['username'],
        'avatar': safe_avatar(row['avatar']),
        'url': row['url'],
        'title': row['title'] or 'Untitled clip',
        'platform': platform,
        'embed_url': embed_url,
        'likes': int(row['likes'] or 0),
        'liked': row['id'] in liked_ids,
        'created_at': row['created_at'],
    }

@app.route('/highlights', methods=['GET', 'POST'])
def highlights():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    if request.method == 'POST':
        parsed = parse_clip_url(request.form.get('url'))
        title = (request.form.get('title') or '').strip()[:80]
        if not parsed:
            conn.close()
            flash('Paste a Twitch, YouTube or Medal.tv link.', 'error')
            return redirect(url_for('highlights'))
        conn.execute(
            "INSERT INTO highlights (user_id, url, title, platform, embed_id) VALUES (?, ?, ?, ?, ?)",
            (session['user_id'], parsed['url'], title, parsed['platform'], parsed['embed_id']),
        )
        conn.commit()
        conn.close()
        flash('Clip dropped into the feed.', 'success')
        return redirect(url_for('highlights'))

    settle_clip_of_week(conn)
    conn.commit()
    liked_ids = {r['highlight_id'] for r in conn.execute(
        "SELECT highlight_id FROM highlight_likes WHERE user_id = ?", (session['user_id'],)
    ).fetchall()}
    rows = conn.execute(
        """SELECT h.id, h.user_id, h.url, h.title, h.platform, h.embed_id, h.created_at,
                  u.username, u.avatar, COUNT(l.user_id) AS likes
           FROM highlights h
           JOIN users u ON u.id = h.user_id
           LEFT JOIN highlight_likes l ON l.highlight_id = h.id
           GROUP BY h.id
           ORDER BY h.created_at DESC"""
    ).fetchall()
    host = request.host
    clips = [_highlight_card(r, liked_ids, host) for r in rows]
    live = week_clip_leader(conn)
    cotw = _highlight_card(live, liked_ids, host) if live and int(live['likes'] or 0) > 0 else None
    last_week = iso_week_id(date.today() - timedelta(days=7))
    last_award = conn.execute(
        """SELECT c.week_id, c.paid, c.highlight_id, u.username
           FROM clip_of_week c LEFT JOIN users u ON u.id = c.creator_id
           WHERE c.week_id = ?""",
        (last_week,),
    ).fetchone()
    conn.close()
    return render_template(
        'highlights.html',
        clips=clips,
        cotw=cotw,
        week_id=iso_week_id(),
        last_award=last_award,
        clip_reward=CLIP_OF_WEEK_OC,
    )

@app.route('/api/highlights/like', methods=['POST'])
def highlights_like():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        highlight_id = int(data.get('id'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid clip'}), 400
    conn = get_db()
    try:
        clip = conn.execute("SELECT id FROM highlights WHERE id = ?", (highlight_id,)).fetchone()
        if not clip:
            return jsonify({'error': 'Clip not found'}), 404
        existing = conn.execute(
            "SELECT user_id FROM highlight_likes WHERE user_id = ? AND highlight_id = ?",
            (session['user_id'], highlight_id),
        ).fetchone()
        if existing:
            return jsonify({'error': 'Already fired.'}), 400
        conn.execute(
            "INSERT INTO highlight_likes (user_id, highlight_id) VALUES (?, ?)",
            (session['user_id'], highlight_id),
        )
        conn.commit()
        likes = conn.execute(
            "SELECT COUNT(*) FROM highlight_likes WHERE highlight_id = ?", (highlight_id,)
        ).fetchone()[0]
        return jsonify({'success': True, 'likes': likes})
    except sqlite3.IntegrityError:
        conn.rollback()
        return jsonify({'error': 'Already fired.'}), 400
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Like failed'}), 500
    finally:
        conn.close()

@app.route('/quests', methods=['GET', 'POST'])
def quests():
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    if request.method == 'POST':
        progress = quest_progress(conn, session['user_id'], session.get('username'))
        if not progress['complete']:
            conn.close()
            flash('Finish all 3 weekly tasks first.', 'error')
            return redirect(url_for('quests'))
        if progress['claimed']:
            conn.close()
            flash('Bounty Crate already claimed this week.', 'error')
            return redirect(url_for('quests'))
        reward = random.randint(BOUNTY_CRATE_MIN, BOUNTY_CRATE_MAX)
        try:
            conn.execute(
                "INSERT INTO quest_claims (user_id, week_id, reward) VALUES (?, ?, ?)",
                (session['user_id'], progress['week_id'], reward),
            )
            _credit_coins(conn, session['user_id'], reward)
            conn.commit()
        except sqlite3.IntegrityError:
            conn.rollback()
            conn.close()
            flash('Bounty Crate already claimed this week.', 'error')
            return redirect(url_for('quests'))
        conn.close()
        flash(f'Bounty Crate cracked: +{reward} OC', 'success')
        return redirect(url_for('quests'))
    progress = quest_progress(conn, session['user_id'], session.get('username'))
    conn.close()
    return render_template(
        'quests.html',
        progress=progress,
        bounty_min=BOUNTY_CRATE_MIN,
        bounty_max=BOUNTY_CRATE_MAX,
    )

def _library_game_pack(game, all_users, steam):
    owned = _steam_owned_index(steam)
    playtimes_ci = {(k or '').strip().lower(): v for k, v in (steam.get('playtimes') or {}).items()}
    no_steam = _steam_nosteam_index(steam)
    try:
        appid_int = int(game['steam_appid'])
    except (TypeError, ValueError):
        appid_int = None
    no_steam_names = []
    pack = {
        'id': game['id'],
        'name': game['name'],
        'appid': game['steam_appid'],
        'is_steam': bool(appid_int) and game['steam_appid'] != 'non',
        'owners': [],
        'missing': [],
        'no_steam': no_steam_names,
    }
    if not pack['is_steam']:
        return pack
    for u in all_users:
        name, steam_id = _steam_user_fields(u)
        if not name:
            continue
        key = name.strip().lower()
        if not steam_id or key in no_steam:
            no_steam_names.append(name)
            continue
        if appid_int in owned.get(key, set()):
            mins = (playtimes_ci.get(key) or {}).get(appid_int, 0)
            pack['owners'].append({'username': name, 'hours': hours_label(mins), 'minutes': mins})
        else:
            pack['missing'].append(name)
    pack['owners'].sort(key=lambda o: o['minutes'], reverse=True)
    pack['missing'].sort(key=str.lower)
    return pack

@app.route('/library')
@app.route('/library/game/<int:game_id>')
def game_library(game_id=None):
    if 'user_id' not in session: return redirect(url_for('index'))
    conn = get_db()
    games = conn.execute("SELECT id, name, steam_appid FROM games ORDER BY name").fetchall()
    all_users = conn.execute("SELECT username, steam_id FROM users").fetchall()
    conn.close()
    steam = refresh_steam_ownership(all_users)
    catalog = []
    selected = None
    for g in games:
        pack = {
            'id': g['id'],
            'name': g['name'],
            'appid': g['steam_appid'],
            'is_steam': g['steam_appid'] not in (None, '', 'non'),
        }
        catalog.append(pack)
        if game_id is not None and g['id'] == game_id:
            selected = _library_game_pack(g, all_users, steam)
    if game_id is not None and selected is None:
        flash('Game not in the library.', 'error')
        return redirect(url_for('game_library'))
    return render_template('library.html', catalog=catalog, selected=selected, roster_size=len(all_users))

@app.route('/api/armory/rate', methods=['POST'])
def armory_rate():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        owner_id = int(data.get('owner_id'))
        stars = int(data.get('stars'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid rating'}), 400
    if stars < 1 or stars > 5:
        return jsonify({'error': 'Rate 1–5 stars'}), 400
    if owner_id == session['user_id']:
        return jsonify({'error': 'You already live in this setup.'}), 400
    conn = get_db()
    try:
        owner = conn.execute("SELECT id FROM users WHERE id = ?", (owner_id,)).fetchone()
        if not owner:
            return jsonify({'error': 'User not found'}), 404
        existing = conn.execute(
            "SELECT stars FROM armory_ratings WHERE rater_id = ? AND owner_id = ?",
            (session['user_id'], owner_id),
        ).fetchone()
        if existing:
            return jsonify({'error': 'You already rated this setup.'}), 400
        conn.execute(
            "INSERT INTO armory_ratings (rater_id, owner_id, stars) VALUES (?, ?, ?)",
            (session['user_id'], owner_id, stars),
        )
        conn.commit()
        row = conn.execute(
            "SELECT AVG(stars) AS avg_stars, COUNT(*) AS votes FROM armory_ratings WHERE owner_id = ?",
            (owner_id,),
        ).fetchone()
        return jsonify({
            'success': True,
            'avg': round(float(row['avg_stars'] or 0), 1),
            'votes': row['votes'],
            'stars': stars,
        })
    except sqlite3.IntegrityError:
        conn.rollback()
        return jsonify({'error': 'You already rated this setup.'}), 400
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Rating failed'}), 500
    finally:
        conn.close()

@app.errorhandler(413)
def too_large(_e):
    flash('File too large (max 3 MB).', 'error')
    return redirect(request.referrer or url_for('armory'))

@app.route('/pass')
@app.route('/battlepass')
def battle_pass():
    if 'user_id' not in session:
        return redirect(url_for('index'))
    conn = get_db()
    resolved = ensure_session_user(conn)
    me = None
    if resolved:
        me = conn.execute(
            "SELECT season_xp, claimed_level_rewards, borders, owned_banners, xp_today, xp_date FROM users WHERE id = ?",
            (resolved['id'],),
        ).fetchone()
    conn.close()
    track = season_track_payload(me)
    xp_today = me['xp_today'] or 0 if me else 0
    if me and (me['xp_date'] or '') != date.today().isoformat():
        xp_today = 0
    return render_template(
        'pass.html',
        track=track,
        season=track,
        xp_today=xp_today,
        daily_xp_cap=DAILY_XP_CAP,
    )

@app.route('/endgame')
def endgame():
    if 'user_id' not in session:
        return redirect(url_for('index'))
    conn = get_db()
    resolved = ensure_session_user(conn)
    me = None
    if resolved:
        me = conn.execute(
            "SELECT username, avatar, ore_coins, season_xp, welkin_until, artifact_date, artifact_runs FROM users WHERE id = ?",
            (resolved['id'],),
        ).fetchone()
    board_rows = conn.execute(
        "SELECT username, avatar, season_xp FROM users ORDER BY COALESCE(season_xp, 0) DESC, username ASC LIMIT 12"
    ).fetchall()
    conn.close()
    season = season_progress_payload(me['season_xp'] if me else 0)
    chamber = endgame_chamber(season.get('level') or 0)
    board = []
    for row in board_rows:
        lv = season_level_from_xp(row['season_xp'] or 0)
        ch = endgame_chamber(lv)
        board.append({
            'username': row['username'],
            'avatar': safe_avatar(row['avatar'] if 'avatar' in row.keys() else None),
            'level': lv,
            'xp': row['season_xp'] or 0,
            'chamber': ch['label'],
        })
    until = welkin_until_date(me)
    return render_template(
        'endgame.html',
        coins=(me['ore_coins'] or 0) if me else 0,
        welkin_active=welkin_active(me),
        welkin_days=welkin_days_left(me),
        welkin_until=until.isoformat() if until else '',
        welkin_cost=WELKIN_COST,
        welkin_daily=WELKIN_DAILY_OC,
        welkin_instant=WELKIN_INSTANT_OC,
        farm_left=artifact_runs_left(me),
        farm_max=ARTIFACT_RUNS_PER_DAY,
        season=season,
        chamber=chamber,
        board=board,
    )

@app.route('/api/endgame/farm', methods=['POST'])
def api_endgame_farm():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    today = date.today()
    conn = get_db()
    try:
        resolved = ensure_session_user(conn)
        user = None
        if resolved:
            user = conn.execute(
                "SELECT artifact_date, artifact_runs FROM users WHERE id = ?",
                (resolved['id'],),
            ).fetchone()
        if not user:
            return jsonify({'error': 'User not found'}), 404
        used = artifact_runs_used(user, today)
        if used >= ARTIFACT_RUNS_PER_DAY:
            return jsonify({'error': 'Domain locked. Resin refills tomorrow.'}), 400
        drop = roll_artifact_drop()
        _credit_coins(conn, session['user_id'], drop['oc'])
        xp_info = grant_xp(conn, session['user_id'], drop['xp'])
        conn.execute(
            "UPDATE users SET artifact_date = ?, artifact_runs = ? WHERE id = ?",
            (today.isoformat(), used + 1, session['user_id']),
        )
        conn.commit()
        new_balance = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (session['user_id'],)).fetchone()['ore_coins']
        season_xp = conn.execute("SELECT season_xp FROM users WHERE id = ?", (session['user_id'],)).fetchone()['season_xp']
        left = ARTIFACT_RUNS_PER_DAY - (used + 1)
        return jsonify({
            'success': True,
            'drop': drop,
            'left': left,
            'max': ARTIFACT_RUNS_PER_DAY,
            'new_balance': new_balance,
            'season': season_progress_payload(season_xp),
            'claimable': xp_info.get('claimable') or [],
            'message': f"{drop['name']} · +{drop['oc']} OC",
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Farm failed'}), 500
    finally:
        conn.close()

@app.route('/api/pass/claim', methods=['POST'])
def api_pass_claim():
    if 'user_id' not in session:
        return jsonify({'error': 'Unauthorized'}), 401
    data = request.json or {}
    try:
        reward_level = int(data.get('level'))
    except (TypeError, ValueError):
        return jsonify({'error': 'Invalid level'}), 400
    conn = get_db()
    try:
        result = _claim_season_reward(conn, session['user_id'], reward_level)
        if not result.get('ok'):
            conn.rollback()
            return jsonify({'error': result.get('error') or 'Claim failed'}), result.get('status') or 400
        conn.commit()
        resolved = ensure_session_user(conn)
        uid = resolved['id'] if resolved else session['user_id']
        me = conn.execute(
            "SELECT season_xp, claimed_level_rewards, borders, owned_banners, ore_coins FROM users WHERE id = ?",
            (uid,),
        ).fetchone()
        track = season_track_payload(me)
        reward = result['reward']
        if reward.get('type') in ('border', 'banner', 'title'):
            emit_shop_live(session.get('username'), reward.get('item'), reward.get('label'), 'pass')
        return jsonify({
            'success': True,
            'reward': reward,
            'track': track,
            'new_balance': (me['ore_coins'] or 0) if me else 0,
            'message': f"Claimed {reward['label']}",
        })
    except Exception:
        conn.rollback()
        return jsonify({'error': 'Claim failed'}), 500
    finally:
        conn.close()

@app.route('/changelog')
def changelog():
    if 'user_id' not in session: return redirect(url_for('index'))
    return render_template('changelog.html')

@app.route('/admin')
def admin():
    if not is_admin(session.get('username')): return redirect(url_for('home'))
    conn = get_db()
    migrate_item_requests_into_wishlist(conn)
    normalize_wishlist_kinds_in_db(conn)

    users = conn.execute("SELECT username, steam_id FROM users").fetchall()
    games = conn.execute("SELECT * FROM games ORDER BY name").fetchall()
    rows = conn.execute(
        """SELECT w.id, w.user_id, w.game_name, w.kind, w.created_at, u.username
           FROM wishlist w
           LEFT JOIN users u ON u.id = w.user_id
           ORDER BY w.id DESC"""
    ).fetchall()
    conn.close()
    wishlist_requests = []
    for r in rows:
        kind = normalize_wishlist_kind(_row_get(r, 'kind', 'game'), default='game')
        created = _row_get(r, 'created_at') or ''
        if created and 'T' in created:
            created = created.replace('T', ' ')[:16]
        elif created:
            created = str(created)[:16]
        wishlist_requests.append({
            'id': r['id'],
            'user_id': r['user_id'],
            'username': r['username'] or f"User #{r['user_id']}",
            'message': r['game_name'] or '',
            'kind': kind,
            'kind_label': wishlist_kind_label(kind),
            'bucket': wishlist_admin_bucket(kind),
            'created_at': created,
        })
    return render_template(
        'admin.html',
        users=users,
        games=games,
        wishlist_requests=wishlist_requests,
    )

@app.route('/cron/session_ping', methods=['GET', 'POST'])
def cron_session_ping():
    key = (request.args.get('key') or request.headers.get('X-Cron-Key') or '').strip()
    allowed = False
    if CRON_SECRET and key and secrets.compare_digest(key, CRON_SECRET):
        allowed = True
    elif is_admin(session.get('username')):
        allowed = True
    if not allowed:
        return jsonify({'error': 'Unauthorized'}), 401
    force = str(request.args.get('force') or '').lower() in ('1', 'true', 'yes')
    ok, msg = try_send_session_ping(force=force, mark=not force)
    return jsonify({'ok': ok, 'message': msg})

@app.route('/admin/grant_oc', methods=['POST'])
def admin_grant_oc():
    if not is_founder(session.get('username')):
        return redirect(url_for('home'))
    username = (request.form.get('username') or '').strip()
    try:
        amount = int(request.form.get('amount') or 0)
    except (TypeError, ValueError):
        amount = 0
    if not username or amount < 1 or amount > 100000:
        flash('Enter a player and an amount between 1 and 100000 OC.', 'error')
        return redirect(url_for('admin'))
    conn = get_db()
    user = conn.execute(
        "SELECT id, username, ore_coins FROM users WHERE username = ? COLLATE NOCASE",
        (username,),
    ).fetchone()
    if not user:
        conn.close()
        flash('User not found.', 'error')
        return redirect(url_for('admin'))
    _credit_coins(conn, user['id'], amount)
    conn.commit()
    new_bal = conn.execute("SELECT ore_coins FROM users WHERE id = ?", (user['id'],)).fetchone()['ore_coins']
    conn.close()
    flash(f"Granted {amount} OC to {user['username']} (now {new_bal} OC).", 'success')
    return redirect(url_for('admin'))

@app.route('/admin/add_game', methods=['POST'])
def add_game():
    if not is_admin(session.get('username')): return redirect(url_for('home'))
    if request.form.get('game_name') and request.form.get('steam_appid'):
        conn = get_db()
        try: 
            conn.execute("INSERT INTO games (name, steam_appid) VALUES (?, ?)", (request.form.get('game_name'), request.form.get('steam_appid')))
            conn.commit()
        except sqlite3.IntegrityError:
            pass 
        conn.close()
    return redirect(url_for('admin'))

@app.route('/admin/delete_game/<int:game_id>', methods=['POST'])
def delete_game(game_id):
    if not is_admin(session.get('username')): return redirect(url_for('home'))
    conn = get_db()
    conn.execute("DELETE FROM games WHERE id = ?", (game_id,)), conn.commit(), conn.close()
    return redirect(url_for('admin'))

@app.route('/admin/delete_wishlist/<int:req_id>', methods=['POST'])
def delete_wishlist(req_id):
    if not is_admin(session.get('username')): return redirect(url_for('home'))
    conn = get_db()
    conn.execute("DELETE FROM wishlist WHERE id = ?", (req_id,))
    conn.commit()
    conn.close()
    return redirect(url_for('admin'))

@app.route('/admin/toggle_lock', methods=['POST'])
def toggle_lock():
    if not is_admin(session.get('username')): return redirect(url_for('home'))
    conn = get_db()
    row = conn.execute("SELECT value FROM config WHERE key = 'voting_locked'").fetchone()
    current = row['value'] if row else 'false'
    new_val = 'false' if current == 'true' else 'true'
    conn.execute("INSERT INTO config (key, value) VALUES ('voting_locked', ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value", (new_val,))
    conn.commit()
    conn.close()
    return redirect(url_for('admin'))

@app.route('/admin/clear_votes', methods=['POST'])
def clear_votes():
    if not is_admin(session.get('username')): return redirect(url_for('admin'))
    conn = get_db()
    conn.execute("DELETE FROM votes"), conn.commit(), conn.close()
    return redirect(url_for('admin'))

if __name__ == '__main__':
    port = int(os.environ.get("PORT", 5000))
    debug = os.environ.get("FLASK_DEBUG", "").lower() in ("1", "true", "yes")
    app.run(host="0.0.0.0", port=port, debug=debug)