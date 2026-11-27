# -*- coding: utf-8 -*-
from html import escape as html_escape, unescape as html_unescape
import telebot
import subprocess
import os
import zipfile
import json
import tempfile
import shutil
from telebot import types
import time
import itertools
import collections
from datetime import datetime, timedelta
import psutil
import sqlite3
import logging
import signal
import threading
import re
import sys
import atexit
import requests
import hashlib
import secrets
import stat as _dbf_stat
import hmac
import io
from urllib.parse import urlsplit, urljoin

# --- Extra imports added by the upgrade ---
from logging.handlers import RotatingFileHandler
from flask import Flask, jsonify
from threading import Thread


# --- Configuration (environment variables) ---------------------------------
def _env_int(name, default):
    raw = os.environ.get(name, '').strip()
    if not raw:
        return default
    try:
        return int(raw)
    except ValueError:
        sys.stderr.write(f"Config warning: {name} must be a whole number; using {default}.\n")
        return default


# Secret: the token is NEVER stored in the code. Set it in your host's environment.
BOT_TOKEN = os.environ.get('BOT_TOKEN', '9207005759:AAF49YIKK4-bqIVKI3YrUhkUww9Kv5seVMw').strip()
if not BOT_TOKEN:
    sys.stderr.write(
        "\nERROR: BOT_TOKEN is not set.\n"
        "Set the BOT_TOKEN environment variable to your bot token from BotFather and start again.\n"
        "Example (Linux/macOS):  export BOT_TOKEN='your-token-here'\n\n")
    sys.exit(1)

OWNER_ID = _env_int('OWNER_ID', 8597878282)
ADMIN_ID = _env_int('ADMIN_ID', 8439335625)
YOUR_USERNAME = os.environ.get('YOUR_USERNAME', 'U_BOTS_u').strip() or 'U_BOTS_u'
UPDATE_CHANNEL = os.environ.get('UPDATE_CHANNEL', 'U_BOT_CHANNEL').strip() or 'U_BOT_CHANNEL'
FREE_USER_LIMIT = _env_int('FREE_USER_LIMIT', 5)
SUBSCRIBED_USER_LIMIT = _env_int('SUBSCRIBED_USER_LIMIT', 10)
ADMIN_LIMIT = float('inf')
OWNER_LIMIT = float('inf')
MAX_UPLOAD_MB = _env_int('MAX_UPLOAD_MB', 20)
MAX_UNZIPPED_MB = _env_int('MAX_UNZIPPED_MB', 200)       # total size allowed after unzipping
MAX_ZIP_FILES = _env_int('MAX_ZIP_FILES', 2000)          # max number of entries in one zip
MAX_SCRIPT_LOG_MB = _env_int('MAX_SCRIPT_LOG_MB', 10)    # a script log above this is trimmed
INSTALL_TIMEOUT = _env_int('INSTALL_TIMEOUT', 300)       # seconds allowed for pip / npm install
LOG_LEVEL = os.environ.get('LOG_LEVEL', 'INFO').strip().upper()
HEALTH_PORT = _env_int('PORT', 8080)

# Folder setup
def _pick_data_dir():
    """Where ALL runtime data lives (database, users' bots, sandbox data, backups, lock file): BOT_DATA_DIR when it is
    set; else a Railway Volume when one is mounted and writable (RAILWAY_VOLUME_MOUNT_PATH); else the folder of this file."""
    chosen = os.environ.get('BOT_DATA_DIR', '').strip()
    if chosen:
        return os.path.abspath(chosen)
    volume = os.environ.get('RAILWAY_VOLUME_MOUNT_PATH', '').strip()
    if volume and os.path.isdir(volume) and os.access(volume, os.W_OK | os.X_OK):
        return os.path.abspath(volume)
    return os.path.dirname(os.path.abspath(__file__))


BASE_DIR = _pick_data_dir()
ON_RAILWAY = any(os.environ.get(_name) for _name in ('RAILWAY_ENVIRONMENT', 'RAILWAY_PROJECT_ID', 'RAILWAY_SERVICE_ID', 'RAILWAY_ENVIRONMENT_ID'))
HAS_RAILWAY_VOLUME = bool(os.environ.get('RAILWAY_VOLUME_MOUNT_PATH', '').strip()) and \
    os.path.abspath(os.environ.get('RAILWAY_VOLUME_MOUNT_PATH', '').strip()) == BASE_DIR
UPLOAD_BOTS_DIR = os.path.join(BASE_DIR, 'upload_bots')
IROTECH_DIR = os.path.join(BASE_DIR, 'inf')
LOG_DIR = os.path.join(IROTECH_DIR, 'logs')
DATABASE_PATH = os.path.join(IROTECH_DIR, 'bot_data.db')

# Create necessary directories
os.makedirs(UPLOAD_BOTS_DIR, exist_ok=True)
os.makedirs(IROTECH_DIR, exist_ok=True)
os.makedirs(LOG_DIR, exist_ok=True)

# The host's own temporary files (backup zips, uploads being unpacked) live inside the data folder, which no hosted script can
# reach. Only then may scripts get the shared /tmp and /dev/shm (see _sandbox_shared_dirs): a script that writes to a fixed
# /tmp path or uses multiprocessing works, and nothing of the host is ever in /tmp.
HOST_TMP_DIR = os.path.join(BASE_DIR, 'host_tmp')
HOST_TMP_PRIVATE = False
try:
    os.makedirs(HOST_TMP_DIR, exist_ok=True)
    os.chmod(HOST_TMP_DIR, 0o711)            # others may walk through to their own work folder inside, nobody can list it
    _stale = time.time() - 6 * 3600
    for _name in os.listdir(HOST_TMP_DIR):   # leftovers of an earlier run
        _full = os.path.join(HOST_TMP_DIR, _name)
        try:
            if os.lstat(_full).st_mtime < _stale:
                shutil.rmtree(_full) if os.path.isdir(_full) and not os.path.islink(_full) else os.unlink(_full)
        except OSError:
            pass
    tempfile.tempdir = HOST_TMP_DIR
    HOST_TMP_PRIVATE = True
except OSError as _exc:
    sys.stderr.write(f"Config warning: could not prepare the private temp folder ({_exc}); the host keeps using /tmp and scripts get no /tmp.\n")


# --- Logging setup (console + rotating file, tokens are masked) ------------
_TOKEN_PATTERN = re.compile(r'\d{6,}:[A-Za-z0-9_-]{30,}')


_SECRET_VALUES = set()     # exact secrets known at run time, masked wherever they would be logged
_KEY_PATTERN = re.compile(r'(?i)\bbearer\s+[A-Za-z0-9._\-]{12,}|\bsk-[A-Za-z0-9_\-]{12,}|\bAIza[A-Za-z0-9_\-]{20,}|\bgsk_[A-Za-z0-9]{16,}')


def redact_secrets(text):
    """Mask anything that looks like a bot token or a key (also the exact configured ones)."""
    text = _TOKEN_PATTERN.sub('<token hidden>', str(text))
    if BOT_TOKEN:
        text = text.replace(BOT_TOKEN, '<token hidden>')
    for secret in list(_SECRET_VALUES):
        if secret and len(secret) >= 8:
            text = text.replace(secret, '<key hidden>')
    return _KEY_PATTERN.sub('<key hidden>', text)


class _RedactingFormatter(logging.Formatter):
    def format(self, record):
        return redact_secrets(super().format(record))


def _setup_logging():
    root = logging.getLogger()
    if getattr(root, '_demon_configured', False):
        return
    root.setLevel(getattr(logging, LOG_LEVEL, logging.INFO))
    fmt = _RedactingFormatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    console = logging.StreamHandler()
    console.setFormatter(fmt)
    root.addHandler(console)
    try:
        file_handler = RotatingFileHandler(os.path.join(LOG_DIR, 'bot.log'), maxBytes=5 * 1024 * 1024,
                                           backupCount=5, encoding='utf-8')
        file_handler.setFormatter(fmt)
        root.addHandler(file_handler)
    except OSError as exc:
        sys.stderr.write(f"Could not open the log file ({exc}); logging to console only.\n")
    # Libraries that are chatty at INFO level.
    logging.getLogger('werkzeug').setLevel(logging.WARNING)
    logging.getLogger('urllib3').setLevel(logging.WARNING)
    root._demon_configured = True


_setup_logging()
logger = logging.getLogger('demon_hosting')

# --- Database lock (defined early so every function can use it) -------------
DB_LOCK = threading.RLock()

# --- Data structures ---
# Several threads touch these dicts (bot handlers, script runners, watchdog), so every
# structural change goes through STATE_LOCK.
STATE_LOCK = threading.RLock()
bot_scripts = {}
MAX_AUTO_RESTARTS = _env_int('MAX_AUTO_RESTARTS', 5)
WATCHDOG_INTERVAL = 8
LAUNCH_WAIT_SECONDS = 40  # how long a Start/Restart press waits for the script to come up before refreshing the panel
RESTART_BACKOFF = (2, 4, 8, 16, 30)
# After MAX_AUTO_RESTARTS quick tries the watchdog does not give up for good: it keeps trying every RESTART_SLOW_DELAY seconds,
# RESTART_SLOW_RETRIES more times (about 2 hours), so a short outage (Telegram, network) never ends a healthy bot for ever.
# Any run of 2 minutes or more resets both counters, so a bot that crashes once a day is never given up on.
RESTART_SLOW_DELAY = 600
RESTART_SLOW_RETRIES = 12
RESTART_START_WAIT = 90                  # seconds a restart gets to really come up (an automatic package install can take a while)
RESTART_STATE = {}
WATCHDOG_START_FAILED = {}               # script_key -> info of a restart that never came up; the watchdog loop plans the next try
WATCHDOG_STARTED = False
# Scheduled restart: OFF by default (0), so no hosted script is ever restarted unless the owner asks for it.
# SCHEDULED_RESTART_HOURS=24 (any number of hours) switches it on: every running script is then restarted on that schedule even if it
# never crashed (clears memory leaks). A single script can opt out with the button in its control panel (shown only when it is on).
SCHEDULED_RESTART_HOURS = max(0, _env_int('SCHEDULED_RESTART_HOURS', 0))
SCHEDULED_RESTART_RETRY_DELAYS = (15, 45, 120)   # a restart that did not come up is tried again after these many seconds
SCHEDULED_RESTART_CHECK_SECONDS = 60     # how often the loop looks for scripts that are due
SCHEDULED_RESTART_MAX_PER_CYCLE = 3      # scripts restarted per check, so a big host never restarts everything at once
SCHEDULED_RESTART_STARTED = False
SCHEDULED_RESTART_LAST = {}              # script_key -> time.time() of the last scheduled restart
SCHEDULED_RESTART_OPTOUT = set()         # script keys that never get a scheduled restart (saved in the database)
# Referral system: every REFERRALS_PER_REWARD new users who join through a person's link give that person
# REFERRAL_REWARD_DAYS days of subscription (premium file limit).
REFERRALS_PER_REWARD = max(1, _env_int('REFERRALS_PER_REWARD', 3))
REFERRAL_REWARD_DAYS = max(1, _env_int('REFERRAL_REWARD_DAYS', 7))
PENDING_REFERRALS = {}                   # new user id -> referrer id, kept until the user passes the channel check
BOT_USERNAME_CACHE = {'name': ''}
HOST_START_TIME = time.time()
BOT_VERSION = 'v22'                      # shown in the start-up log, /health and Bot Information: tells which code really runs
SHUTDOWN_EVENT = threading.Event()
HEALTH_STATE = {'last_poll_start': None, 'poll_restarts': 0, 'last_error': ''}
user_subscriptions = {}
user_files = {}
active_users = set()
admin_ids = {ADMIN_ID, OWNER_ID}
banned_users = set()
suspended_users = set()    # hosting suspended: the user keeps the bot and chat, but nothing of theirs may run
temp_bans = {}             # user id -> datetime when a temporary ban ends (the user is also in banned_users)
user_limits = {}  # Custom limits per user
bot_locked = False

# --- Admin user-management extras (temp ban, suspend, auto-suspend, file search) ---
TEMP_BAN_MAX_DAYS = 365                                              # longest temporary ban an admin can set
TEMP_BAN_CHECK_SECONDS = 60                                          # how often expired temporary bans are lifted
TEMP_BAN_STARTED = False
FILE_PREVIEW_LINES = 200                                             # lines of a file shown by Preview
FILE_PREVIEW_CHARS = 3400                                            # Telegram limit is 4096 per message, with room for the frame
SEARCH_MIN_CHARS = 3
SEARCH_MAX_CHARS = 100
SEARCH_MAX_HITS_PER_FILE = 3
SEARCH_MAX_HITS_TOTAL = 40
SEARCH_MAX_FILE_BYTES = 1024 * 1024                                  # only the first MB of a file is searched
SEARCH_MAX_SECONDS = 25                                              # a search never runs longer than this
BULK_MAX_IDS = 200

# --- Manual Modules Installation System ---
pending_modules = {}  # {user_id: {module_name: package_name}}
manual_install_requests = {}  # {admin_id: {user_id: {module_name: package_name}}}

# --- Mandatory Channels/Groups ---
mandatory_channels = {}  # {channel_id: {'username': 'channel_username', 'name': 'Channel Name', 'invite_link': '...'}}
pending_channel_add = {}  # admin_id -> validated private channel metadata awaiting invite link

# Store pending ZIP files (kept in memory; entries expire, see PENDING_ZIP_TTL)
pending_zip_files = {}  # {user_id: {file_name: file_content}}
pending_zip_times = {}  # {(user_id, file_name): time stored}
PENDING_ZIP_TTL = 6 * 3600
PENDING_ZIP_MAX_TOTAL = 10  # never keep more than this many archives waiting in memory


# Settings that only the hosting bot itself needs. A hosted script never gets them (it can still set its own
# variables of the same name with the Environment button, those are added after this cleaning).
HOST_ONLY_ENV = frozenset({
    'OWNER_ID', 'ADMIN_ID', 'YOUR_USERNAME', 'UPDATE_CHANNEL', 'BOT_DATA_DIR', 'LOG_LEVEL',
    'FREE_USER_LIMIT', 'SUBSCRIBED_USER_LIMIT', 'MAX_UPLOAD_MB', 'MAX_UNZIPPED_MB', 'MAX_ZIP_FILES',
    'MAX_AUTO_RESTARTS', 'SCHEDULED_RESTART_HOURS', 'REFERRALS_PER_REWARD', 'REFERRAL_REWARD_DAYS',
    'DATABASE_URL', 'AI_PROVIDER', 'AI_MODEL', 'AI_BASE_URL',
    'AUTO_RESUME_ON_BOOT', 'AUTO_RESUME_GAP_SECONDS',
    'AUTO_BACKUP_MINUTES', 'AUTO_BACKUP_MIN_GAP_MINUTES', 'AUTO_BACKUP_KEEP', 'AUTO_BACKUP_MAX_MB', 'AUTO_RESTORE_ON_BOOT',
    'SANDBOX_MODE', 'SANDBOX_MEMORY_MB', 'SANDBOX_CPU_SECONDS', 'SANDBOX_FILE_MB', 'SANDBOX_MAX_PROCS', 'SANDBOX_OPEN_FILES', 'SANDBOX_SHARED_TMP', 'SANDBOX_UID_BASE',
})


def child_env():
    """Environment given to hosted user scripts: same as ours but WITHOUT the hosting bot's secrets and settings."""
    env = dict(os.environ)
    for name in list(env):
        upper = name.upper()
        if upper in ('BOT_TOKEN', 'TOKEN', 'GH_TOKEN', 'GITHUB_TOKEN', 'AI_API_KEY', 'OPENAI_API_KEY') \
                or upper in HOST_ONLY_ENV \
                or upper.endswith(('_BOT_TOKEN', '_API_KEY', '_SECRET', '_SECRET_KEY', '_PASSWORD',
                                   '_TOKEN', '_ACCESS_KEY', '_PRIVATE_KEY')) \
                or upper.startswith(('DEMON_', 'HOST_SECRET')):
            env.pop(name, None)
    env.setdefault('PYTHONUNBUFFERED', '1')
    return env


# --- Sandbox (isolation of hosted scripts) -------------------------------------------
# SANDBOX_MODE (environment variable):
#   auto   (default) use the strongest isolation this server really allows (tested at startup, level is logged and
#          shown in the "script started" message); if nothing real is available, scripts still run with the basic
#          protections (own folder, own HOME/TMPDIR, clean environment, resource limits) and the message says "basic".
#   strict same tests, but NO script is started unless a real barrier works (level "full" or "partial");
#          on a server that only gets "basic" nothing runs. Use it when you would rather stop than run unprotected.
#   off    old behaviour (v8): no sandbox at all, scripts see everything the bot can see. Not recommended.
# Levels: full = own private filesystem view (bubblewrap) or own OS user + kernel file lock together;
#         partial = other users' files and the host folder / database are blocked by the kernel (file lock) or by
#         file permissions (separate OS user), but not every limit is as strong;
#         basic = folder + clean environment + limits only, NOT a real wall; off = nothing.
SANDBOX_MODE = os.environ.get('SANDBOX_MODE', 'auto').strip().lower() or 'auto'
if SANDBOX_MODE not in ('auto', 'strict', 'off'):
    sys.stderr.write(f"Config warning: SANDBOX_MODE must be auto, strict or off; using auto (got {SANDBOX_MODE[:20]!r}).\n")
    SANDBOX_MODE = 'auto'
SANDBOX_MEMORY_MB = _env_int('SANDBOX_MEMORY_MB', 0)             # memory (data segment) per script, 0 = no limit (default: the 1 GB cap broke threads, multiprocessing and big bots; Railway's own memory limit still applies)
SANDBOX_CPU_SECONDS = _env_int('SANDBOX_CPU_SECONDS', 0)         # CPU time per run, 0 = no limit (default: a busy bot that runs for days must not be killed by a CPU-time cap)
SANDBOX_FILE_MB = _env_int('SANDBOX_FILE_MB', 4096)              # biggest single file a script may write, 0 = no limit (a file over this size ends the script with SIGXFSZ)
SANDBOX_MAX_PROCS = _env_int('SANDBOX_MAX_PROCS', 4096)          # processes AND threads per user; only used with a separate OS user
SANDBOX_OPEN_FILES = _env_int('SANDBOX_OPEN_FILES', 65536)       # open files / sockets per script (the server's own hard limit still caps it)
SANDBOX_SHARED_TMP = os.environ.get('SANDBOX_SHARED_TMP', '1').strip().lower() not in ('0', 'off', 'false', 'no')   # scripts may use /tmp and /dev/shm
SANDBOX_UID_BASE = _env_int('SANDBOX_UID_BASE', 200000)          # first OS user id handed out (only when running as root)
SANDBOX_DATA_DIR = os.path.join(BASE_DIR, 'sandbox_data')        # per user: home, tmp, cache, pylibs (outside the uploaded files)
_SANDBOX_LOCK = threading.Lock()
_SANDBOX_DETECT_LOCK = threading.Lock()
_SANDBOX_STATE = {'ready': False, 'level': 'basic', 'landlock': False, 'bwrap': None, 'uid': False,
                  'launcher': True, 'detail': 'not checked yet'}

# Tiny program that runs INSIDE the new process, just before the user's script starts: it opens the kernel file lock
# (Landlock), drops to the separate OS user, sets the resource limits and no-new-privileges, blocks ptrace, closes every
# inherited file descriptor and then replaces itself with the script (same PID). If something it was asked to do fails it
# stops with an error instead of starting the script unprotected.
_SANDBOX_LAUNCHER = r'''import ctypes, json, os, platform, resource, struct, sys

def _fail(text):
    sys.stderr.write("sandbox: " + text + "\n")
    sys.stderr.flush()
    os._exit(126)

try:
    cfg = json.loads(sys.argv[1])
    cmd = sys.argv[2:]
except Exception:
    _fail("bad launcher arguments")
if not cmd:
    _fail("no command to run")
libc = ctypes.CDLL(None, use_errno=True)
libc.syscall.restype = ctypes.c_long

# Landlock access bits (kernel ABI 1 = bits 0-12, ABI 2 adds REFER, ABI 3 adds TRUNCATE)
EXEC, WRITE_FILE, READ_FILE, READ_DIR = 1, 2, 4, 8
FILE_RIGHTS = EXEC | WRITE_FILE | READ_FILE
RO_RIGHTS = EXEC | READ_FILE | READ_DIR
REFER, TRUNCATE = 1 << 13, 1 << 14

class _RuleAttr(ctypes.Structure):
    _pack_ = 1
    _fields_ = [("allowed_access", ctypes.c_uint64), ("parent_fd", ctypes.c_int32)]

def _landlock(ro_paths, rw_paths):
    abi = libc.syscall(444, None, 0, 1)
    if abi < 1:
        _fail("kernel file lock (Landlock) is not available")
    handled = (1 << 13) - 1
    if abi >= 2:
        handled |= REFER
    if abi >= 3:
        handled |= TRUNCATE
    attr = ctypes.c_uint64(handled)
    rs_fd = libc.syscall(444, ctypes.byref(attr), 8, 0)
    if rs_fd < 0:
        _fail("could not create the file lock")
    full_rw = handled
    for paths, rights in ((ro_paths, RO_RIGHTS), (rw_paths, full_rw)):
        for path in paths:
            try:
                fd = os.open(path, os.O_PATH | os.O_CLOEXEC)
            except OSError:
                continue
            try:
                allowed = rights
                if not os.path.isdir(path):
                    allowed &= FILE_RIGHTS | TRUNCATE
                rule = _RuleAttr(allowed & handled, fd)
                if libc.syscall(445, rs_fd, 1, ctypes.byref(rule), 0) != 0:
                    _fail("could not add a file lock rule")
            finally:
                os.close(fd)
    return rs_fd, abi

def _seccomp(deny_truncate):
    arch = platform.machine()
    if arch == "x86_64":
        audit, nrs, x32 = 0xC000003E, [101, 310, 311], True
        trunc = 76
    elif arch in ("aarch64", "arm64"):
        audit, nrs, x32 = 0xC00000B7, [117, 270, 271], False
        trunc = 45
    else:
        return False
    if deny_truncate:
        nrs.append(trunc)
    ins = [(0x20, 0, 0, 4), (0x15, 0, 0, audit), (0x20, 0, 0, 0)]
    if x32:
        ins.append((0x35, 0, 0, 0x40000000))
    for nr in nrs:
        ins.append((0x15, 0, 0, nr))
    ins.append((0x06, 0, 0, 0x7FFF0000))          # allow
    ins.append((0x06, 0, 0, 0x00050001))          # deny with EPERM
    allow_at, deny_at = len(ins) - 2, len(ins) - 1
    out = []
    for i, (code, jt, jf, k) in enumerate(ins):
        if i == 1:
            jf = allow_at - i - 1
        elif code in (0x15, 0x35) and i >= 3:
            jt = deny_at - i - 1
        out.append(struct.pack("HBBI", code, jt, jf, k))
    blob = b"".join(out)
    buf = ctypes.create_string_buffer(blob, len(blob))

    class _Prog(ctypes.Structure):
        _fields_ = [("len", ctypes.c_ushort), ("filter", ctypes.c_void_p)]
    prog = _Prog(len(ins), ctypes.addressof(buf))
    if libc.prctl(22, 2, ctypes.byref(prog), 0, 0) != 0:
        return False
    return True

rs_fd, abi = (None, 0)
if cfg.get("landlock"):
    rs_fd, abi = _landlock(cfg.get("ro", []), cfg.get("rw", []))

for name, value in (cfg.get("limits") or {}).items():
    try:
        which = getattr(resource, "RLIMIT_" + name)
        hard = resource.getrlimit(which)[1]
        value = int(value)
        if hard != resource.RLIM_INFINITY and hard < value:
            value = hard
        resource.setrlimit(which, (value, value))
    except (AttributeError, ValueError, OSError):
        pass

if cfg.get("uid") is not None:
    try:
        uid, gid = int(cfg["uid"]), int(cfg.get("gid", cfg["uid"]))
        os.setgroups([])
        os.setresgid(gid, gid, gid)
        os.setresuid(uid, uid, uid)
        if os.getuid() != uid or os.geteuid() != uid:
            raise OSError("uid did not change")
        os.umask(0o077)                              # files in the shared /tmp are not readable by other users
    except OSError:
        _fail("could not switch to the separate user")

if libc.prctl(38, 1, 0, 0, 0) != 0:                # no new privileges
    _fail("could not set no-new-privileges")
if rs_fd is not None and libc.syscall(446, rs_fd, 0) != 0:
    _fail("could not start the file lock")
if cfg.get("seccomp") and not _seccomp(abi < 3):
    if cfg.get("seccomp_required"):
        _fail("could not set the system call filter")
try:
    os.closerange(3, 1 << 20)                       # nothing from the host stays open
except OSError:
    pass
try:
    os.execvpe(cmd[0], cmd, os.environ)
except FileNotFoundError:
    sys.stderr.write("sandbox: command not found: %s\n" % cmd[0])
    os._exit(127)
except OSError as exc:
    sys.stderr.write("sandbox: could not start: %s\n" % exc)
    os._exit(126)'''


class SandboxUnavailable(RuntimeError):
    """SANDBOX_MODE=strict and no real isolation works on this server."""


def sandbox_level_text():
    """Plain-words isolation level for the 'script started' message."""
    level = _SANDBOX_STATE['level'] if SANDBOX_MODE != 'off' else 'off'
    return {'full': "full (own private space; other users' files and the host are not reachable)",
            'partial': "partial (other users' files and the host are blocked, but not every protection is full)",
            'basic': "basic (own folder, clean settings and limits only, NOT a real wall)",
            'off': "off (no sandbox)"}.get(level, level)


def _sandbox_id(user_folder):
    name = os.path.basename(os.path.normpath(user_folder))
    return name if name.isdigit() else re.sub(r'[^0-9A-Za-z_-]', '_', name) or 'user'


def _path_is_under(path, root):
    path, root = os.path.realpath(path), os.path.realpath(root)
    return path == root or path.startswith(root.rstrip(os.sep) + os.sep)


def _sandbox_banned_paths():
    """Host folders no script may see: the data folder (database, backups, every user) and the folder of the bot code."""
    return sorted({os.path.realpath(BASE_DIR), os.path.realpath(os.path.dirname(os.path.abspath(__file__)))})


def _roots_without(root, banned):
    """root minus the banned folders. The kernel file lock can only allow, never carve out, so when a banned folder is
    inside root (for example the bot lives in /usr/src/app and /usr is needed) its siblings are listed instead."""
    root = os.path.realpath(root)
    if any(_path_is_under(root, b) for b in banned):
        return []
    if not any(_path_is_under(b, root) for b in banned):
        return [root]
    out = []
    try:
        names = os.listdir(root)
    except OSError:
        return []
    for name in names:
        out.extend(_roots_without(os.path.join(root, name), banned))
    return out


def _sandbox_read_roots():
    """Read-only (and runnable) places a script needs: the Python and Node runtimes, system libraries, a few /etc files."""
    banned = _sandbox_banned_paths()
    runtime = set()
    for exe in (sys.executable, shutil.which('node'), shutil.which('npm')):
        if not exe:
            continue
        real = os.path.realpath(exe)
        folder = os.path.dirname(real)
        runtime.add(os.path.dirname(folder) if os.path.basename(folder) == 'bin' else folder)
    for prefix in {sys.prefix, sys.base_prefix, sys.exec_prefix}:
        runtime.add(os.path.realpath(prefix))
    # The runtime folders themselves are allowed even if they sit inside the bot folder (a virtualenv in /app);
    # a runtime folder that IS or CONTAINS the bot folder is cut down like the system folders below.
    roots = []
    for item in sorted(runtime):
        if any(_path_is_under(b, item) for b in banned):
            roots.extend(_roots_without(item, banned))
        else:
            roots.append(item)
    for item in ('/usr', '/lib', '/lib32', '/lib64', '/bin', '/sbin', '/nix'):
        if os.path.exists(item):
            roots.extend(_roots_without(item, banned))
    for name in ('resolv.conf', 'hosts', 'nsswitch.conf', 'host.conf', 'gai.conf', 'passwd', 'group', 'localtime',
                 'timezone', 'ld.so.cache', 'ld.so.conf', 'ld.so.conf.d', 'ssl/certs', 'ssl/openssl.cnf', 'ca-certificates',
                 'ca-certificates.conf', 'mime.types', 'protocols', 'services', 'alternatives', 'os-release',
                 'debian_version', 'lsb-release', 'issue'):
        roots.append(os.path.join('/etc', name))
    for var in ('SSL_CERT_FILE', 'NODE_EXTRA_CA_CERTS', 'REQUESTS_CA_BUNDLE', 'CURL_CA_BUNDLE', 'PIP_CERT'):
        cert = os.environ.get(var)       # a public certificate file the host itself is set up to use (pip / npm need it)
        if cert and os.path.isfile(cert) and not any(_path_is_under(b, cert) for b in banned):
            roots.append(os.path.realpath(cert))
    roots.extend(['/proc/self', '/proc/cpuinfo', '/proc/meminfo', '/proc/stat', '/proc/uptime', '/proc/loadavg',
                  '/proc/version', '/proc/sys/vm/overcommit_memory', '/proc/sys/kernel/random/boot_id',
                  '/sys/devices/system/cpu', '/sys/fs/cgroup'])
    return sorted({r for r in roots if os.path.exists(r)})


def _sandbox_dirs(user_folder):
    base = os.path.join(SANDBOX_DATA_DIR, _sandbox_id(user_folder))
    return {'base': base, 'home': os.path.join(base, 'home'), 'tmp': os.path.join(base, 'tmp'),
            'cache': os.path.join(base, 'cache'), 'pylibs': os.path.join(base, 'pylibs')}


def _chown_tree(path, uid, gid):
    """Give a folder and everything in it to one OS user (only used when the bot runs as root)."""
    try:
        os.lchown(path, uid, gid)
    except OSError:
        pass
    for dirpath, dirnames, filenames in os.walk(path):
        for name in dirnames + filenames:
            full = os.path.join(dirpath, name)
            try:
                if os.lstat(full).st_uid != uid:
                    os.lchown(full, uid, gid)
            except OSError:
                pass


def _sandbox_uid_for(user_folder):
    """Stable OS user id of one hosted user (kept by who owns the folder, nothing extra to store)."""
    with _SANDBOX_LOCK:
        try:
            owner = os.stat(user_folder).st_uid
        except OSError:
            owner = None
        if owner is not None and SANDBOX_UID_BASE <= owner < SANDBOX_UID_BASE + (1 << 24):
            return owner
        used = set()
        try:
            for name in os.listdir(UPLOAD_BOTS_DIR):
                try:
                    used.add(os.lstat(os.path.join(UPLOAD_BOTS_DIR, name)).st_uid)
                except OSError:
                    pass
        except OSError:
            pass
        uid = SANDBOX_UID_BASE
        while uid in used:
            uid += 1
        os.chmod(user_folder, 0o700)
        _chown_tree(user_folder, uid, uid)
        return uid


def _sandbox_prepare(user_folder, with_uid):
    """Make the user's private home / tmp / cache / package folders; with a separate OS user, also hand the folders over."""
    dirs = _sandbox_dirs(user_folder)
    for key in ('home', 'tmp', 'cache', 'pylibs'):
        os.makedirs(dirs[key], mode=0o700, exist_ok=True)
    uid = None
    if with_uid:
        uid = _sandbox_uid_for(user_folder)
        _chown_tree(user_folder, uid, uid)          # files the host wrote (uploads, imports) belong to the user too
        _chown_tree(dirs['base'], uid, uid)
        os.chmod(user_folder, 0o700)
        os.chmod(dirs['base'], 0o700)
        for path, mode in ((UPLOAD_BOTS_DIR, 0o711), (SANDBOX_DATA_DIR, 0o711), (IROTECH_DIR, 0o700)):
            try:
                os.chmod(path, mode)                # other users can walk through but not list; the host database is shut
            except OSError:
                pass
    return dirs, uid


def _sandbox_limits(profile):
    limits = {'CORE': 0, 'NOFILE': max(1024, SANDBOX_OPEN_FILES)}
    if SANDBOX_MEMORY_MB > 0:
        limits['DATA'] = SANDBOX_MEMORY_MB * 1024 * 1024 * (2 if profile == 'install' else 1)
    if profile == 'install':
        limits['CPU'] = max(INSTALL_TIMEOUT * 2, 60)       # an install always ends, so it always keeps its own limit
    elif SANDBOX_CPU_SECONDS > 0:
        limits['CPU'] = SANDBOX_CPU_SECONDS
    if SANDBOX_FILE_MB > 0:
        limits['FSIZE'] = SANDBOX_FILE_MB * 1024 * 1024
    return limits


def _bwrap_prefix(bwrap, user_folder, dirs, work_dir=None):
    """bubblewrap command line: a fresh filesystem with only the runtimes (read-only) and this user's own folders."""
    argv = [bwrap, '--die-with-parent', '--new-session', '--unshare-pid', '--unshare-ipc', '--unshare-uts',
            '--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp']
    for root in _sandbox_read_roots():
        if root.startswith(('/proc', '/sys')):
            continue
        argv += ['--ro-bind-try', root, root]
    for path in (user_folder, dirs['base'], work_dir):
        if path:
            argv += ['--bind', path, path]
    return argv + ['--chdir', work_dir or user_folder]


def _sandbox_shared_dirs():
    """/tmp and /dev/shm (Python multiprocessing locks live in /dev/shm). Only handed out when the host keeps nothing of its own
    there (private temp folder in use) and no host folder lies inside them; otherwise scripts keep their own TMPDIR only."""
    if not SANDBOX_SHARED_TMP or not HOST_TMP_PRIVATE:
        return []
    banned = _sandbox_banned_paths()
    out = []
    for path in ('/tmp', '/dev/shm'):
        if not os.path.isdir(path):
            continue
        real = os.path.realpath(path)
        if any(_path_is_under(b, real) or _path_is_under(real, b) for b in banned):
            continue
        out.append(real)
    return out


def _launcher_config(user_folder, dirs, uid, landlock, profile, work_dir=None):
    read_only = _sandbox_read_roots()
    limits = _sandbox_limits(profile)
    if uid is not None and SANDBOX_MAX_PROCS > 0:
        limits['NPROC'] = SANDBOX_MAX_PROCS          # per OS user, so one user's fork bomb cannot touch the others
    return {'landlock': landlock, 'ro': read_only,
            'rw': [os.path.realpath(user_folder), os.path.realpath(dirs['base'])]
                  + ([os.path.realpath(work_dir)] if work_dir else [])
                  + ['/dev/null', '/dev/zero', '/dev/urandom', '/dev/random', '/dev/tty'] + _sandbox_shared_dirs(),
            'limits': limits, 'uid': uid, 'seccomp': True, 'seccomp_required': False}


def _sandbox_build(command, user_folder, profile='run', state=None, work_dir=None):
    """(wrapped command, env additions). The same builder is used by the startup test and by every real start.
    work_dir = one extra folder the command may also write (the temporary folder of an upload whose packages are installed)."""
    state = state or _SANDBOX_STATE
    dirs, uid = _sandbox_prepare(user_folder, state['uid'])
    if work_dir and uid is not None:
        _chown_tree(work_dir, uid, uid)
        parent = os.path.dirname(os.path.realpath(work_dir))
        tmp_root = os.path.realpath(tempfile.gettempdir())
        while parent != tmp_root and _path_is_under(parent, tmp_root):     # let the user walk down to the work folder
            try:
                os.chmod(parent, (os.stat(parent).st_mode & 0o7777) | 0o711)
            except OSError:
                break
            parent = os.path.dirname(parent)
    cfg = _launcher_config(user_folder, dirs, uid, state['landlock'] and not state['bwrap'], profile, work_dir)
    wrapped = [sys.executable, '-I', '-c', _SANDBOX_LAUNCHER, json.dumps(cfg)] + list(command)
    if state['bwrap']:
        wrapped = _bwrap_prefix(state['bwrap'], user_folder, dirs, work_dir) + ['--'] + wrapped
    return wrapped, _sandbox_env(dirs, user_folder)


def _sandbox_env(dirs, user_folder):
    """Environment variables that point a script's HOME, temp files, caches and packages at its own folders."""
    extra = {'HOME': dirs['home'], 'TMPDIR': dirs['tmp'], 'TMP': dirs['tmp'], 'TEMP': dirs['tmp'],
             'XDG_CACHE_HOME': dirs['cache'], 'XDG_CONFIG_HOME': os.path.join(dirs['home'], '.config'),
             'PIP_CACHE_DIR': os.path.join(dirs['cache'], 'pip'), 'npm_config_cache': os.path.join(dirs['cache'], 'npm'),
             'npm_config_update_notifier': 'false', 'PWD': user_folder}
    old_path = os.environ.get('PYTHONPATH', '')
    extra['PYTHONPATH'] = dirs['pylibs'] + (os.pathsep + old_path if old_path else '')
    return extra


def sandbox_allows_start():
    """False only in strict mode when no real barrier works here."""
    if SANDBOX_MODE != 'strict':
        return True
    sandbox_detect()
    return _SANDBOX_STATE['level'] in ('full', 'partial')


def sandbox_wrap(command, user_folder, profile='run', work_dir=None):
    """Command to really start for a hosted script: wrapped in the sandbox launcher unless SANDBOX_MODE=off.
    Returns (command, env additions). profile 'install' is for pip / npm (more memory, CPU limited by INSTALL_TIMEOUT)."""
    if SANDBOX_MODE == 'off' or not sys.platform.startswith('linux'):
        return list(command), {}
    sandbox_detect()
    if not sandbox_allows_start():
        raise SandboxUnavailable('No real isolation is available on this server (SANDBOX_MODE=strict), so nothing is started.')
    if not _SANDBOX_STATE['launcher']:
        dirs, _ = _sandbox_prepare(user_folder, False)
        return list(command), _sandbox_env(dirs, user_folder)
    return _sandbox_build(command, user_folder, profile, None, work_dir)


def sandbox_pip_target(user_folder):
    """Extra pip arguments so packages go to the user's own folder (never into the host's shared Python)."""
    if SANDBOX_MODE == 'off' or not sys.platform.startswith('linux'):
        return []
    return ['--target', _sandbox_dirs(user_folder)['pylibs'], '--upgrade']


_SELFTEST_PROBE = r'''
import json, os, sys
own, other, host_file, host_dir = sys.argv[1:5]
out = {}
try:
    with open(os.path.join(own, "probe.txt"), "w") as handle:
        handle.write("ok")
    out["own_ok"] = open(os.path.join(own, "probe.txt")).read() == "ok" and os.path.exists(os.path.join(own, "own_secret.txt"))
except OSError:
    out["own_ok"] = False
def blocked(fn):
    try:
        fn()
    except OSError:
        return True
    return False
out["other_blocked"] = blocked(lambda: open(other).read()) and blocked(lambda: os.listdir(os.path.dirname(other)))
out["host_blocked"] = blocked(lambda: open(host_file).read()) and blocked(lambda: os.listdir(host_dir))
print(json.dumps(out))
'''


def _sandbox_probe(state):
    """Really start a probe script under `state` and check it: own folder works, another user's folder and the host
    folder are blocked. Returns (ok, note). Nothing is trusted that was not seen working."""
    root = os.path.join(SANDBOX_DATA_DIR, '_selftest')
    mine = os.path.join(root, 'mine')
    other_dir = os.path.join(root, 'other')
    host_file = os.path.join(BASE_DIR, '.sandbox_selftest')
    try:
        for path in (mine, other_dir):
            os.makedirs(path, exist_ok=True)
        os.chmod(root, 0o711)
        for path, text in ((os.path.join(mine, 'own_secret.txt'), 'mine'), (os.path.join(other_dir, 'secret.txt'), 'other'),
                           (host_file, 'host')):
            with open(path, 'w') as handle:
                handle.write(text)
        os.chmod(other_dir, 0o700)
        os.chmod(host_file, 0o600)
        user_folder = os.path.join(UPLOAD_BOTS_DIR, '0')      # not a real user: the probe's own folder
        os.makedirs(user_folder, exist_ok=True)
        os.makedirs(SANDBOX_DATA_DIR, exist_ok=True)
        os.chmod(SANDBOX_DATA_DIR, 0o711)
        with open(os.path.join(user_folder, 'own_secret.txt'), 'w') as handle:
            handle.write('mine')
        command = [sys.executable, '-I', '-c', _SELFTEST_PROBE, user_folder, os.path.join(other_dir, 'secret.txt'),
                   host_file, UPLOAD_BOTS_DIR]
        wrapped, extra = _sandbox_build(command, user_folder, 'install', state)
        env = child_env()
        env.update(extra)
        proc = subprocess.run(wrapped, cwd=user_folder, env=env, capture_output=True, text=True, timeout=60,
                              stdin=subprocess.DEVNULL, start_new_session=True)
        try:
            result = json.loads((proc.stdout or '').strip().splitlines()[-1])
        except (ValueError, IndexError):
            return False, 'the test script did not run (' + (proc.stderr or '').strip()[-120:].replace('\n', ' ') + ')'
        if result.get('own_ok') and result.get('other_blocked') and result.get('host_blocked'):
            return True, 'ok'
        return False, 'test result ' + json.dumps(result)
    except Exception as exc:
        return False, f'test could not run ({type(exc).__name__}: {exc})'
    finally:
        _rmtree_quiet(root)
        for path in (host_file, os.path.join(UPLOAD_BOTS_DIR, '0'), os.path.join(SANDBOX_DATA_DIR, '0')):
            if os.path.isdir(path):
                shutil.rmtree(path, ignore_errors=True)
            elif os.path.exists(path):
                try:
                    os.remove(path)
                except OSError:
                    pass


def _launcher_works(state):
    """Basic level has no wall to test, but the launcher (limits, no-new-privileges) must at least start a script."""
    try:
        wrapped, extra = _sandbox_build([sys.executable, '-I', '-c', 'print(42)'], BASE_DIR, 'install', state)
        env = child_env()
        env.update(extra)
        proc = subprocess.run(wrapped, cwd=BASE_DIR, env=env, capture_output=True, text=True, timeout=30,
                              stdin=subprocess.DEVNULL, start_new_session=True)
        return proc.returncode == 0 and proc.stdout.strip() == '42'
    except Exception:
        return False
    finally:
        shutil.rmtree(_sandbox_dirs(BASE_DIR)['base'], ignore_errors=True)


def sandbox_detect(force=False):
    """Find out ONCE what this server really allows (by trying it, not by guessing) and remember the level."""
    with _SANDBOX_DETECT_LOCK:
        if _SANDBOX_STATE['ready'] and not force:
            return dict(_SANDBOX_STATE)
        state = {'ready': True, 'level': 'basic', 'landlock': False, 'bwrap': None, 'uid': False,
                 'launcher': True, 'detail': ''}
        if SANDBOX_MODE == 'off' or not sys.platform.startswith('linux'):
            state.update(level='off', launcher=False,
                         detail='sandbox switched off' if SANDBOX_MODE == 'off' else 'not a Linux server')
            with _SANDBOX_LOCK:
                _SANDBOX_STATE.update(state)
            return dict(state)
        notes = []
        bwrap = shutil.which('bwrap')
        if bwrap:
            ok, note = _sandbox_probe(dict(state, bwrap=bwrap))
            if ok:
                state['bwrap'] = bwrap
                notes.append('private filesystem (bubblewrap) works')
            else:
                notes.append('bubblewrap is installed but does not work here: ' + note)
        else:
            notes.append('bubblewrap not installed')
        ok, note = _sandbox_probe(dict(state, bwrap=None, landlock=True))
        if ok:
            state['landlock'] = True
            notes.append('kernel file lock (Landlock) works')
        else:
            notes.append('kernel file lock (Landlock) does not work here: ' + note)
        if hasattr(os, 'geteuid') and os.geteuid() == 0:
            ok, note = _sandbox_probe(dict(state, landlock=state['landlock'], uid=True))
            if ok:
                state['uid'] = True
                notes.append('separate OS user per bot works')
            else:
                notes.append('separate OS user per bot does not work: ' + note)
        else:
            notes.append('not running as root, so no separate OS user per bot')
        if state['bwrap'] or (state['landlock'] and state['uid']):
            state['level'] = 'full'
        elif state['landlock'] or state['uid']:
            state['level'] = 'partial'
        else:
            state['level'] = 'basic'
            if not _launcher_works(state):
                state['launcher'] = False
                notes.append('limits helper does not run here, scripts start without limits')
        state['detail'] = '; '.join(notes)
        with _SANDBOX_LOCK:
            _SANDBOX_STATE.update(state)
        return dict(state)


def sandbox_log_startup():
    state = sandbox_detect()
    logger.info("Sandbox: mode=%s, isolation level=%s. %s", SANDBOX_MODE, state['level'].upper(), state['detail'])
    if SANDBOX_MODE == 'strict' and state['level'] not in ('full', 'partial'):
        logger.error("Sandbox: SANDBOX_MODE=strict but no real isolation works here, so NO user script will be started.")
    elif SANDBOX_MODE == 'auto' and state['level'] == 'basic':
        logger.warning("Sandbox: only BASIC protection is possible on this server (not a real wall between users).")
    elif SANDBOX_MODE == 'off':
        logger.warning("Sandbox: switched OFF, hosted scripts can see everything this bot can see.")


# --- Flask keep-alive + health endpoint ---
app = Flask('demon_hosting_keepalive')


@app.route('/')
def home():
    return "I am 👿 DEMON 👿 HOSTING BOT"


@app.route('/health')
def health():
    try:
        with STATE_LOCK:
            running = sum(1 for info in bot_scripts.values()
                          if info.get('process') and info['process'].poll() is None)
            tracked = len(bot_scripts)
        return jsonify(status='ok', version=BOT_VERSION, uptime_seconds=int(time.time() - HOST_START_TIME),
                       scripts_running=running, scripts_tracked=tracked,
                       users=len(active_users), polling_restarts=HEALTH_STATE['poll_restarts'],
                       sandbox_mode=SANDBOX_MODE, isolation=('off' if SANDBOX_MODE == 'off' else _SANDBOX_STATE['level']),
                       auto_backup=auto_backup_health())
    except Exception:  # never let the health page crash
        logger.exception("Health endpoint error")
        return jsonify(status='error'), 500


def run_flask():
    """Keep-alive web server. If it stops or cannot start, it is tried again (the bot itself keeps running meanwhile)."""
    delay = 5
    while not SHUTDOWN_EVENT.is_set():
        started = time.time()
        try:
            app.run(host='0.0.0.0', port=HEALTH_PORT, debug=False, use_reloader=False, threaded=True)
        except (Exception, SystemExit):      # werkzeug can end the thread with SystemExit when the port is taken
            logger.exception("Keep-alive web server stopped (port %s). The bot itself keeps running.", HEALTH_PORT)
        if SHUTDOWN_EVENT.is_set():
            break
        delay = 5 if time.time() - started > 120 else min(delay * 2, 60)
        logger.warning("Keep-alive web server is not up. Trying again in %ss.", delay)
        SHUTDOWN_EVENT.wait(delay)


def keep_alive():
    t = Thread(target=run_flask, name="keepalive-web", daemon=True)
    t.start()
    logger.info("Keep-alive web server starting on port %s (health page: /health)", HEALTH_PORT)


# --- Bot with safer Telegram calls -------------------------------------------
_apihelper = telebot.apihelper
# Do not wait forever on the network.
_apihelper.CONNECT_TIMEOUT = 15
_apihelper.READ_TIMEOUT = 45
_apihelper.RETRY_ON_ERROR = True


def _retry_after_seconds(exc, default=5):
    try:
        return int(exc.result_json.get('parameters', {}).get('retry_after', default))
    except Exception:
        match = re.search(r'retry after (\d+)', str(exc).lower())
        return int(match.group(1)) if match else default


# --- Reply-keyboard navigation -------------------------------------------------
# Every screen is a native Telegram reply keyboard that changes with each action. Screens are still
# described with NavMenu/NavButton (same add/row calls the old inline buttons used); SafeTeleBot turns a
# NavMenu into a ReplyKeyboardMarkup when it sends it. Pressing a key sends its label as normal text; the
# text handler below finds the action behind that label for this chat and runs the existing screen code.
# Colour: labels carry NO coloured-square prefix any more. The colour is the real button "style" field of
# Telegram Bot API 9.4 ("primary" blue, "success" green, "danger" red; no style = default grey). It is added
# to the keyboard JSON by _nav_make_button even if the installed pyTelegramBotAPI does not know the field.
# Clients or servers that ignore the field simply show normal buttons. BUTTON_STYLE=0/off turns it off.
# No custom (premium) emoji ids are used. All of the look is in NAV_THEME below.
NAV_TTL = 6 * 3600           # a keyboard state is forgotten after this many seconds
NAV_MAX_STATES = 5000        # most chats kept in memory
NAV_MAX_BUTTONS = 96         # Telegram allows about 100 keys on a keyboard; longer lists are paged (see _paginate)
NAV_PAGE_SIZE = 8            # list items (rows) on one page of a paged list
NAV_PAGE_TTL = 1800          # a remembered page number is forgotten after this many seconds without use
NAV_PAGER_MAX_CHATS = 3000
NAV_LABEL_MAX = 46
NAV_BACK_STACK_MAX = 12
NAV_CANCEL = '❌ Cancel'
NAV_HOME = '🏠 Home'
NAV_BACK = '⬅️ Back'
NAV_RESERVED = (NAV_CANCEL, NAV_HOME, NAV_BACK)
NAV_OLD_BUTTON_NOTE = "Ye button purana hai, menu se dobara try karo 👇"

# category -> Bot API button style, tried in this order against the label text (first match wins).
# red = danger (stop/delete/reject/cancel/clear/remove/ban/no), green = success (start/run/approve/confirm/yes/
# save/deploy/done/add/join), blue = primary (everything else: Back, Home, Import, Restart, Refresh, lists, admin).
# EVERY button gets one of the three: NAV_FALLBACK_STYLE (blue) is used whenever nothing else applies, so no
# button is ever left plain. (restart/refresh/retry/lock/import/restore sit before 'success' so that "Restart"
# does not turn green because of "start"; they are blue.)
NAV_FALLBACK_STYLE = 'primary'
NAV_THEME = [
    ('danger',  'danger',  r'delete|remove|reject|\bban\b|\bsuspend|\bstop|kill|wipe|clear|cancel|\bno\b'),
    ('confirm', 'success', r'\byes\b|confirm|approve|accept|\bdone'),
    ('warn',    'primary', r'restart|refresh|retry|(?<!un)lock|import|restore|expire'),
    ('success', 'success', r'start|\brun|approve|confirm|\byes\b|unban|unsuspend|unlock|\bdone|accept|\badd\b|join|\bsave|deploy|verify'),
    ('admin',   'primary', r'admin|user management|broadcast|subscription|channel|setting|health|manage'),
    ('info',    'primary', r'.'),
]
NAV_STYLE_ENABLED = os.environ.get('BUTTON_STYLE', '1').strip().lower() not in ('0', 'off', 'false', 'no', 'disable', 'disabled')
NAV_STYLES = ('primary', 'success', 'danger')
# squares an older version put in front of labels; keyboards already on phones may still send them
NAV_OLD_SQUARES = '🟦🟩🟧🟥🟪🟨⬛⬜🟫'
NAV_NUMBERED_PREFIXES = ('file_', 'remove_channel_', 'um_u_', 'um_f_', 'um_r_')

NAV_STATE = {}
NAV_LOCK = threading.RLock()
# Guards against an option switching on by itself (see _nav_wrap_next_step / _nav_dispatch):
STEP_TTL = 120               # a typed-answer prompt is forgotten after this many seconds
NAV_KNOWN_LABELS = {}        # every key label that was ever shown -> last time; separates an old key from a typed answer
NAV_KNOWN_MAX = 4000
NAV_SEEN_MAX = 200           # message ids remembered per chat to drop a re-delivered key press
NAV_SEEN_TTL = 600           # ... and for how many seconds
NAV_SEEN = {}
UPDATE_SEEN_MAX = 2000       # update ids remembered to drop a re-delivered update
UPDATE_SEEN_TTL = 600
UPDATE_SEEN = collections.OrderedDict()
_ACTOR = threading.local()   # who pressed the key that is being handled (set in handle_callbacks)
NAV_COUNTER_RX = re.compile(r'\(\d+\)')
_NAV_TRAIL_COUNT_RX = re.compile(r'^(.*?)(?: \(\d+\))?$', re.S)   # "👥 All Users (3)" -> "👥 All Users"
PAGER = {}                   # chat_id -> {list key -> {'page': n, 'time': t}}
PAGER_LOCK = threading.Lock()
_NAV_CALL_COUNTER = itertools.count(1)
_NAV_BACK_RX = re.compile(r'^\W*(?:back|🔙|⬅)', re.I | re.U)
_NAV_LEAD_RX = re.compile(r'^([^\w\s(\[]+)\s*(.*)$', re.S)


class NavButton:
    """One key. Either callback_data (an action) or url (the link is sent when it is tapped)."""
    def __init__(self, text, callback_data=None, url=None, **_ignored):
        self.text = str(text)
        self.callback_data = callback_data
        self.url = url


class NavMenu:
    """Same building calls as InlineKeyboardMarkup: add() and row()."""
    def __init__(self, row_width=3, **_ignored):
        self.row_width = max(1, int(row_width or 3))
        self.rows = []
        self.live = None          # zero-argument function that builds this same screen again with fresh numbers
        self.offset = 0           # numbered keys (1. 2. ...) of a later page continue after this many

    def add(self, *buttons, row_width=None):
        width = max(1, int(row_width or self.row_width))
        buttons = [b for b in buttons if b is not None]
        for i in range(0, len(buttons), width):
            self.rows.append(list(buttons[i:i + width]))
        return self

    def row(self, *buttons):
        buttons = [b for b in buttons if b is not None]
        if buttons:
            self.rows.append(list(buttons))
        return self

    def pager(self, key, view, page, pages):
        """Prev / Page x/y / Next row of a paged list. `view` is the action that shows the same list again."""
        if pages <= 1:
            return self
        keys = []
        if page > 0:
            keys.append(NavButton('⬅️ Prev', callback_data=f'pg_prev|{key}|{view}'))
        keys.append(NavButton(f'📄 Page {page + 1}/{pages}', callback_data=f'pg_here|{key}|{view}'))
        if page < pages - 1:
            keys.append(NavButton('➡️ Next', callback_data=f'pg_next|{key}|{view}'))
        return self.row(*keys)


def _pager_page(chat_id, key):
    now = time.time()
    with PAGER_LOCK:
        ent = (PAGER.get(chat_id) or {}).get(key)
        if ent and now - ent['time'] <= NAV_PAGE_TTL:
            return ent['page']
    return 0


def _paginate(chat_id, key, items, size=None):
    """(items of the current page, page index from 0, number of pages). The remembered page is clamped to the list as it
    is NOW, so a list that got shorter never shows an empty or missing page."""
    size = max(1, int(size or NAV_PAGE_SIZE))
    items = list(items)
    pages = max(1, -(-len(items) // size))
    page = min(max(_pager_page(chat_id, key), 0), pages - 1)
    now = time.time()
    with PAGER_LOCK:
        PAGER.setdefault(chat_id, {})[key] = {'page': page, 'time': now}
        if len(PAGER) > NAV_PAGER_MAX_CHATS:
            for cid in [c for c, d in PAGER.items() if all(now - e['time'] > NAV_PAGE_TTL for e in d.values())]:
                PAGER.pop(cid, None)
            while len(PAGER) > NAV_PAGER_MAX_CHATS:
                PAGER.pop(next(iter(PAGER)), None)
    return items[page * size:(page + 1) * size], page, pages


def _pager_move(chat_id, key, how):
    cur = _pager_page(chat_id, key)
    new = cur + 1 if how == 'next' else cur - 1 if how == 'prev' else cur
    with PAGER_LOCK:
        PAGER.setdefault(chat_id, {})[key] = {'page': max(new, 0), 'time': time.time()}


def _pager_reset(chat_id):
    with PAGER_LOCK:
        PAGER.pop(chat_id, None)


def _page_note(page, pages):
    return f' · 📄 Page {page + 1}/{pages}' if pages > 1 else ''


# ---- Message style: ONE premium look for every reply (HTML parse mode) --------------------------------------------
# Card         <b>EMOJI Title</b>  + an accent divider (status dot + bar), body rows inside a quote block (left rail)
# Row          EMOJI Label: <b>value</b>      (ids and file names go in <code>, never raw)
# Section      <b>EMOJI Heading</b> after a blank line
# Markers      ok = green, warn = yellow, err = red, info = blue, wait = purple (dot in the divider + icon in the title)
# Badges       green / red / yellow dot + word;  Bars  ▰▰▰▱▱ 60%;  Brand line  "Demon Hosting"
# Every dynamic value goes through html_escape; a text that is already HTML is wrapped in ui_raw().
# The accent line under a title is a plain divider, so it is ALWAYS full. A partly filled line only appears where it is
# a REAL progress bar (ui_divider(progress=0.4) -> 'dot ▰▰▰▰▰▰▱▱▱▱▱▱▱▱▱▱ 40%', always with the percent).
UI_BAR_ON, UI_BAR_OFF = '▰', '▱'
UI_DIV_WIDTH = 16
UI_LINE = UI_BAR_ON * UI_DIV_WIDTH
UI_MARK = {'ok': '✅', 'warn': '⚠️', 'err': '❌', 'info': 'ℹ️', 'wait': '⏳'}
UI_ACCENT = {'✅': '🟢', '⚠': '🟡', '❌': '🔴', 'ℹ': '🔵', '⏳': '🟣', '🎉': '🟢', '🚫': '🔴', '⏸': '🟡', '▶': '🟢', '🛑': '🔴'}
UI_BRAND = '⚡ Demon Hosting · Premium Hosting'
UI_LIMIT = 3900
_UI_DIVIDER_RX = re.compile(r'^(?:🟢|🟡|🔴|🔵|🟣|💎) [▰▱]{16}(?: \d{1,3}%)?$|^━{12,}$', re.M)


def ui_divider(emoji=None, progress=None):
    """The accent line of a card: status dot (green / yellow / red / blue / purple) + bar. Default is a gold diamond.
    progress=None (the normal case) -> a FULL bar, a clean divider. progress=0..1 -> a real progress bar with its percent."""
    key = str(emoji or '').replace('\ufe0f', '')[:1]
    dot = UI_ACCENT.get(key, '💎')
    if progress is None:
        return f"{dot} {UI_LINE}"
    try:
        ratio = max(0.0, min(1.0, float(progress)))
    except (TypeError, ValueError):
        return f"{dot} {UI_LINE}"
    filled = int(round(ratio * UI_DIV_WIDTH))
    if ratio > 0 and filled == 0:
        filled = 1
    if ratio < 1 and filled == UI_DIV_WIDTH:
        filled = UI_DIV_WIDTH - 1
    return f"{dot} {UI_BAR_ON * filled}{UI_BAR_OFF * (UI_DIV_WIDTH - filled)} {int(round(ratio * 100))}%"


class UIRaw(str):
    """Text that is already HTML and must not be escaped again."""


def ui_raw(text):
    return UIRaw(text)


def ui_esc(value):
    return value if isinstance(value, UIRaw) else html_escape(str(value))


def ui_head(emoji, title, progress=None):
    """Header line + accent divider (full, or a real progress bar when progress=0..1 is given)."""
    return f"<b>{emoji} {ui_esc(title)}</b>\n{ui_divider(emoji, progress)}"


def ui_row(emoji, label, value, code=False, bold=True):
    """One 'emoji Label: value' row."""
    shown = ui_esc(value)
    if code:
        shown = f'<code>{shown}</code>'
    elif bold:
        shown = f'<b>{shown}</b>'
    return f"{emoji} {ui_esc(label)}: {shown}"


def ui_section(emoji, title):
    """A small heading inside a screen (preceded by an empty line)."""
    return f"\n<b>{emoji} {ui_esc(title)}</b>"


def ui_note(text):
    """A quiet hint line."""
    return f"<i>{ui_esc(text)}</i>"


def ui_code(value):
    return f"<code>{ui_esc(value)}</code>"


def ui_pre(text, limit=600):
    """A short monospace block (script output). Escaped and cut, never raw."""
    text = str(text or '').strip()
    if len(text) > limit:
        text = text[-limit:]
    return f"<pre>{html_escape(text)}</pre>"


def ui_cap(text, limit=UI_LIMIT):
    """Keep a message under Telegram's 4096 characters without cutting a tag in half."""
    text = str(text)
    if len(text) <= limit:
        return text
    cut = text[:limit - 40]
    nl = cut.rfind('\n')
    if nl > limit // 2:
        cut = cut[:nl]
    return _html_close_open_tags(cut) + '\n<i>... (shortened)</i>'


def ui_brand():
    """The signature line of a main screen."""
    return f"<i>{UI_BRAND}</i>"


def ui_msg(emoji, title, *lines, foot=None, brand=False, progress=None, tip=None):
    """Header, then the lines (None / '' are skipped), then an optional quiet footer and brand line.
    progress=0..1 turns the accent line into a real progress bar; without it the line is a full divider."""
    body = [str(x) for x in lines if x not in (None, '')]
    out = ui_head(emoji, title, progress)
    if body:
        out += '\n' + '\n'.join(body)
    if foot:
        out += '\n\n' + ui_note(foot)
    if tip:
        out += ('\n' if foot else '\n\n') + ui_note(ui_tip(tip))
    if brand:
        out += ('\n' if (foot or tip) else '\n\n') + ui_brand()
    return ui_cap(out)


def ui_bar(value, total, width=10):
    """Progress bar: ui_bar(3, 10) -> '▰▰▰▱▱▱▱▱▱▱ 30%'. Unlimited / zero totals show a full-width infinity bar."""
    try:
        if total in (None, 0) or total == float('inf'):
            return f"{UI_BAR_ON * width} ∞"
        ratio = max(0.0, min(1.0, float(value) / float(total)))
    except (TypeError, ValueError, ZeroDivisionError):
        return f"{UI_BAR_ON * width} ∞"
    filled = int(round(ratio * width))
    if filled == 0 and round(ratio * 100) >= 1:
        filled = 1
    return f"{UI_BAR_ON * filled}{UI_BAR_OFF * (width - filled)} {int(round(ratio * 100))}%"


def ui_badge(state, text=None):
    """Status badge: green / red / yellow dot + word. state: on|off|warn|run|stop|ok|err or a bool."""
    if state is True:
        state = 'on'
    elif state is False:
        state = 'off'
    table = {'on': ('🟢', 'Online'), 'run': ('🟢', 'Running'), 'ok': ('🟢', 'OK'),
             'off': ('🔴', 'Offline'), 'stop': ('🔴', 'Stopped'), 'err': ('🔴', 'Error'),
             'warn': ('🟡', 'Warning'), 'wait': ('🟡', 'Waiting')}
    dot, word = table.get(state, ('⚪', str(state)))
    return UIRaw(f"{dot} {ui_esc(text if text is not None else word)}")


def ui_warn_line(text):
    return f"🟡 <i>{ui_esc(text)}</i>"


def ui_steps(*items):
    """Numbered step list with keycap-style numbers."""
    nums = ['1️⃣', '2️⃣', '3️⃣', '4️⃣', '5️⃣', '6️⃣', '7️⃣', '8️⃣', '9️⃣']
    return '\n'.join(f"{nums[i] if i < len(nums) else '▫️'} {x}" for i, x in enumerate(items))


def ui_bullets(*items, mark='▫️'):
    return '\n'.join(f"{mark} {x}" for x in items if x not in (None, ''))


def _ui_card(text):
    """Put the body of a finished card (everything after the divider line) into a quote block.
    The quiet italic footer lines at the end stay outside. Cards that hold <pre> / a plain quote already are left alone.
    An expandable quote (logs, long lists) stays as it is; the text around it is quoted separately."""
    try:
        if '<pre' in text or '<blockquote>' in text:
            return text
        lines = text.split('\n')
        idx = next((i for i, ln in enumerate(lines[:3]) if _UI_DIVIDER_RX.search(ln)), None)
        if idx is None:
            return text
        head = '\n'.join(lines[:idx + 1])
        rest = '\n'.join(lines[idx + 1:]).strip('\n')
        pieces = re.split(r'(<blockquote expandable>.*?</blockquote>)', rest, flags=re.S)
        tail = ''
        last = pieces[-1]
        paras = last.strip('\n').split('\n\n')
        tl = []
        while paras and re.fullmatch(r'(?:<i>[^<>\n]*</i>\n?)+', paras[-1].strip()):
            tl.insert(0, paras.pop().strip())
        pieces[-1] = '\n\n'.join(paras).strip('\n')
        tail = '\n'.join(tl)
        out = [head]
        for piece in pieces:
            if piece.startswith('<blockquote expandable>'):
                out.append(piece)
            elif piece.strip('\n'):
                out.append(f"<blockquote>{piece.strip(chr(10))}</blockquote>")
        if len(out) == 1:
            return text
        res = '\n'.join(out)
        if tail:
            res += '\n' + tail
        return res
    except Exception:
        return text


def ui_ok(title, *lines, foot=None, progress=None):
    return ui_msg(UI_MARK['ok'], title, *lines, foot=foot, progress=progress)


def ui_warn(title, *lines, foot=None, progress=None):
    return ui_msg(UI_MARK['warn'], title, *lines, foot=foot, progress=progress)


def ui_err(title, *lines, foot=None, progress=None):
    return ui_msg(UI_MARK['err'], title, *lines, foot=foot, progress=progress)


def ui_info(title, *lines, foot=None, progress=None):
    return ui_msg(UI_MARK['info'], title, *lines, foot=foot, progress=progress)


def ui_wait(title, *lines, foot=None, progress=None):
    return ui_msg(UI_MARK['wait'], title, *lines, foot=foot, progress=progress)


def ui_line(kind, text):
    """One-line status: marker + text (text is escaped)."""
    return f"{UI_MARK.get(kind, kind)} {ui_esc(text)}"


def ui_toast(kind, text):
    """Plain text for a pop-up (answer_callback_query has no formatting)."""
    return f"{UI_MARK.get(kind, kind)} {text}"[:200]


def ui_num(value):
    """1234567 -> 1,234,567 (anything else is shown as it is)."""
    try:
        if isinstance(value, float) and value == float('inf'):
            return 'Unlimited'
        return f"{int(value):,}"
    except (TypeError, ValueError, OverflowError):
        return str(value)


def ui_limit(value):
    return 'Unlimited' if value == float('inf') else ui_num(value)


def ui_size(num):
    try:
        return _human_size(num)
    except (TypeError, ValueError):
        return '-'


def ui_uptime(seconds):
    """3725 -> '1h 2m', 45 -> '45s', 90000 -> '1d 1h'."""
    try:
        seconds = max(0, int(seconds))
    except (TypeError, ValueError):
        return '-'
    days, rest = divmod(seconds, 86400)
    hours, rest = divmod(rest, 3600)
    minutes, secs = divmod(rest, 60)
    if days:
        return f"{days}d {hours}h"
    if hours:
        return f"{hours}h {minutes}m"
    if minutes:
        return f"{minutes}m {secs}s"
    return f"{secs}s"


def ui_date(value):
    """A datetime as 'dd Mon yyyy, HH:MM' (anything else is shown as text)."""
    if isinstance(value, datetime):
        return value.strftime('%d %b %Y, %H:%M')
    return str(value)


def ui_lead(text):
    """The first visible characters of a message with a leading <b> removed (to look at its marker)."""
    t = str(text).lstrip()
    return t[3:].lstrip() if t.startswith('<b>') else t



# ---- v18: relative times, rotating tips, expandable quotes, state tags ------------------------------------------------------
def ui_ago(value, now=None):
    """A datetime / epoch seconds as '2h ago' (future values and junk give '-')."""
    try:
        if isinstance(value, datetime):
            secs = ((now or datetime.now()) - value).total_seconds()
        elif isinstance(value, (int, float)):
            secs = (now.timestamp() if isinstance(now, datetime) else (now or time.time())) - float(value)
        else:
            return '-'
        secs = int(secs)
        if secs < -60:
            return '-'
        if secs < 45:
            return 'just now'
        if secs < 3600:
            return f"{max(1, secs // 60)}m ago"
        if secs < 86400:
            return f"{secs // 3600}h ago"
        if secs < 86400 * 30:
            return f"{secs // 86400}d ago"
        return f"{secs // (86400 * 30)}mo ago"
    except Exception:
        return '-'


def ui_in(seconds):
    """Seconds from now as 'in 3d 4h' / 'in 2h 5m'; zero or less gives 'expired'."""
    try:
        seconds = int(seconds)
    except (TypeError, ValueError):
        return '-'
    if seconds <= 0:
        return 'expired'
    return 'in ' + ui_uptime(seconds)


UI_TIPS = {
    'general': ['Tap Help any time for a quick start guide.',
                'Keep your scripts small and log with print() so Logs stays useful.',
                'A .zip upload can hold a whole project with its requirements.txt.',
                'Use Export Backup now and then, it takes one tap.',
                'Invite friends with your Referral link to earn free Premium days.'],
    'files': ['Tap a file to open Start, Stop, Restart, Logs and Environment.',
              'Put secrets in Environment (.env) instead of writing them in code.',
              'Export Backup saves all your bots in one zip you can import later.'],
    'run': ['A script that crashes is restarted for you a few times, check Logs if it keeps stopping.',
            'Open a script and tap Logs to see what it printed last.',
            'Changed Environment values apply the next time the script restarts.'],
}
_UI_TIP_STEP = itertools.count()


def ui_tip(topic='general'):
    """One rotating pro tip line (italic, with a bulb). Used on only a few screens, never on every message."""
    pool = UI_TIPS.get(topic) or UI_TIPS['general']
    return f"💡 Pro tip: {pool[next(_UI_TIP_STEP) % len(pool)]}"


def ui_expand(text, limit=1500, tail=True):
    """Long detail (logs, lists) in a collapsed quote that opens with a tap. Escaped, and cut to `limit` characters
    (the end is kept when tail=True, because the newest log lines matter most)."""
    text = str(text or '').strip('\n')
    if len(text) > limit:
        text = ('…\n' + text[-limit:]) if tail else (text[:limit] + '\n…')
        first = text.find('\n')
        if tail and first != -1 and first < 12 and text.startswith('…'):
            pass
    return UIRaw(f"<blockquote expandable>{html_escape(text)}</blockquote>")


UI_TAGS = {'active': ('🟢', 'ACTIVE'), 'running': ('🟢', 'RUNNING'), 'stopped': ('🔴', 'STOPPED'), 'premium': ('⭐', 'PREMIUM'),
           'free': ('🆓', 'FREE'), 'locked': ('🔒', 'LOCKED'), 'unlocked': ('🔓', 'UNLOCKED'), 'admin': ('🛡️', 'ADMIN'),
           'owner': ('👑', 'OWNER'), 'expired': ('⌛', 'EXPIRED'), 'banned': ('🚫', 'BANNED'), 'suspended': ('⏸️', 'SUSPENDED'),
           'online': ('🟢', 'ONLINE'), 'offline': ('🔴', 'OFFLINE'), 'warn': ('🟡', 'WARNING'), 'ok': ('🟢', 'OK'),
           'off': ('⚪', 'OFF'), 'on': ('🟢', 'ON')}


def ui_tag(state, text=None):
    """A bold capital status badge: 'ACTIVE', 'STOPPED', 'PREMIUM', 'FREE', 'LOCKED' with its dot / icon."""
    icon, word = UI_TAGS.get(str(state).lower(), ('⚪', str(state).upper()))
    return UIRaw(f"{icon} <b>{ui_esc(text if text is not None else word)}</b>")


def ui_meter(emoji, label, value, total, shown=None):
    """A usage row: 'emoji Label: shown' and a real bar line under it (inside <code> so the bars line up)."""
    txt = shown if shown is not None else f"{ui_num(value)} / {ui_limit(total)}"
    return f"{emoji} {ui_esc(label)}: <b>{ui_esc(txt)}</b>\n<code>{ui_bar(value, total)}</code>"


def ui_plan(user_id):
    """('badge html', days_left or None) for the plan of a person: OWNER / ADMIN / PREMIUM / FREE."""
    try:
        if user_id == OWNER_ID:
            return ui_tag('owner'), None
        if user_id in admin_ids:
            return ui_tag('admin'), None
        exp = (user_subscriptions.get(user_id) or {}).get('expiry')
        if exp and exp > datetime.now():
            return ui_tag('premium'), max(0, (exp - datetime.now()).days)
    except Exception:
        pass
    return ui_tag('free'), None


# the same refusals everywhere
MSG_BANNED = ui_err('Access Blocked', 'You are banned from using this bot.')
MSG_NO_ADMIN = ui_err('Not Allowed', 'Admin permissions required.')
MSG_NO_OWNER = ui_err('Not Allowed', 'Owner permissions required.')
MSG_LOCKED = ui_warn('Bot Locked', 'The bot is locked by an admin. Please try again later.')
MSG_GENERIC_ERROR = ui_err('Something Went Wrong', 'Please try again in a moment. If it keeps happening, tell the admin.')


# ---- One central polish for every message that is not built with the ui_* helpers above -------------------------------------
# SafeTeleBot runs each outgoing text through ui_polish(): old Markdown / plain texts become HTML (no literal backticks or **),
# a short header line with a divider is added, and a message that already has the divider is left alone. Messages that must go
# out exactly as written (broadcasts, continuation parts of a long text) are sent with ui_raw=True.
_UI_TITLES = {'✅': 'Done', '❌': 'Error', '⚠': 'Notice', 'ℹ': 'Info', '⏳': 'Please Wait', '🔄': 'Working', '🚫': 'Blocked',
              '⏸': 'Paused', '▶': 'Resumed', '🎉': 'Congrats', '❎': 'Cancelled', '⌛': 'Expired', '🔒': 'Locked',
              '🛑': 'Stopped', '🔁': 'Restart', '🔴': 'Alert', '🟢': 'Running', '⭐': 'Premium', '🎁': 'Reward', '👑': 'Admin',
              '🏃': 'Speed Test', '📦': 'Packages', '📢': 'Broadcast', '📤': 'Upload', '📥': 'Download', '📋': 'Logs',
              '🔧': 'User Limits', '🔍': 'Search', '💳': 'Subscription', '👁': 'Preview', '🗑': 'File Removed',
              '📂': 'Files', '👤': 'User', '💾': 'Backup', '🐙': 'GitHub', '🧹': 'Cleanup', '📊': 'Stats',
              '🔓': 'Unlocked', '🤖': 'Bot', '📝': 'Note', '🛠': 'Admin Tools', '💎': 'Premium', '🔔': 'Notice',
              '🚀': 'Launch', '🔑': 'Access', '📌': 'Pinned', '🧩': 'Modules', '🔐': 'Security', '🩺': 'Health'}
_UI_TAG_SPLIT = re.compile(r'(<[^<>]*>)')
_UI_MD_PRE = re.compile(r'```[a-zA-Z]*\n?(.*?)```', re.S)
_UI_MD_CODE = re.compile(r'`([^`\n]+)`')
_UI_MD_BOLD2 = re.compile(r'\*\*(.+?)\*\*', re.S)
_UI_MD_BOLD1 = re.compile(r'(?<![\w*])\*([^*\n]+)\*(?![\w*])')
_UI_MD_LINK = re.compile(r'\[([^\[\]\n]+)\]\((https?://[^\s)]+)\)')
_UI_ARTIFACT = re.compile(r'`|\*\*')
_UI_ENDS = ('.', '!', '?', '…', ')')


def _ui_md_inline(text, single_star=False):
    """Markdown bits in an already-escaped piece of text -> HTML tags."""
    text = _UI_MD_PRE.sub(lambda m: f"<pre>{m.group(1).strip(chr(10))}</pre>", text)
    text = _UI_MD_CODE.sub(r'<code>\1</code>', text)
    text = _UI_MD_BOLD2.sub(r'<b>\1</b>', text)
    if single_star:
        text = _UI_MD_BOLD1.sub(r'<b>\1</b>', text)
    return _UI_MD_LINK.sub(r'<a href="\2">\1</a>', text)


def _ui_fix_html(text):
    """Leftover backticks / ** in an HTML text -> tags (never inside <code> / <pre>)."""
    if '`' not in text and '**' not in text:
        return text
    out, depth = [], 0
    for piece in _UI_TAG_SPLIT.split(text):
        if piece.startswith('<') and piece.endswith('>'):
            low = piece.lower()
            if low.startswith(('<code', '<pre')):
                depth += 1
            elif low.startswith(('</code', '</pre')):
                depth = max(0, depth - 1)
            out.append(piece)
        elif depth:
            out.append(piece)
        else:
            out.append(_ui_md_inline(piece))
    return ''.join(out)


def _ui_plain_of(html_line):
    return html_unescape(re.sub(r'<[^>]*>', '', html_line)).strip()


def _ui_starts_with_symbol(text):
    return bool(text) and ord(text[0]) > 0x2000


_UI_HALF_LINE_RX = re.compile(r'^((?:🟢|🟡|🔴|🔵|🟣|💎) )[▰▱]{16}$', re.M)


def ui_polish(text, parse_mode=None):
    """(text, parse_mode) as it should go out. A divider without a percent is never partly filled."""
    out, mode = _ui_polish_core(text, parse_mode)
    try:
        if isinstance(out, str) and '▱' in out:
            out = _UI_HALF_LINE_RX.sub(lambda mt: mt.group(1) + UI_LINE, out)
    except Exception:
        pass
    return out, mode


def _ui_polish_core(text, parse_mode=None):
    """(text, parse_mode) as it should go out. Never raises: on any problem the original is returned."""
    try:
        if not isinstance(text, str) or not text.strip():
            return text, parse_mode
        mode = (parse_mode or '').upper() if isinstance(parse_mode, str) else ''
        if mode not in ('HTML', 'MARKDOWN', 'MARKDOWNV2', ''):
            return text, parse_mode
        artifacts = bool(_UI_ARTIFACT.search(text))
        legacy_md = mode in ('MARKDOWN', 'MARKDOWNV2')
        if mode == 'HTML':
            body = _ui_fix_html(text)
        elif legacy_md or artifacts or _ui_starts_with_symbol(text.lstrip()):
            body = _ui_md_inline(html_escape(text, quote=False), single_star=legacy_md)
        else:
            return text, parse_mode
        if _UI_DIVIDER_RX.search(body):
            return ui_cap(_ui_card(body)), 'HTML'
        lines = body.strip('\n').split('\n')
        first = lines[0].strip()
        rest = lines[1:]
        whole_bold = re.fullmatch(r'<b>(.+?)</b>:?', first)
        title_html, tail = None, None
        if whole_bold and len(_ui_plain_of(first)) <= 60:
            inner = whole_bold.group(1)
            title_html = inner if _ui_starts_with_symbol(_ui_plain_of(inner)) else f"ℹ️ {inner}"
        elif _ui_starts_with_symbol(first):
            plain = _ui_plain_of(first)
            words = plain.split()
            no_marker = ' '.join(words[1:])
            if len(plain) <= 42 and not plain.endswith(_UI_ENDS) and (plain.endswith(':') or rest or len(words) <= 4):
                title_html = re.sub(r'</?b>', '', first).rstrip(':').strip()
            else:
                sym = words[0]
                key = sym.replace('️', '')
                key = key[0] if key else ''
                title = _UI_TITLES.get(key, 'Update')
                if key in ('❌', '⚠') and re.search(r'cancel', no_marker, re.I):
                    sym, title = '❎', 'Cancelled'
                title_html = f"{sym} {title}"
                tail = re.sub(r'</?b>', '', first.split(None, 1)[1]) if len(first.split(None, 1)) > 1 else ''
        else:
            title_html, tail = 'ℹ️ Info', first
        parts = [f"<b>{title_html}</b>\n{ui_divider(title_html)}"]
        if tail:
            parts.append(tail)
        parts.extend(rest)
        out = '\n'.join(parts).rstrip()
        return ui_cap(_ui_card(out)), 'HTML'
    except Exception:
        return text, parse_mode


def ui_polish_toast(text):
    """A pop-up has no formatting: take out the Markdown signs."""
    try:
        return re.sub(r'`|\*\*', '', text)[:200] if isinstance(text, str) else text
    except Exception:
        return text


def ui_user_error(exc=None):
    """What a person sees instead of raw Python error text."""
    return 'Something went wrong. Please try again, or tell the admin if it keeps happening.'


def _nav_split_label(text):
    """('emoji', 'rest') where emoji is the leading symbol of the label if there is one."""
    m = _NAV_LEAD_RX.match(text.strip())
    if m and not m.group(1).isascii():
        return m.group(1), m.group(2).strip() or text.strip()
    return '', text.strip()


def _nav_category(text):
    low = text.lower()
    for name, style, rx in NAV_THEME:
        if re.search(rx, low):
            return style if style in NAV_STYLES else NAV_FALLBACK_STYLE
    return NAV_FALLBACK_STYLE


def _nav_style_of(text, action, number=None):
    """The colour of one key. Numbered file keys show the state of the bot (green running, red stopped);
    removal keys are red; every other numbered / list key is blue; the rest follows NAV_THEME."""
    emoji, rest = _nav_split_label(_nav_strip_squares(text))
    if isinstance(action, str):
        if action.startswith(('envk_', 'remove_channel_')):
            return 'danger'
        if action.startswith('file_'):
            if '▶️' in text:
                return 'success'
            if '⏹️' in text or '⏹' in text:
                return 'danger'
            if emoji == '🟢':                 # list of running bots
                return 'success'
            return NAV_FALLBACK_STYLE
    if number is not None:
        return NAV_FALLBACK_STYLE
    return _nav_category(rest)


def _nav_strip_squares(text):
    """Remove leading coloured squares (old labels) and the space after them."""
    t = text.lstrip()
    while t and t[0] in NAV_OLD_SQUARES:
        t = t[1:].lstrip()
    return t


NAV_FALLBACK_EMOJI = '🔹'


def _nav_label(text, action, number=None):
    emoji, rest = _nav_split_label(_nav_strip_squares(text))
    if not emoji and not re.match(r'^\s*\d+\.\s', rest):
        emoji = NAV_FALLBACK_EMOJI                       # every key starts with an emoji (a "1." list number counts as its lead)
    if number is not None:
        label = f"{number}. {rest if not emoji else emoji + ' ' + rest}"
    else:
        label = f"{emoji + ' ' if emoji else ''}{rest}"
    if len(label) > NAV_LABEL_MAX:
        label = label[:NAV_LABEL_MAX - 1].rstrip() + '…'
    return label


def _nav_is_main_menu(buttons):
    acts = {b.callback_data for b in buttons}
    return 'upload' in acts and 'check_files' in acts


def _nav_forget_old():
    now = time.time()
    for key in [k for k, v in NAV_STATE.items() if now - v['time'] > NAV_TTL]:
        NAV_STATE.pop(key, None)
    if len(NAV_STATE) > NAV_MAX_STATES:
        for key, _ in sorted(NAV_STATE.items(), key=lambda kv: kv[1]['time'])[:len(NAV_STATE) - NAV_MAX_STATES + 100]:
            NAV_STATE.pop(key, None)


def _nav_remember_labels(labels):
    now = time.time()
    with NAV_LOCK:
        for lab in labels:
            NAV_KNOWN_LABELS[lab] = now
        if len(NAV_KNOWN_LABELS) > NAV_KNOWN_MAX:
            for lab, _ in sorted(NAV_KNOWN_LABELS.items(), key=lambda kv: kv[1])[:len(NAV_KNOWN_LABELS) - NAV_KNOWN_MAX + 200]:
                NAV_KNOWN_LABELS.pop(lab, None)


def _nav_is_old_key(text):
    """True when the text is exactly the label of a key that was shown at some time (so it is a key press
    from an old keyboard, never an answer somebody typed)."""
    t = _nav_strip_squares(text or '')
    return text in NAV_RESERVED or text in NAV_KNOWN_LABELS or t in NAV_KNOWN_LABELS


def _msg_already_seen(message):
    """True when this exact Telegram message was already handled a moment ago (a re-delivered update). Fake key
    calls have negative ids and are never dropped."""
    try:
        mid = message.message_id
        if not isinstance(mid, int) or mid <= 0:
            return False
        key = (message.chat.id, mid)
        now = time.time()
        with NAV_LOCK:
            seen = NAV_SEEN.setdefault(message.chat.id, collections.OrderedDict())
            if now - seen.get(key, -NAV_SEEN_TTL) < NAV_SEEN_TTL:
                return True
            seen[key] = now
            seen.move_to_end(key)
            while len(seen) > NAV_SEEN_MAX or (seen and now - next(iter(seen.values())) > NAV_SEEN_TTL):
                seen.popitem(last=False)
            if len(NAV_SEEN) > NAV_MAX_STATES:
                NAV_SEEN.pop(next(iter(NAV_SEEN)), None)
    except Exception:
        return False
    return False


def _update_already_seen(update_id):
    """True when Telegram delivered this update_id a second time (polling restart, a second instance)."""
    if not isinstance(update_id, int):
        return False
    now = time.time()
    with NAV_LOCK:
        if now - UPDATE_SEEN.get(update_id, -UPDATE_SEEN_TTL) < UPDATE_SEEN_TTL:
            return True
        UPDATE_SEEN[update_id] = now
        UPDATE_SEEN.move_to_end(update_id)
        while len(UPDATE_SEEN) > UPDATE_SEEN_MAX or (UPDATE_SEEN and now - next(iter(UPDATE_SEEN.values())) > UPDATE_SEEN_TTL):
            UPDATE_SEEN.popitem(last=False)
    return False


def _nav_get(chat_id):
    with NAV_LOCK:
        st = NAV_STATE.get(chat_id)
        if st and time.time() - st['time'] > NAV_TTL:
            NAV_STATE.pop(chat_id, None)
            return None
        return st


def _nav_blank():
    return {'map': {}, 'rows': [], 'time': time.time(), 'cur': None, 'stack': [], 'seq': 0, 'await': False, 'live': None}


def _nav_style_for(label, styles):
    if not NAV_STYLE_ENABLED:
        return None
    st = (styles or {}).get(label)
    return st if st in NAV_STYLES else NAV_FALLBACK_STYLE      # the single fallback: no plain buttons


def _nav_make_button(label, style=None):
    """A KeyboardButton that sends "style" to Telegram, whatever pyTelegramBotAPI version is installed."""
    if not NAV_STYLE_ENABLED:
        return types.KeyboardButton(label)
    if style not in NAV_STYLES:
        style = NAV_FALLBACK_STYLE
    btn = None
    try:
        btn = types.KeyboardButton(label, style=style)       # newer library versions know the field
    except Exception:
        btn = None
    if btn is None:
        btn = types.KeyboardButton(label)
    try:
        has = callable(getattr(btn, 'to_dict', None))
        if has and btn.to_dict().get('style') == style:
            return btn
        btn.style = style
        if has:
            orig = btn.to_dict

            def _to_dict(_orig=orig, _style=style):
                d = _orig()
                if isinstance(d, dict):
                    d['style'] = _style
                return d
            btn.to_dict = _to_dict
    except Exception:
        pass                                                  # worst case: a normal, uncoloured button
    return btn


def _nav_rows_to_markup(rows, styles=None):
    kb = types.ReplyKeyboardMarkup(row_width=2, resize_keyboard=True, one_time_keyboard=False,
                                   input_field_placeholder="Button dabao...")
    for row in rows:
        kb.row(*[_nav_make_button(label, _nav_style_for(label, styles)) for label in row])
    try:                                                      # last safety: styled buttons already turned into dicts
        for row, labels in zip(kb.keyboard, rows):
            for item, label in zip(row, labels):
                sty = _nav_style_for(label, styles)
                if sty and isinstance(item, dict) and 'style' not in item:
                    item['style'] = sty
    except Exception:
        pass
    return kb


def _nav_build(chat_id, menu, cancel_only=False):
    """Turn a NavMenu into a ReplyKeyboardMarkup and remember what each label does for this chat."""
    all_buttons = [b for row in menu.rows for b in row]
    buttons = all_buttons[:NAV_MAX_BUTTONS]
    if len(all_buttons) > len(buttons):
        logger.warning("Keyboard has %s keys; only the first %s are shown (a list should be paged)", len(all_buttons), len(buttons))
    keep = {id(b) for b in buttons}
    main = _nav_is_main_menu(buttons)
    used = set(NAV_RESERVED)
    amap, rows, styles = {}, [], {}
    has_custom_back = False
    counter = int(getattr(menu, 'offset', 0) or 0)
    for row in menu.rows:
        out = []
        for b in row:
            if id(b) not in keep:
                continue
            action = b.callback_data if b.callback_data is not None else ('url:' + str(b.url))
            if not main and action == 'back_to_main':
                continue                                  # the Home key does this
            number = None
            if isinstance(action, str) and action.startswith(NAV_NUMBERED_PREFIXES) and not re.match(r'^\W*\d+\.', b.text):
                counter += 1
                number = counter
            label = _nav_label(b.text, action, number)
            style = _nav_style_of(b.text, action, number)
            if _NAV_BACK_RX.match(b.text):
                has_custom_back = True
            base, n = label, 2
            while label in used:
                label = f"{base} #{n}"       # not "(2)": that form is what a live counter looks like
                n += 1
            used.add(label)
            amap[label] = action
            styles[label] = style
            out.append(label)
        if out:
            rows.append(out)
    if not main:
        tail = []
        if not has_custom_back:
            tail.append(NAV_BACK)
            amap[NAV_BACK] = 'nav_back'
        tail.append(NAV_HOME)
        amap[NAV_HOME] = 'back_to_main'
        rows.append(tail)
        for lab in tail:
            styles[lab] = NAV_FALLBACK_STYLE                  # Back and Home are blue
    _nav_remember_labels(amap)
    with NAV_LOCK:
        _nav_forget_old()
        st = NAV_STATE.get(chat_id) or _nav_blank()
        st.update({'map': amap, 'rows': rows, 'styles': styles, 'time': time.time(), 'await': False,
                   'live': getattr(menu, 'live', None)})
        st['seq'] += 1
        NAV_STATE[chat_id] = st
    return _nav_rows_to_markup(rows, styles)


def _nav_cancel_menu(chat_id):
    """Small keyboard shown while the bot waits for typed text or a file."""
    rows = [[NAV_CANCEL, NAV_HOME]]
    with NAV_LOCK:
        st = NAV_STATE.get(chat_id) or _nav_blank()
        styles = {NAV_CANCEL: 'danger', NAV_HOME: NAV_FALLBACK_STYLE}
        st.update({'map': {NAV_CANCEL: 'nav_cancel', NAV_HOME: 'back_to_main'}, 'rows': rows, 'styles': styles,
                   'time': time.time(), 'await': True, 'live': None})
        _nav_remember_labels(st['map'])
        st['seq'] += 1
        NAV_STATE[chat_id] = st
    return _nav_rows_to_markup(rows, styles)


def _nav_convert_markup(chat_id, menu):
    if isinstance(menu, NavMenu):
        if chat_id is None:
            return None
        return _nav_build(chat_id, menu)
    return menu


# --- fake "call" so the existing callback code runs unchanged ----------------------
class _NavMessage:
    def __init__(self, chat, user, text):
        self.chat = chat
        self.from_user = user
        self.message_id = -next(_NAV_CALL_COUNTER)     # negative: not a real Telegram message
        self.text = text
        self.reply_to_message = None
        self.content_type = 'text'
        self.date = int(time.time())


class _NavCall:
    def __init__(self, message, action):
        self.id = f"nav:{message.chat.id}:{next(_NAV_CALL_COUNTER)}"
        self.from_user = message.from_user
        self.data = action
        self.message = _NavMessage(message.chat, message.from_user, message.text)
        self.inline_message_id = None
        self.game_short_name = None


def _nav_run(message, action):
    """Run a callback action as if its button had been pressed (used by commands and keys)."""
    handle_callbacks(_NavCall(message, action))


_NAV_VIEW_PREFIXES = (
    'check_files', 'file_', 'user_account', 'my_running', 'user_help', 'admin_dashboard', 'admin_panel',
    'user_management', 'admin_settings', 'hosting_health', 'subscription', 'stats', 'manual_install',
    'manage_mandatory_channels', 'all_users', 'list_admins', 'system_info',
    'bot_performance', 'database_backup', 'speed', 'referral',
    'um_files', 'um_u_', 'um_f_', 'um_run', 'um_r_')


def _nav_lookup(st, text):
    if st is None:
        return None
    action = st['map'].get(text)
    if action is None:
        stripped = _nav_strip_squares(text)               # label from an old keyboard with a square in front
        if stripped != text:
            action = st['map'].get(stripped)
            if action is None and stripped.endswith('…'):
                hits = [a for lab, a in st['map'].items() if lab.startswith(stripped[:-1].rstrip())]
                if len(hits) == 1:
                    action = hits[0]
            if action is not None:
                return action
            text = stripped
    if action is None:
        # A key of an older keyboard whose live counter differs from today's ("All Users (2)" while the key now says
        # "All Users (5)"): compared without the trailing counter. Exact labels were tried first, every other digit
        # must match exactly, and the answer must be one single key.
        if _NAV_TRAIL_COUNT_RX.match(text).group(1) != text:
            base = _NAV_TRAIL_COUNT_RX.match(text).group(1)
            hits = [a for lab, a in st['map'].items()
                    if NAV_COUNTER_RX.search(lab) and _NAV_TRAIL_COUNT_RX.match(lab).group(1) == base]
            if len(hits) == 1:
                action = hits[0]
    return action


def _nav_is_label(message):
    try:
        if message.chat.type != 'private' or not message.text or message.text.startswith('/'):
            return False
        if message.text in NAV_RESERVED:
            return True
        return _nav_lookup(_nav_get(message.chat.id), message.text) is not None
    except Exception:
        return False


def _nav_show_main(message, note=None):
    uid = message.from_user.id
    if note:
        bot.send_message(message.chat.id, note, reply_markup=create_main_menu_inline(uid), parse_mode='HTML')
    else:
        _nav_run(message, 'back_to_main')


# Screens that open a paged list from the start: opening one of them again shows page 1.
_PAGER_ENTRY_ACTIONS = ('back_to_main', 'check_files', 'my_running', 'all_users', 'remove_mandatory_channel', 'user_account', 'admin_dashboard',
                        'um_files', 'um_run')


def _nav_live_markup(chat_id, user_id, force=False):
    """The keyboard to put on a message to this chat so that its numbers (for example All Users (3)) are the real ones now.
    It is the fresh build of the screen the person is on, when that screen shows live numbers. Nothing (None) while the
    chat waits for a typed answer (the Cancel key must stay) or sits on a screen without numbers. A chat the bot knows
    nothing about (restart) gets the main menu when force is set."""
    with NAV_LOCK:
        st = _nav_get(chat_id)
        if st is not None and st.get('await'):
            return None
        builder = st.get('live') if st else None
    if builder is None:
        if st is not None or not force:
            return None
        def builder(uid=user_id):
            return create_main_menu_inline(uid)
    try:
        return builder()
    except Exception:
        logger.exception("Could not build the fresh keyboard for chat %s", chat_id)
        return None


def _nav_refresh_chat(chat_id, user_id, note, force=False):
    """Send `note` with the fresh keyboard. Returns True when a message went out."""
    menu = _nav_live_markup(chat_id, user_id, force=force)
    if menu is None:
        return False
    return _safe_send(chat_id, note, reply_markup=menu) is not None


def _nav_forget_screens(except_chat=None):
    """After a full restore every remembered screen (file lists, pickers...) may describe things that are gone."""
    with NAV_LOCK:
        for cid in list(NAV_STATE):
            if cid != except_chat:
                NAV_STATE.pop(cid, None)
    with PAGER_LOCK:
        for cid in list(PAGER):
            if cid != except_chat:
                PAGER.pop(cid, None)


def _nav_page_turn(message, action):
    """Prev / Next / Page key of a paged list: remember the new page, then show the same list again (fresh data)."""
    try:
        head, key, view = action.split('|', 2)
        how = head[3:]
    except ValueError:
        _nav_stale(message)
        return
    if how not in ('prev', 'next', 'here') or not view:
        _nav_stale(message)
        return
    _pager_move(message.chat.id, key, how)
    _nav_run(message, view)


def _nav_dispatch(message):
    chat_id = message.chat.id
    text = message.text
    if _msg_already_seen(message):
        logger.info("Dropped a key press that was delivered twice (chat %s)", chat_id)
        return
    with NAV_LOCK:
        st = _nav_get(chat_id)
    if text == NAV_CANCEL:
        with NAV_LOCK:
            if st:
                st['await'] = False
        _nav_clear_input(message)
        _nav_show_main(message, ui_msg('❎', 'Cancelled', 'Cancel ho gaya.'))
        return
    if text in (NAV_HOME,) and _nav_lookup(st, text) is None:
        _nav_show_main(message)
        return
    action = _nav_lookup(st, text)
    if text == NAV_BACK and action is None:
        action = 'nav_back'
    if action is None:
        _nav_stale(message)
        return
    if action == 'nav_cancel':
        _nav_clear_input(message)
        _nav_show_main(message, ui_msg('❎', 'Cancelled', 'Cancel ho gaya.'))
        return
    if action.startswith('url:'):
        bot.send_message(chat_id, action[4:], disable_web_page_preview=False, ui_raw=True)
        return
    try:
        bot.clear_step_handler_by_chat_id(chat_id)        # a key press ends any typed prompt left over
    except Exception:
        pass
    if action.startswith('pg_'):
        with NAV_LOCK:
            if st is not None:
                st['await'] = False
        _nav_page_turn(message, action)
        return
    if action in _PAGER_ENTRY_ACTIONS:
        _pager_reset(chat_id)
    if action == 'back_to_main':
        _nav_clear_input(message)
    with NAV_LOCK:
        st = NAV_STATE.get(chat_id)
        if st is not None:
            st['await'] = False
        if action == 'nav_back':
            action = st['stack'].pop() if st and st['stack'] else 'back_to_main'
            if st:
                st['cur'] = None
        elif st is not None:
            if action == 'back_to_main':
                st['stack'] = []
                st['cur'] = None
            elif action.startswith(_NAV_VIEW_PREFIXES):
                if st['cur'] and st['cur'] != action:
                    st['stack'].append(st['cur'])
                    del st['stack'][:-NAV_BACK_STACK_MAX]
                st['cur'] = action
    _nav_run(message, action)


def _nav_clear_input(message):
    """Forget a half-finished typed input (Cancel, Home or /start pressed)."""
    with NAV_LOCK:
        st = NAV_STATE.get(message.chat.id)
        if st is not None:
            st['await'] = False
    try:
        bot.clear_step_handler_by_chat_id(message.chat.id)
    except Exception:
        pass
    try:
        _discard_wait(message.from_user.id)
    except Exception:
        pass
    try:
        _gh_cancel_user(message.from_user.id)
    except Exception:
        pass
    try:
        _dbf_wait_drop(message.from_user.id)
    except Exception:
        pass


def _nav_stale(message):
    """Text that matches no key of the current keyboard: put the keyboard back."""
    chat_id = message.chat.id
    st = _nav_get(chat_id)
    note = "Ye option ab available nahi hai. Neeche ke buttons se chuno 👇"
    if st and st.get('await'):
        with NAV_LOCK:
            st['await'] = False                          # nothing is waiting for an answer any more
        st = None
    if st and st.get('rows'):
        bot.send_message(chat_id, note, reply_markup=_nav_rows_to_markup(st['rows'], st.get('styles')))
    else:
        bot.send_message(chat_id, note, reply_markup=create_main_menu_inline(message.from_user.id))


def _nav_wrap_next_step(callback, owner=None):
    """A typed answer normally goes to the waiting step; a key label, Cancel or a /command re-routes.
    A prompt that waited longer than STEP_TTL, or a key label from an old keyboard, is never taken as the answer:
    that is how a forgotten prompt used to switch an option on later without any click.
    In a group only the person who started the prompt can answer it."""
    registered = time.time()

    def wrapped(message, *a, **kw):
        text = getattr(message, 'text', None)
        chat_id = message.chat.id
        expired = time.time() - registered > STEP_TTL
        if (owner is not None and message.from_user.id != owner and getattr(message.chat, 'type', 'private') != 'private'
                and not expired):
            # somebody else talking in the group: handle it normally and keep waiting for the right person
            bot.process_new_messages([message])
            if not bot.next_step_backend.handlers.get(chat_id):
                bot.next_step_backend.register_handler(chat_id, {'callback': wrapped, 'args': (), 'kwargs': {}})
            return
        if text:
            st = _nav_get(chat_id)
            if text == NAV_CANCEL or text == NAV_HOME or text.startswith('/') or _nav_lookup(st, text) is not None:
                try:
                    bot.clear_step_handler_by_chat_id(chat_id)
                except Exception:
                    pass
                if text.startswith('/'):
                    bot.process_new_messages([message])
                else:
                    _nav_dispatch(message)
                return
            if message.chat.type == 'private' and text in BUTTON_TEXT_TO_LOGIC and text not in LEGACY_TEXT_NEEDS_MENU:
                # an exact label of a harmless old key: the prompt is dropped and that key runs, it is never the answer
                try:
                    bot.clear_step_handler_by_chat_id(chat_id)
                except Exception:
                    pass
                _nav_clear_input(message)
                bot.process_new_messages([message])
                return
            if text in LEGACY_TEXT_NEEDS_MENU or _nav_is_old_key(text):
                # a key of an older keyboard, not an answer: forget the prompt and put the keyboard back
                try:
                    bot.clear_step_handler_by_chat_id(chat_id)
                except Exception:
                    pass
                _nav_clear_input(message)
                _nav_stale(message)
                return
        if expired:
            # Forgotten prompt: do not use this message as its answer. Handle it like any new message.
            try:
                bot.clear_step_handler_by_chat_id(chat_id)
            except Exception:
                pass
            _nav_clear_input(message)
            logger.info("Expired prompt dropped in chat %s", chat_id)
            if text and message.chat.type == 'private':
                _nav_show_main(message, ui_warn('Late Reply', 'Ye jawab bahut der baad aaya, isliye use nahi liya.', foot='Dobara button dabao.'))
            else:
                bot.process_new_messages([message])
            return
        if (not text and getattr(message, 'content_type', 'text') != 'text'
                and getattr(callback, '__name__', '') != 'process_broadcast_message'):
            # A photo / sticker / file sent where typed text is needed: ask again instead of crashing the step.
            try:
                bot.send_message(chat_id, "✍️ Yahan sirf text chahiye (photo/sticker/file nahi). Text bhejo ya ❌ Cancel dabao.")
                bot.next_step_backend.register_handler(chat_id, {'callback': wrapped, 'args': a, 'kwargs': kw})
            except Exception:
                logger.exception("Could not ask for text again")
            return
        before = (_nav_get(chat_id) or {}).get('seq', 0)
        _ACTOR.uid = message.from_user.id
        try:
            result = callback(message, *a, **kw)
        finally:
            _ACTOR.uid = None
        st = _nav_get(chat_id)
        if st is None or st.get('seq', 0) == before or st.get('await'):
            try:
                bot.send_message(chat_id, "🏠 Menu", reply_markup=create_main_menu_inline(message.from_user.id))
            except Exception:
                logger.exception("Could not restore the menu keyboard")
        return result
    return wrapped


def _nav_offer_cancel(message):
    """Called when a typed answer is awaited: make sure a Cancel key is on screen."""
    chat_id = message.chat.id
    st = _nav_get(chat_id)
    if st and any('cancel' in lab.lower() for lab in st['map']) and not st.get('await'):
        return
    bot.send_message(chat_id, "✍️ Apna jawab bhejo. Rukna ho to ❌ Cancel dabao.", reply_markup=_nav_cancel_menu(chat_id))


def _nav_convert_call(args, kwargs, chat_id):
    kwargs = dict(kwargs)
    args = list(args)
    for i, v in enumerate(args):
        if isinstance(v, NavMenu):
            args[i] = _nav_convert_markup(chat_id, v)
    if isinstance(kwargs.get('reply_markup'), NavMenu):
        kwargs['reply_markup'] = _nav_convert_markup(chat_id, kwargs['reply_markup'])
        if kwargs['reply_markup'] is None:
            kwargs.pop('reply_markup')
    rp = kwargs.get('reply_parameters')
    if rp is not None and (getattr(rp, 'message_id', 1) or 1) < 0:
        kwargs.pop('reply_parameters')
    if isinstance(kwargs.get('reply_to_message_id'), int) and kwargs['reply_to_message_id'] < 0:
        kwargs.pop('reply_to_message_id')
    return tuple(args), kwargs


# --- Animated progress message (ui_anim / ProgressMessage) ----------------------
# One status message that is edited a few times while the user waits: rotating hourglass, a real filling bar when the
# work is countable (done/total) and a full divider + elapsed time when it is not. Rules: one animated message per
# chat, edits at least PM_TICK seconds apart, flood / "not modified" / any other error never reaches the caller,
# a hard time cap, and finish()/fail() always replace the status with the final result. All drawing happens in one
# small daemon thread through the plain TeleBot call, so a rate limit never blocks the real operation.
PM_TICK = 1.5            # seconds between two edits of the same message
PM_MAX_SECONDS = 900     # the animation stops by itself after this long (the final result still replaces it)
PM_FRAMES = ('⏳', '⌛')
_PM_LOCK = threading.Lock()
_PM_ACTIVE = {}          # (chat_id, message_id) -> ProgressMessage that is animating that message
_PM_CHATS = {}           # chat_id -> ProgressMessage (only one animation per chat)


def _pm_preempt(chat_id, message_id):
    """An outside edit / delete of an animated message stops its animation first, so a late frame can never
    overwrite the new text."""
    try:
        pm = _PM_ACTIVE.get((chat_id, message_id))
        if pm is not None and threading.current_thread() is not pm._thread:
            pm._halt()
    except Exception:
        pass


def _pm_elapsed(seconds):
    seconds = max(0, int(seconds))
    return f"{seconds // 60}m {seconds % 60:02d}s" if seconds >= 60 else f"{seconds}s"


class ProgressMessage:
    """pm = ui_anim(chat_id, 'Restoring backup', 'Reading the file', message_id=None, message=None)
       pm.update(done, total, label)   # real progress (bar fills); pm.update(label='...') only changes the text
       pm.finish(text)  /  pm.fail(text)  # always replace the status with the final card; never raise"""

    def __init__(self, chat_id, title, label='', *, message_id=None, message=None, done=0, total=None,
                 enabled=True, max_seconds=PM_MAX_SECONDS):
        self.chat_id = chat_id
        self.title = str(title)
        self.label = label
        self.message = message
        self.message_id = message_id if isinstance(message_id, int) and message_id > 0 else None
        self.done = done
        self.total = total
        self.enabled = bool(enabled)
        self.max_seconds = max_seconds
        self.passive = False
        self._thread = None
        self._stop = threading.Event()
        self._lock = threading.Lock()
        self._t0 = time.time()
        self._tick = 0
        self._last_text = None
        self._next_ok = 0.0
        self._started = False
        self._done = False

    # -- drawing ----------------------------------------------------------------
    def progress(self):
        try:
            if self.total in (None, 0):
                return None
            return max(0.0, min(1.0, float(self.done) / float(self.total)))
        except (TypeError, ValueError, ZeroDivisionError):
            return None

    def _render(self, tick=None):
        with self._lock:
            title, label, done, total = self.title, self.label, self.done, self.total
        frac = self.progress()
        if tick is not None:
            self._tick = tick
        frame = PM_FRAMES[self._tick % len(PM_FRAMES)]
        lines = []
        if frac is not None:
            lines.append(f"📊 Progress: <b>{ui_esc(done)}/{ui_esc(total)}</b>")
        if label:
            lines.append(ui_esc(str(label)[:300]) if not isinstance(label, UIRaw) else str(label))
        lines.append(f"⏱ {_pm_elapsed(time.time() - self._t0)}")
        out = f"<b>{frame} {ui_esc(title)}</b>\n{ui_divider('⏳', frac)}\n" + '\n'.join(lines)
        return ui_cap(_ui_card(out))

    # -- lifecycle --------------------------------------------------------------
    def start(self):
        if not self.enabled or self._started:
            return self
        self._started = True
        self._t0 = time.time()
        with _PM_LOCK:
            other = _PM_CHATS.get(self.chat_id)
            if other is not None and other is not self:
                self.passive = True         # one animated message per chat: this one stays a still status
            else:
                _PM_CHATS[self.chat_id] = self
        text = self._render(0)
        try:
            if self.message_id is None:
                if self.message is not None:
                    sent = bot.reply_to(self.message, text, parse_mode='HTML')
                else:
                    sent = bot.send_message(self.chat_id, text, parse_mode='HTML')
                self.message_id = getattr(sent, 'message_id', None)
            else:
                bot.edit_message_text(text, self.chat_id, self.message_id, parse_mode='HTML')
            self._last_text = text
        except Exception as exc:
            logger.warning("Progress message could not be shown: %s", redact_secrets(exc))
        if self.message_id is None or self.passive:
            self._release()
            return self
        with _PM_LOCK:
            _PM_ACTIVE[(self.chat_id, self.message_id)] = self
        self._next_ok = time.time() + PM_TICK
        self._thread = threading.Thread(target=self._run, name='progress-anim', daemon=True)
        self._thread.start()
        return self

    def update(self, done=None, total=None, label=None, title=None):
        with self._lock:
            if done is not None:
                self.done = done
            if total is not None:
                self.total = total
            if label is not None:
                self.label = label
            if title is not None:
                self.title = str(title)
        return self

    def _run(self):
        floods = fails = 0
        tick = 0
        try:
            while not self._stop.wait(0.25):
                now = time.time()
                if now - self._t0 > self.max_seconds:
                    break
                if now < self._next_ok:
                    continue
                tick += 1
                text = self._render(tick)
                if text == self._last_text:
                    continue
                try:
                    if self._stop.is_set():
                        break
                    telebot.TeleBot.edit_message_text(bot, text, self.chat_id, self.message_id, parse_mode='HTML')
                    self._last_text = text
                    self._next_ok = time.time() + PM_TICK
                    floods = fails = 0
                except telebot.apihelper.ApiTelegramException as exc:
                    desc = str(exc).lower()
                    if 'message is not modified' in desc:
                        self._last_text = text
                        self._next_ok = time.time() + PM_TICK
                    elif getattr(exc, 'error_code', None) == 429 or 'too many requests' in desc:
                        floods += 1
                        if floods >= 3:
                            break
                        self._next_ok = time.time() + min(_retry_after_seconds(exc) + 1, 30)
                    elif 'not found' in desc or "can't be edited" in desc or 'message_id_invalid' in desc:
                        break
                    else:
                        fails += 1
                        if fails >= 3:
                            break
                        self._next_ok = time.time() + PM_TICK * 2
                except Exception:
                    fails += 1
                    if fails >= 3:
                        break
                    self._next_ok = time.time() + PM_TICK * 2
        except Exception:
            logger.exception("Progress animation stopped")
        finally:
            self._release()

    def _release(self):
        with _PM_LOCK:
            if self.message_id is not None and _PM_ACTIVE.get((self.chat_id, self.message_id)) is self:
                _PM_ACTIVE.pop((self.chat_id, self.message_id), None)
            if _PM_CHATS.get(self.chat_id) is self:
                _PM_CHATS.pop(self.chat_id, None)

    def _halt(self):
        self._stop.set()
        th = self._thread
        if th is not None and th is not threading.current_thread():
            th.join(timeout=20)
        self._release()

    def _deliver(self, text, parse_mode, reply_markup):
        kwargs = {}
        if parse_mode:
            kwargs['parse_mode'] = parse_mode
        if reply_markup is not None:
            kwargs['reply_markup'] = reply_markup
        try:
            if self.message_id is not None:
                return bot.edit_message_text(text, self.chat_id, self.message_id, **kwargs)
        except Exception as exc:
            logger.warning("Final progress edit failed, sending it as a new message: %s", redact_secrets(exc))
        try:
            return bot.send_message(self.chat_id, text, **kwargs)
        except Exception as exc:
            logger.warning("Final progress message could not be sent: %s", redact_secrets(exc))
        if kwargs.get('parse_mode'):
            # Last resort (for example a Markdown / HTML parse error): the same words as plain text.
            plain = re.sub(r'<[^>]+>', '', text) if kwargs['parse_mode'] == 'HTML' else text
            plain_kwargs = {k: v for k, v in kwargs.items() if k != 'parse_mode'}
            try:
                return bot.send_message(self.chat_id, html_unescape(plain) if kwargs['parse_mode'] == 'HTML' else plain, **plain_kwargs)
            except Exception as exc:
                logger.warning("Final progress plain message could not be sent: %s", redact_secrets(exc))
        return None

    def finish(self, text=None, *, parse_mode='HTML', reply_markup=None):
        """Stop the animation and replace the status with the final result (full divider). Never raises."""
        if self._done:
            return None
        self._done = True
        self._halt()
        if not self.enabled:
            return None
        if text is None:
            text = ui_ok(f"{self.title} done")
        return self._deliver(text, parse_mode, reply_markup)

    def fail(self, text=None, *, parse_mode='HTML', reply_markup=None):
        if text is None:
            text = ui_err(f"{self.title} failed", "Kuch gadbad ho gayi. Dobara try karo.")
        return self.finish(text, parse_mode=parse_mode, reply_markup=reply_markup)

    def __enter__(self):
        return self.start()

    def __exit__(self, exc_type, exc, tb):
        if not self._done:
            if exc_type is not None:
                self.fail()
            else:
                self.finish()
        return False


def ui_anim(chat_id, title, label='', **kwargs):
    """Start an animated status message and return it (see ProgressMessage)."""
    return ProgressMessage(chat_id, title, label, **kwargs).start()


class SafeTeleBot(telebot.TeleBot):
    """TeleBot whose common calls survive the usual harmless Telegram errors:
    rate limits (429) are waited out, 'message is not modified' is ignored, broken
    Markdown/HTML falls back to plain text and stale button presses do not raise."""

    @staticmethod
    def _soften_markup(args, kwargs, kind, level):
        """After Telegram refused the formatting: level 1 = an expandable quote becomes a plain quote (still HTML),
        level 2 = plain text without tags. Returns (args, kwargs)."""
        kwargs = dict(kwargs)
        args = list(args)
        pos = {'send_message': 1, 'edit_message_text': 0}.get(kind)
        key = 'text' if 'text' in kwargs else ('caption' if 'caption' in kwargs else None)
        text = kwargs.get(key) if key else (args[pos] if pos is not None and len(args) > pos else None)
        if isinstance(text, str):
            if level == 1:
                new = text.replace('<blockquote expandable>', '<blockquote>')
            else:
                new = html_unescape(re.sub(r'</?(?:b|i|u|s|code|pre|a|blockquote|tg-spoiler)(?:\s[^<>]*)?>', '', text)) if kwargs.get('parse_mode') == 'HTML' else text
            if key:
                kwargs[key] = new
            elif pos is not None and len(args) > pos:
                args[pos] = new
        if level >= 2:
            kwargs['parse_mode'] = None
        return tuple(args), kwargs

    def _guard(self, parent, args, kwargs, kind):
        soft = 0
        for attempt in range(5):
            try:
                return parent(*args, **kwargs)
            except telebot.apihelper.ApiTelegramException as exc:
                desc = str(exc).lower()
                code = getattr(exc, 'error_code', None)
                if code == 429 or 'too many requests' in desc:
                    wait = min(_retry_after_seconds(exc) + 1, 60)
                    logger.warning("Telegram rate limit on %s; waiting %ss (try %s)", kind, wait, attempt + 1)
                    time.sleep(wait)
                    continue
                if 'message is not modified' in desc:
                    return None
                if kind == 'answer_callback_query' and ('query is too old' in desc or 'query id is invalid' in desc):
                    return None
                if kind == 'delete_message' and ('message to delete not found' in desc or "can't be deleted" in desc):
                    return None
                if "can't parse entities" in desc and kwargs.get('parse_mode'):
                    soft += 1
                    if soft == 1 and kwargs.get('parse_mode') == 'HTML' and 'expandable' in (str(kwargs.get('text') or kwargs.get('caption') or '') + ''.join(str(a) for a in args if isinstance(a, str))):
                        logger.warning("Expandable quote rejected by Telegram on %s; resending as a normal quote", kind)
                        args, kwargs = self._soften_markup(args, kwargs, kind, 1)
                        continue
                    logger.warning("Formatting rejected by Telegram on %s; resending as plain text", kind)
                    args, kwargs = self._soften_markup(args, kwargs, kind, 2)
                    continue
                if 'message is too long' in desc and kind in ('send_message', 'edit_message_text'):
                    args, kwargs = _truncate_text_args(args, kwargs)
                    continue
                raise
            except requests.exceptions.RequestException as exc:
                if attempt >= 2:
                    raise
                logger.warning("Network problem on %s (%s); retrying", kind, type(exc).__name__)
                time.sleep(2 * (attempt + 1))
        return None

    def _nav_args(self, args, kwargs, chat_pos=0):
        chat_id = kwargs.get('chat_id', args[chat_pos] if len(args) > chat_pos else None)
        return _nav_convert_call(args, kwargs, chat_id)

    def reply_to(self, message, text, **kwargs):
        # A script started by the boot auto-resume is announced once per user in a summary, not once per script.
        if getattr(message, 'quiet', False) and ui_lead(text).startswith(('✅', '🔄')):
            return None
        return super().reply_to(message, text, **kwargs)

    @staticmethod
    def _polish(args, kwargs, text_pos):
        """Run the outgoing text through ui_polish (unless it was sent with ui_raw=True or has entities)."""
        if kwargs.pop('ui_raw', False) or kwargs.get('entities'):
            return args, kwargs
        kwargs = dict(kwargs)
        args = list(args)
        in_kwargs = 'text' in kwargs
        text = kwargs['text'] if in_kwargs else (args[text_pos] if len(args) > text_pos else None)
        new_text, new_mode = ui_polish(text, kwargs.get('parse_mode'))
        if in_kwargs:
            kwargs['text'] = new_text
        elif len(args) > text_pos:
            args[text_pos] = new_text
        else:
            return tuple(args), kwargs
        if new_mode:
            kwargs['parse_mode'] = new_mode
        return tuple(args), kwargs

    def send_message(self, *args, **kwargs):
        args, kwargs = self._polish(args, kwargs, 1)
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_message, args, kwargs, 'send_message')

    def edit_message_text(self, *args, **kwargs):
        args, kwargs = self._polish(args, kwargs, 0)
        text = kwargs.get('text', args[0] if args else '')
        chat_id = kwargs.get('chat_id', args[1] if len(args) > 1 else None)
        message_id = kwargs.get('message_id', args[2] if len(args) > 2 else None)
        menu = kwargs.get('reply_markup')
        virtual = isinstance(message_id, int) and message_id < 0
        _pm_preempt(chat_id, message_id)
        if isinstance(menu, NavMenu) or (virtual and chat_id is not None):
            # A reply keyboard cannot be attached by editing, so the screen is sent as a new message
            # and the old one is removed when it is a real message.
            send_kwargs = {k: kwargs[k] for k in ('parse_mode', 'entities', 'disable_web_page_preview') if k in kwargs}
            if menu is not None:
                send_kwargs['reply_markup'] = menu
            sent = self.send_message(chat_id, text, **send_kwargs)
            if isinstance(menu, NavMenu) and isinstance(message_id, int) and message_id > 0:
                try:
                    self.delete_message(chat_id, message_id)
                except Exception:
                    pass
            return sent
        return self._guard(super().edit_message_text, args, kwargs, 'edit_message_text')

    def edit_message_reply_markup(self, *args, **kwargs):
        chat_id = kwargs.get('chat_id', args[0] if args else None)
        menu = kwargs.get('reply_markup')
        if isinstance(menu, NavMenu):
            if chat_id is None:
                return None
            return self.send_message(chat_id, "🔄 Menu update ho gaya.", reply_markup=menu)
        message_id = kwargs.get('message_id', args[1] if len(args) > 1 else None)
        if isinstance(message_id, int) and message_id < 0:
            return None
        try:
            return self._guard(super().edit_message_reply_markup, args, kwargs, 'edit_message_reply_markup')
        except Exception as exc:
            logger.warning("edit_message_reply_markup skipped: %s", redact_secrets(exc))
            return None

    def answer_callback_query(self, *args, **kwargs):
        qid = kwargs.get('callback_query_id', args[0] if args else '')
        if isinstance(qid, str) and qid.startswith('nav:'):
            text = kwargs.get('text', args[1] if len(args) > 1 else None)
            if text:
                try:
                    self.send_message(int(qid.split(':')[1]), ui_polish_toast(text))
                except Exception:
                    logger.warning("Could not send the notice for a key press")
            return True
        if isinstance(kwargs.get('text'), str):
            kwargs['text'] = ui_polish_toast(kwargs['text'])
        elif len(args) > 1 and isinstance(args[1], str):
            args = (args[0], ui_polish_toast(args[1])) + tuple(args[2:])
        return self._guard(super().answer_callback_query, args, kwargs, 'answer_callback_query')

    def delete_message(self, *args, **kwargs):
        message_id = kwargs.get('message_id', args[1] if len(args) > 1 else None)
        if isinstance(message_id, int) and message_id < 0:
            return True
        _pm_preempt(kwargs.get('chat_id', args[0] if args else None), message_id)
        return self._guard(super().delete_message, args, kwargs, 'delete_message')

    def register_next_step_handler(self, message, callback, *args, **kwargs):
        try:
            _nav_offer_cancel(message)
        except Exception:
            logger.exception("Could not show the Cancel key")
        # one prompt per chat: an older unanswered prompt must never fire together with (or instead of) this one
        try:
            self.clear_step_handler_by_chat_id(message.chat.id)
        except Exception:
            pass
        return super().register_next_step_handler(
            message, _nav_wrap_next_step(callback, getattr(_ACTOR, 'uid', None)), *args, **kwargs)

    def process_new_updates(self, updates):
        """An update that was already handled (same update_id) is dropped."""
        fresh = [u for u in updates if not _update_already_seen(getattr(u, 'update_id', None))]
        if len(fresh) != len(updates):
            logger.info("Dropped %s re-delivered update(s)", len(updates) - len(fresh))
        return super().process_new_updates(fresh)

    def send_document(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        cap = kwargs.get('caption')
        if isinstance(cap, str) and str(kwargs.get('parse_mode') or '').upper() == 'HTML':
            carded = _ui_card(cap)          # same quote-block look as a normal message
            if len(carded) <= 1024:
                kwargs['caption'] = carded
        return self._guard(super().send_document, args, kwargs, 'send_document')

    def send_photo(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_photo, args, kwargs, 'send_photo')

    def send_video(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_video, args, kwargs, 'send_video')

    def send_audio(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_audio, args, kwargs, 'send_audio')

    def send_voice(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_voice, args, kwargs, 'send_voice')

    def send_sticker(self, *args, **kwargs):
        args, kwargs = self._nav_args(args, kwargs)
        return self._guard(super().send_sticker, args, kwargs, 'send_sticker')


_HTML_TAG_RX = re.compile(r'<(/?)([a-zA-Z][a-zA-Z0-9-]*)[^<>]*>')
_HTML_PAIRED = ('b', 'strong', 'i', 'em', 'u', 'ins', 's', 'strike', 'del', 'code', 'pre', 'a', 'tg-spoiler', 'blockquote')


def _html_close_open_tags(chunk):
    """Cut text may end inside a tag or entity, or leave tags open: Telegram then rejects the whole message.
    Drop a half tag / half entity at the end and close what is still open."""
    cut = chunk.rfind('<')
    if cut != -1 and chunk.find('>', cut) == -1:
        chunk = chunk[:cut]
    amp = chunk.rfind('&')
    if amp != -1 and ';' not in chunk[amp:] and len(chunk) - amp <= 10:
        chunk = chunk[:amp]
    stack = []
    for m in _HTML_TAG_RX.finditer(chunk):
        name = m.group(2).lower()
        if name not in _HTML_PAIRED:
            continue
        if m.group(1):
            if name in stack:
                while stack and stack.pop() != name:
                    pass
        else:
            stack.append(name)
    return chunk + ''.join(f'</{name}>' for name in reversed(stack))


def _html_open_tags(chunk):
    """[(name, raw tag)] of the paired tags still open at the end of `chunk`."""
    stack = []
    for m in _HTML_TAG_RX.finditer(chunk):
        name = m.group(2).lower()
        if name not in _HTML_PAIRED:
            continue
        if m.group(1):
            for idx in range(len(stack) - 1, -1, -1):
                if stack[idx][0] == name:
                    del stack[idx:]
                    break
        else:
            stack.append((name, m.group(0)))
    return stack


def _split_text(text, limit=3900, html=True):
    """Split a long text into messages of at most `limit` characters, cutting at line ends (a very long line is cut
    anywhere). With html=True every part is a valid HTML message: tags that were open at the cut are closed there and
    opened again on the next part. Always returns at least one part."""
    text = str(text if text is not None else '')
    limit = max(300, int(limit))
    if len(text) <= limit:
        return [text]
    room = limit - 120                      # space kept for re-opened and closing tags
    parts, current, carried = [], '', []

    def flush():
        nonlocal current, carried
        body, current = current, ''
        if not body.strip():
            return
        if html:
            chunk = ''.join(raw for _, raw in carried) + body
            carried = _html_open_tags(chunk)
            chunk += ''.join(f'</{name}>' for name, _ in reversed(carried))
        else:
            chunk = body
        parts.append(chunk)

    for line in text.split('\n'):
        while len(line) > room:
            if current:
                flush()
            piece = line[:room]
            if html:
                lt = piece.rfind('<')
                if lt > 0 and piece.find('>', lt) == -1:
                    piece = piece[:lt]
            amp = piece.rfind('&')
            if amp > 0 and ';' not in piece[amp:] and len(piece) - amp <= 10:
                piece = piece[:amp]
            current = piece
            flush()
            line = line[len(piece):]
        if current and len(current) + len(line) + 1 > room:
            flush()
        current = current + ('\n' if current else '') + line
    flush()
    return parts or ['']


def _send_long(chat_id, text, reply_markup=None, **kwargs):
    """Send a long HTML text as several messages (the keyboard goes on the last one). Returns the last message sent."""
    sent = None
    parts = _split_text(text)
    for idx, part in enumerate(parts):
        extra = dict(kwargs)
        if reply_markup is not None and idx == len(parts) - 1:
            extra['reply_markup'] = reply_markup
        if idx > 0:
            extra['ui_raw'] = True
        sent = _safe_send(chat_id, part, **extra) or sent
    return sent


def _truncate_text_args(args, kwargs):
    """Cut an over-long text to Telegram's 4096-character limit (HTML stays valid)."""
    notice = "\n...(shortened)"
    html = (kwargs.get('parse_mode') or '').upper() == 'HTML'

    def cut(value):
        head = value[:4096 - len(notice) - 40]
        if html:
            nl = head.rfind('\n')
            if nl > len(head) // 2:
                head = head[:nl]
            head = _html_close_open_tags(head)
        return head + notice

    kwargs = dict(kwargs)
    if 'text' in kwargs:
        kwargs['text'] = cut(str(kwargs['text']))
        return args, kwargs
    args = list(args)
    # send_message(chat_id, text) / edit_message_text(text, chat_id, message_id)
    for idx, value in enumerate(args):
        if isinstance(value, str) and len(value) > 4000:
            args[idx] = cut(value)
            break
    return tuple(args), kwargs


def safe_text(text, limit=4000):
    """Shorten text for a single Telegram message."""
    text = str(text)
    if len(text) <= limit:
        return text
    return text[:limit - 20] + "\n...(shortened)"


class GlobalErrorHandler(telebot.ExceptionHandler):
    """Last line of defence: an error inside any handler is logged, never kills polling."""

    def handle(self, exception):
        HEALTH_STATE['last_error'] = f"{type(exception).__name__}: {redact_secrets(exception)}"[:300]
        logger.error("Unhandled error in a bot handler: %s", redact_secrets(exception),
                     exc_info=(type(exception), exception, exception.__traceback__))
        return True


# Initialize bot
bot = SafeTeleBot(BOT_TOKEN, threaded=True, num_threads=20, skip_pending=True,
                  exception_handler=GlobalErrorHandler())


# --- Command Button Layouts ---
COMMAND_BUTTONS_LAYOUT_USER_SPEC = [
    ["📢 Updates Channel"],
    ["📤 Upload File", "📂 Check Files"],
    ["⚡ Bot Speed", "📊 Statistics"],
    ["👥 Referral", "📞 Contact Owner"],
    ["📦 Manual Install", "🆘 Help"]
]

ADMIN_COMMAND_BUTTONS_LAYOUT_USER_SPEC = [
    ["📢 Updates Channel"],
    ["📤 Upload File", "📂 Check Files"],
    ["⚡ Bot Speed", "📊 Statistics"],
    ["💳 Subscriptions", "📢 Broadcast"],
    ["👥 Referral"],
    ["🔒 Lock Bot", "🟢 Running All Code"],
    ["👑 Admin Panel", "📞 Contact Owner"],
    ["📢 Channel Add", "🛠️ Manual Install"],
    ["👥 User Management", "⚙️ Settings"],
    ["🩺 Hosting Health"]
]

# --- Database Setup ---
def db_connect():
    """Open a SQLite connection that waits for locks instead of failing right away.
    Callers hold DB_LOCK around read/write work, so connections are never shared between threads."""
    conn = sqlite3.connect(DATABASE_PATH, timeout=30, check_same_thread=False)
    conn.execute("PRAGMA busy_timeout=30000")
    return conn


def _ensure_extra_tables(c):
    """Tables of the referral system and the scheduled restart. Also run before loading, because a database
    restored from an older backup does not have them yet."""
    # One row per referred user: a person can only ever be referred once, so the same user cannot be counted twice.
    c.execute('''CREATE TABLE IF NOT EXISTS referrals
                 (referred_id INTEGER PRIMARY KEY, referrer_id INTEGER, created_at TEXT)''')
    c.execute('CREATE INDEX IF NOT EXISTS idx_referrals_referrer ON referrals (referrer_id)')
    c.execute('''CREATE TABLE IF NOT EXISTS scheduled_restart_optout
                 (script_key TEXT PRIMARY KEY, set_by INTEGER, set_date TEXT)''')
    # Admin user management: hosting suspension and temporary bans.
    c.execute('''CREATE TABLE IF NOT EXISTS suspended_users
                 (user_id INTEGER PRIMARY KEY, reason TEXT, suspended_by INTEGER, suspend_date TEXT, auto INTEGER DEFAULT 0)''')
    c.execute('''CREATE TABLE IF NOT EXISTS temp_bans
                 (user_id INTEGER PRIMARY KEY, until TEXT, reason TEXT, banned_by INTEGER, ban_date TEXT)''')
    # Scripts that were running and should start again after a restart or redeploy (cleared on every deliberate stop).
    c.execute('''CREATE TABLE IF NOT EXISTS autostart
                 (script_key TEXT PRIMARY KEY, owner_id INTEGER, file_name TEXT, file_type TEXT, set_date TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS scan_strikes
                 (user_id INTEGER PRIMARY KEY, strikes INTEGER DEFAULT 0, last_file TEXT, last_reason TEXT, last_date TEXT)''')


def init_db():
    """Initialize the database with required tables"""
    logger.info(f"Initializing database at: {DATABASE_PATH}")
    try:
        conn = db_connect()
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA busy_timeout=30000")
        c = conn.cursor()
        c.execute('''CREATE TABLE IF NOT EXISTS subscriptions
                     (user_id INTEGER PRIMARY KEY, expiry TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS user_files
                     (user_id INTEGER, file_name TEXT, file_type TEXT,
                      PRIMARY KEY (user_id, file_name))''')
        c.execute('''CREATE TABLE IF NOT EXISTS active_users
                     (user_id INTEGER PRIMARY KEY, join_date TEXT, last_seen TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS admins
                     (user_id INTEGER PRIMARY KEY, added_by INTEGER, added_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS banned_users
                     (user_id INTEGER PRIMARY KEY, reason TEXT, banned_by INTEGER, ban_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS user_limits
                     (user_id INTEGER PRIMARY KEY, file_limit INTEGER, set_by INTEGER, set_date TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS mandatory_channels
                     (channel_id TEXT PRIMARY KEY, 
                      channel_username TEXT,
                      channel_name TEXT,
                      invite_link TEXT DEFAULT '',
                      added_by INTEGER,
                      added_date TEXT)''')
        # Migrate databases created by older releases without invite_link.
        c.execute('PRAGMA table_info(mandatory_channels)')
        channel_columns = {row[1] for row in c.fetchall()}
        if 'invite_link' not in channel_columns:
            c.execute("ALTER TABLE mandatory_channels ADD COLUMN invite_link TEXT DEFAULT ''")

        c.execute('''CREATE TABLE IF NOT EXISTS install_logs
                     (id INTEGER PRIMARY KEY AUTOINCREMENT,
                      user_id INTEGER,
                      module_name TEXT,
                      package_name TEXT,
                      status TEXT,
                      log TEXT,
                      install_date TEXT)''')
        
        # Legacy tables of removed features (upload scan, reviews, AI, trusted users). Nothing reads or writes them any more;
        # they stay only so that old databases and old backups keep loading.
        c.execute('''CREATE TABLE IF NOT EXISTS file_scans
                     (user_id INTEGER, file_name TEXT, level TEXT, score INTEGER,
                      reasons TEXT, sha256 TEXT, scanned_at TEXT, decision TEXT DEFAULT '',
                      PRIMARY KEY (user_id, file_name))''')
        c.execute('''CREATE TABLE IF NOT EXISTS pending_reviews
                     (token TEXT PRIMARY KEY, user_id INTEGER, file_name TEXT, file_type TEXT,
                      level TEXT, score INTEGER, reasons TEXT, sha256 TEXT, created REAL,
                      chat_id INTEGER, msg_id INTEGER, uploader TEXT, admin_msgs TEXT, kind TEXT)''')
        c.execute('PRAGMA table_info(file_scans)')
        scan_columns = {row[1] for row in c.fetchall()}
        if 'ai_verdict' not in scan_columns:
            c.execute("ALTER TABLE file_scans ADD COLUMN ai_verdict TEXT DEFAULT ''")
        if 'ai_note' not in scan_columns:
            c.execute("ALTER TABLE file_scans ADD COLUMN ai_note TEXT DEFAULT ''")
        if 'scan_mode' not in scan_columns:
            c.execute("ALTER TABLE file_scans ADD COLUMN scan_mode TEXT DEFAULT ''")
        if 'ai_model' not in scan_columns:
            c.execute("ALTER TABLE file_scans ADD COLUMN ai_model TEXT DEFAULT ''")
        c.execute('''CREATE TABLE IF NOT EXISTS ai_scan_cache
                     (cache_key TEXT PRIMARY KEY, sha256 TEXT, model TEXT, verdict TEXT,
                      confidence REAL, reason TEXT, files TEXT, created REAL)''')
        c.execute('''CREATE TABLE IF NOT EXISTS ai_scan_log
                     (id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, user_id INTEGER, file_name TEXT,
                      status TEXT, verdict TEXT, confidence REAL, ms INTEGER, note TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS trusted_users
                     (user_id INTEGER PRIMARY KEY, added_by INTEGER, added_date TEXT, note TEXT DEFAULT '')''')
        c.execute('''CREATE TABLE IF NOT EXISTS trusted_audit
                     (id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, action TEXT, user_id INTEGER,
                      actor_id INTEGER, note TEXT DEFAULT '')''')
        _ensure_extra_tables(c)
        c.execute('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                  (OWNER_ID, OWNER_ID, datetime.now().isoformat()))
        if ADMIN_ID != OWNER_ID:
            c.execute('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                      (ADMIN_ID, OWNER_ID, datetime.now().isoformat()))
        conn.commit()
        conn.close()
        logger.info("Database initialized successfully.")
    except Exception as e:
        logger.critical(f"❌ Database initialization error: {e}", exc_info=True)
        raise

def load_data():
    """Load data from database into memory"""
    logger.info("Loading data from database...")
    conn = None
    try:
        conn = db_connect()
        c = conn.cursor()

        # Load subscriptions
        c.execute('SELECT user_id, expiry FROM subscriptions')
        for user_id, expiry in c.fetchall():
            try:
                user_subscriptions[user_id] = {'expiry': datetime.fromisoformat(expiry)}
            except ValueError:
                logger.warning(f"⚠️ Invalid expiry date format for user {user_id}: {expiry}. Skipping.")

        # Load user files
        c.execute('SELECT user_id, file_name, file_type FROM user_files')
        for user_id, file_name, file_type in c.fetchall():
            if user_id not in user_files:
                user_files[user_id] = []
            user_files[user_id].append((file_name, file_type))

        # Load active users
        c.execute('SELECT user_id FROM active_users')
        active_users.update(user_id for (user_id,) in c.fetchall())

        # Load admins
        c.execute('SELECT user_id FROM admins')
        admin_ids.update(user_id for (user_id,) in c.fetchall())

        # Load banned users
        c.execute('SELECT user_id FROM banned_users')
        banned_users.update(user_id for (user_id,) in c.fetchall())

        # Load the scripts that opted out of the scheduled restart
        _ensure_extra_tables(c)
        SCHEDULED_RESTART_OPTOUT.clear()
        c.execute('SELECT script_key FROM scheduled_restart_optout')
        SCHEDULED_RESTART_OPTOUT.update(key for (key,) in c.fetchall())

        # Load suspended users and temporary bans
        suspended_users.clear()
        c.execute('SELECT user_id FROM suspended_users')
        suspended_users.update(user_id for (user_id,) in c.fetchall())
        temp_bans.clear()
        c.execute('SELECT user_id, until FROM temp_bans')
        for user_id, until in c.fetchall():
            try:
                temp_bans[user_id] = datetime.fromisoformat(until)
            except (TypeError, ValueError):
                logger.warning(f"⚠️ Invalid temp ban end for user {user_id}: {until}. Skipping.")

        # Load user limits
        c.execute('SELECT user_id, file_limit FROM user_limits')
        for user_id, file_limit in c.fetchall():
            user_limits[user_id] = file_limit

        # Load mandatory channels
        c.execute('SELECT channel_id, channel_username, channel_name, invite_link FROM mandatory_channels')
        for channel_id, channel_username, channel_name, invite_link in c.fetchall():
            mandatory_channels[channel_id] = {
                'username': channel_username,
                'name': channel_name,
                'invite_link': invite_link or ''
            }

        logger.info(f"Data loaded: {len(active_users)} users, {len(user_subscriptions)} subscriptions, {len(admin_ids)} admins, {len(banned_users)} banned users, {len(user_limits)} custom limits, {len(mandatory_channels)} mandatory channels.")
    except Exception as e:
        logger.error(f"❌ Error loading data: {e}", exc_info=True)
    finally:
        if conn is not None:
            conn.close()

# Initialize DB and Load Data at startup
try:
    init_db()
except Exception:
    sys.stderr.write("ERROR: the database could not be created. Check that the folder is writable. See the log for details.\n")
    sys.exit(1)
load_data()

# --- Upload helpers ---

class _ChatRef:
    def __init__(self, ident):
        self.id = ident


class _ReplyTarget:
    """Stand-in for a Telegram message when feedback must go to someone else (for example the user
    whose GitHub deploy is running). Only .chat.id, .message_id and .from_user.id are used."""
    def __init__(self, chat_id, message_id, user_id):
        self.chat = _ChatRef(chat_id)
        self.message_id = message_id
        self.from_user = _ChatRef(user_id)


def _remove_quietly(path):
    try:
        if path and os.path.isfile(path):
            os.remove(path)
    except OSError as exc:
        logger.warning('Could not remove %s: %s', path, exc)


def _file_sha256(path):
    """SHA-256 of a file on disk (streamed), or None when it cannot be read."""
    digest = hashlib.sha256()
    try:
        with open(path, 'rb') as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b''):
                digest.update(block)
    except OSError:
        return None
    return digest.hexdigest()


def _safe_send(chat_id, text, **kwargs):
    try:
        return bot.send_message(chat_id, text, parse_mode='HTML', **kwargs)
    except Exception as exc:
        logger.warning('Could not message %s: %s', chat_id, type(exc).__name__)
        return None


def _deploy_upload(user_id, file_name, file_type, data, reply_obj):
    """Store an upload and start it through the normal launch path. Returns (ok, error_text)."""
    user_folder = get_user_folder(user_id)
    if file_type == 'zip':
        temp_dir = tempfile.mkdtemp(prefix=f'user_{user_id}_zip_')
        try:
            zip_path = os.path.join(temp_dir, file_name)
            with open(zip_path, 'wb') as handle:
                handle.write(data)
            ok = process_zip_file(zip_path, user_id, user_folder, file_name, reply_obj, temp_dir)
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)
        return bool(ok), ('' if ok else 'The archive could not be set up. The reason was sent to you.')
    file_path = os.path.join(user_folder, file_name)
    try:
        fd = os.open(file_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    except FileExistsError:
        return False, f'{file_name} already exists in your storage. Rename it or delete the old one first.'
    with os.fdopen(fd, 'wb') as handle:
        handle.write(data)
    if file_type == 'js':
        handle_js_file(file_path, user_id, user_folder, file_name, reply_obj)
    else:
        handle_py_file(file_path, user_id, user_folder, file_name, reply_obj)
    return True, ''


def _start_hosted(owner_id, file_name, file_type, reply_obj):
    user_folder = get_user_folder(owner_id)
    file_path = os.path.join(user_folder, file_name)
    _reset_restart_state(owner_id, file_name)
    target = run_js_script if file_type == 'js' else run_script
    threading.Thread(target=target, args=(file_path, owner_id, user_folder, file_name, reply_obj)).start()


# ---- launch gate ------------------------------------------------------------------------------
def launch_gate(owner_id, file_name, file_type, actor_id, queue=True, admin_override=True):
    """Decide whether a hosted file may be started. Returns (allowed, note_html).
    A suspended user's files never start, whoever asks. With SANDBOX_MODE=strict nothing starts on a server
    where no real isolation works. Everything else starts directly (no content scan, no approval step)."""
    if not sandbox_allows_start():
        return False, ui_err('Start Blocked', 'Is server par real sandbox isolation available nahi hai aur strict mode on hai, isliye koi script start nahi hogi.',
                             foot='Admin se baat karo.')
    if owner_id in suspended_users and owner_id not in admin_ids:
        return False, ui_err('Hosting Suspended', 'Hosting is suspended for this account, so nothing can be started.',
                             foot='Contact an admin if you think this is a mistake.')
    return True, ''



# --- Mandatory Channels Functions ---
_MEMBER_CACHE = {}          # (user_id, channel_id) -> time of last positive answer
_MEMBER_CACHE_TTL = 120     # seconds; avoids asking Telegram on every single button press
_MEMBER_CACHE_MAX = 5000


def is_user_member(user_id, channel_id):
    """Check if user is member of a channel (positive answers are cached for a short time)"""
    cache_key = (user_id, str(channel_id))
    now = time.time()
    cached_at = _MEMBER_CACHE.get(cache_key)
    if cached_at is not None and now - cached_at < _MEMBER_CACHE_TTL:
        return True
    try:
        chat_member = bot.get_chat_member(channel_id, user_id)
        is_member = (chat_member.status in ['member', 'administrator', 'creator'] or (chat_member.status == 'restricted' and bool(getattr(chat_member, 'is_member', False))))
        if is_member:
            if len(_MEMBER_CACHE) >= _MEMBER_CACHE_MAX:
                _MEMBER_CACHE.clear()
            _MEMBER_CACHE[cache_key] = now
        else:
            _MEMBER_CACHE.pop(cache_key, None)
        return is_member
    except Exception as e:
        logger.error(f"Error checking channel membership for {user_id} in {channel_id}: {e}")
        return False

def check_mandatory_subscription(user_id):
    """Check if user is subscribed to all mandatory channels"""
    if not mandatory_channels:
        return True, []  # No mandatory channels exist
    
    not_joined = []
    for channel_id, channel_info in list(mandatory_channels.items()):
        if not is_user_member(user_id, channel_id):
            not_joined.append((channel_id, channel_info))
    
    if not_joined:
        return False, not_joined
    return True, []

def save_mandatory_channel(channel_id, channel_username, channel_name, added_by, invite_link=''):
    """Save mandatory channel to database"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            added_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO mandatory_channels (channel_id, channel_username, channel_name, invite_link, added_by, added_date) VALUES (?, ?, ?, ?, ?, ?)',
                      (channel_id, channel_username, channel_name, invite_link or '', added_by, added_date))
            conn.commit()
            mandatory_channels[channel_id] = {
                'username': channel_username,
                'name': channel_name,
                'invite_link': invite_link or ''
            }
            logger.info(f"Saved mandatory channel: {channel_name} ({channel_id})")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error saving channel: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error saving channel: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def remove_mandatory_channel_db(channel_id):
    """Remove mandatory channel from database"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM mandatory_channels WHERE channel_id = ?', (channel_id,))
            conn.commit()
            if channel_id in mandatory_channels:
                del mandatory_channels[channel_id]
            logger.info(f"Removed mandatory channel: {channel_id}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error removing channel: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error removing channel: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def create_mandatory_channels_menu():
    """Create mandatory channels management menu"""
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('➕ Add Channel', callback_data='add_mandatory_channel'),
        NavButton('➖ Remove Channel', callback_data='remove_mandatory_channel')
    )
    markup.row(NavButton('📋 List Channels', callback_data='list_mandatory_channels'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_check_message(not_joined_channels):
    """Create subscription verification message"""
    message = ui_head('📢', 'Join Our Channels First') + "\n"
    message += f"🔒 Access: {ui_tag('locked', 'JOIN REQUIRED')}\n\n"
    
    markup = NavMenu()
    
    for channel_id, channel_info in not_joined_channels:
        channel_username = channel_info.get('username', '')
        channel_name = channel_info.get('name', 'Channel')
        
        invite_link = channel_info.get('invite_link', '')
        if channel_username:
            channel_link = f"https://t.me/{channel_username.replace('@', '')}"
        elif invite_link:
            channel_link = invite_link
        else:
            channel_link = None

        message += f"• <b>{html_escape(str(channel_name))}</b>\n"
        if channel_link:
            markup.add(NavButton(f"📢 Join {channel_name}"[:64], url=channel_link))
        else:
            message += "  <i>Private invite link unavailable; contact the bot owner.</i>\n"
    
    markup.add(NavButton("✅ Verify Subscription", callback_data='check_subscription_status'))
    message += "\n" + ui_steps('Tap Join on each channel above', 'Come back here', 'Tap <b>Verify Subscription</b>') + "\n" + ui_note("Bot unlocks the moment you are verified.")
    
    return message, markup


# --- User Management Functions ---
def is_user_banned(user_id):
    """Check if user is banned"""
    return user_id in banned_users

def ban_user_db(user_id, reason, banned_by, until=None):
    """Ban a user. `until` (a datetime) makes it a temporary ban that the temp-ban loop lifts by itself;
    without it the ban is permanent and any temporary end date of an earlier ban is dropped."""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            ban_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO banned_users (user_id, reason, banned_by, ban_date) VALUES (?, ?, ?, ?)',
                      (user_id, reason, banned_by, ban_date))
            if until is not None:
                c.execute('INSERT OR REPLACE INTO temp_bans (user_id, until, reason, banned_by, ban_date) VALUES (?, ?, ?, ?, ?)',
                          (user_id, until.isoformat(), reason, banned_by, ban_date))
            else:
                c.execute('DELETE FROM temp_bans WHERE user_id = ?', (user_id,))
            conn.commit()
            banned_users.add(user_id)
            if until is not None:
                temp_bans[user_id] = until
            else:
                temp_bans.pop(user_id, None)
            logger.warning(f"User {user_id} banned by {banned_by}{' until ' + until.isoformat() if until else ''}. Reason: {reason}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error banning user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error banning user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def unban_user_db(user_id):
    """Unban a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM banned_users WHERE user_id = ?', (user_id,))
            c.execute('DELETE FROM temp_bans WHERE user_id = ?', (user_id,))
            conn.commit()
            banned_users.discard(user_id)
            temp_bans.pop(user_id, None)
            logger.info(f"User {user_id} unbanned")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error unbanning user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error unbanning user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()


# --- Temp ban, hosting suspension, auto-suspend (admin User Management) ---
def _stop_user_scripts(user_id):
    """Stop every running script of exactly this user (not of users whose id merely starts with the same digits)
    without letting the watchdog bring them back. Returns how many were stopped."""
    with STATE_LOCK:
        items = [(key, info) for key, info in bot_scripts.items()
                 if str(info.get('script_owner_id', '')) == str(user_id)]
    stopped = 0
    for key, info in items:
        RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        try:
            kill_process_tree(info)
        except Exception:
            logger.exception("Could not stop %s", key)
        _forget_script(key)
        stopped += 1
    autostart_clear(owner_id=user_id)      # ban / suspension: nothing of this user comes back by itself after a restart
    return stopped


def is_user_suspended(user_id):
    return user_id in suspended_users


def suspend_user_db(user_id, reason, suspended_by, auto=False):
    """Suspend hosting for a user: they keep the bot and chat, but nothing of theirs runs until unsuspended."""
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute('INSERT OR REPLACE INTO suspended_users (user_id, reason, suspended_by, suspend_date, auto) VALUES (?, ?, ?, ?, ?)',
                         (user_id, reason, suspended_by, datetime.now().isoformat(), 1 if auto else 0))
            conn.commit()
            suspended_users.add(user_id)
            logger.warning(f"User {user_id} hosting suspended by {suspended_by}{' (automatic)' if auto else ''}. Reason: {reason}")
            return True
        except Exception as e:
            logger.error(f"❌ Error suspending user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()


def unsuspend_user_db(user_id):
    """Lift a hosting suspension."""
    with DB_LOCK:
        conn = db_connect()
        try:
            conn.execute('DELETE FROM suspended_users WHERE user_id = ?', (user_id,))
            conn.commit()
            suspended_users.discard(user_id)
            logger.info(f"User {user_id} hosting unsuspended")
            return True
        except Exception as e:
            logger.error(f"❌ Error unsuspending user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()


def get_suspend_info(user_id):
    """(reason, suspend_date, auto) of a suspended user, or None."""
    with DB_LOCK:
        conn = db_connect()
        try:
            row = conn.execute('SELECT reason, suspend_date, auto FROM suspended_users WHERE user_id = ?', (user_id,)).fetchone()
            return (row[0] or '', row[1] or '', bool(row[2])) if row else None
        except Exception:
            return None
        finally:
            conn.close()


def _notify_admins_html(text):
    for admin_id in sorted(admin_ids):
        try:
            _safe_send(admin_id, text)
        except Exception as e:
            logger.error(f"Could not notify admin {admin_id}: {e}")


def _lift_expired_temp_bans():
    """Unban every user whose temporary ban has ended. Returns the user ids that were unbanned."""
    now = datetime.now()
    due = [uid for uid, until in list(temp_bans.items()) if until <= now]
    lifted = []
    for uid in due:
        if unban_user_db(uid):
            lifted.append(uid)
            logger.info(f"Temporary ban of user {uid} ended: unbanned automatically")
            try:
                bot.send_message(uid, ui_ok('Ban Ended', f"✅ Status: {ui_tag('active')}", 'Your temporary ban has ended.', foot='Send /start to continue.'), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Failed to notify auto-unbanned user {uid}: {e}")
    return lifted


def temp_ban_loop():
    """Lifts temporary bans once they have run out. The first pass also catches bans that ended while the bot was off."""
    logger.info("Temp ban watcher started (every %s s)", TEMP_BAN_CHECK_SECONDS)
    while not SHUTDOWN_EVENT.is_set():
        try:
            _lift_expired_temp_bans()
        except Exception:
            logger.exception("Temp ban loop error; continuing")
        SHUTDOWN_EVENT.wait(TEMP_BAN_CHECK_SECONDS)
    logger.info("Temp ban watcher stopped.")


def start_temp_ban():
    global TEMP_BAN_STARTED
    if TEMP_BAN_STARTED: return
    TEMP_BAN_STARTED = True
    threading.Thread(target=temp_ban_loop, name="temp-ban", daemon=True).start()

def set_user_limit_db(user_id, limit, set_by):
    """Set custom file limit for a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            set_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO user_limits (user_id, file_limit, set_by, set_date) VALUES (?, ?, ?, ?)',
                      (user_id, limit, set_by, set_date))
            conn.commit()
            user_limits[user_id] = limit
            logger.info(f"Set file limit {limit} for user {user_id} by {set_by}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error setting limit for user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error setting limit for user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

def remove_user_limit_db(user_id):
    """Remove custom file limit for a user"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM user_limits WHERE user_id = ?', (user_id,))
            conn.commit()
            if user_id in user_limits:
                del user_limits[user_id]
            logger.info(f"Removed custom limit for user {user_id}")
            return True
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error removing limit for user {user_id}: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Unexpected error removing limit for user {user_id}: {e}", exc_info=True)
            return False
        finally:
            conn.close()

# --- Modified Helper Functions ---
def get_user_folder(user_id):
    """Get or create user's folder for storing files"""
    user_folder = os.path.join(UPLOAD_BOTS_DIR, str(user_id))
    os.makedirs(user_folder, exist_ok=True)
    return user_folder

def get_sandbox_name(user_id):
    """Stable, visible name of one user's sandbox: always the same for the same user (nothing random, nothing stored).
    A sandbox here = that user's own folder (get_user_folder) + their scripts running as separate processes that start
    inside that folder with a cleaned environment, their own HOME / TMPDIR / package folder and resource limits.
    How strong the wall around it is depends on the server: see the Sandbox section (sandbox_level_text, SANDBOX_MODE)."""
    return f"sandbox_{int(user_id)}"


def _scrub_host_paths(text, user_folder=None):
    """Hide the server's folder layout in text that goes back to a user (their own tracebacks, error messages)."""
    text = str(text or '')
    pairs = []
    if user_folder:
        pairs.append((os.path.abspath(user_folder), '<sandbox>'))
        pairs.append((os.path.realpath(user_folder), '<sandbox>'))
    pairs.extend([(os.path.abspath(UPLOAD_BOTS_DIR), '<host>/upload_bots'), (os.path.realpath(UPLOAD_BOTS_DIR), '<host>/upload_bots'),
                  (BASE_DIR, '<host>')])
    for real, shown in sorted(set(pairs), key=lambda p: -len(p[0])):
        if real and real not in ('/', os.sep):
            text = text.replace(real, shown)
    return text


def get_user_file_limit(user_id):
    """Get the file upload limit for a user"""
    if user_id == OWNER_ID: return OWNER_LIMIT
    if user_id in admin_ids: return ADMIN_LIMIT
    if user_id in user_limits: return user_limits[user_id]
    if user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now():
        return SUBSCRIBED_USER_LIMIT
    return FREE_USER_LIMIT

def get_user_file_count(user_id):
    """Get the number of files uploaded by a user"""
    return len(user_files.get(user_id, []))

def is_bot_running(script_owner_id, file_name):
    """Return process status; leave dead records for watchdog crash recovery."""
    script_key = f"{script_owner_id}_{file_name}"
    info = bot_scripts.get(script_key)
    if not info or not info.get("process"):
        return False
    try:
        return info["process"].poll() is None
    except Exception as exc:
        logger.warning("Could not inspect process %s: %s", script_key, exc)
        return False

def _close_quietly(handle):
    try:
        if handle is not None and not getattr(handle, 'closed', True):
            handle.close()
    except Exception as exc:
        logger.debug("Could not close a handle: %s", exc)


def release_process_resources(process_info):
    """Close the log file and the pipes of a script process (prevents leaked file handles)."""
    _close_quietly(process_info.get('log_file'))
    proc = process_info.get('process')
    if proc is not None:
        for stream_name in ('stdin', 'stdout', 'stderr'):
            _close_quietly(getattr(proc, stream_name, None))


def _signal_process_group(pid, sig):
    """Send a signal to the whole process group of a script (POSIX only).
    Only done when the script leads its own group, so the hosting bot can never signal itself."""
    if os.name != 'posix':
        return
    try:
        if os.getpgid(pid) == pid:
            os.killpg(pid, sig)
    except (ProcessLookupError, PermissionError, OSError):
        pass


def kill_process_tree(process_info):
    """Stop a script and everything it started, wait for it (no zombies) and close its files."""
    script_key = process_info.get('script_key', 'N/A')
    process = process_info.get('process')
    pid = getattr(process, 'pid', None)
    try:
        if not pid:
            logger.error(f"Process object/PID missing for {script_key}; cannot kill (files are still closed).")
            return
        targets = []
        try:
            parent = psutil.Process(pid)
            targets = parent.children(recursive=True) + [parent]
        except psutil.NoSuchProcess:
            logger.info(f"Process {pid} for {script_key} already gone.")
        logger.info(f"Stopping {script_key} (PID {pid}, {max(len(targets) - 1, 0)} child process(es))")
        _signal_process_group(pid, signal.SIGTERM)
        for proc in targets:
            try:
                proc.terminate()
            except psutil.NoSuchProcess:
                pass
            except Exception as exc:
                logger.warning(f"Could not terminate {proc.pid} for {script_key}: {exc}")
        _gone, alive = psutil.wait_procs(targets, timeout=3)
        if alive:
            logger.warning(f"{len(alive)} process(es) of {script_key} ignored SIGTERM; killing.")
            if hasattr(signal, 'SIGKILL'):
                _signal_process_group(pid, signal.SIGKILL)
            for proc in alive:
                try:
                    proc.kill()
                except psutil.NoSuchProcess:
                    pass
                except Exception as exc:
                    logger.error(f"Failed to kill {proc.pid} for {script_key}: {exc}")
            psutil.wait_procs(alive, timeout=2)
        try:
            process.wait(timeout=2)  # reap the child so no zombie is left behind
        except Exception:
            pass
    except Exception as e:
        logger.error(f"❌ Unexpected error killing process tree for PID {pid or 'N/A'} ({script_key}): {e}", exc_info=True)
    finally:
        release_process_resources(process_info)

# --- Map Telegram import names to actual PyPI package names ---
TELEGRAM_MODULES = {
    # Main Bot Frameworks
    'telebot': 'pyTelegramBotAPI',
    'telegram': 'python-telegram-bot',
    'python_telegram_bot': 'python-telegram-bot',
    'aiogram': 'aiogram',
    'pyrogram': 'pyrogram',
    'telethon': 'telethon',
    'telethon.sync': 'telethon', # Handle specific imports
    'from telethon.sync import telegramclient': 'telethon', # Example

    # Additional Libraries (add more specific mappings if import name differs)
    'telepot': 'telepot',
    'pytg': 'pytg',
    'tgcrypto': 'tgcrypto',
    'telegram_upload': 'telegram-upload',
    'telegram_send': 'telegram-send',
    'telegram_text': 'telegram-text',

    # MTProto & Low-Level
    'mtproto': 'telegram-mtproto', # Example, check actual package name
    'tl': 'telethon',  # Part of Telethon, install 'telethon'

    # Utilities & Helpers (examples, verify package names)
    'telegram_utils': 'telegram-utils',
    'telegram_logger': 'telegram-logger',
    'telegram_handlers': 'python-telegram-handlers',

    # Database Integrations (examples)
    'telegram_redis': 'telegram-redis',
    'telegram_sqlalchemy': 'telegram-sqlalchemy',

    # Payment & E-commerce (examples)
    'telegram_payment': 'telegram-payment',
    'telegram_shop': 'telegram-shop-sdk',

    # Testing & Debugging (examples)
    'pytest_telegram': 'pytest-telegram',
    'telegram_debug': 'telegram-debug',

    # Scraping & Analytics (examples)
    'telegram_scraper': 'telegram-scraper',
    'telegram_analytics': 'telegram-analytics',

    # NLP & AI (examples)
    'telegram_nlp': 'telegram-nlp-toogit',
    'telegram_ai': 'telegram-ai', # Assuming this exists

    # Web & API Integration (examples)
    'telegram_api': 'telegram-api-client',
    'telegram_web': 'telegram-web-integration',

    # Gaming & Interactive (examples)
    'telegram_games': 'telegram-games',
    'telegram_quiz': 'telegram-quiz-bot',

    # File & Media Handling (examples)
    'telegram_ffmpeg': 'telegram-ffmpeg',
    'telegram_media': 'telegram-media-utils',

    # Security & Encryption (examples)
    'telegram_2fa': 'telegram-twofa',
    'telegram_crypto': 'telegram-crypto-bot',

    # Localization & i18n (examples)
    'telegram_i18n': 'telegram-i18n',
    'telegram_translate': 'telegram-translate',

    # Common non-telegram examples
    'bs4': 'beautifulsoup4',
    'requests': 'requests',
    'pillow': 'Pillow', # Note the capitalization difference
    'cv2': 'opencv-python', # Common import name for OpenCV
    'yaml': 'PyYAML',
    'dotenv': 'python-dotenv',
    'dateutil': 'python-dateutil',
    'pandas': 'pandas',
    'numpy': 'numpy',
    'flask': 'Flask',
    'django': 'Django',
    'sqlalchemy': 'SQLAlchemy',
    'asyncio': None, # Core module, should not be installed
    'json': None,    # Core module
    'datetime': None,# Core module
    'os': None,      # Core module
    'sys': None,     # Core module
    're': None,      # Core module
    'time': None,    # Core module
    'math': None,    # Core module
    'random': None,  # Core module
    'logging': None, # Core module
    'threading': None,# Core module
    'subprocess':None,# Core module
    'zipfile':None,  # Core module
    'tempfile':None, # Core module
    'shutil':None,   # Core module
    'sqlite3':None,  # Core module
    'psutil': 'psutil',
    'atexit': None   # Core module
}

# --- Manual Modules Installation System ---
def save_install_log(user_id, module_name, package_name, status, log):
    """Save installation log to database"""
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            install_date = datetime.now().isoformat()
            c.execute('INSERT INTO install_logs (user_id, module_name, package_name, status, log, install_date) VALUES (?, ?, ?, ?, ?, ?)',
                      (user_id, module_name, package_name, status, log, install_date))
            conn.commit()
            logger.info(f"Saved install log for user {user_id}: {module_name} - {status}")
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error saving install log: {e}")
        except Exception as e:
            logger.error(f"❌ Unexpected error saving install log: {e}", exc_info=True)
        finally:
            conn.close()

_SAFE_PACKAGE_RE = re.compile(r'^[A-Za-z0-9@][A-Za-z0-9@._/+=<>!~^*,\[\]-]{0,119}$')


def _is_safe_package_name(name):
    """Reject empty names and anything that could be read as a command-line option (leading dash, spaces)."""
    return bool(name) and bool(_SAFE_PACKAGE_RE.match(name))


def attempt_install_pip(module_name, message, manual_request=False, user_folder=None):
    """Install Python package via pip. With user_folder the package goes into that user's own sandbox package folder
    (the install itself runs inside the sandbox), so one user can never change what another user's scripts import."""
    package_name = TELEGRAM_MODULES.get(module_name.lower(), module_name) 
    if package_name is None: 
        logger.info(f"Module '{module_name}' is core. Skipping pip install.")
        return False, "Core module - no installation needed"
    
    pm = None
    try:
        if manual_request:
            pm = _msg_anim(message, 'Installing Package', f"Manual installation requested: {module_name} -> {package_name}")
        else:
            pm = _msg_anim(message, 'Installing Package', f"Module {module_name} not found. Installing {package_name}...")
        
        if not _is_safe_package_name(package_name):
            _reply_via(pm, message, "❌ That package name is not valid. Send just the package name, for example `requests`.", parse_mode='Markdown')
            return False, "Invalid package name"
        command = [sys.executable, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input', package_name]
        run_env, run_cwd = child_env(), None
        if user_folder:
            command[4:4] = sandbox_pip_target(user_folder)
            command, extra_env = sandbox_wrap(command, user_folder, 'install')
            run_env.update(extra_env)
            run_cwd = user_folder
        logger.info(f"Running install: pip install {package_name}")
        result = subprocess.run(command, capture_output=True, text=True, check=False, encoding='utf-8', errors='ignore', cwd=run_cwd,
                                timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=run_env, start_new_session=True)
        
        if result.returncode == 0:
            log_msg = f"Installed {package_name}. Output:\n{result.stdout}"
            logger.info(log_msg)
            success_msg = f"✅ Package `{package_name}` (for `{module_name}`) installed successfully."
            _reply_via(pm, message, success_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, package_name, "success", log_msg)
            return True, log_msg
        else:
            error_msg = f"❌ Failed to install `{package_name}` for `{module_name}`.\nLog:\n```\n{result.stderr or result.stdout}\n```"
            logger.error(error_msg)
            if len(error_msg) > 4000: error_msg = error_msg[:4000] + "\n... (Log truncated)"
            _reply_via(pm, message, error_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, package_name, "failed", error_msg)
            return False, error_msg
    except subprocess.TimeoutExpired:
        error_msg = f"❌ Installing `{package_name}` took longer than {INSTALL_TIMEOUT} seconds and was stopped. Try again later."
        logger.error(error_msg)
        _reply_via(pm, message, error_msg)
        save_install_log(message.from_user.id, module_name, package_name, "error", error_msg)
        return False, error_msg
    except Exception as e:
        error_msg = f"❌ Error installing `{package_name}`: {str(e)}"
        logger.error(error_msg, exc_info=True)
        _reply_via(pm, message, ui_err('Install Failed', ui_row('📦', 'Package', package_name, code=True), ui_user_error(e)), parse_mode='HTML')
        save_install_log(message.from_user.id, module_name, package_name, "error", error_msg)
        return False, error_msg

def attempt_install_npm(module_name, user_folder, message, manual_request=False):
    """Install Node package via npm"""
    pm = None
    try:
        if manual_request:
            pm = _msg_anim(message, 'Installing Node Package', f"Manual Node package installation requested: {module_name}")
        else:
            pm = _msg_anim(message, 'Installing Node Package', f"Node package {module_name} not found. Installing locally...")
        
        if not _is_safe_package_name(module_name):
            _reply_via(pm, message, "❌ That package name is not valid. Send just the package name, for example `npm:axios`.", parse_mode='Markdown')
            return False, "Invalid package name"
        command = ['npm', 'install', module_name]
        logger.info(f"Running npm install: {' '.join(command)} in {user_folder}")
        run_env = child_env()
        command, extra_env = sandbox_wrap(command, user_folder, 'install')
        run_env.update(extra_env)
        result = subprocess.run(command, capture_output=True, text=True, check=False, cwd=user_folder, encoding='utf-8', errors='ignore',
                                timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=run_env, start_new_session=True)
        
        if result.returncode == 0:
            log_msg = f"Installed {module_name}. Output:\n{result.stdout}"
            logger.info(log_msg)
            success_msg = f"✅ Node package `{module_name}` installed locally."
            _reply_via(pm, message, success_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, module_name, "success", log_msg)
            return True, log_msg
        else:
            error_msg = f"❌ Failed to install Node package `{module_name}`.\nLog:\n```\n{result.stderr or result.stdout}\n```"
            logger.error(error_msg)
            if len(error_msg) > 4000: error_msg = error_msg[:4000] + "\n... (Log truncated)"
            _reply_via(pm, message, error_msg, parse_mode='Markdown')
            save_install_log(message.from_user.id, module_name, module_name, "failed", error_msg)
            return False, error_msg
    except subprocess.TimeoutExpired:
        error_msg = f"❌ Installing `{module_name}` took longer than {INSTALL_TIMEOUT} seconds and was stopped. Try again later."
        logger.error(error_msg)
        _reply_via(pm, message, error_msg)
        save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
        return False, error_msg
    except FileNotFoundError:
         error_msg = "❌ Error: 'npm' not found. Ensure Node.js/npm are installed and in PATH."
         logger.error(error_msg)
         _reply_via(pm, message, error_msg)
         save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
         return False, error_msg
    except Exception as e:
        error_msg = f"❌ Error installing Node package `{module_name}`: {str(e)}"
        logger.error(error_msg, exc_info=True)
        _reply_via(pm, message, ui_err('Install Failed', ui_row('📦', 'Package', module_name, code=True), ui_user_error(e)), parse_mode='HTML')
        save_install_log(message.from_user.id, module_name, module_name, "error", error_msg)
        return False, error_msg

def manual_install_module_init(message):
    """Initialize manual module installation"""
    user_id = message.from_user.id
    
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
    
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, MSG_LOCKED, parse_mode='HTML')
        return
    
    msg = bot.reply_to(message, "📦 Send module name to install (e.g., `requests` or `pillow`)\nFor Node.js: `npm:module_name`\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_manual_install_module)

def process_manual_install_module(message):
    """Process manual module installation"""
    user_id = message.from_user.id
    
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_msg('❎', 'Cancelled', 'Installation cancelled.'), parse_mode='HTML')
        return
    
    if not message.text:
        bot.reply_to(message, ui_warn('Text Needed', 'Please send the module name as text.', foot='Send it again or /cancel.'), parse_mode='HTML')
        return
    module_name = message.text.strip()
    
    # Check if it's a Node.js module
    if module_name.lower().startswith('npm:'):
        module_name = module_name[4:].strip()
        user_folder = get_user_folder(user_id)
        success, log = attempt_install_npm(module_name, user_folder, message, manual_request=True)
    else:
        # Python module
        success, log = attempt_install_pip(module_name, message, manual_request=True, user_folder=get_user_folder(user_id))
    
    if success:
        logger.info(f"User {user_id} manually installed module: {module_name}")

# --- Database Operations ---
def save_user_file(user_id, file_name, file_type='py'):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('INSERT OR REPLACE INTO user_files (user_id, file_name, file_type) VALUES (?, ?, ?)',
                      (user_id, file_name, file_type))
            conn.commit()
            if user_id not in user_files: user_files[user_id] = []
            user_files[user_id] = [(fn, ft) for fn, ft in user_files[user_id] if fn != file_name]
            user_files[user_id].append((file_name, file_type))
            logger.info(f"Saved file '{file_name}' ({file_type}) for user {user_id}")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error saving file for user {user_id}, {file_name}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error saving file for {user_id}, {file_name}: {e}", exc_info=True)
        finally: conn.close()

def remove_user_file_db(user_id, file_name):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (user_id, file_name))
            c.execute('DELETE FROM autostart WHERE script_key = ?', (f"{user_id}_{file_name}",))
            conn.commit()
            if user_id in user_files:
                user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
                if not user_files[user_id]: del user_files[user_id]
            logger.info(f"Removed file '{file_name}' for user {user_id} from DB")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error removing file for {user_id}, {file_name}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error removing file for {user_id}, {file_name}: {e}", exc_info=True)
        finally: conn.close()

def add_active_user(user_id):
    if user_id in active_users:
        return  # already stored; avoids a database write on every single message
    active_users.add(user_id)
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            join_date = datetime.now().isoformat()
            c.execute('INSERT OR REPLACE INTO active_users (user_id, join_date, last_seen) VALUES (?, ?, ?)', 
                      (user_id, join_date, join_date))
            conn.commit()
            logger.info(f"Added/Updated active user {user_id} in DB")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error adding active user {user_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error adding active user {user_id}: {e}", exc_info=True)
        finally: conn.close()

def save_subscription(user_id, expiry):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            expiry_str = expiry.isoformat()
            c.execute('INSERT OR REPLACE INTO subscriptions (user_id, expiry) VALUES (?, ?)', (user_id, expiry_str))
            conn.commit()
            user_subscriptions[user_id] = {'expiry': expiry}
            logger.info(f"Saved subscription for {user_id}, expiry {expiry_str}")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error saving subscription for {user_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error saving subscription for {user_id}: {e}", exc_info=True)
        finally: conn.close()

def remove_subscription_db(user_id):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            c.execute('DELETE FROM subscriptions WHERE user_id = ?', (user_id,))
            conn.commit()
            if user_id in user_subscriptions: del user_subscriptions[user_id]
            logger.info(f"Removed subscription for {user_id} from DB")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error removing subscription for {user_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error removing subscription for {user_id}: {e}", exc_info=True)
        finally: conn.close()

# --- Referral system ---
def _bot_username():
    """Username of this bot (needed for the referral link). Asked from Telegram once, then remembered."""
    name = BOT_USERNAME_CACHE.get('name')
    if name:
        return name
    try:
        name = (bot.get_me().username or '').strip()
    except Exception as exc:
        logger.warning("Could not read the bot username: %s", type(exc).__name__)
        name = ''
    BOT_USERNAME_CACHE['name'] = name
    return name


def get_referral_link(user_id):
    name = _bot_username()
    return f"https://t.me/{name}?start=ref_{int(user_id)}" if name else ''


def count_referrals(user_id):
    with DB_LOCK:
        conn = db_connect()
        try:
            return conn.execute('SELECT COUNT(*) FROM referrals WHERE referrer_id = ?', (user_id,)).fetchone()[0]
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error counting referrals for {user_id}: {e}")
            return 0
        finally: conn.close()


def _referral_progress(total):
    """(referrals still needed for the next reward, rewards earned so far)."""
    return REFERRALS_PER_REWARD - (total % REFERRALS_PER_REWARD), total // REFERRALS_PER_REWARD


def parse_referral_payload(text):
    """Referrer id from '/start ref_123', otherwise None."""
    parts = (text or '').split()
    if len(parts) == 2 and parts[0].split('@')[0] == '/start':
        m = re.fullmatch(r'ref_(\d{1,15})', parts[1])
        if m:
            return int(m.group(1))
    return None


def remember_referral_payload(message):
    """Called when somebody presses /start: if it came from a referral link and the person is new, remember who sent them.
    The credit is only given later, once the person has really been added (after the channel check)."""
    try:
        user_id = message.from_user.id
        referrer_id = parse_referral_payload(message.text)
        if referrer_id is None or user_id in active_users or referrer_id == user_id:
            return
        if len(PENDING_REFERRALS) > 5000:
            PENDING_REFERRALS.pop(next(iter(PENDING_REFERRALS)), None)
        PENDING_REFERRALS[user_id] = referrer_id
    except Exception:
        logger.exception("Could not read the referral link")


def record_referral(referrer_id, referred_id):
    """Save one referral. Returns the referrer's new total, or None when it does not count
    (self-referral, unknown or banned referrer, or this user was already referred)."""
    if referrer_id == referred_id or referrer_id not in active_users or referrer_id in banned_users:
        return None
    with DB_LOCK:
        conn = db_connect()
        try:
            cur = conn.execute('INSERT OR IGNORE INTO referrals (referred_id, referrer_id, created_at) VALUES (?, ?, ?)',
                               (referred_id, referrer_id, datetime.now().isoformat()))
            conn.commit()
            if cur.rowcount == 0:
                return None
            return conn.execute('SELECT COUNT(*) FROM referrals WHERE referrer_id = ?', (referrer_id,)).fetchone()[0]
        except sqlite3.Error as e:
            logger.error(f"❌ SQLite error saving referral {referrer_id} -> {referred_id}: {e}")
            return None
        finally: conn.close()


def credit_referral(new_user_id):
    """A brand-new user has just been added: credit whoever sent them, and give the reward on every
    REFERRALS_PER_REWARD-th referral."""
    referrer_id = PENDING_REFERRALS.pop(new_user_id, None)
    if referrer_id is None:
        return
    try:
        total = record_referral(referrer_id, new_user_id)
        if total is None:
            return
        logger.info(f"Referral counted: {referrer_id} -> {new_user_id} (total {total})")
        if total % REFERRALS_PER_REWARD == 0:
            if referrer_id in admin_ids:
                reward_note = ui_row('ℹ️', 'Note', 'Admins already have unlimited uploads, so no extra days were added.', bold=False)
            else:
                current = user_subscriptions.get(referrer_id, {}).get('expiry')
                start = datetime.now()
                if current and current > start: start = current
                new_expiry = start + timedelta(days=REFERRAL_REWARD_DAYS)
                save_subscription(referrer_id, new_expiry)
                reward_note = (ui_row('⭐', 'Reward', f"+{REFERRAL_REWARD_DAYS} days Premium") + "\n"
                               + ui_row('📅', 'Premium till', f"{new_expiry:%Y-%m-%d}"))
            msg = ui_ok('Referral Reward Unlocked', ui_row('👥', 'Referral', f"#{total}"), reward_note,
                        foot='Shukriya! Aur dosto ko bhejo, aur rewards milte rahenge.')
        else:
            need, _rewards = _referral_progress(total)
            msg = ui_info('New Referral', 'Ek naya user aapke referral link se join hua!',
                          ui_row('👥', 'Total referrals', total),
                          ui_row('🎯', 'Next reward', f"{need} more needed"),
                          f"<code>{ui_bar(REFERRALS_PER_REWARD - need, REFERRALS_PER_REWARD)}</code>",
                          foot='Link share karte raho, reward paas hai.')
        _safe_send(referrer_id, msg)
    except Exception:
        logger.exception("Could not credit the referral of %s", new_user_id)


def add_admin_db(admin_id, added_by):
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        try:
            added_date = datetime.now().isoformat()
            c.execute('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                      (admin_id, added_by, added_date))
            conn.commit()
            admin_ids.add(admin_id) 
            logger.info(f"Added admin {admin_id} to DB by {added_by}")
        except sqlite3.Error as e: logger.error(f"❌ SQLite error adding admin {admin_id}: {e}")
        except Exception as e: logger.error(f"❌ Unexpected error adding admin {admin_id}: {e}", exc_info=True)
        finally: conn.close()

def remove_admin_db(admin_id):
    if admin_id == OWNER_ID:
        logger.warning("Attempted to remove OWNER_ID from admins.")
        return False 
    with DB_LOCK:
        conn = db_connect()
        c = conn.cursor()
        removed = False
        try:
            c.execute('SELECT 1 FROM admins WHERE user_id = ?', (admin_id,))
            if c.fetchone():
                c.execute('DELETE FROM admins WHERE user_id = ?', (admin_id,))
                conn.commit()
                removed = c.rowcount > 0 
                if removed: admin_ids.discard(admin_id); logger.info(f"Removed admin {admin_id} from DB")
                else: logger.warning(f"Admin {admin_id} found but delete affected 0 rows.")
            else:
                logger.warning(f"Admin {admin_id} not found in DB.")
                admin_ids.discard(admin_id)
            return removed
        except sqlite3.Error as e: logger.error(f"❌ SQLite error removing admin {admin_id}: {e}"); return False
        except Exception as e: logger.error(f"❌ Unexpected error removing admin {admin_id}: {e}", exc_info=True); return False
        finally: conn.close()

# --- Menu creation (Inline and ReplyKeyboards) ---
def create_main_menu_inline(user_id):
    """Main menu (a NavMenu, sent as a reply keyboard). Backup export/import is here for every user."""
    markup = NavMenu(row_width=2)
    markup.row(NavButton('📤 Upload Script', callback_data='upload'),
               NavButton('📂 My Files', callback_data='check_files'))
    markup.row(NavButton('👤 My Account', callback_data='user_account'),
               NavButton('🤖 My Running Bots', callback_data='my_running'))
    markup.row(NavButton('📦 Export Backup', callback_data=f'ubk_{user_id}'),
               NavButton('♻️ Import Backup', callback_data=f'ubr_{user_id}'))
    markup.row(NavButton('⚡ Speed Test', callback_data='speed'),
               NavButton('📊 Statistics', callback_data='stats'))
    markup.row(NavButton('📦 Module Install', callback_data='manual_install'),
               NavButton('🆘 Help', callback_data='user_help'))
    markup.row(NavButton('👥 Referral', callback_data='referral'))
    markup.row(NavButton('📢 Updates', url=f'https://t.me/{UPDATE_CHANNEL.replace("@", "")}'),
               NavButton('📞 Support', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}'))
    if user_id in admin_ids:
        markup.row(NavButton('👑 Admin Center', callback_data='admin_dashboard'),
                   NavButton('🩺 Hosting Health', callback_data='hosting_health'))
        markup.row(NavButton('⚙️ Admin Settings', callback_data='admin_settings'),
                   NavButton('👥 User Management', callback_data='user_management'))
        markup.row(NavButton('📢 Broadcast', callback_data='broadcast'),
                   NavButton('📢 Channel Add', callback_data='manage_mandatory_channels'))
    return markup


def _file_key_text(file_name, file_type, running, badge):
    short = file_name if len(file_name) <= 18 else file_name[:15] + '...'
    return f"{badge} {short} ({file_type}) {'▶️' if running else '⏹️'}"


def _files_view(user_id):
    """(text, NavMenu) for My Files, one page (NAV_PAGE_SIZE bots) at a time with Prev / Next.
    Export/Import Backup are always on it, even with no files."""
    files = sorted(user_files.get(user_id, []))
    menu = NavMenu(row_width=1)
    shown, page, pages = _paginate(user_id, 'files', files)
    menu.offset = page * NAV_PAGE_SIZE
    for file_name, file_type in shown:
        badge = '📄'
        menu.add(NavButton(_file_key_text(file_name, file_type, is_bot_running(user_id, file_name), badge),
                           callback_data=f'file_{user_id}_{file_name}'))
    menu.pager('files', 'check_files', page, pages)
    menu.row(NavButton('📦 Export Backup', callback_data=f'ubk_{user_id}'),
             NavButton('♻️ Import Backup', callback_data=f'ubr_{user_id}'))
    menu.row(NavButton('📤 Upload Script', callback_data='upload'))
    if files:
        running_now = sum(1 for name, _t in files if is_bot_running(user_id, name))
        limit_txt = get_user_file_limit(user_id)
        text = ui_msg('📂', 'My Files',
                      ui_meter('📦', 'Slots used', len(files), limit_txt, f"{len(files)} / {ui_limit(limit_txt)}"),
                      f"{ui_tag('active')}: <b>{running_now}</b>   {ui_tag('stopped')}: <b>{len(files) - running_now}</b>",
                      foot='Tap a file to manage it, or back up / restore all your bots.' + _page_note(page, pages), tip='files')
    else:
        text = ui_msg('📂', 'My Files', ui_tag('stopped', 'NO FILES YET'),
                      "\n🌱 Abhi koi file upload nahi hui.",
                      ui_bullets('📥 Purana backup hai? Import Backup dabao.', '🚀 Naya hai? Upload Script dabao.'),
                      foot='Your bots will show up here.')
    return text, menu


# --- Full backup / restore ---------------------------------------------------
# Two scopes, both packed into ONE zip:
#   * Admin "Full Backup": the whole hosting database + every user's folder from UPLOAD_BOTS_DIR (scripts, data,
#     .env). Owner / main admin only. The hosting bot's OWN code is never exported and never restored: a restore
#     can therefore never put an older version of the host in place of the running one. Old backups (made before
#     v10) still hold a source/ copy of the bot code; on import that part is skipped and nothing of it is written.
#   * User "My Bots" backup: only that user's own folder (scripts + data) and their script list.
# Every restore is staged first, shown for a Yes/Cancel confirmation, and a backup of the current
# state is written to disk (and sent to the person) before anything is overwritten.
# Zip entries are checked against path traversal (zip-slip), links, duplicates and size limits.
BACKUP_FORMAT_FULL = 'demon-full-backup'
BACKUP_FORMAT_USER = 'demon-user-backup'
BACKUP_VERSION = 1
SQLITE_EXTS = ('.db', '.sqlite', '.sqlite3')
SQLITE_MAGIC = b'SQLite format 3\x00'
BACKUP_SKIP_DIRS = {'node_modules', '__pycache__', 'venv', 'env', 'site-packages', '.git'}
BACKUP_SKIP_SUFFIXES = ('.log', '.pyc', '-wal', '-shm', '-journal')
HOSTING_DB_CORE_TABLES = ('subscriptions', 'user_files', 'active_users', 'admins')
FULL_BACKUP_MAX_MB = _env_int('FULL_BACKUP_MAX_MB', 760)    # total size of a full backup before compression
USER_BACKUP_MAX_MB = _env_int('USER_BACKUP_MAX_MB', 760)     # same, for one user's backup
BACKUP_MAX_FILES = _env_int('BACKUP_MAX_FILES', 50000)
IMPORT_TTL = 600                                             # seconds a pending upload / confirmation stays valid
# Telegram lets a bot read files up to 20 MB, so bigger backups are sent in parts that fit that limit.
PART_BYTES = max(1, min(MAX_UPLOAD_MB, 19)) * 1024 * 1024
MAX_PARTS = 40
BACKUP_KEEP = 3                                              # automatic pre-restore backups kept per scope
FULL_BACKUP_DIR = os.path.join(IROTECH_DIR, 'full_backups')
USER_BACKUP_DIR = os.path.join(IROTECH_DIR, 'user_backups')
PART_RE = re.compile(r'\.zip\.(\d{1,3})$', re.IGNORECASE)
IMPORT_LOCK = threading.RLock()
BACKUP_OP_LOCK = threading.Lock()   # only one export / restore at a time
PENDING_IMPORT_WAIT = {}      # user_id -> {'kind', 'owner', 'time', 'dir', 'parts'}   waiting for the upload
PENDING_IMPORT_CONFIRM = {}   # token -> staged restore waiting for Yes / Cancel


class BackupTooLarge(Exception):
    """The folder is bigger than the configured backup limit."""


def _now_stamp():
    return datetime.now().strftime('%Y%m%d_%H%M%S')


def _path_inside(root, path):
    """True when path (already resolved) is root or below it."""
    try:
        return os.path.commonpath((root, path)) == root
    except ValueError:
        return False


def _rmtree_quiet(path):
    try:
        if path and os.path.isdir(path):
            shutil.rmtree(path, ignore_errors=True)
    except OSError:
        pass


def _human_size(num):
    num = float(num)
    for unit in ('B', 'KB', 'MB', 'GB'):
        if num < 1024 or unit == 'GB':
            return f'{num:.0f} {unit}' if unit == 'B' else f'{num:.1f} {unit}'
        num /= 1024


BACKUP_MAX_REL = 1500       # longest path inside a backup (deep folders, e.g. another hosting bot hosted here, are fine)
BACKUP_MAX_REL_EXPORT = 1400  # export keeps this much room for the 'upload_bots/<id>/' prefix, so what is exported can be imported


def _safe_zip_rel(rel, max_len=BACKUP_MAX_REL):
    """A zip entry / relative path that stays inside its folder: no absolute path, no '..', no backslash."""
    if not rel or len(rel) > max_len or any(ord(ch) < 32 for ch in rel):
        return False
    if rel.startswith('/') or '\\' in rel or (len(rel) > 1 and rel[1] == ':'):
        return False
    return all(part not in ('', '.', '..') and len(part) <= 255 for part in rel.split('/'))


def _unsafe_why(rel):
    """Short plain reason why _safe_zip_rel refused a path (shown to the owner)."""
    if not rel:
        return 'empty name'
    if len(rel) > BACKUP_MAX_REL:
        return f'path longer than {BACKUP_MAX_REL} characters'
    if any(ord(ch) < 32 for ch in rel):
        return 'control character in the name'
    if rel.startswith('/') or '\\' in rel or (len(rel) > 1 and rel[1] == ':'):
        return 'absolute path or backslash'
    for part in rel.split('/'):
        if part in ('', '.', '..'):
            return 'empty, . or .. folder name'
        if len(part) > 255:
            return 'a single name longer than 255 characters'
    return 'not allowed'


def _expire_pending_imports():
    """Forget stale waiting states and delete staged files nobody confirmed."""
    now = time.time()
    with IMPORT_LOCK:
        for uid in [u for u, p in PENDING_IMPORT_WAIT.items() if now - p['time'] > IMPORT_TTL]:
            pend = PENDING_IMPORT_WAIT.pop(uid, None)
            if pend:
                _rmtree_quiet(pend.get('dir'))
        for token in [t for t, e in PENDING_IMPORT_CONFIRM.items() if now - e['time'] > IMPORT_TTL]:
            entry = PENDING_IMPORT_CONFIRM.pop(token, None)
            if entry:
                _rmtree_quiet(entry.get('dir'))


def _prune_backups(folder, prefix, keep=BACKUP_KEEP):
    try:
        names = sorted(n for n in os.listdir(folder) if n.startswith(prefix))
        for old in names[:-keep]:
            try:
                os.remove(os.path.join(folder, old))
            except OSError:
                pass
    except OSError:
        pass


def _sqlite_snapshot(source_path, dest_path):
    """Consistent copy of a SQLite file (works while it is in use). Falls back to a plain copy."""
    try:
        src = sqlite3.connect(f'file:{source_path}?mode=ro', uri=True, timeout=10)
        try:
            dst = sqlite3.connect(dest_path)
            try:
                src.backup(dst)
            finally:
                dst.close()
        finally:
            src.close()
    except sqlite3.Error:
        shutil.copyfile(source_path, dest_path)


def _call_anim(call, title, label='', **kwargs):
    """Animated status message for a button press (see ProgressMessage). The next _edit_or_send(call, ...) is the final
    result and replaces it. Returns None when the animation could not be started."""
    try:
        pm = ProgressMessage(call.message.chat.id, title, label,
                             message_id=getattr(call.message, 'message_id', None), **kwargs).start()
    except Exception:
        logger.exception("Could not start the progress message")
        return None
    try:
        call._pm = pm
    except Exception:
        pass
    return pm


def _say_via(pm, chat_id, text, markup=None):
    """Final text of an operation: replaces the animated status when there is one, otherwise a normal message."""
    if isinstance(pm, ProgressMessage) and pm.enabled and not pm._done:
        return pm.finish(text, reply_markup=markup)
    return bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=markup)


def _msg_anim(message, title, label='', only_if_free=False, **kwargs):
    """Animated status as a reply to a user's message. Quiet (auto-resume) messages stay silent.
    only_if_free=True: no status at all when another animation already runs in that chat (bulk starts)."""
    try:
        quiet = bool(getattr(message, 'quiet', False))
        if only_if_free and not quiet and message.chat.id in _PM_CHATS:
            return None
        return ProgressMessage(message.chat.id, title, label, message=message, enabled=not quiet, **kwargs).start()
    except Exception:
        logger.exception("Could not start the progress message")
        return None


def _reply_via(pm, message, text, **kwargs):
    """Like bot.reply_to, but when an animated status is running the text replaces that status message."""
    if isinstance(pm, ProgressMessage) and pm.enabled and not pm._done:
        return pm.finish(text, parse_mode=kwargs.get('parse_mode'), reply_markup=kwargs.get('reply_markup'))
    return bot.reply_to(message, text, **kwargs)


def _edit_or_send(call, text, markup=None):
    pm = getattr(call, '_pm', None)
    if isinstance(pm, ProgressMessage) and not pm._done:
        pm.finish(text, reply_markup=markup)
        return
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                              parse_mode='HTML', reply_markup=markup)
    except Exception:
        bot.send_message(call.message.chat.id, text, parse_mode='HTML', reply_markup=markup)


def _download_upload(message, max_mb):
    """Download the document of a message into memory with a size limit."""
    doc = message.document
    limit = max_mb * 1024 * 1024
    if (doc.file_size or 0) > limit:
        raise ValueError(f'That file is too big for me to read (maximum {max_mb} MB per file). '
                         'Big backups are sent as several parts (.zip.001, .zip.002 ...); send those one by one.')
    file_info = bot.get_file(doc.file_id)
    content = bot.download_file(file_info.file_path)
    if len(content) > limit:
        raise ValueError(f'That file is too big for me to read (maximum {max_mb} MB per file).')
    return content


def _confirm_markup(token):
    markup = NavMenu(row_width=2)
    markup.row(NavButton('✅ Yes, restore', callback_data=f'impc_yes_{token}'),
               NavButton('❌ Cancel', callback_data=f'impc_no_{token}'))
    return markup


def _cancel_markup():
    return NavMenu().add(NavButton('❌ Cancel', callback_data='impc_cancel'))


def _parts_markup():
    markup = NavMenu(row_width=2)
    markup.row(NavButton('✅ Done, check backup', callback_data='impc_done'),
               NavButton('❌ Cancel', callback_data='impc_cancel'))
    return markup


def _store_confirm(entry):
    token = os.urandom(6).hex()
    entry['time'] = time.time()
    with IMPORT_LOCK:
        PENDING_IMPORT_CONFIRM[token] = entry
    return token


def _can_backup_global(user_id):
    """The full backup holds every user's code, data and the admin list, so only the configured
    owner / main admin may export or restore it (not admins that were added later)."""
    return user_id in (OWNER_ID, ADMIN_ID) and user_id in admin_ids


def _may_manage_bot_data(user_id, owner_id):
    # Same rule as the existing per-file handlers (start / stop / delete / logs).
    return user_id == owner_id or user_id in admin_ids


# --- Building a backup zip ---------------------------------------------------
def _iter_backup_files(folder):
    """Regular files below folder as (relative path with '/', full path). Never follows links."""
    root = os.path.realpath(folder)
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        dirnames[:] = sorted(d for d in dirnames
                             if d not in BACKUP_SKIP_DIRS and not os.path.islink(os.path.join(dirpath, d)))
        for name in sorted(filenames):
            if name.endswith(BACKUP_SKIP_SUFFIXES) or (name.startswith('.import_') and name.endswith('.tmp')):
                continue
            full = os.path.join(dirpath, name)
            if os.path.islink(full) or not os.path.isfile(full):
                continue
            rel = os.path.relpath(full, root).replace(os.sep, '/')
            if _safe_zip_rel(rel, BACKUP_MAX_REL_EXPORT):
                yield rel, full


def _zip_add_folder(archive, folder, prefix, snap_dir, budget):
    """Add every file of folder to the zip under prefix. budget = {'bytes', 'files', 'max_bytes'} (optional
    'max_file' leaves out single files bigger than that and counts them in 'skipped').
    SQLite files are written from a consistent snapshot. Returns the number of files added."""
    added = 0
    for rel, full in _iter_backup_files(folder):
        try:
            size = os.path.getsize(full)
        except OSError:
            continue
        if budget.get('max_file') and size > budget['max_file']:
            budget['skipped'] = budget.get('skipped', 0) + 1
            continue
        budget['bytes'] += size
        budget['files'] += 1
        if budget['files'] > BACKUP_MAX_FILES or (budget['max_bytes'] and budget['bytes'] > budget['max_bytes']):
            raise BackupTooLarge('The data is bigger than the backup size limit.')
        try:
            source = full
            snap = None
            if rel.lower().endswith(SQLITE_EXTS):
                with open(full, 'rb') as handle:
                    is_db = handle.read(16) == SQLITE_MAGIC
                if is_db:
                    snap = os.path.join(snap_dir, f'snap_{os.urandom(4).hex()}.tmp')
                    _sqlite_snapshot(full, snap)
                    source = snap
            archive.write(source, prefix + rel)
            if snap:
                os.remove(snap)
            added += 1
        except OSError as exc:      # a file that vanished or cannot be read must not break the whole backup
            logger.warning("Backup skipped %s: %s", full, redact_secrets(exc))
    return added


def _user_dirs():
    """[(user_id_text, folder)] for every numeric folder in UPLOAD_BOTS_DIR (the folder name is the owner)."""
    found = []
    try:
        names = sorted(os.listdir(UPLOAD_BOTS_DIR))
    except OSError:
        return found
    for name in names:
        folder = os.path.join(UPLOAD_BOTS_DIR, name)
        if name.isdigit() and len(name) <= 19 and os.path.isdir(folder) and not os.path.islink(folder):
            found.append((name, folder))
    return found


def _snapshot_live_database(dest_path):
    with DB_LOCK:
        source = db_connect()
        try:
            target = sqlite3.connect(dest_path)
            try:
                source.backup(target)
            finally:
                target.close()
        finally:
            source.close()


def _db_counts(path):
    """(users, scripts, subscriptions, admins) of a database file."""
    conn = sqlite3.connect(path, timeout=10)
    try:
        return tuple(conn.execute(f'SELECT COUNT(*) FROM {table}').fetchone()[0]
                     for table in ('active_users', 'user_files', 'subscriptions', 'admins'))
    finally:
        conn.close()


def _build_full_backup(zip_path, limit_mb=FULL_BACKUP_MAX_MB, extra_manifest=None, max_file_bytes=None):
    """Write the full backup zip (database + every user folder; never the bot's own code). limit_mb=None means
    no size limit (used for the automatic safety backup). extra_manifest (dict) is added to the manifest;
    max_file_bytes leaves out bigger single files (the automatic Telegram backup uses it when the data is too big
    to send whole). Returns a summary dict."""
    work = tempfile.mkdtemp(prefix='demon_fullbk_')
    try:
        db_snap = os.path.join(work, 'bot_data.db')
        _snapshot_live_database(db_snap)
        counts = _db_counts(db_snap)
        budget = {'bytes': 0, 'files': 0, 'max_bytes': limit_mb * 1024 * 1024 if limit_mb else None,
                  'max_file': max_file_bytes, 'skipped': 0}
        users = {}
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED, allowZip64=True) as archive:
            archive.write(db_snap, 'database/bot_data.db')
            for uid_text, folder in _user_dirs():
                added = _zip_add_folder(archive, folder, f'upload_bots/{uid_text}/', work, budget)
                if added:
                    users[uid_text] = added
            manifest = {'format': BACKUP_FORMAT_FULL, 'version': BACKUP_VERSION,
                        'created': datetime.now().isoformat(timespec='seconds'),
                        'bot_code_included': False,
                        'database_counts': {'users': counts[0], 'scripts': counts[1],
                                            'subscriptions': counts[2], 'admins': counts[3]},
                        'users': users}
            if budget['skipped']:
                manifest['skipped_big_files'] = budget['skipped']
            if extra_manifest:
                manifest.update(extra_manifest)
            archive.writestr('manifest.json', json.dumps(manifest, indent=1))
        return {'counts': counts, 'users': len(users), 'files': sum(users.values()), 'skipped': budget['skipped']}
    finally:
        _rmtree_quiet(work)


def _build_user_backup(owner_id, zip_path, limit_mb=USER_BACKUP_MAX_MB):
    """Write one user's backup zip (their folder + script list). Returns a summary dict;
    'files' is 0 when the folder holds nothing to back up."""
    work = tempfile.mkdtemp(prefix=f'demon_userbk_{owner_id}_')
    try:
        folder = get_user_folder(owner_id)
        budget = {'bytes': 0, 'files': 0, 'max_bytes': limit_mb * 1024 * 1024 if limit_mb else None}
        scripts = [{'name': name, 'type': ftype} for name, ftype in sorted(user_files.get(owner_id, []))]
        with zipfile.ZipFile(zip_path, 'w', zipfile.ZIP_DEFLATED, allowZip64=True) as archive:
            added = _zip_add_folder(archive, folder, 'bots/', work, budget)
            manifest = {'format': BACKUP_FORMAT_USER, 'version': BACKUP_VERSION, 'owner': owner_id,
                        'created': datetime.now().isoformat(timespec='seconds'),
                        'scripts': scripts, 'files': added}
            archive.writestr('manifest.json', json.dumps(manifest, indent=1))
        return {'files': added, 'scripts': len(scripts), 'bytes': budget['bytes']}
    finally:
        _rmtree_quiet(work)


def _send_backup_file(chat_id, zip_path, base_name, caption, progress=None):
    """Send a zip as one document, or as numbered parts (name.zip.001 ...) that fit Telegram's 20 MB read
    limit, so the same file can be sent back for a restore. Returns the number of parts (0 = too big)."""
    size = os.path.getsize(zip_path)
    if size <= PART_BYTES:
        with open(zip_path, 'rb') as handle:
            bot.send_document(chat_id, handle, caption=caption, parse_mode='HTML')
        return 1
    total = -(-size // PART_BYTES)
    if total > MAX_PARTS:
        return 0
    part_dir = tempfile.mkdtemp(prefix='demon_parts_')
    try:
        with open(zip_path, 'rb') as src:
            for index in range(1, total + 1):
                if progress is not None:
                    progress.update(index - 1, total, f'Sending part {index} of {total}...')
                part_path = os.path.join(part_dir, f'{base_name}.zip.{index:03d}')
                with open(part_path, 'wb') as out:
                    out.write(src.read(PART_BYTES))
                text = caption if index == 1 else f'Part {index} of {total}'
                if index == 1:
                    text += (f'\n\nThis backup is big, so it comes in <b>{total} parts</b> '
                             '(.zip.001, .zip.002 ...). Keep all of them; send them back in any order when restoring.')
                with open(part_path, 'rb') as handle:
                    bot.send_document(chat_id, handle, caption=text, parse_mode='HTML')
                os.remove(part_path)
    finally:
        _rmtree_quiet(part_dir)
    return total


# --- Reading a backup zip (shared, zip-slip safe) -----------------------------
def _extract_backup_zip(zip_path, payload_dir, rel_ok, max_bytes, skip_rel=None, skipped=None):
    """Check every entry, then extract into payload_dir. rel_ok(rel) says which entry names are allowed.
    Entries for which skip_rel(rel) is true are checked like the rest but never written (their names are added
    to the skipped list). Returns (manifest_dict, error_text)."""
    try:
        archive = zipfile.ZipFile(zip_path)
    except (zipfile.BadZipFile, OSError):
        return None, 'That file is damaged or is not a zip backup.'
    try:
        with archive:
            items = [i for i in archive.infolist() if not i.is_dir()]
            if not items:
                return None, 'That backup is empty.'
            if len(items) > BACKUP_MAX_FILES:
                return None, f'Too many files in the backup (maximum {BACKUP_MAX_FILES}).'
            seen = set()
            for item in items:
                rel = item.filename
                if not _safe_zip_rel(rel):
                    return None, (f'The backup contains an unsafe path: {rel[:60]!r}... '
                                  f'({len(rel)} characters; {_unsafe_why(rel)}).')
                if item.flag_bits & 0x1:
                    return None, 'The backup is password protected.'
                if ((item.external_attr >> 16) & 0o170000) == 0o120000:
                    return None, f'The backup contains a link, which is not allowed: {rel[:60]!r}.'
                if rel != 'manifest.json' and not rel_ok(rel):
                    return None, f'The backup contains something that does not belong here: {rel[:60]!r}.'
                if rel.lower() in seen:
                    return None, f'The backup contains the same file twice: {rel[:60]!r}.'
                seen.add(rel.lower())
            if 'manifest.json' not in seen:
                return None, 'This is not a backup made by this bot (manifest missing).'
            if skip_rel:
                if skipped is not None:
                    skipped.extend(i.filename for i in items if skip_rel(i.filename))
                items = [i for i in items if not skip_rel(i.filename)]
            if sum(max(0, i.file_size) for i in items) > max_bytes:
                return None, f'The backup is bigger than the {max_bytes // (1024 * 1024)} MB limit.'
            root = os.path.realpath(payload_dir)
            written = 0
            for item in items:
                dest = os.path.realpath(os.path.join(root, item.filename))
                if dest == root or not _path_inside(root, dest):
                    return None, 'The backup contains an unsafe path.'
                os.makedirs(os.path.dirname(dest), exist_ok=True)
                with archive.open(item) as src, open(dest, 'wb') as out:
                    while True:
                        chunk = src.read(1024 * 1024)
                        if not chunk:
                            break
                        written += len(chunk)
                        if written > max_bytes:
                            return None, f'The backup is bigger than the {max_bytes // (1024 * 1024)} MB limit.'
                        out.write(chunk)
    except (zipfile.BadZipFile, OSError, RuntimeError, NotImplementedError):
        return None, 'That backup could not be read (damaged or unsupported zip).'
    try:
        manifest_path = os.path.join(payload_dir, 'manifest.json')
        if os.path.getsize(manifest_path) > 2 * 1024 * 1024:
            return None, 'The backup manifest is too big.'
        with open(manifest_path, 'r', encoding='utf-8') as handle:
            manifest = json.load(handle)
    except (OSError, ValueError):
        return None, 'The backup manifest could not be read.'
    if not isinstance(manifest, dict):
        return None, 'The backup manifest could not be read.'
    try:
        if int(manifest.get('version', 0)) > BACKUP_VERSION:
            return None, 'This backup was made by a newer version of the bot.'
    except (TypeError, ValueError):
        return None, 'The backup manifest could not be read.'
    return manifest, ''


def _inspect_hosting_db(path):
    """Check a file really is a hosting-bot database. Returns (ok, message, counts)."""
    try:
        with open(path, 'rb') as handle:
            if handle.read(16) != SQLITE_MAGIC:
                return False, 'The database inside the backup is not a SQLite database.', None
        conn = sqlite3.connect(path, timeout=10)
        try:
            result = conn.execute('PRAGMA integrity_check').fetchone()
            if not result or result[0] != 'ok':
                return False, 'The database inside the backup is damaged, so I did not restore it.', None
            tables = {row[0] for row in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        finally:
            conn.close()
        missing = [t for t in HOSTING_DB_CORE_TABLES if t not in tables]
        if missing:
            return False, ('The database inside the backup does not look like one from this hosting bot '
                           f'(missing: {", ".join(missing)}). Nothing was changed.'), None
        return True, '', _db_counts(path)
    except sqlite3.Error:
        return False, 'The database inside the backup could not be read. Nothing was changed.', None


def _full_rel_ok(rel):
    parts = rel.split('/')
    if parts[0] == 'source':
        return len(parts) >= 2      # the bot code of an old backup: accepted as an entry, but skipped (see _backup_is_bot_code)
    if parts[0] == 'database':
        return rel == 'database/bot_data.db'
    if parts[0] == 'upload_bots':
        return len(parts) >= 3 and parts[1].isdigit() and len(parts[1]) <= 19
    return False


def _backup_is_bot_code(rel):
    """Entries that hold the hosting bot's own code (old full backups have source/<bot>.py). Never restored."""
    return rel.split('/')[0] == 'source'


def _inspect_full_backup(zip_path, payload_dir):
    """Validate + extract a full backup. The bot code of an old backup is skipped, never extracted.
    Returns (ok, error_text, info)."""
    ignored_code = []
    manifest, err = _extract_backup_zip(zip_path, payload_dir, _full_rel_ok, FULL_BACKUP_MAX_MB * 1024 * 1024,
                                        skip_rel=_backup_is_bot_code, skipped=ignored_code)
    if err:
        return False, err, None
    if manifest.get('format') != BACKUP_FORMAT_FULL:
        return False, ('This is not a full backup. Use <b>Export Full Backup</b> in the admin panel '
                       'to make one.'), None
    db_path = os.path.join(payload_dir, 'database', 'bot_data.db')
    if not os.path.isfile(db_path):
        return False, 'The backup has no database in it.', None
    ok, problem, counts = _inspect_hosting_db(db_path)
    if not ok:
        return False, problem, None
    users = {}
    upload_root = os.path.join(payload_dir, 'upload_bots')
    if os.path.isdir(upload_root):
        for uid_text in sorted(os.listdir(upload_root)):
            count = sum(len(files) for _d, _n, files in os.walk(os.path.join(upload_root, uid_text)))
            users[uid_text] = count
    info = {'counts': counts, 'users': users, 'files': sum(users.values()),
            'ignored_code': [os.path.basename(name) for name in ignored_code],
            'created': str(manifest.get('created', ''))[:19]}
    return True, '', info


def _user_rel_ok(rel):
    parts = rel.split('/')
    return parts[0] == 'bots' and len(parts) >= 2


def _inspect_user_backup(zip_path, payload_dir, owner_id, importer_id):
    """Validate + extract a single user's backup for owner_id. Returns (ok, error_text, info)."""
    manifest, err = _extract_backup_zip(zip_path, payload_dir, _user_rel_ok, USER_BACKUP_MAX_MB * 1024 * 1024)
    if err:
        return False, err, None
    if manifest.get('format') != BACKUP_FORMAT_USER:
        return False, ('This is not a "My Bots" backup. Use the <b>Export My Bots</b> button '
                       'in My Files to make one.'), None
    if manifest.get('owner') != owner_id:
        return False, 'This backup belongs to a different account, so I cannot restore it here.', None
    bots_root = os.path.join(payload_dir, 'bots')
    files = []
    for dirpath, _dirs, names in os.walk(bots_root):
        for name in names:
            files.append(os.path.relpath(os.path.join(dirpath, name), bots_root).replace(os.sep, '/'))
    files.sort()
    if not files:
        return False, 'That backup has no files in it.', None
    # Databases must really be databases, so a bad file cannot break the bot.
    for rel in files:
        if rel.lower().endswith(SQLITE_EXTS):
            full = os.path.join(bots_root, rel)
            try:
                with open(full, 'rb') as handle:
                    magic_ok = handle.read(16) == SQLITE_MAGIC
                if not magic_ok:
                    return False, f'"{rel}" is not a valid SQLite database.', None
                conn = sqlite3.connect(full, timeout=10)
                try:
                    result = conn.execute('PRAGMA integrity_check').fetchone()
                finally:
                    conn.close()
                if not result or result[0] != 'ok':
                    return False, f'"{rel}" is a damaged database.', None
            except sqlite3.Error:
                return False, f'"{rel}" could not be read as a database.', None
    scripts = []
    for entry in manifest.get('scripts') or []:
        name = entry.get('name') if isinstance(entry, dict) else None
        ftype = entry.get('type') if isinstance(entry, dict) else None
        if (not isinstance(name, str) or '/' in name or '\\' in name or not _safe_zip_rel(name)
                or ftype not in ('py', 'js') or not name.lower().endswith('.' + ftype)):
            continue
        if name in files:
            scripts.append((name, ftype))
    existing = {item[0] for item in user_files.get(owner_id, [])}
    new_scripts = [s for s in scripts if s[0] not in existing]
    limit = get_user_file_limit(owner_id)
    if len(existing) + len(new_scripts) > limit:
        return False, (f'Restoring would put you over your file limit ({len(existing)} now + {len(new_scripts)} new, '
                       f'limit {limit}). Delete a bot first or ask an admin. Nothing was changed.'), None
    info = {'files': files, 'scripts': scripts, 'new_scripts': len(new_scripts), 'bots_root': bots_root,
            'existing_files': sum(1 for rel in files if os.path.isfile(os.path.join(get_user_folder(owner_id), rel))),
            'created': str(manifest.get('created', ''))[:19]}
    return True, '', info


# --- Stopping scripts before a restore -----------------------------------------
def _stop_scripts(owner_id=None):
    """Stop running scripts (all, or one user's) without letting the watchdog bring them back."""
    with STATE_LOCK:
        items = [(key, info) for key, info in bot_scripts.items()
                 if owner_id is None or str(info.get('script_owner_id', '')) == str(owner_id)]
    for key, info in items:
        RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        try:
            kill_process_tree(info)
        except Exception:
            logger.exception("Could not stop %s before restore", key)
        _forget_script(key)
    if owner_id is None:
        autostart_clear()
    else:
        autostart_clear(owner_id=owner_id)
    return len(items)


# --- Admin: full backup ----------------------------------------------------------
def _reload_memory_state():
    """After a database restore: reload the in-memory copies from the new database."""
    with STATE_LOCK:
        user_subscriptions.clear()
        user_files.clear()
        active_users.clear()
        admin_ids.clear()
        admin_ids.update({ADMIN_ID, OWNER_ID})
        banned_users.clear()
        user_limits.clear()
        mandatory_channels.clear()
        load_data()


def _replace_live_database(source_path):
    """Overwrite the live database with source_path (SQLite backup API, safe while in use) and reload memory."""
    with DB_LOCK:
        source = sqlite3.connect(source_path, timeout=30)
        try:
            dest = db_connect()
            try:
                try:
                    dest.execute('PRAGMA journal_mode=DELETE')
                except sqlite3.Error:
                    pass
                source.backup(dest)
            finally:
                dest.close()
        finally:
            source.close()
        init_db()            # missing tables are created and the owner / main admin are always kept
        _reload_memory_state()


def full_backup_callback(call):
    """Send ONE zip: database + every user's uploaded bots and data (not the hosting bot's own code)."""
    if not _can_backup_global(call.from_user.id):
        bot.answer_callback_query(call.id, '⚠️ Only the owner can export the full backup.', show_alert=True)
        return
    if not BACKUP_OP_LOCK.acquire(blocking=False):
        bot.answer_callback_query(call.id, '⏳ Another backup or restore is running. Try again in a minute.', show_alert=True)
        return
    tmp_dir = tempfile.mkdtemp(prefix='demon_fullexport_')
    pm = None
    try:
        bot.answer_callback_query(call.id, 'Preparing the full backup...')
        pm = ui_anim(call.message.chat.id, 'Building Backup', 'Database + all users\' bots and data. This can take a minute.')
        base = f'demon_full_backup_{_now_stamp()}'
        zip_path = os.path.join(tmp_dir, base + '.zip')
        try:
            summary = _build_full_backup(zip_path)
        except BackupTooLarge:
            _say_via(pm, call.message.chat.id,
                     ui_warn('Backup Too Big', ui_row('📏', 'Limit', f'{FULL_BACKUP_MAX_MB} MB'),
                             'The data is bigger than the backup limit.',
                             foot='The limit can be raised with FULL_BACKUP_MAX_MB.'))
            return
        counts = summary['counts']
        caption = ui_msg('📦', 'Full Backup',
                         ui_row('🗄', 'Database', f'{ui_num(counts[0])} users, {ui_num(counts[1])} scripts, '
                                f'{ui_num(counts[2])} subs, {ui_num(counts[3])} admins'),
                         ui_row('📂', 'Bots and data', f'{ui_num(summary["users"])} users, {ui_num(summary["files"])} files'),
                         ui_row('💾', 'Size', _human_size(os.path.getsize(zip_path))),
                         ui_row('🧩', 'Bot code', 'not included', bold=False),
                         foot='Keep it safe, it holds everyone\'s code and data. Use Import Full Backup to restore it. '
                              'A restore never changes the running version.')
        if pm is not None:
            pm.update(label='Backup is ready, sending the file...')
        sent = _send_backup_file(call.message.chat.id, zip_path, base, caption, progress=pm)
        if not sent:
            _say_via(pm, call.message.chat.id,
                     ui_warn('Backup Too Big To Send', 'Telegram cannot take it, even in parts.',
                             foot='Copy the data folder from the server instead.'))
        else:
            _say_via(pm, call.message.chat.id, ui_ok('Backup Ready', 'The backup file is attached below.'))
        logger.info("Full backup exported by admin %s (%s users, %s files, %s part(s))",
                    call.from_user.id, summary['users'], summary['files'], sent)
    except Exception as exc:
        logger.exception('Full backup export failed')
        _say_via(pm, call.message.chat.id,
                 ui_err('Backup Failed', 'The full backup could not be made. Nothing was changed.', foot='The details are in the server log.'))
    finally:
        if pm is not None and not pm._done:
            pm.fail()
        BACKUP_OP_LOCK.release()
        _rmtree_quiet(tmp_dir)


def _start_waiting(call, kind, owner_id, title, body):
    bot.answer_callback_query(call.id)
    _expire_pending_imports()
    with IMPORT_LOCK:
        old = PENDING_IMPORT_WAIT.pop(call.from_user.id, None)
        PENDING_IMPORT_WAIT[call.from_user.id] = {'kind': kind, 'owner': owner_id, 'time': time.time(),
                                                  'dir': None, 'parts': {}}
    if old:
        _rmtree_quiet(old.get('dir'))
    _t_emoji, _, _t_rest = title.partition(' ')
    bot.send_message(call.message.chat.id,
                     ui_msg(_t_emoji, _t_rest or title, ui_raw(body), foot=f'The request expires in {IMPORT_TTL // 60} minutes.'),
                     parse_mode='HTML', reply_markup=_cancel_markup())


def full_restore_callback(call):
    if not _can_backup_global(call.from_user.id):
        bot.answer_callback_query(call.id, '⚠️ Only the owner can import the full backup.', show_alert=True)
        return
    _start_waiting(
        call, 'full', None, '♻️ Import Full Backup',
        'Send me the full backup <code>.zip</code> you exported earlier (as a file). If it came in parts '
        '(<code>.zip.001</code>, <code>.zip.002</code> ...), send every part, then tap <b>Done</b>.\n\n'
        '⚠️ This restores <b>everything</b>: the database, every user\'s bots and data (back into each user\'s '
        'own folder). The code of the hosting bot itself is never touched. I will show you a summary and ask you to confirm first. '
        'A backup of the current state is saved automatically before anything is overwritten.')


# --- User: My Bots backup -------------------------------------------------------
def _user_target(call):
    """Parse 'ubk_<owner>' / 'ubr_<owner>' and check the requester may manage that folder."""
    try:
        owner_id = int(call.data.split('_', 1)[1])
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, 'Error: invalid action data.', show_alert=True)
        return None
    if not _may_manage_bot_data(call.from_user.id, owner_id):
        logger.warning("User %s tried a bot backup for user %s", call.from_user.id, owner_id)
        bot.answer_callback_query(call.id, '⚠️ You can only export or import your own bots.', show_alert=True)
        return None
    return owner_id


def user_backup_callback(call):
    """Send ONE zip with this user's own bots (scripts) and their data."""
    owner_id = _user_target(call)
    if owner_id is None:
        return
    if not BACKUP_OP_LOCK.acquire(blocking=False):
        bot.answer_callback_query(call.id, '⏳ Another backup is running. Try again in a minute.', show_alert=True)
        return
    tmp_dir = tempfile.mkdtemp(prefix=f'demon_userexport_{owner_id}_')
    pm = None
    try:
        bot.answer_callback_query(call.id, 'Preparing your backup...')
        pm = ui_anim(call.message.chat.id, 'Building Backup', 'Packing your bots and their data.')
        base = f'my_bots_backup_{owner_id}_{_now_stamp()}'
        zip_path = os.path.join(tmp_dir, base + '.zip')
        try:
            summary = _build_user_backup(owner_id, zip_path)
        except BackupTooLarge:
            _say_via(pm, call.message.chat.id,
                     ui_warn('Backup Too Big', ui_row('📏', 'Limit', f'{USER_BACKUP_MAX_MB} MB'),
                             'Your bots and data are bigger than the backup limit.'))
            return
        if not summary['files']:
            _say_via(pm, call.message.chat.id, ui_warn('Nothing To Export', 'You have no bots or data to export yet.'))
            return
        caption = ui_msg('📦', 'My Bots Backup',
                         ui_row('🤖', 'Bots', ui_num(summary['scripts'])),
                         ui_row('📄', 'Files', ui_num(summary['files'])),
                         ui_row('💾', 'Size', _human_size(os.path.getsize(zip_path))),
                         foot='Your bot code and its data. Use Import My Bots in My Files to restore it.')
        if pm is not None:
            pm.update(label='Backup is ready, sending the file...')
        sent = _send_backup_file(call.message.chat.id, zip_path, base, caption, progress=pm)
        if not sent:
            _say_via(pm, call.message.chat.id, ui_warn('Backup Too Big To Send', 'Telegram cannot take this file.'))
        else:
            _say_via(pm, call.message.chat.id, ui_ok('Backup Ready', 'Your backup file is attached below.'))
        logger.info("User backup exported: owner=%s by=%s files=%s", owner_id, call.from_user.id, summary['files'])
    except Exception as exc:
        logger.exception('User backup export failed')
        _say_via(pm, call.message.chat.id,
                 ui_err('Export Failed', 'Your backup could not be made. Nothing was changed.', foot='Please try again in a minute.'))
    finally:
        if pm is not None and not pm._done:
            pm.fail()
        BACKUP_OP_LOCK.release()
        _rmtree_quiet(tmp_dir)


def user_restore_callback(call):
    owner_id = _user_target(call)
    if owner_id is None:
        return
    _start_waiting(
        call, 'user', owner_id, '♻️ Import My Bots',
        'Send me the <code>.zip</code> you exported with <b>Export My Bots</b> (as a file). If it came in parts '
        '(<code>.zip.001</code>, <code>.zip.002</code> ...), send every part, then tap <b>Done</b>.\n\n'
        '⚠️ Your bots and data go back into your own folder only; files with the same name are replaced. '
        'Your running bots are stopped for the restore. I will show you a summary and ask you to confirm first, '
        'and your current files are backed up automatically (and sent to you).')


# --- Receiving the uploaded backup (single zip or parts) --------------------------
def _say(chat_id, text, markup=None):
    return bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=markup)


def _wait_permission_ok(uid, pend):
    if pend['kind'] == 'full':
        return _can_backup_global(uid)
    return _may_manage_bot_data(uid, pend['owner'])


def _discard_wait(uid):
    with IMPORT_LOCK:
        pend = PENDING_IMPORT_WAIT.pop(uid, None)
    if pend:
        _rmtree_quiet(pend.get('dir'))
    return pend


def _receive_backup_upload(message, pend):
    uid = message.from_user.id
    chat_id = message.chat.id
    if not _wait_permission_ok(uid, pend):
        _discard_wait(uid)
        _say(chat_id, '⚠️ You are not allowed to do this restore. Nothing was changed.')
        return
    name = message.document.file_name or ''
    part = PART_RE.search(name)
    if not part and not name.lower().endswith('.zip'):
        _say(chat_id, '⚠️ Please send the backup <code>.zip</code> (or its <code>.zip.001</code>, '
                      '<code>.zip.002</code> parts). Nothing was changed.', _cancel_markup())
        return
    try:
        content = _download_upload(message, MAX_UPLOAD_MB)
    except ValueError as exc:
        _say(chat_id, f'⚠️ {html_escape(str(exc))}', _cancel_markup())
        return
    except Exception as exc:
        logger.warning("Backup download failed: %s", redact_secrets(exc))
        _say(chat_id, '⚠️ I could not download that file. Please try again.', _cancel_markup())
        return
    with IMPORT_LOCK:
        if not pend.get('dir'):
            pend['dir'] = tempfile.mkdtemp(prefix='demon_restore_')
        work = pend['dir']
        pend['time'] = time.time()
    if part:
        number = int(part.group(1))
        if number < 1 or number > MAX_PARTS:
            _say(chat_id, '⚠️ That part number is not valid.', _cancel_markup())
            return
        part_path = os.path.join(work, f'part_{number:03d}')
        with open(part_path, 'wb') as handle:
            handle.write(content)
        pend['parts'][number] = part_path
        have_numbers = sorted(pend['parts'])
        have = ', '.join(str(n) for n in have_numbers)
        missing = [n for n in range(1, have_numbers[-1] + 1) if n not in pend['parts']]
        # Every part except the last is exactly PART_BYTES long, so the size tells whether more parts are coming.
        is_last = len(content) < PART_BYTES
        if is_last:
            pend['last_part'] = number
        last_known = pend.get('last_part')
        if missing:
            need = ', '.join(f'<code>.zip.{n:03d}</code>' for n in missing[:12])
            body = (f'✅ Part {number} received. Parts so far: {have}.\n'
                    f'⏳ <b>Still missing:</b> {need}. Send {"it" if len(missing) == 1 else "them"} now.')
        elif is_last or (last_known and last_known == have_numbers[-1]):
            body = (f'✅ Part {number} received. Parts so far: {have}.\n'
                    f'🎉 This was the last part and nothing is missing ({len(have_numbers)} parts in total). '
                    'Tap <b>Done, check backup</b> now.')
        elif last_known and have_numbers[-1] < last_known:
            body = (f'✅ Part {number} received. Parts so far: {have}.\n'
                    f'⏳ <b>More parts are still to come.</b> Send <code>.zip.{have_numbers[-1] + 1:03d}</code> next.')
        else:
            body = (f'✅ Part {number} received. Parts so far: {have}.\n'
                    f'⏳ <b>More parts are still to come</b> (this one is full size, so it is not the last). '
                    f'Send <code>.zip.{have_numbers[-1] + 1:03d}</code> next. '
                    'If you have already sent every part, tap <b>Done, check backup</b>.')
        _say(chat_id, body, _parts_markup())
        return
    with IMPORT_LOCK:
        PENDING_IMPORT_WAIT.pop(uid, None)
    zip_path = os.path.join(work, 'upload.zip')
    with open(zip_path, 'wb') as handle:
        handle.write(content)
    _stage_backup(chat_id, uid, pend, zip_path)


def _assemble_parts(pend):
    """Join the received parts into one zip. Returns (zip_path, error_text)."""
    numbers = sorted(pend['parts'])
    if numbers != list(range(1, numbers[-1] + 1)):
        missing = [str(n) for n in range(1, numbers[-1] + 1) if n not in pend['parts']]
        return None, f'Part(s) missing: {", ".join(missing)}. Send them, then tap Done again.'
    limit = (FULL_BACKUP_MAX_MB if pend['kind'] == 'full' else USER_BACKUP_MAX_MB) * 1024 * 1024
    zip_path = os.path.join(pend['dir'], 'upload.zip')
    total = 0
    with open(zip_path, 'wb') as out:
        for number in numbers:
            with open(pend['parts'][number], 'rb') as src:
                while True:
                    chunk = src.read(1024 * 1024)
                    if not chunk:
                        break
                    total += len(chunk)
                    if total > limit:
                        return None, 'The parts together are bigger than the backup size limit.'
                    out.write(chunk)
            os.remove(pend['parts'][number])
    return zip_path, ''


def _stage_backup(chat_id, uid, pend, zip_path):
    """Validate the uploaded zip and ask for confirmation. Owns pend['dir'] from here on."""
    work = pend['dir']
    keep = False
    pm = ui_anim(chat_id, 'Checking Backup', 'Reading the file and checking that it is safe.')
    try:
        payload = os.path.join(work, 'payload')
        os.makedirs(payload, exist_ok=True)
        if pend['kind'] == 'full':
            ok, problem, info = _inspect_full_backup(zip_path, payload)
        else:
            ok, problem, info = _inspect_user_backup(zip_path, payload, pend['owner'], uid)
        if not ok:
            _say_via(pm, chat_id, f'⚠️ {problem} Nothing was changed.')
            return
        try:
            os.remove(zip_path)
        except OSError:
            pass
        if pend['kind'] == 'full':
            counts = info['counts']
            now = _db_counts(DATABASE_PATH)
            code_line = ('• Bot code: this is an older backup that holds a copy of the bot code. That copy is skipped; '
                         'the running bot code stays exactly as it is'
                         if info['ignored_code'] else '• Bot code: not touched, the running version stays')
            text = ui_msg('⚠️', 'Confirm Full Restore',
                          ui_row('🕒', 'Backup from', info['created']) if info['created'] else None,
                          ui_row('📦', 'In the backup', f'{ui_num(counts[0])} users, {ui_num(counts[1])} scripts, {ui_num(counts[2])} subs, '
                                 f'{ui_num(counts[3])} admins; {ui_num(len(info["users"]))} user folders, {ui_num(info["files"])} files'),
                          ui_row('🟢', 'Live now', f'{ui_num(now[0])} users, {ui_num(now[1])} scripts, {ui_num(now[2])} subs, {ui_num(now[3])} admins'),
                          ui_section('♻️', 'This will replace'),
                          '• The whole database',
                          f'• Each of the {ui_num(len(info["users"]))} user folders (every user\'s bots and data go back to that same user)',
                          ui_esc(code_line),
                          foot='All running bots are stopped. A full backup of the current state is saved first and sent to you. Continue?')
            entry = {'kind': 'full', 'user_id': uid, 'dir': work, 'payload': payload, 'info': info}
        else:
            text = ui_msg('⚠️', 'Confirm Restore',
                          ui_row('🕒', 'Backup from', info['created']) if info['created'] else None,
                          ui_row('📄', 'Files', ui_num(len(info['files']))),
                          ui_row('🤖', 'Bots', f'{ui_num(len(info["scripts"]))} ({ui_num(info["new_scripts"])} not in your list yet)'),
                          ui_row('♻️', 'Will be replaced', f'{ui_num(info["existing_files"])} existing file(s) with the same name'),
                          foot='Your running bots will be stopped. Your current files are backed up first and sent to you. Continue?')
            entry = {'kind': 'user', 'user_id': uid, 'owner': pend['owner'], 'dir': work, 'payload': payload,
                     'info': info}
        token = _store_confirm(entry)
        keep = True
        _say_via(pm, chat_id, text, _confirm_markup(token))
    except Exception:
        logger.exception('Restore staging failed')
        _say_via(pm, chat_id, '⚠️ Something went wrong while checking that backup. Nothing was changed.')
    finally:
        if pm is not None and not pm._done:
            pm.fail()
        if not keep:
            _rmtree_quiet(work)


def _handle_pending_import_upload(message):
    """Called first by the document handler. True when the document belonged to a waiting restore."""
    uid = message.from_user.id
    with IMPORT_LOCK:
        _expire_pending_imports()
        pend = PENDING_IMPORT_WAIT.get(uid)
    if not pend:
        return False
    try:
        _receive_backup_upload(message, pend)
    except Exception:
        logger.exception('Restore upload failed')
        _discard_wait(uid)
        bot.reply_to(message, ui_warn('Something Went Wrong', 'Something went wrong while checking that file.', foot='Nothing was changed.'), parse_mode='HTML')
    return True


# --- Applying a restore -----------------------------------------------------------
def _report(progress, done, total, label):
    """Tell an optional progress callback how far a long job is. A broken callback never stops the job."""
    if progress is None:
        return
    try:
        progress(done, total, label)
    except Exception:
        pass


def _apply_full_restore(entry, progress=None):
    """Safety backup -> database -> user folders. The bot code is never written. Returns a result dict.
    progress(done, total, label) is optional and only reports the 5 stages."""
    info = entry['info']
    payload = entry['payload']
    os.makedirs(FULL_BACKUP_DIR, exist_ok=True)
    _report(progress, 0, 5, 'Stopping running bots...')
    stopped = _stop_scripts()
    _report(progress, 1, 5, 'Saving a safety backup of the current data...')
    pre_path = os.path.join(FULL_BACKUP_DIR, f'full_backup_before_restore_{_now_stamp()}.zip')
    _build_full_backup(pre_path, limit_mb=None)       # nothing is touched if this fails
    _prune_backups(FULL_BACKUP_DIR, 'full_backup_before_restore_')
    prev_db = os.path.join(entry['dir'], 'previous_bot_data.db')
    _snapshot_live_database(prev_db)
    _report(progress, 2, 5, 'Preparing the user folders...')
    incoming = tempfile.mkdtemp(prefix='.restore_in_', dir=UPLOAD_BOTS_DIR)
    old_dir = tempfile.mkdtemp(prefix='.restore_old_', dir=UPLOAD_BOTS_DIR)
    swapped = []
    db_replaced = False
    try:
        upload_root = os.path.join(payload, 'upload_bots')
        for uid_text in sorted(info['users']):
            shutil.move(os.path.join(upload_root, uid_text), os.path.join(incoming, uid_text))
        _report(progress, 3, 5, 'Restoring the database...')
        _replace_live_database(os.path.join(payload, 'database', 'bot_data.db'))
        db_replaced = True
        _report(progress, 4, 5, 'Putting the user folders back...')
        for uid_text in sorted(info['users']):
            target = os.path.join(UPLOAD_BOTS_DIR, uid_text)
            if os.path.lexists(target):
                os.rename(target, os.path.join(old_dir, uid_text))
            swapped.append(uid_text)
            os.rename(os.path.join(incoming, uid_text), target)
    except Exception:
        rollback_ok = True
        for uid_text in reversed(swapped):          # put every folder back the way it was
            target = os.path.join(UPLOAD_BOTS_DIR, uid_text)
            saved = os.path.join(old_dir, uid_text)
            try:
                if os.path.lexists(saved):
                    _rmtree_quiet(target)
                    os.rename(saved, target)
            except OSError:
                rollback_ok = False
                logger.exception("Could not roll back folder %s (original kept in %s)", uid_text, old_dir)
        if db_replaced:
            try:
                _replace_live_database(prev_db)
            except Exception:
                logger.exception("Could not roll back the database")
        _rmtree_quiet(incoming)
        if rollback_ok:
            _rmtree_quiet(old_dir)
        raise
    _rmtree_quiet(incoming)
    _rmtree_quiet(old_dir)
    _report(progress, 5, 5, 'Checking the restored files...')
    missing = 0
    for owner_id, items in list(user_files.items()):
        for file_name, _ftype in list(items):
            if not os.path.isfile(os.path.join(UPLOAD_BOTS_DIR, str(owner_id), file_name)):
                missing += 1
    return {'pre_path': pre_path, 'stopped': stopped, 'missing': missing}


def _apply_user_restore(entry, progress=None):
    """Back up the user's current folder, then write the staged files into their own folder only.
    progress(done, total, label) is optional: 2 steps + one per restored file."""
    owner_id = entry['owner']
    info = entry['info']
    root = os.path.realpath(get_user_folder(owner_id))
    upload_root = os.path.realpath(UPLOAD_BOTS_DIR)
    if root == upload_root or not _path_inside(upload_root, root) or os.path.basename(root) != str(owner_id):
        raise RuntimeError('Your folder could not be verified.')
    total_steps = 2 + len(info['files'])
    _report(progress, 0, total_steps, 'Stopping your running bots...')
    stopped = _stop_scripts(owner_id)
    _report(progress, 1, total_steps, 'Saving a safety backup of your files...')
    pre_path = None
    backup_dir = os.path.join(USER_BACKUP_DIR, str(owner_id))
    os.makedirs(backup_dir, exist_ok=True)
    candidate = os.path.join(backup_dir, f'my_bots_before_restore_{_now_stamp()}.zip')
    if _build_user_backup(owner_id, candidate, limit_mb=None)['files']:
        pre_path = candidate
        _prune_backups(backup_dir, 'my_bots_before_restore_')
    else:
        os.remove(candidate)
    written = 0
    _report(progress, 2, total_steps, 'Restoring your files...')
    for rel in info['files']:
        src = os.path.join(info['bots_root'], rel)
        dest = os.path.join(root, rel)
        dest_dir = os.path.dirname(dest)
        os.makedirs(dest_dir, exist_ok=True)
        if not _path_inside(root, os.path.realpath(dest_dir)):
            raise RuntimeError('Unsafe target folder.')
        tmp_target = os.path.join(dest_dir, f'.import_{os.urandom(4).hex()}.tmp')
        try:
            shutil.copyfile(src, tmp_target)
            os.replace(tmp_target, dest)
        finally:
            if os.path.exists(tmp_target):
                try:
                    os.remove(tmp_target)
                except OSError:
                    pass
        if rel.lower().endswith(SQLITE_EXTS):
            for suffix in ('-wal', '-shm', '-journal'):   # stale side files would corrupt the restored database
                try:
                    os.remove(dest + suffix)
                except OSError:
                    pass
        written += 1
        _report(progress, 2 + written, total_steps, f'Restoring your files ({written}/{len(info["files"])})...')
    for name, ftype in info['scripts']:
        save_user_file(owner_id, name, ftype)
    return {'pre_path': pre_path, 'stopped': stopped, 'written': written}


def import_confirm_callback(call):
    uid = call.from_user.id
    if call.data == 'impc_cancel':
        _discard_wait(uid)
        bot.answer_callback_query(call.id, 'Cancelled.')
        _edit_or_send(call, ui_msg('❎', 'Cancelled', 'Nothing was changed.'))
        return
    if call.data == 'impc_done':
        _finish_parts(call)
        return
    try:
        _, action, token = call.data.split('_', 2)
    except ValueError:
        bot.answer_callback_query(call.id, 'Invalid action.', show_alert=True)
        return
    with IMPORT_LOCK:
        _expire_pending_imports()
        entry = PENDING_IMPORT_CONFIRM.get(token)
        if not entry:
            bot.answer_callback_query(call.id, '⚠️ This request expired. Start the restore again.', show_alert=True)
            return
        if entry['user_id'] != uid:
            bot.answer_callback_query(call.id, '⚠️ This is not your request.', show_alert=True)
            return
        PENDING_IMPORT_CONFIRM.pop(token, None)      # one use only
    try:
        if action != 'yes':
            bot.answer_callback_query(call.id, 'Cancelled.')
            _edit_or_send(call, ui_msg('❎', 'Cancelled', 'Nothing was changed.'))
            return
        if not BACKUP_OP_LOCK.acquire(blocking=False):
            with IMPORT_LOCK:                 # keep the staged restore so the same button can be tapped again
                PENDING_IMPORT_CONFIRM[token] = entry
            entry = {}
            bot.answer_callback_query(call.id, '⏳ Another backup or restore is running. Tap Yes again in a minute.', show_alert=True)
            return
        try:
            bot.answer_callback_query(call.id, 'Restoring...')
            pm = _call_anim(call, 'Restoring', 'Please wait, this can take a minute.')
            try:
                if entry['kind'] == 'full':
                    _confirm_full_restore(call, entry)
                else:
                    _confirm_user_restore(call, entry)
            finally:
                if pm is not None and not pm._done:
                    pm.fail()
        finally:
            BACKUP_OP_LOCK.release()
    finally:
        _rmtree_quiet(entry.get('dir'))


def _finish_parts(call):
    uid = call.from_user.id
    with IMPORT_LOCK:
        pend = PENDING_IMPORT_WAIT.get(uid)
    if not pend or not pend.get('parts'):
        bot.answer_callback_query(call.id, '⚠️ No parts received yet. Send the backup file(s) first.', show_alert=True)
        return
    if not _wait_permission_ok(uid, pend):
        _discard_wait(uid)
        bot.answer_callback_query(call.id, '⚠️ You are not allowed to do this restore.', show_alert=True)
        return
    try:
        zip_path, problem = _assemble_parts(pend)
    except OSError:
        zip_path, problem = None, 'I could not join the parts.'
    if not zip_path:
        bot.answer_callback_query(call.id, f'⚠️ {problem}', show_alert=True)
        return
    with IMPORT_LOCK:
        PENDING_IMPORT_WAIT.pop(uid, None)
    bot.answer_callback_query(call.id, 'Checking the backup...')
    _stage_backup(call.message.chat.id, uid, pend, zip_path)


def _send_safety_backup(chat_id, pre_path, caption):
    if not pre_path:
        return
    try:
        base = os.path.splitext(os.path.basename(pre_path))[0]
        sent = _send_backup_file(chat_id, pre_path, base, caption)
        if not sent:
            _say(chat_id, 'The safety backup is too big for Telegram; it is kept on the server '
                          f'(<code>{html_escape(os.path.relpath(pre_path, BASE_DIR))}</code>).')
    except Exception:
        logger.exception('Could not send the safety backup')


def _restore_done(call, text, full=False):
    """Final message of a restore. It carries a FRESH main menu: the old keyboard still showed the numbers (Files, Users,
    counts...) from before the restore, and a keyboard only changes when a new message brings one. After a full
    restore every other remembered screen is dropped (it described the old data) and every other admin gets a fresh menu."""
    chat_id = call.message.chat.id
    uid = call.from_user.id
    if full:
        _nav_forget_screens()
    try:
        menu = create_main_menu_inline(uid)
    except Exception:
        logger.exception('Could not build the menu after the restore')
        menu = None
    _edit_or_send(call, text, menu)
    if full:
        for admin_id in sorted(admin_ids):
            if admin_id != chat_id:
                try:
                    _nav_refresh_chat(admin_id, admin_id, '🔄 Backup restore hua. Menu ke numbers naye hain.', force=True)
                except Exception:
                    logger.exception('Could not refresh the menu of admin %s', admin_id)


def _confirm_full_restore(call, entry):
    uid = call.from_user.id
    if not _can_backup_global(uid):
        _edit_or_send(call, '⚠️ Only the owner can restore the full backup. Nothing was changed.')
        return
    try:
        pm = getattr(call, '_pm', None)
        pm = pm if isinstance(pm, ProgressMessage) else None
        result = _apply_full_restore(entry, progress=(pm.update if pm is not None else None))
    except Exception as exc:
        logger.exception('Full restore failed')
        _edit_or_send(call, ui_err('Restore Failed', 'The database and user folders were put back the way they were.',
                                   foot='The details are in the server log.'))
        return
    logger.warning("Full backup restored by admin %s; safety backup at %s", uid, result['pre_path'])
    info = entry['info']
    lines = [ui_row('🗄', 'Database', f'{ui_num(len(active_users))} users, {ui_num(sum(len(v) for v in user_files.values()))} scripts, '
                    f'{ui_num(len(user_subscriptions))} subs, {ui_num(len(admin_ids))} admins'),
             ui_row('📂', 'Bots and data', f'{ui_num(len(info["users"]))} user folders, {ui_num(info["files"])} files'),
             ui_row('🧩', 'Bot code', 'not touched, the running version stays'
                    + (' (old copy in this backup skipped)' if info['ignored_code'] else ''), bold=False)]
    if result['stopped']:
        lines.append(ui_row('🛑', 'Stopped', f'{ui_num(result["stopped"])} running bot(s); start them again from My Files or Run All'))
    if result['missing']:
        lines.append(ui_row('⚠️', 'No file on disk', f'{ui_num(result["missing"])} script(s) in the list'))
    _restore_done(call, ui_ok('Full Backup Restored', *lines, foot='The state from before the restore was saved and is attached below.'), full=True)
    _send_safety_backup(call.message.chat.id, result['pre_path'], 'Backup of everything as it was before this restore.')


def _confirm_user_restore(call, entry):
    uid = call.from_user.id
    owner_id = entry['owner']
    if not _may_manage_bot_data(uid, owner_id):
        _edit_or_send(call, '⚠️ You can only restore your own bots. Nothing was changed.')
        return
    try:
        pm = getattr(call, '_pm', None)
        pm = pm if isinstance(pm, ProgressMessage) else None
        result = _apply_user_restore(entry, progress=(pm.update if pm is not None else None))
    except Exception as exc:
        logger.exception('User restore failed')
        _edit_or_send(call, ui_err('Restore Failed', 'Some files may not have been replaced; your previous files '
                                   'are in the backup that was made first.', foot='The details are in the server log.'))
        return
    logger.info("User backup restored: owner=%s by=%s files=%s", owner_id, uid, result['written'])
    text = ui_ok('Bots Restored',
                 ui_row('📄', 'Files back', ui_num(result['written'])),
                 ui_row('🤖', 'Bots in My Files', ui_num(len(user_files.get(owner_id, [])))),
                 foot='Start your bots again to use them.'
                      + (' Your previous files were backed up and are attached below.' if result['pre_path'] else ''))
    _restore_done(call, text)
    _send_safety_backup(call.message.chat.id, result['pre_path'], 'Backup of your files as they were before this restore.')


# --- Automatic Telegram backup + restore after a wipe (v13, OFF by default since v15) -------------------------------------------------------
# Default since v15: everything below is OFF. Nothing is sent, pinned or restored unless the owner sets
# AUTO_BACKUP_MINUTES (for example 30) and/or AUTO_RESTORE_ON_BOOT=1. The manual full backup (Export / Import) is separate.
# Why: on a host whose disk is wiped on every redeploy / restart (Railway without a Volume) the database and every
# user's files are gone, and the v11 auto-resume has nothing to resume. So the bot keeps a copy OUTSIDE the server:
#   * The normal full backup (same zip as "Export Full Backup": database + every user's bots, data and .env, never
#     the host code) is sent to the owner's private chat, pinned, and the previous pinned one is unpinned.
#     It runs on a timer (AUTO_BACKUP_MINUTES, default 0 = off) and a little after a real change (new or deleted
#     file, subscription, ban, admin or limit change). At most one every AUTO_BACKUP_MIN_GAP_MINUTES (5), and nothing
#     is sent when nothing changed since the last one.
#   * On boot, when this install is empty (wiped), the pinned message of the owner chat is read. Only a zip document
#     that THIS bot sent itself to the owner chat is accepted; it goes through the same safe import checks as a manual
#     restore (zip-slip, links, size, database check). Existing data is never replaced.
# Telegram lets a bot download files up to 20 MB, so the backup must stay under about 19 MB. A bigger one falls back to
# database + small files, and the owner is told once.
AUTO_BACKUP_MINUTES = max(0, _env_int('AUTO_BACKUP_MINUTES', 0))      # 0 = off (default); e.g. 30 switches it on
AUTO_BACKUP_MIN_GAP_SECONDS = max(1, _env_int('AUTO_BACKUP_MIN_GAP_MINUTES', 5)) * 60
AUTO_BACKUP_KEEP = max(1, min(10, _env_int('AUTO_BACKUP_KEEP', 3)))              # backup messages kept in the chat
AUTO_BACKUP_MAX_BYTES = max(1, min(_env_int('AUTO_BACKUP_MAX_MB', 19), 19)) * 1024 * 1024
AUTO_RESTORE_ON_BOOT = os.environ.get('AUTO_RESTORE_ON_BOOT', '0').strip().lower() in ('1', 'on', 'true', 'yes', 'enable', 'enabled')   # off unless switched on
AUTO_BACKUP_SETTLE_SECONDS = 20          # a change waits this long, so a burst of changes becomes one backup
AUTO_BACKUP_RAW_LIMIT_MB = 150           # stop packing early when the data is far too big to ever fit
AUTO_BACKUP_TIERS = ((None, 'full'), (1024 * 1024, 'light'), (128 * 1024, 'light'))   # (biggest single file kept, level)
AUTO_RESTORE_RETRY_DELAYS = (0, 20, 60, 180, 600, 1800)
AUTO_RESTORE_BOOT_WAIT = 90              # boot waits this long for the restore before it goes on (the rest continues in the background)
TELEGRAM_DOWNLOAD_LIMIT = 20 * 1024 * 1024
AUTO_BACKUP_NAME_RE = re.compile(r'^demon_(auto|full)_backup_\d{8}_\d{6}\.zip$')
AUTO_BACKUP_STATE_PATH = os.path.join(IROTECH_DIR, 'auto_backup_state.json')
_AB_STATE_KEYS = ('last_ok', 'last_size', 'last_level', 'last_fp', 'ids', 'last_error', 'big_warned', 'intro_sent',
                  'last_skipped', 'restored_at')
_AB_LOCK = threading.RLock()
_AB = {'state': {}, 'loaded': False, 'pending': 0.0, 'hold': False, 'last_check': 0.0, 'next_ok': 0.0,
       'started': False, 'late': False, 'worker_alive': False}
_AB_FP_TABLES = (('subscriptions', 'SELECT * FROM subscriptions ORDER BY 1'),
                 ('user_files', 'SELECT * FROM user_files ORDER BY 1, 2'),
                 ('admins', 'SELECT * FROM admins ORDER BY 1'),
                 ('banned_users', 'SELECT * FROM banned_users ORDER BY 1'),
                 ('user_limits', 'SELECT * FROM user_limits ORDER BY 1'),
                 ('mandatory_channels', 'SELECT * FROM mandatory_channels ORDER BY 1'),
                 ('suspended_users', 'SELECT * FROM suspended_users ORDER BY 1'),
                 ('temp_bans', 'SELECT * FROM temp_bans ORDER BY 1'),
                 ('referrals', 'SELECT * FROM referrals ORDER BY 1'),
                 ('scheduled_restart_optout', 'SELECT * FROM scheduled_restart_optout ORDER BY 1'),
                 ('autostart', 'SELECT script_key, owner_id, file_name FROM autostart ORDER BY 1'))
# Tables whose rows mean "this install holds something worth keeping" (active_users alone does not count).
_AB_REAL_TABLES = ('subscriptions', 'user_files', 'banned_users', 'user_limits', 'mandatory_channels',
                   'suspended_users', 'temp_bans', 'referrals', 'autostart')


def _ab_state():
    with _AB_LOCK:
        if not _AB['loaded']:
            _AB['loaded'] = True
            try:
                with open(AUTO_BACKUP_STATE_PATH, 'r', encoding='utf-8') as handle:
                    raw = json.load(handle)
                if isinstance(raw, dict):
                    _AB['state'] = {k: raw[k] for k in _AB_STATE_KEYS if k in raw}
            except (OSError, ValueError):
                _AB['state'] = {}
            ids = _AB['state'].get('ids')
            _AB['state']['ids'] = [i for i in ids if isinstance(i, int)][-AUTO_BACKUP_KEEP:] if isinstance(ids, list) else []
        return _AB['state']


def _ab_state_save():
    with _AB_LOCK:
        state = _ab_state()
        tmp = AUTO_BACKUP_STATE_PATH + '.tmp'
        try:
            with open(tmp, 'w', encoding='utf-8') as handle:
                json.dump({k: state[k] for k in _AB_STATE_KEYS if k in state}, handle)
            os.replace(tmp, AUTO_BACKUP_STATE_PATH)
        except OSError as exc:
            logger.warning("Auto backup: could not save its state file: %s", redact_secrets(exc))


def _install_is_fresh():
    """True when this install holds nothing worth protecting: no real database rows and no files in any user folder.
    When that cannot be read, it counts as NOT fresh (never restore over something we cannot look at)."""
    try:
        with DB_LOCK:
            conn = db_connect()
            try:
                for table in _AB_REAL_TABLES:
                    if conn.execute(f'SELECT COUNT(*) FROM {table}').fetchone()[0]:
                        return False
                if conn.execute('SELECT COUNT(*) FROM admins WHERE user_id NOT IN (?, ?)', (OWNER_ID, ADMIN_ID)).fetchone()[0]:
                    return False
            finally:
                conn.close()
        for _uid, folder in _user_dirs():
            for _rel, _full in _iter_backup_files(folder):
                return False
        return True
    except Exception as exc:
        logger.warning("Auto backup: could not tell if this install is empty (%s); treating it as not empty.", redact_secrets(exc))
        return False


def _ab_fingerprint():
    """Short hash of everything a backup would hold (database rows that matter + every file's size and time).
    None when it cannot be worked out, which counts as 'changed'."""
    try:
        digest = hashlib.sha1()
        with DB_LOCK:
            conn = db_connect()
            try:
                for table, query in _AB_FP_TABLES:
                    digest.update(table.encode())
                    try:
                        for row in conn.execute(query):
                            digest.update(repr(tuple(row)).encode('utf-8', 'replace'))
                    except sqlite3.Error:
                        continue
            finally:
                conn.close()
        for uid_text, folder in _user_dirs():
            for rel, full in _iter_backup_files(folder):
                try:
                    stat = os.stat(full)
                except OSError:
                    continue
                digest.update(f'{uid_text}/{rel}:{stat.st_size}:{int(stat.st_mtime)}'.encode('utf-8', 'replace'))
                if rel.lower().endswith(SQLITE_EXTS):       # a database in WAL mode keeps recent writes in its side file
                    try:
                        wal = os.stat(full + '-wal')
                        digest.update(f'w{wal.st_size}:{int(wal.st_mtime)}'.encode())
                    except OSError:
                        pass
        return digest.hexdigest()
    except Exception as exc:
        logger.warning("Auto backup: could not compare data (%s)", redact_secrets(exc))
        return None


def auto_backup_note(reason=''):
    """Something that matters changed: a backup is due shortly (debounced by the watcher). Cheap and never raises."""
    if AUTO_BACKUP_MINUTES <= 0:
        return
    with _AB_LOCK:
        if not _AB['pending']:
            _AB['pending'] = time.time()


def _ab_wrap_change(name):
    original = globals().get(name)
    if original is None or getattr(original, '_ab_wrapped', False):
        return

    def wrapper(*args, **kwargs):
        result = original(*args, **kwargs)
        auto_backup_note(name)
        return result
    wrapper.__name__ = original.__name__
    wrapper.__doc__ = original.__doc__
    wrapper._ab_wrapped = True
    globals()[name] = wrapper


# The writers of data that matters. Wrapped here once, so none of them needs to know about backups.
for _ab_name in ('save_user_file', 'remove_user_file_db', 'save_subscription', 'remove_subscription_db',
                 'ban_user_db', 'unban_user_db', 'suspend_user_db', 'unsuspend_user_db', 'add_admin_db',
                 'remove_admin_db', 'set_user_limit_db', 'remove_user_limit_db', 'save_mandatory_channel',
                 'remove_mandatory_channel_db'):
    _ab_wrap_change(_ab_name)


def _ab_when(stamp):
    try:
        zone = time.strftime('%Z', time.localtime(stamp)).strip()
        return datetime.fromtimestamp(stamp).strftime('%d %b %H:%M') + (f' {zone}' if zone else '')
    except (OverflowError, OSError, ValueError, TypeError):
        return '?'


def auto_backup_status_lines():
    """Plain-text lines for the status screens: the auto backup state, and on Railway without a Volume the honest note."""
    state = _ab_state()
    if AUTO_BACKUP_MINUTES <= 0:
        lines = ['Auto backup: off']
    elif state.get('last_ok'):
        line = f"Auto backup: last at {_ab_when(state['last_ok'])}, size {_human_size(state.get('last_size', 0))}"
        if state.get('last_level') == 'light':
            line += ' (light: badi files shamil nahi)'
        lines = [line]
        if state.get('last_error'):
            lines.append('Auto backup: abhi ka try fail hua, dobara try hoga')
    elif state.get('last_error'):
        lines = ['Auto backup: abhi tak nahi gaya (owner chat tak nahi pahunch pa raha)']
    elif _AB['hold']:
        lines = ['Auto backup: purana backup wapas laa raha hai']
    else:
        lines = ['Auto backup: pehla backup jaldi jayega']
    if ON_RAILWAY and not HAS_RAILWAY_VOLUME and AUTO_BACKUP_MINUTES > 0:
        lines.append(f'Railway par Volume nahi hai: data Telegram backup se bachta hai. Last backup ke baad ka naya data '
                     f'redeploy par ja sakta hai (max {AUTO_BACKUP_MINUTES} min ka gap).')
    return lines


def auto_backup_health():
    if AUTO_BACKUP_MINUTES <= 0:
        return {'enabled': False}
    state = _ab_state()
    return {'enabled': AUTO_BACKUP_MINUTES > 0, 'interval_minutes': AUTO_BACKUP_MINUTES,
            'last_ok_age_seconds': int(time.time() - state['last_ok']) if state.get('last_ok') else None,
            'last_size': state.get('last_size'), 'level': state.get('last_level'),
            'failing': bool(state.get('last_error')), 'on_railway': ON_RAILWAY, 'volume': HAS_RAILWAY_VOLUME}


def _ab_notify_owner(text):
    """One message to the owner. A chat the owner never opened or blocked is only logged."""
    try:
        bot.send_message(OWNER_ID, text, parse_mode='HTML')
        return True
    except Exception as exc:
        logger.warning("Auto backup: could not message the owner (%s).", redact_secrets(exc))
        return False


def _ab_owner_unreachable(exc):
    """True when Telegram says the owner chat cannot be used at all (never started the bot, blocked it, wrong id)."""
    code = getattr(exc, 'error_code', None)
    desc = str(exc).lower()
    return (code in (400, 403, 404) or 'chat not found' in desc or 'blocked' in desc or 'forbidden' in desc
            or "can't initiate" in desc)


def _ab_make_zip(work):
    """Build the backup (full, else lighter) under the 19 MB cap. Returns (path, size, level, summary) or None when even
    the lightest one does not fit. Raises on real errors."""
    state = _ab_state()
    stamp = _now_stamp()
    path = os.path.join(work, f'demon_auto_backup_{stamp}.zip')
    previous = None
    for max_file, level in AUTO_BACKUP_TIERS:
        extra = {'auto': {'prev_ids': list(state.get('ids') or []), 'level': level, 'host': BOT_VERSION}}
        try:
            summary = _build_full_backup(path, limit_mb=AUTO_BACKUP_RAW_LIMIT_MB, extra_manifest=extra, max_file_bytes=max_file)
        except BackupTooLarge:
            continue
        if max_file and not summary['skipped'] and previous is not None:
            break                                    # nothing was left out, so it would be as big as the last try
        size = os.path.getsize(path)
        previous = size
        if size <= AUTO_BACKUP_MAX_BYTES:
            return path, size, level, summary
    return None


def _ab_caption(summary, size, level):
    counts = summary['counts']
    lines = [ui_row('👥', 'Users', summary['users']),
             ui_row('📦', 'Scripts', counts[1]),
             ui_row('💎', 'Subscriptions', counts[2]),
             ui_row('🗂️', 'Files', f"{summary['files']} ({_human_size(size)})")]
    if level == 'light':
        lines.append(ui_row('🪶', 'Light backup', f"{summary['skipped']} badi file(s) shamil nahi"))
    return ui_msg('💾', f"Auto backup {_ab_when(time.time())}", *lines,
                  foot='Private rakho: isme users ka .env bhi hai. Pin mat hatao.')


def _ab_pin_and_tidy(message_id, previous_ids):
    """Pin the new backup, unpin the older ones, then delete the ones past AUTO_BACKUP_KEEP. Returns True when pinned."""
    pinned = False
    for _ in range(2):
        try:
            bot.pin_chat_message(OWNER_ID, message_id, disable_notification=True)
            pinned = True
            break
        except Exception as exc:
            logger.warning("Auto backup: could not pin the backup (%s).", redact_secrets(exc))
            time.sleep(1)
    if pinned:
        for old in previous_ids:
            try:
                bot.unpin_chat_message(OWNER_ID, old)
            except Exception as exc:
                logger.debug("Auto backup: old backup not unpinned: %s", redact_secrets(exc))
    return pinned


def _ab_run(reason='timer', force=False):
    """One automatic backup now. Returns a word: sent, unchanged, empty, held, busy, off, failed, toobig."""
    if AUTO_BACKUP_MINUTES <= 0 and not force:
        return 'off'
    if _AB['hold']:
        return 'held'
    if not BACKUP_OP_LOCK.acquire(blocking=False):
        return 'busy'
    work = None
    try:
        if _AB['hold']:
            return 'held'
        if _install_is_fresh():
            return 'empty'
        state = _ab_state()
        fingerprint = _ab_fingerprint()
        if not force and fingerprint is not None and fingerprint == state.get('last_fp'):
            return 'unchanged'
        work = tempfile.mkdtemp(prefix='demon_autobk_')
        made = _ab_make_zip(work)
        if made is None:
            state['last_error'] = 'too_big'
            if state.get('big_warned') != 'none':
                state['big_warned'] = 'none'
                _ab_notify_owner(ui_warn('Auto Backup Nahi Ho Paya',
                                         ui_row('📏', 'Limit', f'{AUTO_BACKUP_MAX_BYTES // (1024 * 1024)} MB'),
                                         'Data itna bada hai ki Telegram se wapas padha nahi ja sakta, isliye backup nahi bheja.',
                                         'Redeploy par naya data jaa sakta hai.',
                                         foot='Badi ya purani files hata de, ya Export Full Backup se khud backup le.'))
            _ab_state_save()
            return 'toobig'
        path, size, level, summary = made
        previous_ids = list(state.get('ids') or [])
        with open(path, 'rb') as handle:
            sent = bot.send_document(OWNER_ID, handle, caption=_ab_caption(summary, size, level), parse_mode='HTML')
        message_id = getattr(sent, 'message_id', None)
        if not isinstance(message_id, int):
            raise RuntimeError('Telegram did not return the message id of the backup')
        pinned = _ab_pin_and_tidy(message_id, previous_ids)
        ids = previous_ids + [message_id]
        for old in ids[:-AUTO_BACKUP_KEEP]:
            try:
                bot.delete_message(OWNER_ID, old)
            except Exception as exc:
                logger.debug("Auto backup: old backup message not deleted: %s", redact_secrets(exc))
        state['ids'] = ids[-AUTO_BACKUP_KEEP:]
        state.update({'last_ok': time.time(), 'last_size': size, 'last_level': level, 'last_fp': fingerprint,
                      'last_skipped': summary['skipped'], 'last_error': '' if pinned else 'not_pinned'})
        first_time = not state.get('intro_sent')
        state['intro_sent'] = True
        warn_light = level == 'light' and state.get('big_warned') != 'light'
        state['big_warned'] = 'light' if level == 'light' else ''
        _ab_state_save()
        logger.info("Auto backup sent (%s): %s, level %s, pinned=%s", reason, _human_size(size), level, pinned)
        if warn_light:
            _ab_notify_owner(ui_warn('Auto Backup: Light Mode',
                                     f'Data {AUTO_BACKUP_MAX_BYTES // (1024 * 1024)} MB se bada hai, isliye backup mein database aur '
                                     f'chhoti files ja rahi hain ({summary["skipped"]} badi file(s) nahi).',
                                     'Redeploy ke baad wo badi files wapas nahi aayengi.'))
        elif first_time:
            _ab_notify_owner(ui_ok('Auto Backup Chalu',
                                   'Ab tera data (users ke .env sameth) is chat mein backup hokar pin hota rahega.',
                                   'Redeploy se disk wipe ho gayi to bot isi se sab wapas laa lega. Ye chat private rakh, pin mat hata.',
                                   *[ui_esc(line) for line in auto_backup_status_lines()]))
        return 'sent'
    except Exception as exc:
        state = _ab_state()
        state['last_error'] = 'owner_chat' if _ab_owner_unreachable(exc) else 'send_failed'
        _AB['next_ok'] = time.time() + (3600 if state['last_error'] == 'owner_chat' else AUTO_BACKUP_MIN_GAP_SECONDS)
        if state['last_error'] == 'owner_chat':
            logger.warning("Auto backup: the owner chat cannot be used (the owner has not started the bot, or blocked it): %s",
                           redact_secrets(exc))
        else:
            logger.warning("Auto backup failed: %s", redact_secrets(exc))
        _ab_state_save()
        return 'failed'
    finally:
        if work:
            _rmtree_quiet(work)
        BACKUP_OP_LOCK.release()


def _ab_tick():
    now = time.time()
    if _AB['hold'] or now < _AB['next_ok']:
        return
    state = _ab_state()
    timer_due = now - _AB['last_check'] >= AUTO_BACKUP_MINUTES * 60
    pending = _AB['pending']
    change_due = bool(pending) and now - pending >= AUTO_BACKUP_SETTLE_SECONDS
    if not (timer_due or change_due):
        return
    if now - float(state.get('last_ok') or 0) < AUTO_BACKUP_MIN_GAP_SECONDS:
        return                                   # at most one backup per gap; a waiting change is kept for later
    with _AB_LOCK:
        _AB['pending'] = 0.0
    result = _ab_run('change' if change_due else 'timer')
    if result in ('busy', 'held'):
        with _AB_LOCK:
            _AB['pending'] = _AB['pending'] or pending or now
        return
    _AB['last_check'] = time.time()


def _ab_loop():
    SHUTDOWN_EVENT.wait(45)                      # let the boot restore and auto-resume finish first
    while not SHUTDOWN_EVENT.is_set():
        try:
            _ab_tick()
        except Exception:
            logger.exception("Auto backup watcher error; continuing")
        SHUTDOWN_EVENT.wait(15)


def start_auto_backup():
    """Start the background watcher (timer + change trigger)."""
    if AUTO_BACKUP_MINUTES <= 0:
        logger.info("Auto backup to Telegram is OFF (AUTO_BACKUP_MINUTES=0).")
        return
    with _AB_LOCK:
        if _AB['started']:
            return
        _AB['started'] = True
    _ab_state()
    logger.info("Auto backup to Telegram: every %s min when something changed (and shortly after changes), owner chat %s, "
                "limit %s MB, keeps %s.", AUTO_BACKUP_MINUTES, OWNER_ID, AUTO_BACKUP_MAX_BYTES // (1024 * 1024), AUTO_BACKUP_KEEP)
    threading.Thread(target=_ab_loop, name='auto-backup', daemon=True).start()


# --- Restore from the pinned backup -----------------------------------------------------------------------------
def _ab_find_pinned_backup():
    """Look at the pinned message of the owner chat. Returns (kind, document, message_id), kind one of: found, none,
    ignored (a pin we do not trust), unreachable (owner chat unusable), retry (Telegram problem, try again)."""
    try:
        me = bot.get_me()
        chat = bot.get_chat(OWNER_ID)
    except Exception as exc:
        if _ab_owner_unreachable(exc):
            logger.warning("Auto restore: the owner chat cannot be read (the owner has not started the bot, or blocked it): %s",
                           redact_secrets(exc))
            return 'unreachable', None, None
        logger.warning("Auto restore: Telegram did not answer (%s).", redact_secrets(exc))
        return 'retry', None, None
    pinned = getattr(chat, 'pinned_message', None)
    if pinned is None:
        return 'none', None, None
    author = getattr(pinned, 'from_user', None)
    pin_chat = getattr(pinned, 'chat', None)
    doc = getattr(pinned, 'document', None)
    forwarded = (getattr(pinned, 'forward_origin', None) or getattr(pinned, 'forward_date', None)
                 or getattr(pinned, 'forward_from', None) or getattr(pinned, 'forward_from_chat', None))
    name = str(getattr(doc, 'file_name', '') or '')
    size = getattr(doc, 'file_size', None)
    trusted = (author is not None and getattr(author, 'id', None) == getattr(me, 'id', object())
               and bool(getattr(author, 'is_bot', True))
               and pin_chat is not None and getattr(pin_chat, 'id', None) == OWNER_ID
               and getattr(pin_chat, 'type', 'private') == 'private'
               and doc is not None and not forwarded and AUTO_BACKUP_NAME_RE.match(name)
               and isinstance(getattr(pinned, 'message_id', None), int)
               and (size is None or 0 < size <= TELEGRAM_DOWNLOAD_LIMIT))
    if not trusted:
        logger.warning("Auto restore: the pinned message in the owner chat is not a backup made by this bot; ignoring it.")
        return 'ignored', None, None
    return 'found', doc, pinned.message_id


def _ab_restore_attempt():
    """One try to restore. Returns: restored, nothing (no usable backup, or not needed), failed (told the owner), retry."""
    if not _install_is_fresh():
        logger.info("Auto restore: this install already holds data; not touching it.")
        return 'nothing'
    kind, doc, message_id = _ab_find_pinned_backup()
    if kind == 'retry':
        return 'retry'
    if kind != 'found':
        logger.info("Auto restore: no backup to restore (%s).", kind)
        return 'nothing'
    work = tempfile.mkdtemp(prefix='demon_autorestore_')
    reason = ''
    try:
        try:
            file_info = bot.get_file(doc.file_id)
            data = bot.download_file(file_info.file_path)
        except Exception as exc:
            if 'too big' in str(exc).lower():
                reason = 'download'
                logger.warning("Auto restore: the backup is too big for Telegram to hand out.")
            else:
                logger.warning("Auto restore: could not download the backup (%s).", redact_secrets(exc))
                return 'retry'
        else:
            if not data or len(data) > TELEGRAM_DOWNLOAD_LIMIT:
                reason = 'damaged'
            else:
                zip_path = os.path.join(work, 'backup.zip')
                with open(zip_path, 'wb') as handle:
                    handle.write(data)
                payload = os.path.join(work, 'payload')
                os.makedirs(payload, exist_ok=True)
                ok, problem, info = _inspect_full_backup(zip_path, payload)
                if not ok:
                    logger.warning("Auto restore: the pinned backup was refused: %s", re.sub(r'<[^>]+>', '', str(problem))[:200])
                    reason = 'newer' if 'newer version' in str(problem) else 'damaged'
                else:
                    os.remove(zip_path)
                    result = _ab_apply_restore(work, payload, info, message_id, doc)
                    if result is None:
                        return 'nothing'              # data appeared meanwhile; nothing was replaced
                    if result == 'error':
                        reason = 'apply'
                    else:
                        return 'restored'
    except Exception:
        logger.exception("Auto restore failed")
        reason = reason or 'damaged'
    finally:
        _rmtree_quiet(work)
    texts = {'download': 'Backup file Telegram se utar nahi paayi.',
             'newer': 'Ye backup bot ke naye version ka hai, mera version ise nahi padh sakta.',
             'apply': 'Backup lagate waqt dikkat aayi, isliye sab pehle jaisa chhod diya.'}
    _ab_notify_owner(ui_err('Purana Data Wapas Nahi Aaya',
                            texts.get(reason, 'Pin kiya hua backup kharab ya adhoora lag raha hai.'),
                            'Bot abhi khali install ke saath chal raha hai. Wo backup file chat mein hi hai: '
                            'Admin Panel mein Import Full Backup se khud bhi daal sakta hai.'))
    return 'failed'


def _ab_apply_restore(work, payload, info, message_id, doc):
    """Check again that nothing is here, then use the normal safe restore. Returns 'ok', 'error' or None (not needed)."""
    if not BACKUP_OP_LOCK.acquire(timeout=120):
        return 'error'
    try:
        if not _install_is_fresh():
            logger.info("Auto restore: data appeared while the backup was being read; leaving it as it is.")
            return None
        prev_ids = []
        try:
            with open(os.path.join(payload, 'manifest.json'), 'r', encoding='utf-8') as handle:
                manifest = json.load(handle)
            raw_ids = (manifest.get('auto') or {}).get('prev_ids') or []
            prev_ids = [i for i in raw_ids if isinstance(i, int)][-20:]
        except (OSError, ValueError, AttributeError):
            pass
        try:
            outcome = _apply_full_restore({'dir': work, 'payload': payload, 'info': info})
        except Exception:
            logger.exception("Auto restore: applying the backup failed; everything was put back")
            return 'error'
        state = _ab_state()
        state['ids'] = ([i for i in prev_ids if i != message_id] + [message_id])[-AUTO_BACKUP_KEEP:]
        state.update({'last_ok': time.time(), 'last_size': getattr(doc, 'file_size', 0) or 0, 'last_level': 'full',
                      'last_fp': _ab_fingerprint(), 'last_error': '', 'intro_sent': True, 'restored_at': time.time()})
        _ab_state_save()
        counts = info['counts']
        scripts_back = len(autostart_rows()) if AUTO_RESUME_ON_BOOT else 0
        logger.warning("Auto restore: data restored from the pinned backup (%s users, %s scripts, %s files).",
                       len(info['users']), counts[1], info['files'])
        lines = [ui_row('👥', 'Users', ui_num(len(info['users']))), ui_row('📄', 'Scripts', ui_num(counts[1])),
                 ui_row('⭐', 'Subscriptions', ui_num(counts[2])), ui_row('📂', 'Files', ui_num(info['files']))]
        if scripts_back:
            lines.append(ui_row('🔁', 'Wapas chalu hongi', f'{ui_num(scripts_back)} script(s)'))
        if outcome.get('missing'):
            lines.append(ui_row('⚠️', 'File nahi mili', f'{ui_num(outcome["missing"])} script(s)'))
        _ab_notify_owner(ui_ok('Data Wapas Aa Gaya', 'Redeploy ke baad disk khali thi, pin kiye hue backup se sab restore kar diya.',
                               *lines, foot='Backup ke baad ka kuch naya data nahi aaya hoga.'))
        return 'ok'
    finally:
        BACKUP_OP_LOCK.release()


def _ab_restore_worker():
    outcome = 'nothing'
    try:
        for delay in AUTO_RESTORE_RETRY_DELAYS:
            if delay and SHUTDOWN_EVENT.wait(delay):
                return
            outcome = _ab_restore_attempt()
            if outcome != 'retry':
                break
        else:
            logger.warning("Auto restore: Telegram stayed unreachable; giving up for this start.")
    except Exception:
        logger.exception("Auto restore worker crashed")
    finally:
        with _AB_LOCK:
            _AB['hold'] = False
            _AB['worker_alive'] = False
            late = _AB['late']
        if outcome == 'restored' and late and not SHUTDOWN_EVENT.is_set():
            try:
                resume_scripts_on_boot()      # the normal boot resume already ran on the empty install
            except Exception:
                logger.exception("Auto restore: resume after a late restore failed")


def auto_restore_on_boot():
    """Run before polling and before the boot auto-resume. A wiped install asks Telegram for the pinned backup of the
    owner chat. Waits a little for it; when Telegram is slow the work goes on in the background (and resumes the
    scripts itself once done). Never raises."""
    if not AUTO_RESTORE_ON_BOOT:
        logger.info("Auto restore on boot is OFF (set AUTO_RESTORE_ON_BOOT=1 to enable).")
        return False
    try:
        if not _install_is_fresh():
            return False
        with _AB_LOCK:
            _AB['hold'] = True                  # no new backup may replace the pinned one before it was read
            _AB['worker_alive'] = True
        worker = threading.Thread(target=_ab_restore_worker, name='auto-restore', daemon=True)
        worker.start()
        worker.join(AUTO_RESTORE_BOOT_WAIT)
        with _AB_LOCK:
            if worker.is_alive():
                _AB['late'] = True
                logger.info("Auto restore: still working in the background; scripts resume when it is done.")
        return True
    except Exception:
        logger.exception("Auto restore could not start; going on with an empty install")
        _AB['hold'] = False
        return False


def create_control_buttons(script_owner_id, file_name, is_running=True):
    markup = NavMenu(row_width=2)
    if is_running:
        markup.row(
            NavButton("🔴 Stop", callback_data=f'stop_{script_owner_id}_{file_name}'),
            NavButton("🔄 Restart", callback_data=f'restart_{script_owner_id}_{file_name}')
        )
        markup.row(
            NavButton("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{file_name}'),
            NavButton("📜 Logs", callback_data=f'logs_{script_owner_id}_{file_name}')
        )
    else:
        markup.row(
            NavButton("🟢 Start", callback_data=f'start_{script_owner_id}_{file_name}'),
            NavButton("🗑️ Delete", callback_data=f'delete_{script_owner_id}_{file_name}')
        )
        markup.row(
            NavButton("📜 View Logs", callback_data=f'logs_{script_owner_id}_{file_name}')
        )
    try:
        if gh_read_sidecar(get_user_folder(script_owner_id), file_name)[0] is not None:
            markup.row(NavButton("🔄 Update from GitHub", callback_data=f'ghu_{script_owner_id}_{file_name}'))
    except Exception:
        pass
    markup.row(NavButton("🔑 Environment (.env)", callback_data=f'envm_{script_owner_id}_{file_name}'))
    if SCHEDULED_RESTART_HOURS > 0:
        opted_out = _script_key(script_owner_id, file_name) in SCHEDULED_RESTART_OPTOUT
        markup.row(NavButton(f"⏰ Scheduled Restart: {'OFF' if opted_out else 'ON'}",
                             callback_data=f'srt_{script_owner_id}_{file_name}'))
    if getattr(_ACTOR, 'uid', None) in (None, script_owner_id):     # v19: only the owner sees his bot's data files
        markup.row(NavButton("🗄️ Data Files", callback_data=f'dbf_e_{script_owner_id}_{file_name}'))
    markup.row(
        NavButton("📦 Export My Bots", callback_data=f'ubk_{script_owner_id}'),
        NavButton("♻️ Import My Bots", callback_data=f'ubr_{script_owner_id}')
    )
    markup.add(NavButton("🔙 Back to Files", callback_data='check_files'))
    return markup

def create_admin_panel():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('➕ Add Admin', callback_data='add_admin'),
        NavButton('➖ Remove Admin', callback_data='remove_admin')
    )
    markup.row(NavButton('📋 List Admins', callback_data='list_admins'))
    markup.row(NavButton('🗄 Database Backup', callback_data='database_backup'),
               NavButton('📤 Export Users', callback_data='export_users'))
    markup.row(NavButton('📦 Export Full Backup', callback_data='export_database'),
               NavButton('♻️ Import Full Backup', callback_data='import_database'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_user_management_menu():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('🚫 Ban User', callback_data='ban_user'),
        NavButton('✅ Unban User', callback_data='unban_user')
    )
    markup.row(
        NavButton('📊 User Info', callback_data='user_info'),
        NavButton('👥 All Users', callback_data='all_users')
    )
    markup.row(
        NavButton('🔧 Set User Limit', callback_data='set_user_limit'),
        NavButton('🗑️ Remove User Limit', callback_data='remove_user_limit')
    )
    markup.row(
        NavButton('⏳ Temp Ban', callback_data='um_tempban'),
        NavButton('⏸️ Suspend Hosting', callback_data='um_suspend')
    )
    markup.row(
        NavButton('▶️ Unsuspend Hosting', callback_data='um_unsuspend'),
        NavButton('📦 Bulk Actions', callback_data='um_bulk')
    )
    markup.row(
        NavButton('📂 User Files', callback_data='um_files'),
        NavButton('🟢 Running Bots', callback_data='um_run')
    )
    markup.row(NavButton('🔍 Search Files', callback_data='um_search'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_subscription_menu():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('➕ Add Subscription', callback_data='add_subscription'),
        NavButton('➖ Remove Subscription', callback_data='remove_subscription')
    )
    markup.row(NavButton('🔍 Check Subscription', callback_data='check_subscription'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

def create_admin_settings_menu():
    markup = NavMenu(row_width=2)
    markup.row(
        NavButton('📊 System Info', callback_data='system_info'),
        NavButton('📈 Bot Performance', callback_data='bot_performance')
    )
    markup.row(
        NavButton('🧹 Cleanup Files', callback_data='cleanup_files'),
        NavButton('📋 Installation Logs', callback_data='install_logs')
    )
    markup.row(
        NavButton('🔄 Retry Failed Bots', callback_data='retry_failed_bots'),
        NavButton('🔁 Restart All Bots', callback_data='admin_restart_all')
    )
    markup.row(
        NavButton('🩺 Hosting Health', callback_data='hosting_health'),
        NavButton('👑 Admin Dashboard', callback_data='admin_dashboard')
    )
    markup.row(
        NavButton('📢 Channel Add', callback_data='manage_mandatory_channels'),
        NavButton('🛠️ Admin Install', callback_data='admin_install')
    )
    markup.row(
        NavButton('🔒 Lock Bot', callback_data='lock_bot'),
        NavButton('🔓 Unlock Bot', callback_data='unlock_bot')
    )
    markup.row(NavButton('🟢 Running All Code', callback_data='run_all_scripts'))
    markup.row(NavButton('🔙 Back to Main', callback_data='back_to_main'))
    return markup

# --- File Handling ---
# =====================================================================================
# Deploy from GitHub (public repositories only)
# The repo is cloned into a NEW temp folder, only the important files are picked, packed into a zip
# (plus a signed manifest) and handed to the SAME zip-deploy code as a manual zip upload.
# Nothing from the repo is ever run during the clone or the file picking.
# =====================================================================================
GH_CLONE_TIMEOUT = _env_int('GITHUB_CLONE_TIMEOUT', 120)      # seconds for clone / archive download
GH_MAX_REPO_MB = _env_int('GITHUB_MAX_REPO_MB', 100)          # size of the fresh clone (all of it, .git included)
GH_MAX_SELECTED_MB = _env_int('GITHUB_MAX_SELECTED_MB', 40)   # total size of the files that are kept
GH_MAX_FILES = _env_int('GITHUB_MAX_FILES', 600)              # number of files that are kept
GH_MAX_DATA_KB = 2048                                          # one json / yaml / txt / csv file
GH_MAX_ASSET_KB = 512                                          # one image / font
GH_PICK_TTL = 600                                              # seconds a "which file is the main one?" list waits
GH_GLOBAL_LIMIT = 2                                            # deploys running at the same time (all users)
GH_MANIFEST_NAME = '.demon_github.json'
GH_SIDECAR_SUFFIX = '.github.json'

GH_OWNER_RE = re.compile(r'^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$')
GH_REPO_RE = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9._-]{0,99}$')
GH_BRANCH_RE = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9._-]{0,99}$')
GH_SEG_RE = re.compile(r'^[A-Za-z0-9_][A-Za-z0-9._-]{0,99}$')
GH_CODE_EXTS = ('.py', '.js', '.mjs', '.cjs')
GH_DATA_EXTS = ('.json', '.yaml', '.yml', '.toml', '.ini', '.cfg', '.txt', '.csv', '.html', '.htm', '.css', '.jinja', '.j2')
GH_ASSET_EXTS = ('.png', '.jpg', '.jpeg', '.gif', '.svg', '.ico', '.webp', '.ttf', '.otf', '.woff', '.woff2')
GH_INFO_NAMES = ('package.json', 'package-lock.json', 'requirements.txt', 'runtime.txt', 'procfile',
                 '.env.example', '.env.sample', '.env.template')
GH_SKIP_DIRS = frozenset({'.git', '.github', '.gitlab', 'node_modules', 'venv', '.venv', 'env', '__pycache__', 'site-packages',
                          'tests', 'test', '__tests__', 'docs', 'doc', '.idea', '.vscode', '.pytest_cache', '.mypy_cache',
                          '.tox', '.cache', 'dist', 'build', '.next', 'coverage'})
GH_PROTECTED_SUFFIXES = ('.env', '.db', '.sqlite', '.sqlite3')
GH_UPDATE_CODE_EXTS = ('.py', '.js', '.mjs', '.cjs', '.html', '.htm', '.css', '.jinja', '.j2')
GH_UPDATE_CODE_NAMES = ('package.json', 'package-lock.json', 'requirements.txt', 'runtime.txt', 'procfile',
                        '.env.example', '.env.sample', '.env.template')

GH_LOCK = threading.Lock()
GH_ACTIVE_USERS = set()          # users with a deploy running or a picker waiting
GH_PENDING = {}                  # token -> picker context
GH_SLOTS = threading.BoundedSemaphore(GH_GLOBAL_LIMIT)


class GithubError(Exception):
    """A problem with a repo link or its content. .text is safe to show to the user."""
    def __init__(self, code, text):
        super().__init__(text)
        self.code = code
        self.text = text


def parse_github_url(text):
    """Strict check of a pasted GitHub link. Returns {'owner','repo','branch','subdir','url','clone_url'} or raises GithubError.
    Only https://github.com/<owner>/<repo>[.git][/tree/<branch>[/<subfolder>]] is accepted. The clone address is REBUILT from the
    validated owner and repo, the pasted text itself is never used for anything else."""
    bad = GithubError('url', 'Ye valid GitHub repo link nahi lag raha. Aisa bhejo: https://github.com/owner/repo '
                             '(sirf github.com, https, public repo).')
    raw = (text or '').strip()
    if raw.startswith('<') and raw.endswith('>'):
        raw = raw[1:-1].strip()
    if not raw or len(raw) > 300:
        raise bad
    if any(ch.isspace() or ord(ch) < 33 or ord(ch) > 126 for ch in raw):
        raise bad
    if '\\' in raw or '%' in raw or '@' in raw.split('github.com', 1)[0]:
        raise bad
    lowered = raw.lower()
    if lowered.startswith('http://'):
        raise GithubError('url', 'Sirf https link chalega (http nahi). Aisa bhejo: https://github.com/owner/repo')
    if lowered.startswith('github.com/') or lowered.startswith('www.github.com/'):
        raw = 'https://' + raw
    try:
        parts = urlsplit(raw)
    except ValueError:
        raise bad
    if parts.scheme.lower() != 'https' or (parts.hostname or '').lower() not in ('github.com', 'www.github.com'):
        raise bad
    try:
        port = parts.port
    except ValueError:
        raise bad
    if parts.username or parts.password or port:
        raise bad
    segs = [s for s in parts.path.split('/') if s != '']
    if len(segs) < 2:
        raise bad
    owner, repo = segs[0], segs[1]
    if repo.lower().endswith('.git'):
        repo = repo[:-4]
    if not GH_OWNER_RE.fullmatch(owner) or not GH_REPO_RE.fullmatch(repo) or repo in ('.', '..') or '..' in repo:
        raise bad
    branch, subdir = None, None
    rest = segs[2:]
    if rest:
        if rest[0] != 'tree' or len(rest) < 2 or len(rest) > 9:
            raise GithubError('url', 'Sirf repo ka link do (ya /tree/branch/folder wala link). Issues/blob/pull links nahi chalte.')
        branch = rest[1]
        if not GH_BRANCH_RE.fullmatch(branch) or '..' in branch or branch.endswith('.lock') or branch.endswith('.'):
            raise bad
        sub = rest[2:]
        for seg in sub:
            if not GH_SEG_RE.fullmatch(seg) or seg in ('.', '..') or '..' in seg:
                raise bad
        subdir = '/'.join(sub) or None
    base = f'https://github.com/{owner}/{repo}'
    return {'owner': owner, 'repo': repo, 'branch': branch, 'subdir': subdir, 'url': base, 'clone_url': base + '.git'}


def _gh_dir_size(path):
    total = 0
    for base, dirs, files in os.walk(path):
        for name in files:
            try:
                total += os.lstat(os.path.join(base, name)).st_size
            except OSError:
                pass
    return total


def _gh_git_env(home_dir):
    env = child_env()
    env.update({'GIT_TERMINAL_PROMPT': '0', 'GIT_ASKPASS': 'true', 'SSH_ASKPASS': 'true', 'GCM_INTERACTIVE': 'never',
                'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': os.devnull, 'GIT_LFS_SKIP_SMUDGE': '1',
                'GIT_OPTIONAL_LOCKS': '0', 'HOME': home_dir, 'XDG_CONFIG_HOME': home_dir, 'LC_ALL': 'C'})
    for name in list(env):
        if name.startswith('GIT_') and name not in ('GIT_TERMINAL_PROMPT', 'GIT_ASKPASS', 'GIT_CONFIG_NOSYSTEM', 'GIT_CONFIG_GLOBAL',
                                                    'GIT_LFS_SKIP_SMUDGE', 'GIT_OPTIONAL_LOCKS'):
            env.pop(name, None)
    return env


def gh_clone_command(url, dest, branch=None, local_test=False):
    """Argument list for the shallow clone (never a shell string). `--` keeps the address from being read as an option.
    local_test=True is only used by the tests to clone a file:// repo; users can never reach it."""
    protocol = ['-c', 'protocol.allow=never', '-c', 'protocol.https.allow=always']
    if local_test:
        protocol = ['-c', 'protocol.allow=never', '-c', 'protocol.file.allow=always']
    cmd = ['git', '-c', 'credential.helper=', '-c', 'core.hooksPath=' + os.devnull, '-c', 'core.symlinks=false',
           '-c', 'core.fsmonitor=false', '-c', 'submodule.recurse=false', '-c', 'http.followRedirects=false'] + protocol
    cmd += ['clone', '--depth', '1', '--single-branch', '--no-tags', '--no-recurse-submodules', '--quiet']
    if branch:
        cmd += ['--branch', branch]
    cmd += ['--', url, dest]
    return cmd


def _gh_stderr_code(text):
    low = (text or '').lower()
    if 'remote branch' in low and 'not found' in low:
        return 'branch'
    if any(key in low for key in ('not found', 'authentication', 'could not read username', 'terminal prompts disabled',
                                  'repository access', 'permission denied', 'invalid username')):
        return 'notfound'
    return 'fail'


def gh_clone(url, dest, branch=None, timeout=None, max_mb=None, local_test=False, home_dir=None):
    """Shallow clone into `dest` (must not exist). Returns None on success, else one of
    'nogit', 'notfound', 'branch', 'timeout', 'toobig', 'fail'. The partial folder is removed on any failure."""
    timeout = GH_CLONE_TIMEOUT if timeout is None else timeout
    max_bytes = (GH_MAX_REPO_MB if max_mb is None else max_mb) * 1024 * 1024
    home = home_dir or tempfile.mkdtemp(prefix='demon_ghhome_')
    code = 'fail'
    try:
        try:
            proc = subprocess.Popen(gh_clone_command(url, dest, branch, local_test), stdin=subprocess.DEVNULL,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, env=_gh_git_env(home),
                                    cwd=home, text=True, errors='ignore')
        except FileNotFoundError:
            return 'nogit'
        except OSError:
            return 'nogit'
        started = time.time()
        stderr_text = ''
        while True:
            try:
                _, stderr_text = proc.communicate(timeout=1)
                break
            except subprocess.TimeoutExpired:
                if time.time() - started > timeout:
                    code = 'timeout'
                elif os.path.isdir(dest) and _gh_dir_size(dest) > max_bytes:
                    code = 'toobig'
                else:
                    continue
                try:
                    proc.kill()
                    proc.communicate(timeout=10)
                except Exception:
                    pass
                _rmtree_quiet(dest)
                return code
        if proc.returncode == 0 and os.path.isdir(dest):
            if _gh_dir_size(dest) > max_bytes:
                _rmtree_quiet(dest)
                return 'toobig'
            return None
        code = _gh_stderr_code(stderr_text)
        logger.info('git clone failed (%s)', code)
        _rmtree_quiet(dest)
        return code
    finally:
        if home_dir is None:
            _rmtree_quiet(home)


def gh_extract_archive(zip_path, dest):
    """Safely unpack a GitHub source archive into `dest`, dropping the single top-level folder. Same limits as a zip upload."""
    os.makedirs(dest, exist_ok=True)
    root_dir = os.path.realpath(dest)
    with zipfile.ZipFile(zip_path, 'r') as archive:
        items = archive.infolist()
        if len(items) > MAX_ZIP_FILES:
            raise GithubError('toobig', 'Repo mein files bahut zyada hain.')
        if sum(max(0, i.file_size) for i in items) > GH_MAX_REPO_MB * 1024 * 1024:
            raise GithubError('toobig', f'Repo {GH_MAX_REPO_MB} MB se bada hai.')
        for item in items:
            name = item.filename.replace('\\', '/')
            parts = [p for p in name.split('/') if p]
            if name.startswith('/') or '..' in parts or (len(name) > 1 and name[1] == ':'):
                raise GithubError('fail', 'Archive mein unsafe path mila.')
            if ((item.external_attr >> 16) & 0o170000) == 0o120000:
                continue                                           # symlinks are simply not created
            rel = '/'.join(parts[1:])                              # drop "<repo>-<branch>/"
            if not rel or item.is_dir():
                continue
            target = os.path.realpath(os.path.join(root_dir, rel))
            if os.path.commonpath((root_dir, target)) != root_dir:
                raise GithubError('fail', 'Archive mein unsafe path mila.')
            os.makedirs(os.path.dirname(target), exist_ok=True)
            with archive.open(item) as src, open(target, 'wb') as out:
                shutil.copyfileobj(src, out, 1024 * 1024)


def gh_fetch_archive(info, zip_path, timeout=None):
    """Fallback when git is not installed: download the repo as a zip from GitHub's code archive host (https only, redirects
    only to github.com / codeload.github.com, size and time limited). Raises GithubError. Needs the network, so never run in tests."""
    timeout = GH_CLONE_TIMEOUT if timeout is None else timeout
    if info.get('branch'):
        url = f"https://github.com/{info['owner']}/{info['repo']}/archive/refs/heads/{info['branch']}.zip"
    else:
        url = f"https://github.com/{info['owner']}/{info['repo']}/archive/HEAD.zip"
    deadline = time.time() + timeout
    limit = GH_MAX_REPO_MB * 1024 * 1024
    for _ in range(4):
        parts = urlsplit(url)
        if parts.scheme != 'https' or parts.hostname not in ('github.com', 'codeload.github.com'):
            raise GithubError('fail', 'Download ka raasta safe nahi tha, roka gaya.')
        try:
            resp = requests.get(url, stream=True, allow_redirects=False, timeout=(10, 20), headers={'User-Agent': 'demon-hosting-bot'})
        except requests.exceptions.RequestException:
            raise GithubError('fail', 'GitHub se connect nahi ho paya.')
        try:
            if resp.status_code in (301, 302, 303, 307, 308):
                url = urljoin(url, resp.headers.get('Location', ''))
                continue
            if resp.status_code in (404, 401, 403):
                raise GithubError('notfound', '')
            if resp.status_code != 200:
                raise GithubError('fail', 'GitHub ne download nahi diya.')
            size = 0
            with open(zip_path, 'wb') as handle:
                for block in resp.iter_content(1024 * 256):
                    size += len(block)
                    if size > limit:
                        raise GithubError('toobig', '')
                    if time.time() > deadline:
                        raise GithubError('timeout', '')
                    handle.write(block)
            return
        except requests.exceptions.RequestException:
            raise GithubError('fail', 'Download beech mein ruk gaya.')
        finally:
            resp.close()
    raise GithubError('fail', 'Bahut zyada redirect.')


# ---- picking the important files ----------------------------------------------------------
def _gh_rel_ok(rel):
    parts = rel.split('/')
    if len(parts) > 8:
        return False
    return all(GH_SEG_RE.fullmatch(p) or p in ('.env.example', '.env.sample', '.env.template') for p in parts)


def gh_collect_files(root, subdir=None):
    """Walk a cloned repo and pick the files worth hosting. Returns {'files': [(rel, abs, size)], 'skipped': {reason: count}}.
    Raises GithubError for a symlink that points outside the repo, or a selection that is too big. Nothing is copied here."""
    base = os.path.realpath(root)
    if subdir:
        base = os.path.realpath(os.path.join(base, *subdir.split('/')))
        if os.path.commonpath((os.path.realpath(root), base)) != os.path.realpath(root) or not os.path.isdir(base):
            raise GithubError('subdir', 'Ye folder repo mein nahi mila. Link ka /tree/branch/folder part check karo.')
    skipped = {}
    picked = []
    total = 0

    def skip(reason):
        skipped[reason] = skipped.get(reason, 0) + 1

    for current, dirs, names in os.walk(base, followlinks=False):
        keep_dirs = []
        for d in sorted(dirs):
            full = os.path.join(current, d)
            if os.path.islink(full):
                if os.path.commonpath((base, os.path.realpath(full))) != base:
                    raise GithubError('symlink', 'Repo mein aisa shortcut (symlink) hai jo repo ke bahar jaata hai. Safety ke liye roka gaya.')
                skip('symlink')
                continue
            if d.lower() in GH_SKIP_DIRS:
                skip('junk folder')
                continue
            keep_dirs.append(d)
        dirs[:] = keep_dirs
        for name in sorted(names):
            full = os.path.join(current, name)
            rel = os.path.relpath(full, base).replace(os.sep, '/')
            if os.path.islink(full):
                if os.path.commonpath((base, os.path.realpath(full))) != base:
                    raise GithubError('symlink', 'Repo mein aisa shortcut (symlink) hai jo repo ke bahar jaata hai. Safety ke liye roka gaya.')
                skip('symlink')
                continue
            try:
                size = os.lstat(full).st_size
            except OSError:
                continue
            low = name.lower()
            ext = os.path.splitext(low)[1]
            if low.endswith(GH_PROTECTED_SUFFIXES) and low not in GH_INFO_NAMES:
                skip('env/db file')
                continue
            if low in GH_INFO_NAMES:
                kind = 'info'
            elif ext in GH_CODE_EXTS:
                kind = 'code'
            elif ext in GH_DATA_EXTS:
                kind = 'data'
            elif ext in GH_ASSET_EXTS:
                kind = 'asset'
            else:
                skip('other')
                continue
            if not _gh_rel_ok(rel):
                skip('odd name')
                continue
            if kind == 'data' and size > GH_MAX_DATA_KB * 1024:
                skip('big data file')
                continue
            elif kind == 'asset' and size > GH_MAX_ASSET_KB * 1024:
                skip('big image')
                continue
            elif kind == 'info' and size > GH_MAX_DATA_KB * 1024:
                skip('big data file')
                continue
            total += size
            picked.append((rel, full, size))
            if len(picked) > GH_MAX_FILES:
                raise GithubError('toobig', f'Zyada files hain (max {GH_MAX_FILES} important files).')
            if total > GH_MAX_SELECTED_MB * 1024 * 1024:
                raise GithubError('toobig', f'Important files ka total {GH_MAX_SELECTED_MB} MB se bada hai.')
    return {'files': picked, 'skipped': skipped}


GH_MAIN_ORDER = ('bot.py', 'main.py', 'app.py', 'index.js', 'bot.js', 'main.js')


def gh_detect_main(files):
    """files: list of (rel, abs, size). Returns an ordered list of runnable candidates found at the top level
    (bot.py, main.py, app.py, index.js, bot.js, main.js, package.json start/main, Procfile worker:/web:)."""
    rels = {rel for rel, _, _ in files}
    top_code = {r for r in rels if '/' not in r and r.lower().endswith(GH_CODE_EXTS) and not r.lower().endswith(('.mjs', '.cjs'))}
    found = []

    def add(name):
        name = (name or '').strip().lstrip('./')
        if name in top_code and name not in found:
            found.append(name)

    for name in GH_MAIN_ORDER:
        add(name)
    by_rel = {rel: path for rel, path, _ in files}
    if 'package.json' in by_rel:
        try:
            with open(by_rel['package.json'], 'r', encoding='utf-8', errors='ignore') as handle:
                pkg = json.load(handle)
            start = (pkg.get('scripts') or {}).get('start') if isinstance(pkg, dict) else None
            if isinstance(start, str):
                m = re.match(r'^\s*node\s+([A-Za-z0-9_./-]+\.js)\s*$', start)
                if m:
                    add(m.group(1))
            main = pkg.get('main') if isinstance(pkg, dict) else None
            if isinstance(main, str):
                add(main)
        except (OSError, ValueError):
            pass
    proc_key = next((r for r in rels if r.lower() == 'procfile'), None)
    if proc_key:
        try:
            with open(by_rel[proc_key], 'r', encoding='utf-8', errors='ignore') as handle:
                for line in handle.read(20000).splitlines():
                    m = re.match(r'^\s*(?:worker|web)\s*:\s*(?:python3?|node)\s+([A-Za-z0-9_./-]+\.(?:py|js))\b', line)
                    if m:
                        add(m.group(1))
        except OSError:
            pass
    return found


def gh_main_choices(files):
    """(candidates, fallback_used). Falls back to every top-level .py/.js when none of the usual names exists."""
    found = gh_detect_main(files)
    if found:
        return found, False
    others = sorted(r for r, _, _ in files if '/' not in r and r.lower().endswith(('.py', '.js')))
    return others, True


# ---- dependency files: only plain package names, no links, no install scripts --------------
GH_REQ_LINE_RE = re.compile(r'^[A-Za-z0-9][A-Za-z0-9._-]*(\[[A-Za-z0-9._,-]+\])?\s*((==|>=|<=|~=|!=|<|>|===)\s*[A-Za-z0-9*.+!_-]+\s*(,\s*(==|>=|<=|~=|!=|<|>)\s*[A-Za-z0-9*.+!_-]+\s*)*)?'
                            r'(;\s*[A-Za-z0-9_.\s\'"<>=!~()]+)?$')


def gh_clean_requirements(text):
    """Keep only plain 'name [version]' lines. Options (-r, -e, --index-url ...), links, VCS and path requirements are dropped,
    because they could pull code from anywhere. Returns (clean_text, dropped_count)."""
    kept, dropped = [], 0
    for line in text.splitlines():
        stripped = line.split(' #', 1)[0].strip()
        if not stripped or stripped.startswith('#'):
            continue
        if GH_REQ_LINE_RE.fullmatch(stripped) and '://' not in stripped and '@' not in stripped:
            kept.append(stripped)
        else:
            dropped += 1
    return '\n'.join(kept) + ('\n' if kept else ''), dropped


def gh_clean_package_json(raw):
    """Drop dependencies that point at a link, git repo or local path (npm would fetch code from there). Returns (bytes, dropped_names)."""
    try:
        pkg = json.loads(raw.decode('utf-8-sig'))
    except (ValueError, UnicodeDecodeError):
        return raw, []
    if not isinstance(pkg, dict):
        return raw, []
    dropped = []
    for section in ('dependencies', 'optionalDependencies', 'devDependencies', 'peerDependencies'):
        deps = pkg.get(section)
        if not isinstance(deps, dict):
            continue
        for name in list(deps):
            spec = str(deps[name]).strip().lower()
            if (not re.fullmatch(r'[a-z0-9@/._~^<>=*|\s-]*', spec) or '/' in spec or spec.startswith(('git', 'file', 'link', 'http', 'github', 'npm:'))
                    or not re.fullmatch(r'(@[a-z0-9._~-]+/)?[a-z0-9._~-]+', name.lower())):
                dropped.append(name)
                del deps[name]
    if dropped:
        return json.dumps(pkg, indent=2).encode('utf-8'), dropped
    return raw, []


def gh_lock_is_safe(raw):
    """A package-lock.json is kept only when every download address in it is the normal npm registry."""
    try:
        for url in re.findall(rb'"resolved"\s*:\s*"([^"]*)"', raw):
            if not url.startswith(b'https://registry.npmjs.org/'):
                return False
        return b'"git+' not in raw and b'"file:' not in raw
    except Exception:
        return False


# ---- manifest + zip -------------------------------------------------------------------------
def _gh_sign_key():
    return hashlib.sha256(('github-manifest:' + BOT_TOKEN).encode()).digest()


def gh_sign_manifest(manifest):
    body = {k: v for k, v in manifest.items() if k != 'sig'}
    data = json.dumps(body, sort_keys=True, separators=(',', ':')).encode()
    return hmac.new(_gh_sign_key(), data, hashlib.sha256).hexdigest()


def gh_manifest_valid(manifest):
    """True only for a manifest made by this bot (a user's own zip cannot fake it)."""
    try:
        return (isinstance(manifest, dict) and isinstance(manifest.get('sig'), str)
                and hmac.compare_digest(manifest['sig'], gh_sign_manifest(manifest))
                and isinstance(manifest.get('repo'), str) and isinstance(manifest.get('main'), str))
    except Exception:
        return False


def gh_build_zip(files, out_path, info, main_name, update=False, notes=None):
    """Write the picked files (+ cleaned dependency files + signed manifest) into one zip. Returns the list of kept relative names."""
    notes = notes if notes is not None else {}
    kept = []
    with zipfile.ZipFile(out_path, 'w', zipfile.ZIP_DEFLATED) as archive:
        for rel, path, _ in files:
            low = rel.lower()
            with open(path, 'rb') as handle:
                raw = handle.read()
            if low == 'requirements.txt':
                clean, dropped = gh_clean_requirements(raw.decode('utf-8', 'ignore'))
                if dropped:
                    notes['req_dropped'] = dropped
                raw = clean.encode()
                if not raw.strip():
                    continue
            elif low == 'package.json':
                raw, dropped_pkgs = gh_clean_package_json(raw)
                if dropped_pkgs:
                    notes['pkg_dropped'] = dropped_pkgs
            elif low == 'package-lock.json' and not gh_lock_is_safe(raw):
                notes['lock_dropped'] = True
                continue
            archive.writestr(rel, raw)
            kept.append(rel)
        manifest = {'v': 1, 'repo': info['url'], 'branch': info.get('branch') or '', 'subdir': info.get('subdir') or '',
                    'main': main_name, 'update': bool(update), 'files': kept[:GH_MAX_FILES]}
        manifest['sig'] = gh_sign_manifest(manifest)
        archive.writestr(GH_MANIFEST_NAME, json.dumps(manifest))
    return kept


def gh_manifest_from_zip_bytes(data):
    """The verified manifest of a zip held in memory / on disk, or None."""
    try:
        with zipfile.ZipFile(io.BytesIO(data) if isinstance(data, (bytes, bytearray)) else data) as archive:
            info = archive.getinfo(GH_MANIFEST_NAME)
            if info.file_size > 200000:
                return None
            manifest = json.loads(archive.read(info).decode('utf-8'))
        return manifest if gh_manifest_valid(manifest) else None
    except Exception:
        return None


def gh_take_manifest(extract_dir):
    """Read and REMOVE the manifest from an extracted archive. Returns it only when the signature is ours."""
    path = os.path.join(extract_dir, GH_MANIFEST_NAME)
    if not os.path.isfile(path) or os.path.islink(path):
        return None
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            manifest = json.loads(handle.read(300000))
    except (OSError, ValueError):
        manifest = None
    _remove_quietly(path)          # never left behind in the user's storage, valid or not
    if manifest is not None and gh_manifest_valid(manifest):
        return manifest
    return None


# ---- sidecar (<bot file>.github.json inside the user's folder: travels with every backup) --------
def gh_sidecar_path(user_folder, file_name):
    base = bot_env_path(user_folder, file_name)
    return None if base is None else os.path.join(user_folder, file_name + GH_SIDECAR_SUFFIX)


def gh_write_sidecar(user_folder, file_name, manifest):
    path = gh_sidecar_path(user_folder, file_name)
    if path is None:
        return False
    body = {'repo': manifest['repo'], 'branch': manifest.get('branch', ''), 'subdir': manifest.get('subdir', ''),
            'main': file_name, 'files': list(manifest.get('files', []))[:GH_MAX_FILES], 'updated': int(time.time())}
    tmp = path + '.tmp'
    try:
        with open(tmp, 'w', encoding='utf-8') as handle:
            json.dump(body, handle)
        os.replace(tmp, path)
        return True
    except OSError as exc:
        logger.warning('Could not write GitHub info for %s: %s', file_name, exc)
        _remove_quietly(tmp)
        return False


def gh_read_sidecar(user_folder, file_name):
    """Stored source of a bot, re-validated (a restored backup could carry anything). Returns (info, data) or (None, None)."""
    path = gh_sidecar_path(user_folder, file_name)
    if path is None or not os.path.isfile(path) or os.path.islink(path):
        return None, None
    try:
        with open(path, 'r', encoding='utf-8') as handle:
            data = json.loads(handle.read(400000))
        link = data['repo'] + ('/tree/' + data['branch'] + ('/' + data['subdir'] if data.get('subdir') else '') if data.get('branch') else '')
        info = parse_github_url(link)
        if not isinstance(data.get('files', []), list):
            data['files'] = []
        data['files'] = [f for f in data['files'] if isinstance(f, str)][:GH_MAX_FILES]
        return info, data
    except Exception:
        return None, None


# ---- running a deploy (clone -> pick files -> pack -> SAME zip deploy as a manual zip) -----------------
def gh_begin(user_id):
    """One GitHub deploy at a time per user. True when this user may start one."""
    with GH_LOCK:
        if user_id in GH_ACTIVE_USERS:
            return False
        GH_ACTIVE_USERS.add(user_id)
        return True


def gh_end(user_id):
    with GH_LOCK:
        GH_ACTIVE_USERS.discard(user_id)


def _gh_say(ctx, text):
    """Final / plain line: edit the status message (never raises). While the status is animated the animation is
    replaced by this text."""
    pm = ctx.get('pm')
    if isinstance(pm, ProgressMessage) and not pm._done and pm.message_id is not None:
        pm.finish(text)
        return
    try:
        bot.edit_message_text(text, ctx['chat_id'], ctx['status_id'], parse_mode='HTML')
    except Exception as exc:
        logger.debug('GitHub status edit failed: %s', type(exc).__name__)


GH_STEPS = 4    # clone, pick files, pack, deploy


def _gh_stage(ctx, done, line):
    """A step of the deploy: moves the real progress bar (done of GH_STEPS) on the animated status message."""
    pm = ctx.get('pm')
    if isinstance(pm, ProgressMessage) and not pm._done and not pm.passive and pm.message_id is not None:
        repo = f"{ctx['info']['owner']}/{ctx['info']['repo']}"
        pm.update(done, GH_STEPS, UIRaw(f"🐙 <code>{html_escape(repo)}</code>\n{line}"))
        return
    _gh_say(ctx, f"{_gh_head(ctx)}\n{line}")


def _gh_start_status(ctx, kind):
    """Send the animated status message of a deploy. Raises when it cannot be shown (like the plain message did)."""
    repo = f"{ctx['info']['owner']}/{ctx['info']['repo']}"
    pm = ui_anim(ctx['chat_id'], f'GitHub {kind}', UIRaw(f"🐙 <code>{html_escape(repo)}</code>\n⏳ Shuru ho raha hai..."),
                 done=0, total=GH_STEPS)
    if pm.message_id is None:
        raise RuntimeError('GitHub status message could not be sent')
    ctx['pm'] = pm
    ctx['status_id'] = pm.message_id


def _gh_head(ctx):
    kind = 'Update' if ctx.get('update') else 'Deploy'
    return f"🐙 <b>GitHub {kind}</b> - <code>{html_escape(ctx['info']['owner'])}/{html_escape(ctx['info']['repo'])}</code>"


def _gh_error_text(err):
    """User-facing text for a GithubError (plain next step, no raw errors)."""
    code = getattr(err, 'code', 'fail')
    if code == 'notfound':
        return ('Repo nahi mila, ya woh private hai. Abhi sirf PUBLIC repos chalte hain (token/password main nahi leta). '
                'Link check karo, ya repo ko Public karke dobara try karo.')
    if code == 'branch':
        return 'Ye branch repo mein nahi mili. Link ka /tree/<branch> part check karo, ya branch ke bina sirf repo ka link do.'
    if code == 'timeout':
        return f'Download {GH_CLONE_TIMEOUT} second se zyada lag raha tha, isliye roka gaya. Thodi der baad dobara try karo.'
    if code == 'toobig':
        return f'Repo bahut bada hai (limit {GH_MAX_REPO_MB} MB). Chhota repo ya /tree/branch/folder wala link try karo.'
    if code == 'nogit':
        return 'Server par git nahi mila aur backup tareeka bhi nahi chala. Admin ko batao.'
    if code == 'fail':
        return 'GitHub se repo nahi aa paya (network ya link ki problem). Thodi der baad dobara try karo.'
    return getattr(err, 'text', '') or 'Kuch gadbad ho gayi. Dobara try karo.'


def gh_prepare(info, work_dir):
    """Clone the repo into <work_dir>/repo (git first, GitHub's zip archive when git is not installed). Returns the folder
    with the .git data removed. Raises GithubError."""
    dest = os.path.join(work_dir, 'repo')
    code = gh_clone(info['clone_url'], dest, info.get('branch'))
    if code == 'nogit':
        archive = os.path.join(work_dir, 'repo_archive.zip')
        try:
            gh_fetch_archive(info, archive)
            gh_extract_archive(archive, dest)
        finally:
            _remove_quietly(archive)
    elif code:
        raise GithubError(code, '')
    _rmtree_quiet(os.path.join(dest, '.git'))
    return dest


def _gh_top_clashes(user_id, files):
    """Top-level names of the picked files that already exist in the user's storage."""
    folder = get_user_folder(user_id)
    known = {item[0] for item in user_files.get(user_id, [])}
    tops = sorted({rel.split('/')[0] for rel, _, _ in files})
    return [name for name in tops if name in known or os.path.lexists(os.path.join(folder, name))]


def _gh_skip_summary(skipped):
    if not skipped:
        return ''
    return ', '.join(f'{count} {reason}' for reason, count in sorted(skipped.items(), key=lambda kv: -kv[1])[:4])


def _gh_cleanup(ctx):
    pm = ctx.get('pm')
    if isinstance(pm, ProgressMessage) and not pm._done:
        pm.fail(f"{_gh_head(ctx)}\n❌ Kuch gadbad ho gayi, kuch save nahi hua. Thodi der baad dobara try karo.")
    _rmtree_quiet(ctx.get('work'))
    gh_end(ctx['user_id'])


def _gh_run(ctx):
    """Whole deploy in a background thread. Cleans its temp folder in every case except while a picker is waiting."""
    picking = False
    slot = False
    try:
        if not GH_SLOTS.acquire(blocking=False):
            _gh_say(ctx, f"{_gh_head(ctx)}\n⏳ Abhi {GH_GLOBAL_LIMIT} deploy chal rahe hain, server busy hai. 1-2 minute baad dobara try karo.")
            return
        slot = True
        ctx['work'] = tempfile.mkdtemp(prefix=f"user_{ctx['user_id']}_gh_")
        _gh_stage(ctx, 0, "⏳ Repo clone ho raha hai (public repo, sirf padhne ke liye)...")
        try:
            repo_dir = gh_prepare(ctx['info'], ctx['work'])
            _gh_stage(ctx, 1, "📂 Important files chun raha hoon...")
            picked = gh_collect_files(repo_dir, ctx['info'].get('subdir'))
        except GithubError as err:
            _gh_say(ctx, f"{_gh_head(ctx)}\n❌ {html_escape(_gh_error_text(err))}")
            return
        files = picked['files']
        ctx['files'] = files
        ctx['skipped'] = picked['skipped']
        if not any(rel.lower().endswith(('.py', '.js')) for rel, _, _ in files):
            _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Is repo (ya folder) mein koi .py ya .js file nahi mili, to chalane layak kuch nahi hai.")
            return
        if ctx.get('update'):
            if ctx['main'] not in {rel for rel, _, _ in files}:
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Update nahi hua: <code>{html_escape(ctx['main'])}</code> ab repo ke top par nahi mili. Purana version waise hi hai.")
                return
            main = ctx['main']
        else:
            candidates, fallback = gh_main_choices(files)
            if not candidates:
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Main file nahi mili. Repo ke top par bot.py, main.py, app.py, index.js ya bot.js honi chahiye "
                             "(ya /tree/branch/folder wala link do jahan wo file ho).")
                return
            clashes = _gh_top_clashes(ctx['user_id'], files)
            if clashes:
                shown = ', '.join(html_escape(c) for c in clashes[:6])
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Tumhari storage mein ye naam pehle se hain: <code>{shown}</code>. "
                             "Pehle wali file delete ya rename karo, phir dobara try karo (kuch overwrite nahi kiya).")
                return
            if len(candidates) > 1:
                picking = _gh_offer_pick(ctx, candidates[:9], fallback)
                if picking:
                    return
                _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Main file ki list nahi dikha paya. Dobara try karo.")
                return
            main = candidates[0]
        _gh_finish(ctx, main)
    except Exception:
        logger.exception('GitHub deploy crashed for user %s', ctx.get('user_id'))
        _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Kuch gadbad ho gayi, kuch save nahi hua. Thodi der baad dobara try karo.")
    finally:
        if slot:
            GH_SLOTS.release()
        if not picking:
            _gh_cleanup(ctx)


def _gh_offer_pick(ctx, candidates, fallback):
    """Several possible main files: ask which one runs. The clone stays in a temp folder until the user answers (or GH_PICK_TTL)."""
    token = secrets.token_hex(4)
    ctx['candidates'] = list(candidates)
    ctx['created'] = time.time()
    ctx['token'] = token
    with GH_LOCK:
        GH_PENDING[token] = ctx
    keycaps = ['1️⃣', '2️⃣', '3️⃣', '4️⃣', '5️⃣', '6️⃣', '7️⃣', '8️⃣', '9️⃣']
    menu = NavMenu(row_width=1)
    for index, name in enumerate(candidates):
        menu.row(NavButton(f'{keycaps[index]} {name}', callback_data=f'ghp_{token}_{index}'))
    menu.row(NavButton('❌ Cancel', callback_data=f'ghx_{token}'))
    why = 'Usual naam nahi mila, ye .py/.js files top par hain' if fallback else 'Kai main file mil gayi'
    text = f"{_gh_head(ctx)}\n🤔 {why}. Kaun si file chalani hai? Number dabao:"
    _gh_say(ctx, text)
    sent = _safe_send(ctx['chat_id'], f'Main file chuno (ye {GH_PICK_TTL // 60} minute tak rukega) 👇', reply_markup=menu)
    if sent is None:
        with GH_LOCK:
            GH_PENDING.pop(token, None)
        return False
    timer = threading.Timer(GH_PICK_TTL + 5, _gh_expire_token, args=(token,))
    timer.daemon = True
    timer.start()
    return True


def _gh_menu_back(ctx):
    """After a cancelled / expired deploy: put the main menu keyboard back (never raises)."""
    try:
        bot.send_message(ctx['chat_id'], "🏠 Menu", reply_markup=create_main_menu_inline(ctx['actor_id']))
    except Exception:
        logger.debug('Could not restore the menu after a GitHub cancel')


def _gh_expire_token(token):
    with GH_LOCK:
        ctx = GH_PENDING.pop(token, None)
    if ctx is not None:
        _gh_say(ctx, f"{_gh_head(ctx)}\n⌛ Main file chuni nahi gayi, isliye deploy cancel ho gaya. Dobara Upload se shuru karo.")
        _gh_cleanup(ctx)
        _gh_menu_back(ctx)


def _gh_cancel_user(user_id):
    """Cancel pressed: drop any 'pick the main file' list this user left open."""
    with GH_LOCK:
        tokens = [t for t, c in GH_PENDING.items() if c['user_id'] == user_id or c['actor_id'] == user_id]
        dropped = [GH_PENDING.pop(t) for t in tokens]
    for ctx in dropped:
        _gh_say(ctx, f"{_gh_head(ctx)}\n❎ Cancel ho gaya, kuch save nahi hua.")
        _gh_cleanup(ctx)


def _gh_resume(ctx, main):
    """After the user picked the main file."""
    slot = False
    try:
        slot = GH_SLOTS.acquire(timeout=60)
        if not slot:
            _gh_say(ctx, f"{_gh_head(ctx)}\n⏳ Server busy hai, kuch save nahi hua. Thodi der baad dobara try karo.")
            return
        pm = ctx.get('pm')
        if isinstance(pm, ProgressMessage) and ctx.get('status_id') is not None:
            repo = f"{ctx['info']['owner']}/{ctx['info']['repo']}"
            ctx['pm'] = ui_anim(ctx['chat_id'], pm.title, UIRaw(f"🐙 <code>{html_escape(repo)}</code>\n⏳ Files pack karne ki taiyaari..."),
                                message_id=ctx['status_id'], done=2, total=GH_STEPS)
        _gh_finish(ctx, main)
    except Exception:
        logger.exception('GitHub deploy (after pick) crashed for user %s', ctx.get('user_id'))
        _gh_say(ctx, f"{_gh_head(ctx)}\n❌ Kuch gadbad ho gayi, kuch save nahi hua. Thodi der baad dobara try karo.")
    finally:
        if slot:
            GH_SLOTS.release()
        _gh_cleanup(ctx)


def _gh_finish(ctx, main):
    """Pack the picked files, then hand the zip to the same deploy path as a manual zip upload."""
    user_id, chat_id, info = ctx['user_id'], ctx['chat_id'], ctx['info']
    files = ctx['files']
    label = f"{info['owner']}/{info['repo']}"
    zip_name = f"{info['repo']}-update.zip" if ctx.get('update') else f"{info['repo']}.zip"
    zip_path = os.path.join(ctx['work'], 'pack.zip')
    notes = {}
    _gh_stage(ctx, 2, "📦 Files pack ho rahi hain...")
    try:
        kept = gh_build_zip(files, zip_path, info, main, update=bool(ctx.get('update')), notes=notes)
        with open(zip_path, 'rb') as handle:
            data = handle.read()
    except GithubError as err:
        _gh_say(ctx, f"{_gh_head(ctx)}\n❌ {html_escape(_gh_error_text(err))}")
        return
    total = sum(size for _, _, size in files)
    lines = [_gh_head(ctx), f"✅ {len(kept)} important files li ({_human_size(total)}). Main: <code>{html_escape(main)}</code>"]
    skip_text = _gh_skip_summary(ctx.get('skipped'))
    if skip_text:
        lines.append(f"↪️ Skip: {html_escape(skip_text)}")
    if notes.get('req_dropped'):
        lines.append(f"⚠️ requirements.txt ki {notes['req_dropped']} line(s) hatayi (link/option wali, safety ke liye).")
    if notes.get('pkg_dropped'):
        lines.append(f"⚠️ package.json ki ye dependencies hatayi (link/git wali): {html_escape(', '.join(notes['pkg_dropped'][:5]))}")
    if notes.get('lock_dropped'):
        lines.append('⚠️ package-lock.json hata di (registry ke bahar ke links the).')
    summary = '\n'.join(lines)
    _gh_stage(ctx, 3, '\n'.join(lines[1:]) + '\n🚀 Deploy ho raha hai...')
    logger.info('GitHub deploy: user=%s repo=%s update=%s', user_id, label, bool(ctx.get('update')))
    reply_obj = _ReplyTarget(chat_id, ctx['status_id'], user_id)
    try:
        ok, err = _deploy_upload(user_id, zip_name, 'zip', data, reply_obj)
    except Exception:
        _gh_say(ctx, summary + '\n❌ Deploy poora nahi hua. Dobara try karo.')
        raise
    _gh_say(ctx, summary + ('\n✅ Deploy ho gaya. Details neeche wale message mein hain.' if ok
                            else '\n⚠️ Deploy poora nahi hua. Reason neeche bheja gaya hai.'))
    if not ok and err:
        _safe_send(chat_id, ui_warn('Upload Problem', ui_esc(err)))


# ---- link prompt, picker answers, update button ------------------------------------------------------------------------
def _gh_upload_menu():
    menu = NavMenu(row_width=1)
    menu.row(NavButton('🐙 Deploy from GitHub', callback_data='gh_start'))
    menu.row(NavButton('📤 Manual Upload', callback_data='gh_manual'))
    menu.row(NavButton('❌ Cancel', callback_data='nav_cancel'))
    return menu


UPLOAD_CHOICE_TEXT = ui_msg('🚀', 'Upload Script', 'Upload kaise karna hai? Ek option chuno:\n',
                            ui_row('🐙', 'Deploy from GitHub', 'apne public GitHub repo ka link do, main important files clone karke chala dunga', bold=False),
                            ui_row('📤', 'Manual Upload', 'apni .py, .js ya .zip file khud bhejo', bold=False),
                            foot='Supported: .py  .js  .zip', brand=True)


def _file_limit_text(current_files, limit_str):
    return ui_warn('File Limit Reached', ui_row('📂', 'Files', f"{current_files}/{limit_str}"),
                   f"<code>{ui_bar(current_files, int(limit_str) if str(limit_str).isdigit() else (current_files or 1))}</code>",
                   foot='Purani file delete karo, ya backup export/import karo.')


def _send_upload_choice(chat_id):
    bot.send_message(chat_id, UPLOAD_CHOICE_TEXT, parse_mode='HTML', reply_markup=_gh_upload_menu())


def _upload_limit_ok(user_id, chat_id):
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = str(file_limit) if file_limit != float('inf') else 'Unlimited'
        bot.send_message(chat_id, _file_limit_text(current_files, limit_str),
                         reply_markup=_files_view(user_id)[1], parse_mode='HTML')
        return False
    return True


def gh_manual_callback(call):
    bot.answer_callback_query(call.id)
    if _upload_limit_ok(call.from_user.id, call.message.chat.id):
        bot.send_message(call.message.chat.id, "📤 Send your Python (`.py`), JS (`.js`), or ZIP (`.zip`) file.",
                         reply_markup=NavMenu().add(NavButton('❌ Cancel', callback_data='nav_cancel')))


def gh_start_callback(call):
    bot.answer_callback_query(call.id)
    user_id, chat_id = call.from_user.id, call.message.chat.id
    if not _upload_limit_ok(user_id, chat_id):
        return
    with GH_LOCK:
        busy = user_id in GH_ACTIVE_USERS
    if busy:
        bot.send_message(chat_id, '⏳ Tumhara ek GitHub deploy abhi chal raha hai (ya main file ka intezaar hai). Pehle use khatam hone do.')
        return
    prompt = ("🐙 <b>Deploy from GitHub</b>\n\nApne <b>public</b> repo ka link bhejo, jaise:\n"
              "<code>https://github.com/owner/repo</code>\n"
              "Branch/folder ke liye: <code>https://github.com/owner/repo/tree/main/folder</code>\n\n"
              "Private repo abhi support nahi hai, aur main koi token/password nahi maangta.")
    sent = bot.send_message(chat_id, prompt, parse_mode='HTML', reply_markup=NavMenu().add(NavButton('❌ Cancel', callback_data='nav_cancel')))
    bot.register_next_step_handler(sent, _gh_receive_link, user_id)


def _gh_receive_link(message, actor_id):
    chat_id = message.chat.id
    user_id = message.from_user.id
    text = getattr(message, 'text', None)
    if user_id != actor_id or not text:
        sent = bot.send_message(chat_id, ui_warn('Text Needed', 'Link text mein bhejo, jaise https://github.com/owner/repo', foot='Dobara link bhejo, ya Cancel dabao.'), parse_mode='HTML')
        bot.register_next_step_handler(sent, _gh_receive_link, actor_id)
        return
    try:
        info = parse_github_url(text)
    except GithubError as err:
        sent = bot.send_message(chat_id, f"⚠️ {err.text}\nDobara link bhejo, ya Cancel dabao.")
        bot.register_next_step_handler(sent, _gh_receive_link, actor_id)
        return
    if is_user_banned(user_id) or (bot_locked and user_id not in admin_ids):
        bot.send_message(chat_id, ui_warn('Heads Up', 'Abhi deploy nahi ho sakta.', foot='Thodi der baad dobara try karo.'), parse_mode='HTML')
        return
    if not _upload_limit_ok(user_id, chat_id):
        return
    if not gh_begin(user_id):
        bot.send_message(chat_id, '⏳ Tumhara ek GitHub deploy abhi chal raha hai. Pehle use khatam hone do.')
        return
    uploader = message.from_user.first_name or message.from_user.username or str(user_id)
    ctx = {'user_id': user_id, 'actor_id': user_id, 'chat_id': chat_id, 'status_id': None, 'info': info,
           'update': False, 'uploader': uploader, 'work': None}
    try:
        _gh_start_status(ctx, 'Deploy')
    except Exception:
        gh_end(user_id)
        raise
    threading.Thread(target=_gh_run, args=(ctx,), daemon=True).start()


def gh_pick_callback(call):
    """ghp_<token>_<index> = chosen main file, ghx_<token> = cancel."""
    parts = call.data.split('_')
    token = parts[1] if len(parts) > 1 else ''
    with GH_LOCK:
        ctx = GH_PENDING.get(token)
        allowed = ctx is not None and call.from_user.id in (ctx['actor_id'], ctx['user_id'])
        if allowed:
            GH_PENDING.pop(token, None)
    if ctx is None or not allowed:
        bot.answer_callback_query(call.id, 'Ye list purani ho gayi. Upload se dobara shuru karo.', show_alert=True)
        return
    if parts[0] == 'ghx':
        bot.answer_callback_query(call.id, 'Cancel ho gaya.')
        _gh_say(ctx, f"{_gh_head(ctx)}\n❎ Cancel ho gaya, kuch save nahi hua.")
        _gh_cleanup(ctx)
        _gh_menu_back(ctx)
        return
    try:
        main = ctx['candidates'][int(parts[2])]
    except (IndexError, ValueError):
        bot.answer_callback_query(call.id, 'Galat choice.', show_alert=True)
        _gh_cleanup(ctx)
        return
    bot.answer_callback_query(call.id, f'{main} chuni.')
    threading.Thread(target=_gh_resume, args=(ctx, main), daemon=True).start()


def gh_update_callback(call):
    """ghu_<ownerid>_<file>: pull the repo again and deploy it."""
    try:
        _, owner_str, file_name = call.data.split('_', 2)
        owner_id = int(owner_str)
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, 'Galat button.', show_alert=True)
        return
    actor = call.from_user.id
    if not (actor == owner_id or actor in admin_ids):
        bot.answer_callback_query(call.id, '⚠️ Permission denied.', show_alert=True)
        return
    if not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        bot.answer_callback_query(call.id, '⚠️ File not found.', show_alert=True)
        return
    info, side = gh_read_sidecar(get_user_folder(owner_id), file_name)
    if info is None:
        bot.answer_callback_query(call.id, 'Is bot ka GitHub source yaad nahi hai.', show_alert=True)
        return
    if not gh_begin(owner_id):
        bot.answer_callback_query(call.id, 'Ek GitHub deploy pehle se chal raha hai.', show_alert=True)
        return
    bot.answer_callback_query(call.id, 'Update shuru...')
    chat_id = call.message.chat.id
    uploader = call.from_user.first_name or call.from_user.username or str(actor)
    ctx = {'user_id': owner_id, 'actor_id': actor, 'chat_id': chat_id, 'status_id': None, 'info': info,
           'update': True, 'main': file_name, 'uploader': uploader, 'work': None}
    try:
        _gh_start_status(ctx, 'Update')
    except Exception:
        gh_end(owner_id)
        raise
    threading.Thread(target=_gh_run, args=(ctx,), daemon=True).start()


# ---- applying an update to an already hosted bot ------------------------------------------------------------------------
def _gh_apply_update(extract_dir, manifest, user_id, user_folder, message, state):
    """Update branch of the zip deploy. Only code files the earlier GitHub deploy put there are overwritten;
    .env / .db / .sqlite files, data files and anything else of the user stay untouched. If anything fails the old files
    are put back. The bot is restarted only after everything worked."""
    main = manifest['main']
    info, side = gh_read_sidecar(user_folder, main)
    entry = next((item for item in user_files.get(user_id, []) if item[0] == main), None)
    if info is None or info['url'] != manifest.get('repo') or entry is None or not os.path.isfile(os.path.join(user_folder, main)):
        bot.reply_to(message, ui_err('Could Not Do That', 'Update nahi hua: is bot ka GitHub source ya file ab maujood nahi hai.', foot='Purana version waise hi hai.'), parse_mode='HTML')
        return
    file_type = entry[1]
    known = set(side.get('files') or [])
    root_real = os.path.realpath(user_folder)
    plan, kept_count = [], 0
    for base, dirs, names in os.walk(extract_dir):
        for name in names:
            src = os.path.join(base, name)
            rel = os.path.relpath(src, extract_dir).replace(os.sep, '/')
            low = rel.lower()
            leaf = os.path.basename(low)
            if os.path.islink(src) or not _gh_rel_ok(rel):
                continue
            if low.endswith(GH_PROTECTED_SUFFIXES) and leaf not in GH_INFO_NAMES:
                kept_count += 1
                continue
            dest = os.path.join(user_folder, *rel.split('/'))
            real = os.path.realpath(dest)
            if os.path.commonpath((root_real, real)) != root_real or real != os.path.join(os.path.realpath(os.path.dirname(dest)), os.path.basename(dest)):
                continue
            if os.path.lexists(dest):
                is_code = low.endswith(GH_UPDATE_CODE_EXTS) or leaf in GH_UPDATE_CODE_NAMES
                if os.path.isfile(dest) and not os.path.islink(dest) and rel in known and is_code:
                    plan.append((rel, src, dest, 'update'))
                else:
                    kept_count += 1
            else:
                plan.append((rel, src, dest, 'new'))
    if main not in {rel for rel, _, _, _ in plan}:
        bot.reply_to(message, ui_err('Could Not Do That', 'Update nahi hua: main file update list mein nahi aayi.', foot='Purana version waise hi hai.'), parse_mode='HTML')
        return
    if os.path.isfile(os.path.join(extract_dir, 'requirements.txt')):
        if not _install_zip_deps(extract_dir, message, user_id, safe=True, do_npm=False):
            return
    backup_dir = os.path.join(os.path.dirname(extract_dir), 'update_backup')
    os.makedirs(backup_dir, exist_ok=True)
    touched = []          # (rel, dest, action)

    def rollback():
        for rel, dest, action in reversed(touched):
            try:
                if action == 'new':
                    _remove_quietly(dest)
                else:
                    shutil.copyfile(os.path.join(backup_dir, *rel.split('/')), dest)
            except OSError as exc:
                logger.error('GitHub update rollback failed for %s: %s', rel, exc)

    try:
        for rel, src, dest, action in plan:
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            if action == 'update':
                backup = os.path.join(backup_dir, *rel.split('/'))
                os.makedirs(os.path.dirname(backup), exist_ok=True)
                shutil.copyfile(dest, backup)
            tmp = dest + '.ghtmp'
            shutil.copyfile(src, tmp)
            os.replace(tmp, dest)
            touched.append((rel, dest, action))
    except OSError as exc:
        logger.error('GitHub update copy failed: %s', exc)
        rollback()
        bot.reply_to(message, ui_err('Could Not Do That', 'Update ke beech file likhne mein dikkat aayi.', foot='Purani files wapas rakh di, kuch nahi badla.'), parse_mode='HTML')
        return
    if any(rel == 'package.json' for rel, _, _ in touched):
        if not _install_zip_deps(user_folder, message, user_id, safe=True, do_pip=False):
            rollback()
            bot.reply_to(message, '↩️ Update wapas le liya, purani files waise hi hain.')
            return

    script_key = _script_key(user_id, main)
    RESTART_STATE.setdefault(script_key, {'attempts': 0, 'manual_stop': False})['manual_stop'] = True
    if is_bot_running(user_id, main):
        process_info = bot_scripts.get(script_key)
        if process_info:
            kill_process_tree(process_info)
        _forget_script(script_key)
        time.sleep(1.5)
    _reset_restart_state(user_id, main)
    main_path = os.path.join(user_folder, main)
    gh_write_sidecar(user_folder, main, manifest)
    state['ok'] = True
    updated = sum(1 for _, _, _, action in plan if action == 'update')
    added = len(plan) - updated
    bot.reply_to(message, f"✅ Update ho gaya: {updated} file badli, {added} nayi, {kept_count} waise hi chhodi (.env/data/db). "
                          f"Ab <code>{html_escape(main)}</code> restart ho raha hai...", parse_mode='HTML')
    target = run_js_script if file_type == 'js' else run_script
    threading.Thread(target=target, args=(main_path, user_id, user_folder, main, message)).start()


def _install_zip_deps(folder, message, user_id, safe=False, do_pip=True, do_npm=True):
    """Install requirements.txt / package.json found in `folder` (same behaviour as before for manual zips).
    safe=True (GitHub deploys): npm runs with --ignore-scripts so no repo install hook is executed.
    Returns False when something failed (the user was told why)."""
    req_path = os.path.join(folder, 'requirements.txt')
    if do_pip and os.path.isfile(req_path):
        req_file = 'requirements.txt'
        logger.info(f"requirements.txt found, installing: {req_path}")
        pm = _msg_anim(message, 'Installing Requirements', f"Installing Python deps from {req_file}...")
        try:
            command = [sys.executable, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input',
                       *sandbox_pip_target(get_user_folder(user_id)), '-r', req_path]
            command, extra_env = sandbox_wrap(command, get_user_folder(user_id), 'install', work_dir=folder)
            run_env = child_env()
            run_env.update(extra_env)
            result = subprocess.run(command, capture_output=True, text=True, check=True, encoding='utf-8', errors='ignore', cwd=folder,
                                    timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=run_env, start_new_session=True)
            logger.info(f"pip install from requirements.txt OK. Output:\n{result.stdout}")
            _reply_via(pm, message, f"✅ Python deps from `{req_file}` installed.")
        except subprocess.CalledProcessError as e:
            log_tail = _short_code_block((e.stderr or e.stdout or '')[-2500:], 2500)
            error_msg = f"❌ Failed to install Python deps from `{req_file}`.\nLog:\n```\n{log_tail}\n```"
            logger.error(error_msg)
            _reply_via(pm, message, error_msg, parse_mode='Markdown'); return False
        except subprocess.TimeoutExpired:
            logger.error(f"pip install -r timed out for user {user_id}")
            _reply_via(pm, message, f"❌ Installing the Python deps took longer than {INSTALL_TIMEOUT} seconds and was stopped."); return False
        except Exception as e:
            error_msg = f"❌ Unexpected error installing Python deps: {e}"
            logger.error(error_msg, exc_info=True); _reply_via(pm, message, ui_err('Install Failed', 'Python dependencies could not be installed.', ui_user_error(e)), parse_mode='HTML'); return False

    pkg_json = 'package.json'
    if do_npm and os.path.isfile(os.path.join(folder, pkg_json)):
        logger.info(f"package.json found, npm install in: {folder}")
        pm = _msg_anim(message, 'Installing Node Packages', f"Installing Node deps from {pkg_json}...")
        try:
            command = ['npm', 'install', '--ignore-scripts'] if safe else ['npm', 'install']
            command, extra_env = sandbox_wrap(command, get_user_folder(user_id), 'install', work_dir=folder)
            run_env = child_env()
            run_env.update(extra_env)
            result = subprocess.run(command, capture_output=True, text=True, check=True, cwd=folder, encoding='utf-8', errors='ignore',
                                    timeout=INSTALL_TIMEOUT, stdin=subprocess.DEVNULL, env=run_env, start_new_session=True)
            logger.info(f"npm install OK. Output:\n{result.stdout}")
            _reply_via(pm, message, f"✅ Node deps from `{pkg_json}` installed.")
        except FileNotFoundError:
            _reply_via(pm, message, "❌ 'npm' not found. Cannot install Node deps."); return False
        except subprocess.CalledProcessError as e:
            log_tail = _short_code_block((e.stderr or e.stdout or '')[-2500:], 2500)
            error_msg = f"❌ Failed to install Node deps from `{pkg_json}`.\nLog:\n```\n{log_tail}\n```"
            logger.error(error_msg)
            _reply_via(pm, message, error_msg, parse_mode='Markdown'); return False
        except subprocess.TimeoutExpired:
            logger.error(f"npm install timed out for user {user_id}")
            _reply_via(pm, message, f"❌ Installing the Node deps took longer than {INSTALL_TIMEOUT} seconds and was stopped."); return False
        except Exception as e:
            error_msg = f"❌ Unexpected error installing Node deps: {e}"
            logger.error(error_msg, exc_info=True); _reply_via(pm, message, ui_err('Install Failed', 'Node dependencies could not be installed.', ui_user_error(e)), parse_mode='HTML'); return False
    return True


def process_zip_file(zip_path, user_id, user_folder, file_name_zip, message, temp_dir=None):
    """Process ZIP file extraction and setup. Returns True when the archive was set up and its main script started."""
    state = {'ok': False}
    _process_zip_file_impl(zip_path, user_id, user_folder, file_name_zip, message, temp_dir, state)
    return state['ok']


def _process_zip_file_impl(zip_path, user_id, user_folder, file_name_zip, message, temp_dir, state):
    cleanup_temp = False
    if temp_dir is None:
        temp_dir = tempfile.mkdtemp(prefix=f"user_{user_id}_zip_")
        cleanup_temp = True
        
    try:
        # Extract into a sub folder so the uploaded .zip itself is never copied into the user's storage.
        extract_dir = os.path.join(temp_dir, 'extracted')
        os.makedirs(extract_dir, exist_ok=True)
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            # Validate archive paths and expansion limits before extracting.
            archive_items = zip_ref.infolist()
            if len(archive_items) > MAX_ZIP_FILES:
                raise zipfile.BadZipFile(f'Archive contains too many entries (maximum {MAX_ZIP_FILES}).')
            total_uncompressed = sum(max(0, item.file_size) for item in archive_items)
            if total_uncompressed > MAX_UNZIPPED_MB * 1024 * 1024:
                raise zipfile.BadZipFile(f'Archive expands beyond the {MAX_UNZIPPED_MB} MB extraction limit.')
            root_dir = os.path.realpath(extract_dir)
            for member in archive_items:
                _norm_name = member.filename.replace(chr(92), '/')
                if _norm_name.startswith('/') or '..' in _norm_name.split('/') or (len(_norm_name) > 1 and _norm_name[1] == ':'):
                    raise zipfile.BadZipFile(f"Zip has unsafe path: {member.filename}")
                member_path = os.path.realpath(os.path.join(root_dir, member.filename))
                if os.path.commonpath((root_dir, member_path)) != root_dir:
                    raise zipfile.BadZipFile(f"Zip has unsafe path: {member.filename}")
                # Reject symlink entries; they can redirect extracted paths.
                unix_mode = (member.external_attr >> 16) & 0o170000
                if unix_mode == 0o120000:
                    raise zipfile.BadZipFile(f"Zip contains a symbolic link: {member.filename}")
            zip_ref.extractall(extract_dir)
            logger.info(f"Extracted zip to {extract_dir}")

        # A zip packed by the GitHub deploy carries a signed manifest (a manual zip cannot fake it; it is removed here).
        manifest = gh_take_manifest(extract_dir)
        if manifest and manifest.get('update'):
            _gh_apply_update(extract_dir, manifest, user_id, user_folder, message, state)
            return

        extracted_items = os.listdir(extract_dir)
        py_files = [f for f in extracted_items if f.endswith('.py')]
        js_files = [f for f in extracted_items if f.endswith('.js')]
        req_file = 'requirements.txt' if 'requirements.txt' in extracted_items else None
        pkg_json = 'package.json' if 'package.json' in extracted_items else None

        if not _install_zip_deps(extract_dir, message, user_id, safe=bool(manifest)):
            return

        main_script_name = None; file_type = None
        preferred_py = ['main.py', 'bot.py', 'app.py']; preferred_js = ['index.js', 'main.js', 'bot.js', 'app.js']
        for p in preferred_py:
            if p in py_files: main_script_name = p; file_type = 'py'; break
        if not main_script_name:
             for p in preferred_js:
                 if p in js_files: main_script_name = p; file_type = 'js'; break
        if not main_script_name:
            if py_files: main_script_name = py_files[0]; file_type = 'py'
            elif js_files: main_script_name = js_files[0]; file_type = 'js'
        if manifest:
            wanted = str(manifest.get('main', ''))
            if wanted in extracted_items and wanted.endswith(('.py', '.js')):
                main_script_name = wanted; file_type = 'js' if wanted.endswith('.js') else 'py'
        if not main_script_name:
            bot.reply_to(message, "❌ No `.py` or `.js` script found in archive!"); return

        logger.info(f"Moving extracted files from {extract_dir} to {user_folder}")
        moved_count = 0
        for item_name in os.listdir(extract_dir):
            dest_path = os.path.join(user_folder, item_name)
            if os.path.exists(dest_path):
                raise FileExistsError(f"Archive item already exists in your storage: {item_name}")
        for item_name in os.listdir(extract_dir):
            src_path = os.path.join(extract_dir, item_name)
            dest_path = os.path.join(user_folder, item_name)
            shutil.move(src_path, dest_path); moved_count += 1
        logger.info(f"Moved {moved_count} items to {user_folder}")

        save_user_file(user_id, main_script_name, file_type)
        _reset_restart_state(user_id, main_script_name)
        logger.info(f"Saved main script '{main_script_name}' ({file_type}) for {user_id} from zip.")
        main_script_path = os.path.join(user_folder, main_script_name)
        state['ok'] = True
        if manifest:
            gh_write_sidecar(user_folder, main_script_name, manifest)
            bot.reply_to(message, f"✅ GitHub repo se files lag gayi. Starting main script: `{main_script_name}`...\n🐙 Source: {manifest.get('repo', '')}")
        else:
            bot.reply_to(message, f"✅ Files extracted. Starting main script: `{main_script_name}`...", parse_mode='Markdown')

        # Use user_id as script_owner_id for script key context
        if file_type == 'py':
             threading.Thread(target=run_script, args=(main_script_path, user_id, user_folder, main_script_name, message)).start()
        elif file_type == 'js':
             threading.Thread(target=run_js_script, args=(main_script_path, user_id, user_folder, main_script_name, message)).start()
             
    except Exception as e:
        logger.error(f"Error processing zip file: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Zip Error', 'Could not process this zip file.', ui_user_error(e)), parse_mode='HTML')
    finally:
        if cleanup_temp and temp_dir and os.path.exists(temp_dir):
            try: shutil.rmtree(temp_dir); logger.info(f"Cleaned temp dir: {temp_dir}")
            except Exception as e: logger.error(f"Failed to clean temp dir {temp_dir}: {e}", exc_info=True)

# --- Per-bot environment variables (.env style) -------------------------------------
# Each bot keeps its variables in "<bot file name>.env" next to the script, inside the user's own folder
# (for example bot.py.env). The file is a normal part of that folder, so My Bots export / import and full
# backups carry it along. It is read every time the bot is launched (first start, Restart button, watchdog).
ENV_KEY_RE = re.compile(r'^[A-Za-z_][A-Za-z0-9_]{0,39}$')
ENV_MAX_VARS = 40
ENV_MAX_VALUE_CHARS = 2000
ENV_MAX_FILE_BYTES = 128 * 1024
# Names that change how the interpreter / loader itself behaves; they could change how the interpreter or loader runs the script.
ENV_RESERVED_KEYS = frozenset({
    'PATH', 'HOME', 'USER', 'SHELL', 'IFS', 'ENV', 'BASH_ENV', 'PWD', 'TMPDIR',
    'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONINSPECT', 'PYTHONSAFEPATH', 'PYTHONUSERBASE',
    'PYTHONBREAKPOINT', 'PYTHONEXECUTABLE', 'NODE_OPTIONS', 'NODE_PATH', 'NODE_EXTRA_CA_CERTS',
    'NPM_CONFIG_PREFIX', 'SSL_CERT_FILE', 'REQUESTS_CA_BUNDLE',
})
ENV_RESERVED_PREFIXES = ('LD_', 'DYLD_')
ENV_LOCK = threading.RLock()
_ENV_SENSITIVE_RE = re.compile(r'TOKEN|SECRET|PASS|KEY|HASH|AUTH|CRED|PRIVATE|SESSION|DSN|URL|URI|COOKIE', re.IGNORECASE)


def _env_key_reserved(key):
    upper = key.upper()
    return upper in ENV_RESERVED_KEYS or upper.startswith(ENV_RESERVED_PREFIXES)


def _env_safe_label(text, limit=30):
    """A piece of user input that is safe to show back (printable ASCII only, shortened, no values)."""
    return re.sub(r'[^\x21-\x7e]', '?', str(text))[:limit]


def bot_env_path(user_folder, file_name):
    """Where the variables of one bot live; None when the name is not a plain file name."""
    if not file_name or file_name != os.path.basename(file_name) or file_name in ('.', '..') or '\\' in file_name:
        return None
    return os.path.join(user_folder, file_name + '.env')


def _parse_env_value(raw):
    """Value part of a KEY=VALUE line -> (value, error). Understands "double", 'single' and unquoted values."""
    raw = raw.strip()
    if not raw:
        return '', None
    quote = raw[0]
    if quote in ('"', "'"):
        out = []
        i = 1
        escapes = {'n': '\n', 'r': '\r', 't': '\t', '"': '"', '\\': '\\'}
        while i < len(raw):
            ch = raw[i]
            if quote == '"' and ch == '\\' and i + 1 < len(raw):
                nxt = raw[i + 1]
                out.append(escapes.get(nxt, '\\' + nxt))
                i += 2
                continue
            if ch == quote:
                rest = raw[i + 1:].strip()
                if rest and not rest.startswith('#'):
                    return None, 'there is text after the closing quote'
                return ''.join(out), None
            out.append(ch)
            i += 1
        return None, 'the quote is not closed'
    match = re.search(r'\s#', raw)       # unquoted values may end with a " # comment"
    if match:
        raw = raw[:match.start()]
    return raw.strip(), None


def parse_env_text(text):
    """Parse .env style text. Returns (pairs, problems): pairs is {KEY: value}; problems is a list of
    (line number, key label or None, reason). Values are never put into problems."""
    pairs = {}
    problems = []
    text = (text or '').lstrip('\ufeff')
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith('#'):
            continue
        if re.match(r'export\s', stripped):
            stripped = stripped[6:].lstrip()
        if '=' not in stripped:
            problems.append((number, None, 'needs the form KEY=VALUE'))
            continue
        key, _, raw_value = stripped.partition('=')
        key = key.strip()
        label = _env_safe_label(key)
        if not ENV_KEY_RE.match(key):
            problems.append((number, label, 'name can only use letters, digits and _ (not starting with a digit, max 40 characters)'))
            continue
        if _env_key_reserved(key):
            problems.append((number, key, 'this name is reserved by the host and cannot be changed'))
            continue
        value, error = _parse_env_value(raw_value)
        if error:
            problems.append((number, key, error))
            continue
        if len(value) > ENV_MAX_VALUE_CHARS:
            problems.append((number, key, f'value is longer than {ENV_MAX_VALUE_CHARS} characters'))
            continue
        if any((ord(ch) < 32 and ch not in '\t\n\r') or ch == '\x7f' for ch in value):
            problems.append((number, key, 'value has unsupported control characters'))
            continue
        pairs[key] = value
    return pairs, problems


def _format_env_value(value):
    if re.fullmatch(r'[A-Za-z0-9_@%+=:,./-]*', value):
        return value
    escaped = value.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\r', '\\r')
    return f'"{escaped}"'


def serialize_env(env):
    return ''.join(f'{key}={_format_env_value(value)}\n' for key, value in sorted(env.items()))


def load_bot_env(user_folder, file_name):
    """Saved variables of one bot as a plain dict. Never raises: a missing or broken file simply gives {}.
    Anything that is not a valid, allowed name is dropped here as well, so a hand-made file or a restored
    backup cannot smuggle in reserved names."""
    try:
        path = bot_env_path(user_folder, file_name)
        if not path or os.path.islink(path) or not os.path.isfile(path):
            return {}
        if os.path.getsize(path) > ENV_MAX_FILE_BYTES:
            logger.warning("Environment file for %s is too large and was ignored.", file_name)
            return {}
        with open(path, 'r', encoding='utf-8', errors='replace') as handle:
            pairs, problems = parse_env_text(handle.read())
        if problems:
            logger.warning("Environment file for %s: %d line(s) ignored.", file_name, len(problems))
        return dict(list(pairs.items())[:ENV_MAX_VARS])
    except Exception as exc:
        logger.warning("Could not read the environment of %s: %s", file_name, redact_secrets(exc))
        return {}


def _write_bot_env(path, env):
    """Atomic write (owner-only permissions). An empty set removes the file."""
    if not env:
        try:
            os.remove(path)
        except FileNotFoundError:
            pass
        return
    data = serialize_env(env)
    if len(data.encode('utf-8')) > ENV_MAX_FILE_BYTES:
        raise ValueError('The environment is too large.')
    tmp_path = f'{path}.{os.urandom(4).hex()}.tmp'
    try:
        fd = os.open(tmp_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, 'w', encoding='utf-8', newline='\n') as handle:
            handle.write(data)
        os.replace(tmp_path, path)
    finally:
        if os.path.exists(tmp_path):
            try:
                os.remove(tmp_path)
            except OSError:
                pass


def update_bot_env(user_folder, file_name, new_pairs):
    """Add or update variables. Returns (added keys, updated keys, unchanged keys). Raises ValueError with a
    plain message when the result would be too big or the name is unusable."""
    path = bot_env_path(user_folder, file_name)
    if not path:
        raise ValueError('That bot name cannot have variables.')
    with ENV_LOCK:
        current = load_bot_env(user_folder, file_name)
        merged = dict(current)
        added, updated, unchanged = [], [], []
        for key, value in new_pairs.items():
            if key not in current:
                added.append(key)
            elif current[key] != value:
                updated.append(key)
            else:
                unchanged.append(key)
            merged[key] = value
        if len(merged) > ENV_MAX_VARS:
            raise ValueError(f'A bot can have at most {ENV_MAX_VARS} variables '
                             f'(you have {len(current)}, this would make {len(merged)}). Delete some first.')
        _write_bot_env(path, merged)
    return added, updated, unchanged


def delete_bot_env_key(user_folder, file_name, key):
    path = bot_env_path(user_folder, file_name)
    if not path:
        return False
    with ENV_LOCK:
        current = load_bot_env(user_folder, file_name)
        if key not in current:
            return False
        del current[key]
        _write_bot_env(path, current)
    return True


def clear_bot_env(user_folder, file_name):
    """Remove every saved variable of one bot. Returns how many were set."""
    path = bot_env_path(user_folder, file_name)
    if not path:
        return 0
    with ENV_LOCK:
        count = len(load_bot_env(user_folder, file_name))
        _write_bot_env(path, {})
    return count


def _env_key_tag(key):
    return hashlib.sha1(key.encode('utf-8')).hexdigest()[:6]


def _env_display_value(key, value, reveal):
    shown = value.replace('\r', ' ').replace('\n', ' ')
    if not reveal and _ENV_SENSITIVE_RE.search(key):
        return (shown[:3] + '••••') if len(shown) > 8 else '••••'
    return shown if len(shown) <= 24 else shown[:24] + '…'


def _prepare_log_file(log_file_path):
    """Open a script log for appending; start a fresh file if the old one is already too big."""
    try:
        if os.path.exists(log_file_path) and os.path.getsize(log_file_path) > MAX_SCRIPT_LOG_MB * 1024 * 1024:
            os.replace(log_file_path, log_file_path + '.old')
    except OSError as exc:
        logger.warning(f"Could not rotate log {log_file_path}: {exc}")
    return open(log_file_path, 'a', encoding='utf-8', errors='ignore')


def _popen_kwargs(user_folder=None, file_name=None):
    """Extra Popen arguments: own process group on POSIX (so children can be stopped too) and a clean environment.
    With user_folder + file_name, the variables saved for that one bot (Environment button) are merged in.
    Only the dict handed to this one child is changed; the hosting bot's own os.environ is never touched."""
    env = child_env()
    folder_name = os.path.basename(os.path.normpath(user_folder)) if user_folder else ''
    if folder_name.isdigit():
        env['SANDBOX_NAME'] = get_sandbox_name(folder_name)      # the script can read its own sandbox name
    if user_folder and file_name:
        env.update(load_bot_env(user_folder, file_name))
    kwargs = {'env': env}
    if os.name == 'posix':
        kwargs['start_new_session'] = True
    return kwargs


def _sandboxed(command, user_folder, file_name):
    """(command to start, extra Popen arguments) for one hosted script, wrapped in the sandbox (SANDBOX_MODE)."""
    kwargs = _popen_kwargs(user_folder, file_name)
    wrapped, extra = sandbox_wrap(command, user_folder)
    own_env = load_bot_env(user_folder, file_name) if file_name else {}
    for key, value in extra.items():
        if key == 'PYTHONPATH' and own_env.get('PYTHONPATH'):
            value = value.split(os.pathsep)[0] + os.pathsep + own_env['PYTHONPATH']
        elif key in own_env:
            continue                         # the user's own variable of the same name wins (not for the sandbox folders)
        kwargs['env'][key] = value
    return wrapped, kwargs


def _kill_check_process(check_proc):
    """Stop a pre-check process (and anything it started) and reap it."""
    if check_proc is None:
        return
    try:
        if check_proc.poll() is None:
            if os.name == 'posix':
                try:
                    os.killpg(check_proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    check_proc.kill()
            else:
                check_proc.kill()
        check_proc.communicate(timeout=5)
    except Exception as exc:
        logger.debug(f"Pre-check cleanup problem: {exc}")


def _register_script(script_key, info):
    """Store a running script; if an older one with the same key is still alive, stop it first (no leaked processes)."""
    with STATE_LOCK:
        old = bot_scripts.get(script_key)
        bot_scripts[script_key] = info
    if info.get('script_owner_id') is not None and info.get('file_name'):
        autostart_mark(script_key, info['script_owner_id'], info['file_name'], info.get('type', 'py'))
    if old and old.get('process') is not None and old['process'] is not info['process']:
        try:
            if old['process'].poll() is None:
                logger.warning(f"Replacing a still-running process for {script_key}; stopping the old one.")
                kill_process_tree(old)
            else:
                release_process_resources(old)
        except Exception as exc:
            logger.error(f"Could not clean up the old process for {script_key}: {exc}")


def _forget_script(script_key):
    with STATE_LOCK:
        return bot_scripts.pop(script_key, None)


# --- "Was running" memory: scripts that start again by themselves after a restart or redeploy -------------------------
# A script is marked when it really starts and unmarked at every deliberate stop (Stop button, admin stop, delete, ban,
# suspension, restore, retry limit reached). A normal shutdown (cleanup) does NOT unmark anything, so after the next
# boot exactly the scripts that were running at that moment come back.
AUTO_RESUME_ON_BOOT = os.environ.get('AUTO_RESUME_ON_BOOT', '1').strip().lower() not in ('0', 'off', 'false', 'no', 'disable', 'disabled')
AUTO_RESUME_GAP_SECONDS = max(0, _env_int('AUTO_RESUME_GAP_SECONDS', 4))     # pause between two starts, so a boot is not one big spike


def autostart_mark(script_key, owner_id, file_name, file_type):
    """Remember that this script is meant to be running."""
    try:
        with DB_LOCK:
            conn = db_connect()
            try:
                conn.execute('INSERT OR REPLACE INTO autostart (script_key, owner_id, file_name, file_type, set_date) VALUES (?, ?, ?, ?, ?)',
                             (script_key, int(owner_id), file_name, file_type, datetime.now().isoformat()))
                conn.commit()
            finally:
                conn.close()
    except Exception as exc:
        logger.warning("Could not save the was-running state of %s: %s", script_key, exc)


def autostart_clear(script_key=None, owner_id=None):
    """Forget the was-running state of one script, or of every script of one user."""
    try:
        with DB_LOCK:
            conn = db_connect()
            try:
                if script_key is not None:
                    conn.execute('DELETE FROM autostart WHERE script_key = ?', (script_key,))
                elif owner_id is not None:
                    conn.execute('DELETE FROM autostart WHERE owner_id = ?', (int(owner_id),))
                else:
                    conn.execute('DELETE FROM autostart')
                conn.commit()
            finally:
                conn.close()
    except Exception as exc:
        logger.warning("Could not clear the was-running state (%s): %s", script_key or owner_id or 'all', exc)


def autostart_rows():
    with DB_LOCK:
        conn = db_connect()
        try:
            return [tuple(r) for r in conn.execute('SELECT script_key, owner_id, file_name, file_type FROM autostart ORDER BY set_date')]
        finally:
            conn.close()


_RUN_PM = threading.local()     # the animated "Starting ..." status of the script start running in this thread


def _run_reply(message, text):
    """Send a finished (HTML) status card as a reply. While a start is animated the card replaces that status."""
    pm = getattr(_RUN_PM, 'pm', None)
    if isinstance(pm, ProgressMessage) and pm.enabled and not pm._done and pm.message_id is not None:
        pm.finish(text)
        return
    bot.reply_to(message, text, parse_mode='HTML')


def _run_auto(runner, *args):
    """Run a start for an automatic restart (watchdog, schedule): nobody waits for it, so no animated status."""
    _RUN_PM.auto = True
    try:
        return runner(*args)
    finally:
        _RUN_PM.auto = False


def _run_start_status(kind, file_name, message, attempt):
    """Animated 'Starting ...' status for the first attempt of a script start (None when it is not wanted)."""
    if attempt != 1 or getattr(_RUN_PM, 'auto', False):
        return None
    return _msg_anim(message, f'Starting {kind} Script', UIRaw(f"📄 <code>{html_escape(file_name)}</code>\nChecking the script and starting it..."), only_if_free=True)


def _run_with_status(kind, impl, script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt):
    pm = _run_start_status(kind, file_name, message_obj_for_reply, attempt)
    previous = getattr(_RUN_PM, 'pm', None)
    _RUN_PM.pm = pm
    try:
        return impl(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt)
    finally:
        _RUN_PM.pm = previous
        if pm is not None and not pm._done:
            pm.fail()


def _run_status_end(text):
    """End the animated start status with its own text (used before a package install takes over)."""
    pm = getattr(_RUN_PM, 'pm', None)
    if isinstance(pm, ProgressMessage) and not pm._done:
        pm.finish(text)


def _start_card(kind, file_name, pid, owner_id):
    """The 'script started' card (kind is 'Python' or 'JS')."""
    return ui_ok(f'{kind} Script Started',
                 f"📡 Status: {ui_tag('active')}",
                 ui_row('📄', 'File', file_name, code=True),
                 ui_row('🆔', 'PID', pid, code=True),
                 ui_row('⏱️', 'Uptime', 'just started'),
                 ui_row('👤', 'Owner', owner_id, code=True),
                 ui_row('🧱', 'Sandbox', get_sandbox_name(owner_id)),
                 ui_row('🛡️', 'Isolation', sandbox_level_text()),
                 foot='🚀 Live now. Open My Files for logs, stop and restart.')


def _precheck_card(kind, file_name, stderr, user_folder, hint):
    return ui_err(f'{kind} Pre-check Failed',
                  ui_row('📄', 'File', file_name, code=True),
                  ui_pre(_scrub_host_paths(stderr, user_folder), 500),
                  foot=hint)


def _short_code_block(text, limit=500):
    """Shorten text for use inside a Markdown code block (a stray triple backtick would break the message)."""
    return (text or '')[:limit].replace('```', "'" * 3)


def handle_js_file(file_path, script_owner_id, user_folder, file_name, message):
    try:
        save_user_file(script_owner_id, file_name, 'js')
        _reset_restart_state(script_owner_id, file_name)
        threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, message)).start()
    except Exception as e:
        logger.error(f"❌ Error processing JS file {file_name} for {script_owner_id}: {e}", exc_info=True)
        _run_reply(message, ui_err('Could Not Process File', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))

def handle_py_file(file_path, script_owner_id, user_folder, file_name, message):
    try:
        save_user_file(script_owner_id, file_name, 'py')
        _reset_restart_state(script_owner_id, file_name)
        threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, file_name, message)).start()
    except Exception as e:
        logger.error(f"❌ Error processing Python file {file_name} for {script_owner_id}: {e}", exc_info=True)
        _run_reply(message, ui_err('Could Not Process File', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))

# --- Automatic Package Installation & Script Running ---
def run_script(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt=1):
    return _run_with_status('Python', _run_script_impl, script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt)


def run_js_script(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt=1):
    return _run_with_status('JS', _run_js_script_impl, script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt)


def _run_script_impl(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt=1):
    """Run Python script. script_owner_id is used for the script_key. message_obj_for_reply is for sending feedback."""
    max_attempts = 2 
    if attempt > max_attempts:
        _run_reply(message_obj_for_reply, ui_err('Could Not Start Script', ui_row('📄', 'File', file_name, code=True), ui_row('🔁', 'Attempts', max_attempts), foot='Check the logs for details.'))
        return

    script_key = f"{script_owner_id}_{file_name}"
    logger.info(f"Attempt {attempt} to run Python script: {script_path} (Key: {script_key}) for user {script_owner_id}")

    try:
        if not os.path.exists(script_path):
             _run_reply(message_obj_for_reply, ui_err('Script Not Found', ui_row('📄', 'File', file_name, code=True), ui_row('🧱', 'Sandbox', get_sandbox_name(script_owner_id))))
             logger.error(f"Script not found: {script_path} for user {script_owner_id}")
             if script_owner_id in user_files:
                 user_files[script_owner_id] = [f for f in user_files.get(script_owner_id, []) if f[0] != file_name]
             remove_user_file_db(script_owner_id, file_name)
             return

        if attempt == 1:
            # Every start path (watchdog, Run All, imports) passes the launch gate (suspension, sandbox) before
            # the test run below.
            allowed, gate_note = launch_gate(script_owner_id, file_name, 'py', 0, queue=False, admin_override=False)
            if not allowed:
                logger.warning("Security gate stopped %s for user %s", file_name, script_owner_id)
                _say_via(getattr(_RUN_PM, 'pm', None), message_obj_for_reply.chat.id, gate_note)
                return

        if attempt == 1:
            check_command = [sys.executable, script_path]
            logger.info(f"Running Python pre-check: {' '.join(check_command)}")
            check_proc = None
            try:
                check_command, popen_kw = _sandboxed(check_command, user_folder, file_name)
                check_proc = subprocess.Popen(check_command, cwd=user_folder, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, text=True, encoding='utf-8', errors='ignore', **popen_kw)
                stdout, stderr = check_proc.communicate(timeout=5)
                return_code = check_proc.returncode
                logger.info(f"Python Pre-check early. RC: {return_code}. Stderr: {stderr[:200]}...")
                if return_code != 0 and stderr:
                    match_py = re.search(r"ModuleNotFoundError: No module named '(.+?)'", stderr)
                    if match_py:
                        module_name = match_py.group(1).strip().strip("'\"")
                        logger.info(f"Detected missing Python module: {module_name}")
                        _run_status_end(ui_info('Missing Package', ui_row('📦', 'Package', module_name, code=True), foot='Installing it now...'))
                        success, _ = attempt_install_pip(module_name, message_obj_for_reply, user_folder=user_folder)
                        if success:
                            logger.info(f"Install OK for {module_name}. Retrying run_script...")
                            _run_reply(message_obj_for_reply, ui_msg('🔄', 'Install Done', ui_row('📄', 'File', file_name, code=True), foot='Retrying now...'))
                            time.sleep(2)
                            threading.Thread(target=run_script, args=(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt + 1)).start()
                            return
                        else:
                            _run_reply(message_obj_for_reply, ui_err('Install Failed', ui_row('📄', 'File', file_name, code=True), foot='The script cannot run without its packages.'))
                            return
                    else:
                         _run_reply(message_obj_for_reply, _precheck_card('Python', file_name, stderr, user_folder, 'Fix the script and upload it again.'))
                         return
            except subprocess.TimeoutExpired:
                logger.info("Python Pre-check timed out (>5s), imports likely OK. Killing check process.")
                _kill_check_process(check_proc)
                logger.info("Python Check process killed. Proceeding to long run.")
            except FileNotFoundError:
                 logger.error(f"Python interpreter not found: {sys.executable}")
                 _run_reply(message_obj_for_reply, ui_err('Python Not Available', 'The Python runtime is missing on the host.', foot='Please contact the admin.'))
                 return
            except Exception as e:
                 logger.error(f"Error in Python pre-check for {script_key}: {e}", exc_info=True)
                 _run_reply(message_obj_for_reply, ui_err('Pre-check Error', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))
                 return
            finally:
                 if check_proc and check_proc.poll() is None:
                     logger.warning(f"Python Check process {check_proc.pid} still running. Killing.")
                     _kill_check_process(check_proc)

        logger.info(f"Starting long-running Python process for {script_key}")
        log_file_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        log_file = None; process = None
        try: log_file = _prepare_log_file(log_file_path)
        except Exception as e:
             logger.error(f"Failed to open log file '{log_file_path}' for {script_key}: {e}", exc_info=True)
             _run_reply(message_obj_for_reply, ui_err('Log File Problem', ui_row('📄', 'File', file_name, code=True), ui_row('🧱', 'Sandbox', get_sandbox_name(script_owner_id)), foot='Could not open the log file. Please try again.'))
             return
        try:
            run_command, popen_kw = _sandboxed([sys.executable, '-u', script_path], user_folder, file_name)
            process = subprocess.Popen(
                run_command, cwd=user_folder, stdout=log_file, stderr=log_file,
                stdin=subprocess.PIPE, encoding='utf-8', errors='ignore', **popen_kw
            )
            logger.info(f"Started Python process {process.pid} for {script_key}")
            _register_script(script_key, {
                'process': process, 'log_file': log_file, 'file_name': file_name,
                'chat_id': message_obj_for_reply.chat.id, # Chat ID for potential future direct replies from script, defaults to admin/triggering user
                'script_owner_id': script_owner_id, # Actual owner of the script
                'start_time': datetime.now(), 'user_folder': user_folder, 'type': 'py', 'script_key': script_key, 'reply_target': message_obj_for_reply
            })
            _run_reply(message_obj_for_reply, _start_card('Python', file_name, process.pid, script_owner_id))
        except FileNotFoundError:
             logger.error(f"Python interpreter {sys.executable} not found for long run {script_key}")
             _run_reply(message_obj_for_reply, ui_err('Python Not Available', 'The Python runtime is missing on the host.', foot='Please contact the admin.'))
             if log_file and not log_file.closed: log_file.close()
             _forget_script(script_key)
        except Exception as e:
            if log_file and not log_file.closed: log_file.close()
            logger.error(f"Error starting Python script '{file_name}': {e}", exc_info=True)
            _run_reply(message_obj_for_reply, ui_err('Could Not Start Script', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))
            if process and process.poll() is None:
                 logger.warning(f"Killing potentially started Python process {process.pid} for {script_key}")
                 kill_process_tree({'process': process, 'log_file': log_file, 'script_key': script_key})
            _forget_script(script_key)
    except Exception as e:
        logger.error(f"Unexpected error running Python script '{file_name}': {e}", exc_info=True)
        _run_reply(message_obj_for_reply, ui_err('Could Not Start Script', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))
        stale = _forget_script(script_key)
        if stale:
             logger.warning(f"Cleaning up {script_key} due to error in run_script.")
             kill_process_tree(stale)

def _run_js_script_impl(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt=1):
    """Run JS script. script_owner_id is used for the script_key. message_obj_for_reply is for sending feedback."""
    max_attempts = 2
    if attempt > max_attempts:
        _run_reply(message_obj_for_reply, ui_err('Could Not Start Script', ui_row('📄', 'File', file_name, code=True), ui_row('🔁', 'Attempts', max_attempts), foot='Check the logs for details.'))
        return

    script_key = f"{script_owner_id}_{file_name}"
    logger.info(f"Attempt {attempt} to run JS script: {script_path} (Key: {script_key}) for user {script_owner_id}")

    try:
        if not os.path.exists(script_path):
             _run_reply(message_obj_for_reply, ui_err('Script Not Found', ui_row('📄', 'File', file_name, code=True), ui_row('🧱', 'Sandbox', get_sandbox_name(script_owner_id))))
             logger.error(f"JS Script not found: {script_path} for user {script_owner_id}")
             if script_owner_id in user_files:
                 user_files[script_owner_id] = [f for f in user_files.get(script_owner_id, []) if f[0] != file_name]
             remove_user_file_db(script_owner_id, file_name)
             return

        if attempt == 1:
            # Every start path (watchdog, Run All, imports) passes the launch gate (suspension, sandbox) before
            # the test run below.
            allowed, gate_note = launch_gate(script_owner_id, file_name, 'js', 0, queue=False, admin_override=False)
            if not allowed:
                logger.warning("Security gate stopped %s for user %s", file_name, script_owner_id)
                _say_via(getattr(_RUN_PM, 'pm', None), message_obj_for_reply.chat.id, gate_note)
                return

        if attempt == 1:
            check_command = ['node', script_path]
            logger.info(f"Running JS pre-check: {' '.join(check_command)}")
            check_proc = None
            try:
                check_command, popen_kw = _sandboxed(check_command, user_folder, file_name)
                check_proc = subprocess.Popen(check_command, cwd=user_folder, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL, text=True, encoding='utf-8', errors='ignore', **popen_kw)
                stdout, stderr = check_proc.communicate(timeout=5)
                return_code = check_proc.returncode
                logger.info(f"JS Pre-check early. RC: {return_code}. Stderr: {stderr[:200]}...")
                if return_code != 0 and stderr:
                    match_js = re.search(r"Cannot find module '(.+?)'", stderr)
                    if match_js:
                        module_name = match_js.group(1).strip().strip("'\"")
                        if not module_name.startswith('.') and not module_name.startswith('/'):
                             logger.info(f"Detected missing Node module: {module_name}")
                             _run_status_end(ui_info('Missing Package', ui_row('📦', 'Package', module_name, code=True), foot='Installing it now...'))
                             success, _ = attempt_install_npm(module_name, user_folder, message_obj_for_reply)
                             if success:
                                 logger.info(f"NPM Install OK for {module_name}. Retrying run_js_script...")
                                 _run_reply(message_obj_for_reply, ui_msg('🔄', 'Install Done', ui_row('📄', 'File', file_name, code=True), foot='Retrying now...'))
                                 time.sleep(2)
                                 threading.Thread(target=run_js_script, args=(script_path, script_owner_id, user_folder, file_name, message_obj_for_reply, attempt + 1)).start()
                                 return
                             else:
                                 _run_reply(message_obj_for_reply, ui_err('Install Failed', ui_row('📄', 'File', file_name, code=True), foot='The script cannot run without its packages.'))
                                 return
                        else: logger.info(f"Skipping npm install for relative/core: {module_name}")
                    _run_reply(message_obj_for_reply, _precheck_card('JS', file_name, stderr, user_folder, 'Fix the script or install the package manually.'))
                    return
            except subprocess.TimeoutExpired:
                logger.info("JS Pre-check timed out (>5s), imports likely OK. Killing check process.")
                _kill_check_process(check_proc)
                logger.info("JS Check process killed. Proceeding to long run.")
            except FileNotFoundError:
                 logger.error("Error: 'node' not found. Ensure Node.js is installed for JS files.")
                 _run_reply(message_obj_for_reply, ui_err('Node.js Not Available', 'Node.js is missing on the host.', foot='Please contact the admin.'))
                 return
            except Exception as e:
                 logger.error(f"Error in JS pre-check for {script_key}: {e}", exc_info=True)
                 _run_reply(message_obj_for_reply, ui_err('Pre-check Error', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))
                 return
            finally:
                 if check_proc and check_proc.poll() is None:
                     logger.warning(f"JS Check process {check_proc.pid} still running. Killing.")
                     _kill_check_process(check_proc)

        logger.info(f"Starting long-running JS process for {script_key}")
        log_file_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        log_file = None; process = None
        try: log_file = _prepare_log_file(log_file_path)
        except Exception as e:
            logger.error(f"Failed to open log file '{log_file_path}' for JS script {script_key}: {e}", exc_info=True)
            _run_reply(message_obj_for_reply, ui_err('Log File Problem', ui_row('📄', 'File', file_name, code=True), ui_row('🧱', 'Sandbox', get_sandbox_name(script_owner_id)), foot='Could not open the log file. Please try again.'))
            return
        try:
            run_command, popen_kw = _sandboxed(['node', script_path], user_folder, file_name)
            process = subprocess.Popen(
                run_command, cwd=user_folder, stdout=log_file, stderr=log_file,
                stdin=subprocess.PIPE, encoding='utf-8', errors='ignore', **popen_kw
            )
            logger.info(f"Started JS process {process.pid} for {script_key}")
            _register_script(script_key, {
                'process': process, 'log_file': log_file, 'file_name': file_name,
                'chat_id': message_obj_for_reply.chat.id, # Chat ID for potential future direct replies
                'script_owner_id': script_owner_id, # Actual owner of the script
                'start_time': datetime.now(), 'user_folder': user_folder, 'type': 'js', 'script_key': script_key, 'reply_target': message_obj_for_reply
            })
            _run_reply(message_obj_for_reply, _start_card('JS', file_name, process.pid, script_owner_id))
        except FileNotFoundError:
             logger.error("Error: 'node' not found for long run. Ensure Node.js is installed.")
             if log_file and not log_file.closed: log_file.close()
             _run_reply(message_obj_for_reply, ui_err('Node.js Not Available', 'Node.js is missing on the host.', foot='Please contact the admin.'))
             _forget_script(script_key)
        except Exception as e:
            if log_file and not log_file.closed: log_file.close()
            logger.error(f"Error starting JS script '{file_name}': {e}", exc_info=True)
            _run_reply(message_obj_for_reply, ui_err('Could Not Start Script', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))
            if process and process.poll() is None:
                 logger.warning(f"Killing potentially started JS process {process.pid} for {script_key}")
                 kill_process_tree({'process': process, 'log_file': log_file, 'script_key': script_key})
            _forget_script(script_key)
    except Exception as e:
        logger.error(f"Unexpected error running JS script '{file_name}': {e}", exc_info=True)
        _run_reply(message_obj_for_reply, ui_err('Could Not Start Script', ui_row('📄', 'File', file_name, code=True), foot='Something went wrong. Please try again.'))
        stale = _forget_script(script_key)
        if stale:
             logger.warning(f"Cleaning up {script_key} due to error in run_js_script.")
             kill_process_tree(stale)

# --- Logic Functions (called by commands and text handlers) ---
def _user_running(user_id):
    """[(file_name, key, uptime_seconds or None)] of the scripts this person has running right now."""
    out = []
    for key, info in list(bot_scripts.items()):
        try:
            if int(info.get('script_owner_id', -1)) != user_id:
                continue
            proc = info.get('process')
            if proc and proc.poll() is None:
                started = info.get('start_time')
                up = (datetime.now() - started).total_seconds() if isinstance(started, datetime) else None
                out.append((info.get('file_name', 'Unknown'), key, up))
        except Exception:
            continue
    return out


def _main_menu_text(user_name, user_id, user_status, days_left, current_files, limit_str, back=False):
    """The main-menu card (welcome and 'back to main')."""
    try:
        limit_num = int(str(limit_str).replace(',', '')) if str(limit_str).replace(',', '').isdigit() else 0
    except Exception:
        limit_num = 0
    try:
        live = len(_user_running(user_id))
    except Exception:
        live = 0
    hour = datetime.now().hour
    hello = 'Good morning' if 5 <= hour < 12 else ('Good afternoon' if 12 <= hour < 17 else ('Good evening' if 17 <= hour < 22 else 'Hello'))
    plan_tag = ui_plan(user_id)[0]
    return ui_msg('💎', 'DEMON HOSTING',
                  f"👋 {'Welcome back' if back else hello}, <b>{ui_esc(user_name)}</b>",
                  "<i>Your premium Python and JavaScript hosting, live 24/7.</i>\n",
                  ui_row('🆔', 'User ID', user_id, code=True),
                  f"👑 Plan: {plan_tag}",
                  ui_row('⏳', 'Days left', f"{days_left} days") if days_left is not None else None,
                  ui_section('📊', 'Your hosting'),
                  ui_meter('📁', 'File slots', current_files, limit_num, f"{current_files} / {limit_str}"),
                  f"{'🟢' if live else '⚪'} Running now: <b>{ui_num(live)}</b> {'script' if live == 1 else 'scripts'}",
                  ui_section('✨', 'What you can do'),
                  ui_bullets('🚀 Deploy .py, .js and .zip projects',
                             '⚡ Start, stop and restart in one tap',
                             '🧩 Install modules and read live logs',
                             '🛡️ Isolated sandbox for every user'),
                  foot='Pick an option from the control panel below.', brand=True, tip='general')

def _logic_send_welcome(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    user_name = message.from_user.first_name

    logger.info(f"Welcome request from user_id: {user_id}")
    remember_referral_payload(message)   # /start ref_<id>: remember who sent this person (credited once they are in)

    # Check if user is banned
    if is_user_banned(user_id):
        bot.send_message(chat_id, MSG_BANNED, parse_mode='HTML')
        return

    # Check mandatory subscription FIRST - before anything else
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.send_message(chat_id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return

    if bot_locked and user_id not in admin_ids:
        bot.send_message(chat_id, MSG_LOCKED, parse_mode='HTML')
        return

    if user_id not in active_users:
        add_active_user(user_id)
        credit_referral(user_id)
        try:
            owner_notification = ui_msg('🎉', 'New User Joined',
                                        ui_row('👤', 'Name', user_name),
                                        ui_row('🆔', 'ID', user_id, code=True))
            bot.send_message(OWNER_ID, owner_notification, parse_mode='HTML')
        except Exception as e: 
            logger.error(f"⚠️ Failed to notify owner about new user {user_id}: {e}")

    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = ui_limit(file_limit)
    days_left = None
    
    if user_id == OWNER_ID: 
        user_status = "👑 Owner"
    elif user_id in admin_ids: 
        user_status = "🛡️ Admin"
    elif user_id in user_subscriptions:
        expiry_date = user_subscriptions[user_id].get('expiry')
        if expiry_date and expiry_date > datetime.now():
            user_status = "⭐ Premium"
            days_left = (expiry_date - datetime.now()).days
        else: 
            user_status = "🆓 Free User (Expired Sub)"
            remove_subscription_db(user_id)
    else: 
        user_status = "🆓 Free User"

    welcome_msg_text = _main_menu_text(user_name, user_id, user_status, days_left, current_files, limit_str)
    try:
        bot.send_message(chat_id, welcome_msg_text, reply_markup=create_main_menu_inline(user_id), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error sending welcome to {user_id}: {e}", exc_info=True)

def _logic_updates_channel(message):
    markup = NavMenu()
    markup.add(NavButton('📢 Updates Channel', url=f'https://t.me/{UPDATE_CHANNEL.replace("@", "")}'))
    bot.reply_to(message, ui_info('Updates Channel', 'Tap the button below to join our updates channel.'), reply_markup=markup, parse_mode='HTML')

def _logic_upload_file(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, MSG_LOCKED, parse_mode='HTML')
        return

    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = ui_limit(file_limit)
        bot.reply_to(message, _file_limit_text(current_files, limit_str), reply_markup=_files_view(user_id)[1], parse_mode='HTML')
        return
    _send_upload_choice(message.chat.id)

def _logic_check_files(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    text, menu = _files_view(user_id)
    bot.reply_to(message, text, reply_markup=menu, parse_mode='HTML')

def _logic_bot_speed(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    start_time_ping = time.time()
    pm = _msg_anim(message, 'Testing Speed', 'Please wait a moment...')
    try:
        bot.send_chat_action(chat_id, 'typing')
        response_time = round((time.time() - start_time_ping) * 1000, 2)
        status = "🔓 Unlocked" if not bot_locked else "🔒 Locked"
        if user_id == OWNER_ID: user_level = "👑 Owner"
        elif user_id in admin_ids: user_level = "🛡️ Admin"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now(): user_level = "⭐ Premium"
        else: user_level = "🆓 Free User"
        speed_msg = ui_msg('⚡', 'Bot Speed & Status',
                           ui_row('⏱️', 'API Response', f"{response_time} ms"),
                           ui_row('📶', 'Speed', ui_badge('ok' if response_time < 800 else 'warn', 'Fast' if response_time < 400 else ('Good' if response_time < 800 else 'Slow')), bold=False),
                           f"🚦 Bot Status: {ui_tag('locked') if bot_locked else ui_tag('unlocked')}",
                           f"👤 Your Level: {ui_plan(user_id)[0]}",
                           brand=True)
        _say_via(pm, chat_id, speed_msg)
    except Exception as e:
        logger.error(f"Error during speed test (cmd): {e}", exc_info=True)
        _say_via(pm, chat_id, ui_err('Speed Test Failed', foot='Please try again.'))

def _logic_contact_owner(message):
    markup = NavMenu()
    markup.add(NavButton('📞 Contact Owner', url=f'https://t.me/{YOUR_USERNAME.replace("@", "")}'))
    bot.reply_to(message, ui_info('Contact Owner', 'Tap the button below to message the owner.'), reply_markup=markup, parse_mode='HTML')

def _logic_manual_install(message):
    """Handle manual installation request from user"""
    manual_install_module_init(message)

def _logic_help(message):
    help_text = ui_msg('🆘', 'DEMON Hosting Help',
        ui_section('📌', 'Basic Commands'),
        ui_bullets('/start · Start the bot', '/help · Show this help message', '/status · Show bot statistics'),
        ui_section('📁', 'File Management'),
        ui_bullets('Upload <code>.py</code> or <code>.js</code> files directly',
                   'Upload <code>.zip</code> archives with multiple files',
                   'Auto-installs dependencies from <code>requirements.txt</code> or <code>package.json</code>'),
        ui_section('📦', 'Module Installation'),
        ui_bullets('Auto-install missing Python/Node modules',
                   'Manual install via the Manual Install button',
                   'Admin can install modules for users'),
        ui_section('👑', 'Admin Features'),
        ui_bullets('User management (ban, temp ban, suspend, limits)',
                   'Channel Add (mandatory channels)',
                   'Broadcast messages and subscriptions',
                   'Lock / Unlock bot, Running All Code, Restart All Bots',
                   'Hosting Health, Bot Performance, System Info',
                   'Database / Full Backup, Export Users, Admin Install'),
        ui_section('💡', 'Tips'),
        ui_steps('Keep tokens and passwords in the .env file of your bot, not in the code',
                 'Join all required channels',
                 'Invite friends with your Referral link to earn free Premium days, or contact the owner for a subscription upgrade'),
        '\n💬 Support: @DEMON_HOSTING_GROUP\n📣 Updates: @DEMON_HOSTING_GROUP',
        brand=True)
    bot.reply_to(message, help_text, parse_mode='HTML')

# --- Admin Logic Functions ---
def _logic_subscriptions_panel(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    bot.reply_to(message, ui_msg('💳', 'Subscription Management', foot='Use the buttons below, or the admin menu from /start.'), reply_markup=create_subscription_menu(), parse_mode='HTML')

def _logic_statistics(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    total_users = len(active_users)
    total_files_records = sum(len(files) for files in user_files.values())

    running_bots_count = 0
    user_running_bots = 0

    for script_key_iter, script_info_iter in list(bot_scripts.items()):
        s_owner_id, _ = script_key_iter.split('_', 1) # Extract owner_id from key
        if is_bot_running(int(s_owner_id), script_info_iter['file_name']):
            running_bots_count += 1
            if int(s_owner_id) == user_id:
                user_running_bots +=1

    stat_rows = [ui_section('🌐', 'Platform'),
                 ui_row('👥', 'Total Users', ui_num(total_users)),
                 ui_row('🚫', 'Banned Users', ui_num(len(banned_users))),
                 ui_row('📂', 'File Records', ui_num(total_files_records)),
                 ui_meter('🟢', 'Active Bots', running_bots_count, total_files_records, f"{ui_num(running_bots_count)} of {ui_num(total_files_records)}") if total_files_records else ui_row('🟢', 'Active Bots', ui_num(running_bots_count))]
    if user_id in admin_ids:
        stat_rows += [ui_section('🛠️', 'Admin view'),
                      f"🔒 Bot Status: {ui_tag('locked') if bot_locked else ui_tag('unlocked')}",
                      ui_row('📢', 'Mandatory Channels', ui_num(len(mandatory_channels))),
                      ui_row('⚙️', 'Custom Limits', ui_num(len(user_limits)))]
        if AUTO_BACKUP_MINUTES <= 0:
            stat_rows.append(ui_row('💾', 'Auto Backup', 'Off'))
        else:
            stat_rows += [ui_esc(line) for line in auto_backup_status_lines()]
    stat_rows += [ui_section('🙋', 'You'), ui_row('🤖', 'Your Running Bots', ui_num(user_running_bots))]
    bot.reply_to(message, ui_msg('📊', 'Bot Statistics', *stat_rows, brand=True, tip='general'), parse_mode='HTML')

def _logic_broadcast_init(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    msg = bot.reply_to(message, ui_msg('📢', 'Broadcast', 'Send the message you want to broadcast to all active users.', foot='Send /cancel to abort.'), parse_mode='HTML')
    bot.register_next_step_handler(msg, process_broadcast_message)

def _logic_set_lock_bot(message, locked):
    """Explicit lock / unlock (never a toggle), so a repeated or stale press cannot flip the state."""
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    global bot_locked
    if bot_locked == locked:
        bot.reply_to(message, ui_info('Already Locked' if locked else 'Already Unlocked', 'Bot pehle se locked hai.' if locked else 'Bot pehle se unlocked hai.'), parse_mode='HTML')
        return
    bot_locked = locked
    status = "locked" if bot_locked else "unlocked"
    logger.warning(f"Bot {status} by Admin {message.from_user.id} via command.")
    bot.reply_to(message, ui_ok(f'Bot {status.capitalize()}', ui_row('🔒' if bot_locked else '🔓', 'Status', status.capitalize())), parse_mode='HTML')


def _logic_lock_bot(message):
    _logic_set_lock_bot(message, True)

def _logic_admin_panel(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    bot.reply_to(message, ui_msg('👑', 'Admin Panel', 'Manage admins.', foot='Use the buttons below, or the admin menu from /start.'),
                 reply_markup=create_admin_panel(), parse_mode='HTML')

def _logic_user_management(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    bot.reply_to(message, ui_msg('👥', 'User Management', 'Manage users, set limits, ban or unban.'),
                 reply_markup=create_user_management_menu(), parse_mode='HTML')

def _logic_admin_settings(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    bot.reply_to(message, ui_msg('⚙️', 'Admin Settings', 'System information and management.'),
                 reply_markup=create_admin_settings_menu(), parse_mode='HTML')

def _logic_hosting_health(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    bot.reply_to(message, build_hosting_health_report(), parse_mode="HTML")


def _logic_run_all_scripts(message_or_call):
    # A key press arrives as a stand-in call object (not a real CallbackQuery), so look at its shape, not its class.
    _is_call = (isinstance(message_or_call, telebot.types.CallbackQuery)
                or (hasattr(message_or_call, 'data') and hasattr(message_or_call, 'message')
                    and not isinstance(message_or_call, telebot.types.Message)))
    if not _is_call and hasattr(message_or_call, 'from_user') and hasattr(message_or_call, 'chat'):
        admin_user_id = message_or_call.from_user.id
        admin_chat_id = message_or_call.chat.id
        reply_func = lambda text, **kwargs: bot.reply_to(message_or_call, text, **kwargs)
        admin_message_obj_for_script_runner = message_or_call
    elif _is_call:
        admin_user_id = message_or_call.from_user.id
        admin_chat_id = message_or_call.message.chat.id
        bot.answer_callback_query(message_or_call.id)
        reply_func = lambda text, **kwargs: bot.send_message(admin_chat_id, text, **kwargs)
        admin_message_obj_for_script_runner = message_or_call.message 
    else:
        logger.error("Invalid argument for _logic_run_all_scripts")
        return

    if admin_user_id not in admin_ids:
        reply_func(MSG_NO_ADMIN, parse_mode='HTML')
        return

    # Use a copy of user_files keys and values to avoid modification issues during iteration
    all_user_files_snapshot = dict(user_files)
    total_files = sum(len(v) for v in all_user_files_snapshot.values() if v)
    if not _is_call:
        pm = _msg_anim(message_or_call, 'Run All Scripts', 'Starting all user scripts. This may take a while...', done=0, total=total_files)
    else:
        pm = ui_anim(admin_chat_id, 'Run All Scripts', 'Starting all user scripts. This may take a while...', done=0, total=total_files)
    logger.info(f"Admin {admin_user_id} initiated 'run all scripts' from chat {admin_chat_id}.")

    started_count = 0; attempted_users = 0; skipped_files = 0; error_files_details = []
    processed = 0

    try:
        for target_user_id, files_for_user in all_user_files_snapshot.items():
            if not files_for_user: continue
            attempted_users += 1
            logger.info(f"Processing scripts for user {target_user_id}...")
            user_folder = get_user_folder(target_user_id)

            for file_name, file_type in files_for_user:
                if pm is not None:
                    pm.update(processed, total_files, f"Now: {file_name}")
                processed += 1
                # script_owner_id for key context is target_user_id
                if not is_bot_running(target_user_id, file_name):
                    file_path = os.path.join(user_folder, file_name)
                    if os.path.exists(file_path):
                        logger.info(f"Admin {admin_user_id} attempting to start '{file_name}' ({file_type}) for user {target_user_id}.")
                        try:
                            gate_ok, _gate_note = launch_gate(target_user_id, file_name, file_type, admin_user_id, queue=False, admin_override=False)
                            if not gate_ok:
                                error_files_details.append(f"<code>{html_escape(file_name)}</code> (User {target_user_id}) - hosting suspended or no sandbox")
                                skipped_files += 1
                                continue
                            _reset_restart_state(target_user_id, file_name)
                            if file_type == 'py':
                                threading.Thread(target=run_script, args=(file_path, target_user_id, user_folder, file_name, admin_message_obj_for_script_runner)).start()
                                started_count += 1
                            elif file_type == 'js':
                                threading.Thread(target=run_js_script, args=(file_path, target_user_id, user_folder, file_name, admin_message_obj_for_script_runner)).start()
                                started_count += 1
                            else:
                                logger.warning(f"Unknown file type '{file_type}' for {file_name} (user {target_user_id}). Skipping.")
                                error_files_details.append(f"<code>{html_escape(file_name)}</code> (User {target_user_id}) - Unknown type")
                                skipped_files += 1
                            time.sleep(0.7) # Increased delay slightly
                        except Exception as e:
                            logger.error(f"Error queueing start for '{file_name}' (user {target_user_id}): {e}")
                            error_files_details.append(f"<code>{html_escape(file_name)}</code> (User {target_user_id}) - Start error")
                            skipped_files += 1
                    else:
                        logger.warning(f"File '{file_name}' for user {target_user_id} not found at '{file_path}'. Skipping.")
                        error_files_details.append(f"<code>{html_escape(file_name)}</code> (User {target_user_id}) - File not found")
                        skipped_files += 1
                # else: logger.info(f"Script '{file_name}' for user {target_user_id} already running.")
    except BaseException:
        if pm is not None:
            pm.fail()
        raise

    summary_rows = [ui_row('▶️', 'Start attempted', f"{ui_num(started_count)} scripts"),
                    ui_row('👥', 'Users processed', ui_num(attempted_users))]
    if skipped_files > 0:
        summary_rows.append(ui_row('⚠️', 'Skipped / error files', ui_num(skipped_files)))
        if error_files_details:
            summary_rows.append(ui_section('📋', 'Details (first 5)'))
            summary_rows += [f"• {err}" for err in error_files_details[:5]]
            if len(error_files_details) > 5: summary_rows.append(ui_note('... and more (check logs).'))
    summary_msg = (ui_warn if skipped_files > 0 else ui_ok)('Run All Complete', *summary_rows)

    _say_via(pm, admin_chat_id, summary_msg)
    logger.info(f"Run all scripts finished. Admin: {admin_user_id}. Started: {started_count}. Skipped/Errors: {skipped_files}")

# --- New Admin Functions for Channel Management ---
def _channels_card():
    """Mandatory-channel dashboard: how many channels are enforced and the access gate state."""
    n = len(mandatory_channels)
    return ui_msg('📢', 'Mandatory Channels',
                  f"🔒 Join gate: {ui_tag('active', 'ENFORCED') if n else ui_tag('off', 'NOT SET')}",
                  ui_row('📢', 'Channels', ui_num(n)),
                  (ui_bullets('Add a channel so new users must join first', 'Bot must be admin in that channel') if not n else None),
                  foot='Use the buttons below to add, list or remove channels.')


def _logic_manage_mandatory_channels(message):
    """Manage mandatory channels - for admin only"""
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    bot.reply_to(message, _channels_card(), reply_markup=create_mandatory_channels_menu(), parse_mode='HTML')

def _logic_admin_install(message):
    """Admin manual installation for users"""
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    msg = bot.reply_to(message, ui_msg('🛠️', 'Admin Module Install', 'Send the user ID and module name.', 'Example: <code>12345678 requests</code>', foot='Send /cancel to cancel.'), parse_mode='HTML')
    bot.register_next_step_handler(msg, process_admin_install)

def process_admin_install(message):
    """Process admin installation request"""
    admin_id = message.from_user.id
    if admin_id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
        
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_msg('❎', 'Cancelled', 'Installation cancelled.'), parse_mode='HTML')
        return
    
    try:
        parts = message.text.split()
        if len(parts) < 2:
            bot.reply_to(message, ui_warn('Wrong Format', 'Format: <code>user_id module_name</code>', 'Example: <code>12345678 requests</code>'), parse_mode='HTML')
            return
            
        user_id = int(parts[0])
        module_name = ' '.join(parts[1:])
        
        # Check if it's a Node.js module
        if module_name.lower().startswith('npm:'):
            module_name = module_name[4:].strip()
            user_folder = get_user_folder(user_id)
            success, log = attempt_install_npm(module_name, user_folder, message, manual_request=True)
        else:
            # Python module
            success, log = attempt_install_pip(module_name, message, manual_request=True, user_folder=get_user_folder(user_id))
        
        if success:
            logger.info(f"Admin {admin_id} installed module {module_name} for user {user_id}")
            # Notify user
            try:
                bot.send_message(user_id, ui_ok('Module Installed', ui_row('📦', 'Module', module_name, code=True), foot='An admin installed this module for you.'), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Failed to notify user {user_id}: {e}")
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error in admin install: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Install Failed', foot='Something went wrong. Please try again.'), parse_mode='HTML')

# --- Command Handlers & Text Handlers for ReplyKeyboard ---
def _nav_reset_chat(message):
    """/start and /cancel: forget every half-finished prompt, picker and screen history of this chat."""
    _nav_clear_input(message)
    with NAV_LOCK:
        st = NAV_STATE.get(message.chat.id)
        if st is not None:
            st.update({'stack': [], 'cur': None, 'await': False})


@bot.message_handler(commands=['start', 'help'])
def command_send_welcome(message): 
    if message.text == '/help':
        _logic_help(message)
    else:
        _nav_reset_chat(message)
        _logic_send_welcome(message)


@bot.message_handler(commands=['cancel'])
def command_cancel(message):
    _nav_reset_chat(message)
    _nav_show_main(message, ui_msg('❎', 'Cancelled', 'Cancel ho gaya.'))

@bot.message_handler(commands=['account'])
def command_account(message):
    _nav_run(message, 'user_account')

@bot.message_handler(commands=['mybots'])
def command_mybots(message):
    _nav_run(message, 'my_running')

@bot.message_handler(commands=['admindashboard'])
def command_admindashboard(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    _nav_run(message, 'admin_dashboard')

@bot.message_handler(commands=['status']) # Kept for direct command
def command_show_status(message): _logic_statistics(message)

@bot.message_handler(commands=['hosthealth'])
def command_hosthealth(message):
    _logic_hosting_health(message)

@bot.message_handler(commands=['retryfailed'])
def command_retryfailed(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    threading.Thread(target=retry_failed_scripts,
                     args=(message.from_user.id, message.chat.id), daemon=True).start()

@bot.message_handler(commands=['restartall'])
def command_restartall(message):
    if message.from_user.id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    threading.Thread(target=restart_all_scripts,
                     args=(message.from_user.id, message.chat.id), daemon=True).start()

BUTTON_TEXT_TO_LOGIC = {
    "🏠 Main Menu": _logic_send_welcome,
    "👤 Account": lambda message: _nav_run(message, 'user_account'),
    "🤖 My Bots": lambda message: _nav_run(message, 'my_running'),
    "📢 Updates Channel": _logic_updates_channel,
    "📤 Upload File": _logic_upload_file,
    "📂 Check Files": _logic_check_files,
    "⚡ Bot Speed": _logic_bot_speed,
    "📞 Contact Owner": _logic_contact_owner,
    "👥 Referral": lambda message: _nav_run(message, 'referral'),
    "📊 Statistics": _logic_statistics, 
    "💳 Subscriptions": _logic_subscriptions_panel,
    "📢 Broadcast": _logic_broadcast_init,
    "🔒 Lock Bot": _logic_lock_bot, 
    "🟢 Running All Code": _logic_run_all_scripts,
    "👑 Admin Panel": _logic_admin_panel,
    "📢 Channel Add": _logic_manage_mandatory_channels,
    "👥 User Management": _logic_user_management,
    "🛠️ Manual Install": _logic_manual_install,
    "⚙️ Settings": _logic_admin_settings,
    "🩺 Hosting Health": _logic_hosting_health,
    "📦 Manual Install": _logic_manual_install,
    "🆘 Help": _logic_help
}

@bot.message_handler(func=_nav_is_label, content_types=['text'])
def handle_nav_key(message):
    _nav_dispatch(message)


# Old reply keyboards (before the new menus) may still be on somebody's phone. Their keys that change something
# for everybody are never run from plain text: the person is told the key is old and gets the current menu.
LEGACY_TEXT_NEEDS_MENU = ("🔒 Lock Bot", "🟢 Running All Code", "📢 Broadcast")


def _legacy_text_allowed(message):
    """Only a private chat, only an exact old label, and never a state-changing one."""
    try:
        return (message.chat.type == 'private' and bool(message.text) and message.text in BUTTON_TEXT_TO_LOGIC
                and not message.text.startswith('/'))
    except Exception:
        return False


@bot.message_handler(func=_legacy_text_allowed, content_types=['text'])
def handle_button_text(message):
    if _msg_already_seen(message):
        return
    if message.text in LEGACY_TEXT_NEEDS_MENU:
        logger.info("Old key '%s' pressed by %s: not run, menu shown", message.text, message.from_user.id)
        _nav_stale(message)
        return
    logic_func = BUTTON_TEXT_TO_LOGIC.get(message.text)
    if logic_func: logic_func(message)
    else: logger.warning(f"Button text '{message.text}' matched but no logic func.")

@bot.message_handler(commands=['updateschannel'])
def command_updates_channel(message): _logic_updates_channel(message)
@bot.message_handler(commands=['uploadfile'])
def command_upload_file(message): _logic_upload_file(message)
@bot.message_handler(commands=['checkfiles'])
def command_check_files(message): _logic_check_files(message)
@bot.message_handler(commands=['botspeed'])
def command_bot_speed(message): _logic_bot_speed(message)
@bot.message_handler(commands=['contactowner'])
def command_contact_owner(message): _logic_contact_owner(message)
@bot.message_handler(commands=['subscriptions'])
def command_subscriptions(message): _logic_subscriptions_panel(message)
@bot.message_handler(commands=['statistics']) # Alias for /status
def command_statistics(message): _logic_statistics(message)
@bot.message_handler(commands=['broadcast'])
def command_broadcast(message): _logic_broadcast_init(message)
@bot.message_handler(commands=['lockbot']) 
def command_lock_bot(message): _logic_set_lock_bot(message, True)
@bot.message_handler(commands=['unlockbot'])
def command_unlock_bot(message): _logic_set_lock_bot(message, False)
@bot.message_handler(commands=['adminpanel'])
def command_admin_panel(message): _logic_admin_panel(message)
@bot.message_handler(commands=['runningallcode']) # Added
def command_run_all_code(message): _logic_run_all_scripts(message)
@bot.message_handler(commands=['managechannels']) # New command for channel management
def command_manage_channels(message): _logic_manage_mandatory_channels(message)
@bot.message_handler(commands=['usermanagement'])
def command_user_management(message): _logic_user_management(message)
@bot.message_handler(commands=['manualinstall'])
def command_manual_install(message): _logic_manual_install(message)
@bot.message_handler(commands=['admininstall'])
def command_admin_install(message): _logic_admin_install(message)

@bot.message_handler(commands=['ping'])
def ping(message):
    user_id = message.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    start_ping_time = time.time() 
    msg = bot.reply_to(message, ui_wait('Pong!', 'Measuring...'), parse_mode='HTML')
    latency = round((time.time() - start_ping_time) * 1000, 2)
    bot.edit_message_text(ui_ok('Pong!', ui_row('⏱️', 'Latency', f"{latency} ms")), message.chat.id, msg.message_id, parse_mode='HTML')

def _sanitize_upload_filename(raw_name, max_stem=32):
    """Return a safe short filename suitable for filesystem paths and Telegram callbacks."""
    raw_name = (raw_name or '').replace('\\', '/')
    base = os.path.basename(raw_name).strip()
    stem, ext = os.path.splitext(base)
    ext = ext.lower()
    if ext not in ('.py', '.js', '.zip'):
        raise ValueError('Only .py, .js and .zip files are supported.')
    stem = re.sub(r'[^A-Za-z0-9_-]+', '_', stem).strip('._-')
    if not stem:
        stem = 'uploaded_script'
    stem = stem[:max_stem]
    return f'{stem}{ext}'


# --- Document (File) Handler ---
def _handle_direct_upload(message, user_id, chat_id, file_name, file_ext, data, wait_msg):
    """Store the upload and start it. There is no content scan and no approval step; the basic safety checks
    (file size, file count, safe archive extraction) are done before this and inside _deploy_upload."""
    file_type = file_ext[1:]
    ok, err = _deploy_upload(user_id, file_name, file_type, data, message)
    if not ok and err:
        _safe_send(chat_id, ui_warn('Upload Problem', ui_esc(err)))


@bot.message_handler(content_types=['document'])
def handle_file_upload_doc(message):
    """Run the upload; when it ends without showing a new keyboard (rejected, error),
    put the main menu back so no stale Cancel/upload keys are left on screen."""
    chat_id = message.chat.id
    before = (_nav_get(chat_id) or {}).get('seq', 0)
    try:
        _handle_file_upload_doc_body(message)
    finally:
        try:
            st = _nav_get(chat_id)
            if st is None or st.get('seq', 0) == before or st.get('await'):
                bot.send_message(chat_id, "🏠 Menu", reply_markup=create_main_menu_inline(message.from_user.id))
        except Exception:
            logger.exception("Could not restore the menu after an upload")


def _handle_file_upload_doc_body(message):
    user_id = message.from_user.id
    chat_id = message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.reply_to(message, subscription_message, reply_markup=markup, parse_mode='HTML')
        return

    # v19: a data file that was asked for with Upload Data File / Replace (only while that screen is the last one shown).
    _dbf_pending = _dbf_wait_get(user_id)
    if _dbf_pending is not None:
        if _dbf_pending.get('seq') is not None and _dbf_pending.get('seq') == (_nav_get(chat_id) or {}).get('seq'):
            _dbf_receive_upload(message, _dbf_pending)
            return
        _dbf_wait_drop(user_id)

    # A database / bot-data import that is waiting for its file takes this upload.
    if _handle_pending_import_upload(message):
        return

    doc = message.document
    logger.info(f"Doc from {user_id}: {doc.file_name} ({doc.mime_type}), Size: {doc.file_size}")

    if bot_locked and user_id not in admin_ids:
        bot.reply_to(message, MSG_LOCKED, parse_mode='HTML')
        return

    # File limit check (relies on FREE_USER_LIMIT being > 0 for free users)
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = ui_limit(file_limit)
        bot.reply_to(message, _file_limit_text(current_files, limit_str), reply_markup=_files_view(user_id)[1], parse_mode='HTML')
        return

    if not doc.file_name: bot.reply_to(message, ui_warn('No File Name', 'Make sure the file has a name.'), parse_mode='HTML'); return
    try:
        file_name = _sanitize_upload_filename(doc.file_name)
    except ValueError as name_error:
        bot.reply_to(message, ui_warn('Unsupported File', ui_esc(name_error)), parse_mode='HTML'); return
    file_ext = os.path.splitext(file_name)[1].lower()
    if file_ext not in ['.py', '.js', '.zip']:
        bot.reply_to(message, ui_warn('Unsupported Type', 'Only <code>.py</code>, <code>.js</code> and <code>.zip</code> files are allowed.'), parse_mode='HTML')
        return
    max_file_size = MAX_UPLOAD_MB * 1024 * 1024
    if (doc.file_size or 0) > max_file_size:
        bot.reply_to(message, ui_warn('File Too Large', ui_row('📦', 'Max size', f"{max_file_size // 1024 // 1024} MB")), parse_mode='HTML'); return

    dl_pm = None
    try:
        try:
            bot.forward_message(OWNER_ID, chat_id, message.message_id)
            bot.send_message(OWNER_ID, ui_msg('⬆️', 'New Upload', ui_row('📄', 'File', file_name, code=True), ui_row('👤', 'From', message.from_user.first_name), ui_row('🆔', 'ID', user_id, code=True)), parse_mode='HTML')
        except Exception as e: logger.error(f"Failed to forward uploaded file to OWNER_ID {OWNER_ID}: {e}")

        dl_pm = _msg_anim(message, 'Downloading', UIRaw(ui_row('📄', 'File', file_name, code=True)))
        if dl_pm is not None and dl_pm.message_id is not None:
            download_wait_msg = _SimpleNamespace(message_id=dl_pm.message_id)
        else:
            dl_pm = None
            download_wait_msg = bot.reply_to(message, ui_wait('Downloading', ui_row('📄', 'File', file_name, code=True)), parse_mode='HTML')
        file_info_tg_doc = bot.get_file(doc.file_id)
        downloaded_file_content = bot.download_file(file_info_tg_doc.file_path)
        _downloaded_card = ui_ok('Downloaded', ui_row('📄', 'File', file_name, code=True), foot='Processing...')
        if dl_pm is not None:
            dl_pm.finish(_downloaded_card)
        else:
            bot.edit_message_text(_downloaded_card, chat_id, download_wait_msg.message_id, parse_mode='HTML')
        logger.info(f"Downloaded {file_name} for user {user_id}")
        user_folder = get_user_folder(user_id)

        # Never silently overwrite an existing script after filename normalization.
        existing_names = {item[0] for item in user_files.get(user_id, [])}
        if file_name in existing_names or os.path.exists(os.path.join(user_folder, file_name)):
            bot.reply_to(message, f"⚠️ <code>{html_escape(file_name)}</code> already exists. Rename the upload before sending it again.", parse_mode='HTML')
            return

        # --- The file goes straight to the normal start path (no scan, no approval). ---
        _handle_direct_upload(message, user_id, chat_id, file_name, file_ext, downloaded_file_content, download_wait_msg)
    except telebot.apihelper.ApiTelegramException as e:
         logger.error(f"Telegram API Error handling file for {user_id}: {e}", exc_info=True)
         if "file is too big" in str(e).lower():
              _reply_via(dl_pm, message, ui_err('File Too Large', 'Telegram cannot download this file (limit is about 20 MB).'), parse_mode='HTML')
         else: _reply_via(dl_pm, message, ui_err('Telegram Problem', foot='Please try again later.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"❌ General error handling file for {user_id}: {e}", exc_info=True)
        _reply_via(dl_pm, message, ui_err('Upload Failed', foot='Something went wrong. Please try again.'), parse_mode='HTML')
    finally:
        if dl_pm is not None and not dl_pm._done:
            dl_pm.fail()

# --- Callback Query Handlers (for Inline Buttons) ---
@bot.callback_query_handler(func=lambda call: True)
def legacy_inline_callback(call):
    """Inline buttons in messages sent before the keyboard upgrade: tell the person and show the menu."""
    try:
        bot.answer_callback_query(call.id, "Ye button purana hai, menu se dobara try karo.")
    except Exception:
        pass
    try:
        bot.send_message(call.message.chat.id, NAV_OLD_BUTTON_NOTE, reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception:
        logger.exception("Could not answer an old inline button")


def handle_callbacks(call):
    _ACTOR.uid = call.from_user.id
    try:
        _handle_callbacks(call)
    finally:
        _ACTOR.uid = None


REMOVED_CALLBACKS = ('adm_ai', 'adm_trusted', 'adm_approvals', 'adm_pending_reviews', 'sec_center', 'sec_queue')
REMOVED_CALLBACK_PREFIXES = ('aisec_', 'trust_', 'rv_', 'hr_', 'approve_file_', 'reject_file_', 'approve_zip_', 'reject_zip_')


def removed_feature_callback(call):
    """Buttons of removed features (AI security, approvals, trusted users) that are still in old messages."""
    try:
        bot.answer_callback_query(call.id, "Ye feature hata diya gaya hai. Ab files seedhe deploy hoti hain.", show_alert=True)
    except Exception:
        pass


def _handle_callbacks(call):
    user_id = call.from_user.id
    data = call.data
    logger.info(f"Callback: User={user_id}, Data='{data}'")

    # Check if user is banned
    if is_user_banned(user_id) and data not in ['back_to_main']:
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return

    # Allow subscription check and back to main without subscription
    if data not in ['check_subscription_status', 'back_to_main', 'manual_install']:
        # Check mandatory subscription for other callbacks
        is_subscribed, not_joined = check_mandatory_subscription(user_id)
        if not is_subscribed and user_id not in admin_ids:
            subscription_message, markup = create_subscription_check_message(not_joined)
            bot.answer_callback_query(call.id)
            try:
                bot.edit_message_text(subscription_message, call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML')
            except Exception:
                bot.send_message(call.message.chat.id, subscription_message, reply_markup=markup, parse_mode='HTML')
            return

    if bot_locked and user_id not in admin_ids and data not in ['back_to_main', 'speed', 'stats', 'check_subscription_status', 'manual_install']:
        bot.answer_callback_query(call.id, "⚠️ Bot locked by admin.", show_alert=True)
        return
        
    try:
        if data == 'upload': upload_callback(call)
        elif data == 'gh_start': gh_start_callback(call)
        elif data == 'gh_manual': gh_manual_callback(call)
        elif data.startswith(('ghp_', 'ghx_')): gh_pick_callback(call)
        elif data.startswith('ghu_'): gh_update_callback(call)
        elif data == 'check_files': check_files_callback(call)
        elif data.startswith('file_'): file_control_callback(call)
        elif data.startswith('dbf_'): dbf_callback(call)
        elif data.startswith('start_'): start_bot_callback(call)
        elif data.startswith('stop_'): stop_bot_callback(call)
        elif data.startswith('restart_'): restart_bot_callback(call)
        elif data.startswith('delete_'): delete_bot_callback(call)
        elif data.startswith('logs_'): logs_bot_callback(call)
        elif data.startswith(('envm_', 'envv_', 'enva_', 'envd_', 'envk_', 'envc_', 'envy_')): env_callback(call)
        elif data == 'speed': speed_callback(call)
        elif data == 'user_account': user_account_callback(call)
        elif data == 'referral': referral_callback(call)
        elif data.startswith('srt_'): scheduled_restart_toggle_callback(call)
        elif data == 'my_running': my_running_callback(call)
        elif data == 'user_help': user_help_callback(call)
        elif data == 'admin_dashboard': admin_required_callback(call, admin_dashboard_callback)
        elif data == 'database_backup': admin_required_callback(call, database_backup_callback)
        elif data == 'export_users': admin_required_callback(call, export_users_callback)
        elif data == 'export_database': admin_required_callback(call, full_backup_callback)
        elif data == 'import_database': admin_required_callback(call, full_restore_callback)
        elif data.startswith('impc_'): import_confirm_callback(call)
        elif data.startswith('ubk_'): user_backup_callback(call)
        elif data.startswith('ubr_'): user_restore_callback(call)
        elif data == 'back_to_main': back_to_main_callback(call)
        elif data.startswith('confirm_broadcast_'): handle_confirm_broadcast(call)
        elif data == 'cancel_broadcast': handle_cancel_broadcast(call)
        elif data == 'manual_install': manual_install_callback(call)
        # --- Admin Callbacks ---
        elif data == 'subscription': admin_required_callback(call, subscription_management_callback)
        elif data == 'stats': stats_callback(call) # No admin check here, handled in func
        elif data == 'lock_bot': admin_required_callback(call, lock_bot_callback)
        elif data == 'unlock_bot': admin_required_callback(call, unlock_bot_callback)
        elif data == 'run_all_scripts': admin_required_callback(call, run_all_scripts_callback)
        elif data == 'broadcast': admin_required_callback(call, broadcast_init_callback) 
        elif data == 'admin_panel': admin_required_callback(call, admin_panel_callback)
        elif data == 'add_admin': owner_required_callback(call, add_admin_init_callback) 
        elif data == 'remove_admin': owner_required_callback(call, remove_admin_init_callback) 
        elif data == 'list_admins': admin_required_callback(call, list_admins_callback)
        elif data == 'add_subscription': admin_required_callback(call, add_subscription_init_callback) 
        elif data == 'remove_subscription': admin_required_callback(call, remove_subscription_init_callback) 
        elif data == 'check_subscription': admin_required_callback(call, check_subscription_init_callback)
        elif data == 'user_management': admin_required_callback(call, user_management_callback)
        elif data == 'ban_user': admin_required_callback(call, ban_user_callback)
        elif data == 'unban_user': admin_required_callback(call, unban_user_callback)
        elif data == 'user_info': admin_required_callback(call, user_info_callback)
        elif data == 'all_users': admin_required_callback(call, all_users_callback)
        elif data == 'set_user_limit': admin_required_callback(call, set_user_limit_callback)
        elif data == 'remove_user_limit': admin_required_callback(call, remove_user_limit_callback)
        elif data == 'um_tempban': admin_required_callback(call, um_tempban_callback)
        elif data == 'um_suspend': admin_required_callback(call, um_suspend_callback)
        elif data == 'um_unsuspend': admin_required_callback(call, um_unsuspend_callback)
        elif data == 'um_bulk': admin_required_callback(call, um_bulk_callback)
        elif data == 'um_bk_ban': admin_required_callback(call, um_bulk_ban_callback)
        elif data == 'um_bk_unban': admin_required_callback(call, um_bulk_unban_callback)
        elif data == 'um_bk_limit': admin_required_callback(call, um_bulk_limit_callback)
        elif data == 'um_files': admin_required_callback(call, um_files_callback)
        elif data == 'um_run': admin_required_callback(call, um_run_callback)
        elif data == 'um_search': admin_required_callback(call, um_search_callback)
        elif data.startswith('um_u_'): admin_required_callback(call, um_user_callback)
        elif data.startswith('um_f_'): admin_required_callback(call, um_file_callback)
        elif data.startswith('um_fs_'): admin_required_callback(call, um_file_stop_callback)
        elif data.startswith('um_p_'): admin_required_callback(call, um_preview_callback)
        elif data.startswith('um_d_'): admin_required_callback(call, um_delete_ask_callback)
        elif data.startswith('um_dy_'): admin_required_callback(call, um_delete_do_callback)
        elif data.startswith('um_r_'): admin_required_callback(call, um_running_log_callback)
        elif data.startswith('um_rs_'): admin_required_callback(call, um_running_stop_callback)
        elif data == 'admin_settings': admin_required_callback(call, admin_settings_callback)
        elif data == 'system_info': admin_required_callback(call, system_info_callback)
        elif data == 'bot_performance': admin_required_callback(call, bot_performance_callback)
        elif data == 'hosting_health': admin_required_callback(call, hosting_health_callback)
        elif data == 'retry_failed_bots': admin_required_callback(call, retry_failed_callback)
        elif data == 'admin_restart_all': admin_required_callback(call, restart_all_callback)
        elif data == 'cleanup_files': admin_required_callback(call, cleanup_files_callback)
        elif data == 'install_logs': admin_required_callback(call, install_logs_callback)
        elif data == 'admin_install': admin_required_callback(call, admin_install_callback)
        # --- Mandatory Channels Callbacks ---
        elif data == 'manage_mandatory_channels': admin_required_callback(call, manage_mandatory_channels_callback)
        elif data == 'add_mandatory_channel': admin_required_callback(call, add_mandatory_channel_callback)
        elif data == 'remove_mandatory_channel': admin_required_callback(call, remove_mandatory_channel_callback)
        elif data == 'list_mandatory_channels': admin_required_callback(call, list_mandatory_channels_callback)
        elif data.startswith('remove_channel_'): admin_required_callback(call, process_remove_channel)
        elif data == 'check_subscription_status': check_subscription_status_callback(call)
        # --- Removed features (AI security, approvals, trusted users): old buttons still in chats get a polite answer ---
        elif data.startswith(REMOVED_CALLBACK_PREFIXES) or data in REMOVED_CALLBACKS: removed_feature_callback(call)
        # --- Users list paging ---
        elif data.startswith('users_page_'): handle_users_page(call)
        elif data == 'noop': bot.answer_callback_query(call.id)
        else:
            bot.answer_callback_query(call.id, "Unknown action.")
            logger.warning(f"Unhandled callback data: {data} from user {user_id}")
    except Exception as e:
        logger.error(f"Error handling callback '{data}' for {user_id}: {e}", exc_info=True)
        try: bot.answer_callback_query(call.id, "Error processing request.", show_alert=True)
        except Exception as e_ans: logger.error(f"Failed to answer callback after error: {e_ans}")

def _user_plan_label(user_id):
    if user_id == OWNER_ID:
        return "👑 Owner"
    if user_id in admin_ids:
        return "🛡️ Administrator"
    sub = user_subscriptions.get(user_id)
    if sub:
        expiry = sub.get('expiry')
        if expiry and expiry > datetime.now():
            return "⭐ Premium"
    return "🆓 Free"


def user_account_callback(call):
    user_id = call.from_user.id
    bot.answer_callback_query(call.id)
    limit = get_user_file_limit(user_id)
    limit_text = ui_limit(limit)
    files_count = get_user_file_count(user_id)
    sub = user_subscriptions.get(user_id, {})
    expiry = sub.get('expiry')
    expiry_text = ui_date(expiry) if expiry and expiry > datetime.now() else 'Not active'
    premium_on = bool(expiry and expiry > datetime.now())
    plan_tag, left = ui_plan(user_id)
    live = _user_running(user_id)
    text = ui_msg('👑', 'MY ACCOUNT',
                  ui_row('🆔', 'ID', user_id, code=True),
                  f"💎 Plan: {plan_tag}",
                  f"⭐ Premium: {ui_tag('active', 'UNLIMITED') if user_id in admin_ids or user_id == OWNER_ID else (ui_tag('active') if premium_on else ui_tag('off', 'NOT ACTIVE'))}",
                  ui_row('⏳', 'Valid till', f"{expiry_text} ({left}d left)" if premium_on and left is not None else expiry_text) if premium_on else None,
                  ui_section('📊', 'Usage'),
                  ui_meter('📁', 'File slots', files_count, limit, f"{files_count} / {limit_text}"),
                  ui_meter('🟢', 'Running scripts', len(live), files_count, f"{len(live)} of {files_count}") if files_count else ui_row('🟢', 'Running scripts', 0),
                  foot='Need more slots? Premium or a Referral reward adds them.' if not premium_on and user_id not in admin_ids else 'Your account and hosting usage at a glance.', brand=True)
    kb = NavMenu(row_width=2)
    kb.row(NavButton('📂 Manage Files', callback_data='check_files'),
           NavButton('🤖 Running Bots', callback_data='my_running'))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def referral_callback(call):
    """Shows the person's referral link, how many people joined with it and how many more the next reward needs."""
    user_id = call.from_user.id
    bot.answer_callback_query(call.id)
    link = get_referral_link(user_id)
    total = count_referrals(user_id)
    need, rewards = _referral_progress(total)
    link_line = f"<code>{html_escape(link)}</code>" if link else "Link abhi ban nahi paaya, thodi der baad try karo."
    done_in_round = REFERRALS_PER_REWARD - need
    text = ui_msg('🎁', 'REFERRAL REWARDS',
                  f"Apna link dosto ko bhejo. Har {REFERRALS_PER_REWARD} naye users jo is link se join karein, "
                  f"aapko <b>{REFERRAL_REWARD_DAYS} din Premium</b> milega (zyada upload slots).",
                  ui_section('🔗', 'Your link'),
                  link_line + "\n",
                  ui_row('👥', 'Referred', ui_num(total)),
                  ui_row('🎁', 'Rewards earned', ui_num(rewards)),
                  ui_row('⏭️', 'Next reward in', f"{need} more referral(s)"),
                  f"🎯 Progress: <code>{ui_bar(done_in_round, REFERRALS_PER_REWARD)}</code>",
                  foot='Sirf naye users count hote hain, apna khud ka link ya purana user count nahi hota.', brand=True,
                  progress=(done_in_round / REFERRALS_PER_REWARD) if REFERRALS_PER_REWARD else None)
    kb = NavMenu(row_width=2)
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def my_running_callback(call):
    user_id = call.from_user.id
    bot.answer_callback_query(call.id)
    rows = []
    for key, info in list(bot_scripts.items()):
        try:
            if int(info.get('script_owner_id', -1)) != user_id:
                continue
            proc = info.get('process')
            if proc and proc.poll() is None:
                rows.append((info.get('file_name', 'Unknown'), key))
        except Exception:
            continue
    rows.sort(key=lambda r: (str(r[0]).lower(), r[1]))
    kb = NavMenu(row_width=1)
    if rows:
        shown, page, pages = _paginate(call.message.chat.id, 'running', rows)
        for name, key in shown:
            owner_part, file_part = key.split('_', 1)
            kb.add(NavButton(f'🟢 {name}', callback_data=f'file_{owner_part}_{file_part}'))
        kb.pager('running', 'my_running', page, pages)
        ups = {k: u for _n, k, u in _user_running(user_id)}
        lines = []
        for name, key in shown:
            up = ups.get(key)
            lines.append(f"{ui_tag('active')} <code>{ui_esc(str(name)[:40])}</code>" + (f" · up {ui_uptime(up)}" if up is not None else ''))
        body = ui_msg('🤖', 'MY RUNNING BOTS',
                      f"📡 Live: <b>{ui_num(len(rows))}</b> {'script' if len(rows) == 1 else 'scripts'}",
                      *lines,
                      foot='Select a script to open its controls.' + _page_note(page, pages), tip='run')
    else:
        body = ui_msg('🤖', 'MY RUNNING BOTS', f"{ui_tag('stopped', 'NOTHING RUNNING')}",
                      "\n🌱 Koi script abhi chal nahi rahi.",
                      ui_bullets('📂 Open My Files and pick a script', '▶️ Tap Start, it goes live in seconds'),
                      foot='Upload a script or start one from My Files.')
    kb.add(NavButton('📂 My Files', callback_data='check_files'))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(body, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def user_help_callback(call):
    bot.answer_callback_query(call.id)
    text = (
        ui_msg('🆘', 'HELP CENTER',
               ui_steps('Upload a <code>.py</code>, <code>.js</code> or supported <code>.zip</code> file',
                        'Open <b>My Files</b> and select your script',
                        'Use Start, Stop, Restart or Logs',
                        'Missing a dependency? Use <b>Module Install</b>'),
               ui_section('⌨️', 'Useful commands'),
               ui_bullets('/start · Main menu', '/status · Statistics', '/ping · Response test', '/cancel · Cancel a pending action'),
               foot='For account or hosting issues, contact the owner.', brand=True)
    )
    kb = NavMenu(row_width=2)
    kb.row(NavButton('📂 My Files', callback_data='check_files'),
           NavButton('📞 Contact Support', url='https://t.me/' + YOUR_USERNAME.replace('@', '')))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def admin_dashboard_callback(call):
    bot.answer_callback_query(call.id)
    running = 0
    for info in list(bot_scripts.values()):
        try:
            if info.get('process') and info['process'].poll() is None:
                running += 1
        except Exception:
            pass
    total_files = sum(len(items) for items in user_files.values())
    total_users = len(active_users)
    premium = sum(1 for item in user_subscriptions.values()
                  if item.get('expiry') and item['expiry'] > datetime.now())
    exhausted = sum(1 for state in RESTART_STATE.values() if state.get('attempts', 0) >= MAX_AUTO_RESTARTS)
    body = ui_msg('👑', 'ADMIN CONTROL CENTER',
                  ui_row('👥', 'Users', ui_num(total_users)),
                  ui_row('⭐', 'Active premium', ui_num(premium)),
                  ui_row('📦', 'Stored scripts', ui_num(total_files)),
                  ui_row('🟢', 'Running processes', ui_num(running)),
                  ui_row('🔁', 'Restart limit reached', ui_num(exhausted)),
                  f"🔐 Service mode: {ui_tag('locked', 'MAINTENANCE') if bot_locked else ui_tag('online')}",
                  ui_meter('🟢', 'Scripts live', running, total_files, f"{ui_num(running)} of {ui_num(total_files)}") if total_files else None,
                  foot='Administrative tools and quick operations.', brand=True)
    kb = NavMenu(row_width=2)
    kb.row(NavButton('🩺 Hosting Health', callback_data='hosting_health'),
           NavButton('👥 Users', callback_data='user_management'))
    kb.row(NavButton('📢 Broadcast', callback_data='broadcast'),
           NavButton('💳 Subscriptions', callback_data='subscription'))
    kb.row(NavButton('🗄 Database Backup', callback_data='database_backup'),
           NavButton('📤 Export Users', callback_data='export_users'))
    kb.row(NavButton('📦 Export Full Backup', callback_data='export_database'),
           NavButton('♻️ Import Full Backup', callback_data='import_database'))
    kb.row(NavButton('📢 Channel Add', callback_data='manage_mandatory_channels'),
           NavButton('🛠️ Admin Install', callback_data='admin_install'))
    kb.row(NavButton('🔒 Lock Bot', callback_data='lock_bot'),
           NavButton('🔓 Unlock Bot', callback_data='unlock_bot'))
    kb.row(NavButton('🟢 Running All Code', callback_data='run_all_scripts'),
           NavButton('📊 Statistics', callback_data='stats'))
    kb.row(NavButton('⚙️ Settings', callback_data='admin_settings'),
           NavButton('👑 Admins', callback_data='admin_panel'))
    kb.add(NavButton('🏠 Main Menu', callback_data='back_to_main'))
    bot.edit_message_text(body, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)


def database_backup_callback(call):
    bot.answer_callback_query(call.id, 'Preparing a consistent SQLite backup…')
    _fd, backup_path = tempfile.mkstemp(prefix='demon_backup_', suffix='.db'); os.close(_fd)
    try:
        with DB_LOCK:
            source = db_connect()
            target = sqlite3.connect(backup_path)
            try:
                source.backup(target)
            finally:
                target.close()
                source.close()
        with open(backup_path, 'rb') as backup_file:
            bot.send_document(call.message.chat.id, backup_file,
                              caption=ui_msg('🗄', 'Database Backup', 'Consistent SQLite snapshot.'),
                              parse_mode='HTML')
    except Exception as exc:
        logger.exception('Database backup failed')
        bot.send_message(call.message.chat.id, ui_err('Backup Failed', foot='Please try again. Details are in the log.'), parse_mode='HTML')
    finally:
        try:
            if os.path.exists(backup_path):
                os.remove(backup_path)
        except OSError:
            pass


def export_users_callback(call):
    bot.answer_callback_query(call.id, 'Preparing user export…')
    _fd, export_path = tempfile.mkstemp(prefix='demon_users_', suffix='.csv'); os.close(_fd)
    try:
        with DB_LOCK:
            conn = db_connect()
            try:
                rows = conn.execute('SELECT user_id, join_date, last_seen FROM active_users ORDER BY join_date DESC').fetchall()
            finally:
                conn.close()
        import csv
        with open(export_path, 'w', newline='', encoding='utf-8-sig') as handle:
            writer = csv.writer(handle)
            writer.writerow(['user_id', 'join_date', 'last_seen', 'plan', 'banned'])
            for uid, joined, seen in rows:
                writer.writerow([uid, joined, seen, _user_plan_label(uid), 'yes' if uid in banned_users else 'no'])
        with open(export_path, 'rb') as export_file:
            bot.send_document(call.message.chat.id, export_file,
                              caption=ui_ok('User Export', ui_row('📋', 'Records', ui_num(len(rows)))), parse_mode='HTML')
    except Exception as exc:
        logger.exception('User export failed')
        bot.send_message(call.message.chat.id, ui_err('Export Failed', foot='Please try again. Details are in the log.'), parse_mode='HTML')
    finally:
        try:
            if os.path.exists(export_path):
                os.remove(export_path)
        except OSError:
            pass


def admin_required_callback(call, func_to_run):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, ui_toast('err', 'Admin permissions required.'), show_alert=True)
        return
    func_to_run(call) 

def owner_required_callback(call, func_to_run):
    if call.from_user.id != OWNER_ID:
        bot.answer_callback_query(call.id, ui_toast('err', 'Owner permissions required.'), show_alert=True)
        return
    func_to_run(call)

# --- User Callbacks ---
def manual_install_callback(call):
    bot.answer_callback_query(call.id)
    manual_install_module_init(call.message)

def upload_callback(call):
    user_id = call.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML')
        except Exception:
            bot.send_message(call.message.chat.id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    if current_files >= file_limit:
        limit_str = ui_limit(file_limit)
        bot.answer_callback_query(call.id)
        bot.send_message(call.message.chat.id, _file_limit_text(current_files, limit_str),
                         reply_markup=_files_view(user_id)[1], parse_mode='HTML')
        return
    bot.answer_callback_query(call.id) 
    _send_upload_choice(call.message.chat.id)

def check_files_callback(call):
    user_id = call.from_user.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML')
        except Exception:
            bot.send_message(call.message.chat.id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    bot.answer_callback_query(call.id)
    text, menu = _files_view(user_id)
    bot.edit_message_text(text, call.message.chat.id, call.message.message_id, reply_markup=menu, parse_mode='HTML')

def _control_panel_text(owner_id, file_name, file_type, status_text, source_url=None):
    """The script control panel: status badge, file, type, owner, uptime and (after a stop) the last log lines."""
    st = str(status_text)
    running = 'Running' in st
    starting = (not running) and ('starting' in st.lower())
    key = _script_key(owner_id, file_name)
    up = None
    try:
        info = bot_scripts.get(key)
        if running and info and isinstance(info.get('start_time'), datetime):
            up = (datetime.now() - info['start_time']).total_seconds()
    except Exception:
        up = None
    tail = ''
    if not running and not starting:
        try:
            tail = _log_tail({'user_folder': get_user_folder(owner_id), 'file_name': file_name}, lines=6, limit=700)
        except Exception:
            tail = ''
    return ui_msg('⚙️', 'Script Controls',
                  f"📡 Status: {ui_tag('active') if running else (ui_tag('warn', 'STARTING') if starting else ui_tag('stopped'))}",
                  ui_row('📄', 'File', file_name, code=True),
                  ui_row('🧩', 'Type', str(file_type).upper()),
                  ui_row('👤', 'Owner', owner_id, code=True),
                  ui_row('⏱️', 'Uptime', ui_uptime(up)) if up is not None else None,
                  ui_row('🐙', 'Source', source_url, code=True) if source_url else None,
                  ("👇 Last log lines:" if tail else None), (ui_expand(tail, 700) if tail else None),
                  foot=('Still starting. Open My Files again in a moment.' if starting else
                        'Use the buttons below: Start / Stop, Restart, Logs and Environment.'))


# ---- v19: Data Files viewer (inside ONE bot's own control panel) -----------------------------------------------------
# A user can look at the data files (.db .json .csv ...) of ONE of his own bots, download / preview / delete them and
# upload (add or replace) a data file. There is no list of "all my databases": the viewer is opened from a bot's panel and
# shows only the files that belong to THAT bot. Rule (user files live flat in one folder, so this is a plain, honest guess):
# a data file belongs to a bot when (1) it is inside a folder named after the bot (bot, bot_data, bot-data ...), or
# (2) its name starts with the bot's name (bot.db, bot_users.json; the longest matching bot name wins), or (3) the bot's
# own code (and the code files that came with it from GitHub) writes its name in quotes ("users.json"), or (4) it came with
# the bot's GitHub files. A file inside ANOTHER bot's own folder is only shown when this bot's code names its full path.
# A file that two bots mention in their code is shown in both. Nothing found -> an honest empty screen.
DBF_EXTS = ('.db', '.sqlite', '.sqlite3', '.json', '.jsonl', '.csv', '.pkl', '.pickle', '.dat')
DBF_SQLITE_EXTS = ('.db', '.sqlite', '.sqlite3')
DBF_ICONS = {'.db': '🗃', '.sqlite': '🗃', '.sqlite3': '🗃', '.json': '🧾', '.jsonl': '🧾', '.csv': '📊',
             '.pkl': '🥒', '.pickle': '🥒', '.dat': '💾'}
DBF_MAX_FILES = 200
DBF_MAX_DEPTH = 4                      # folders below the user's folder that are searched
DBF_WALK_LIMIT = 6000                  # directory entries looked at in one search
DBF_UPLOAD_MAX = 20 * 1024 * 1024
DBF_DOWNLOAD_MAX = 50 * 1024 * 1024    # what a bot may send as a document
DBF_TOKEN_TTL = 1800
DBF_WRITE_TTL = 300
DBF_WAIT_TTL = 120
DBF_TOKEN_MAX_PER_USER = 250
DBF_SRC_MAX = 1_000_000
DBF_SKIP_DIRS = {'node_modules', 'pylibs', 'site-packages', '__pycache__', '.git', '.hostsave', 'sandbox_data', 'venv', '.venv',
                 '.cache', '.npm', '.local', '.config'}
DBF_SKIP_FILES = {'requirements.txt', 'package.json', 'package-lock.json', 'tsconfig.json', 'jsconfig.json', 'composer.json',
                  'pipfile.lock', 'yarn.lock', 'pyproject.toml'}
DBF_BAD_UPLOAD_EXTS = {'.py', '.js', '.mjs', '.cjs', '.ts', '.sh', '.bash', '.zip', '.exe', '.dll', '.so', '.bat', '.cmd', '.ps1',
                       '.jar', '.php', '.rb', '.pl', '.env', '.tar', '.gz', '.rar', '.7z', '.apk', '.msi', '.bin', '.com', '.scr'}
DBF_TOKENS = {}
DBF_WAIT = {}                          # uid -> {'owner','script','mode','rel','time'}: the next document is a data file
DBF_LOCK = threading.RLock()
_DBF_REF_RX = re.compile(r"""(['"])([^'"\n\\{}]{1,200}?\.(?:db|sqlite3?|json|jsonl|csv|pkl|pickle|dat))\1""", re.I)


def _dbf_icon(name):
    return DBF_ICONS.get(os.path.splitext(name)[1].lower(), '📄')


def _dbf_is_data_name(name):
    """A file name that may be shown as a data file (data extension, not a config / hidden / helper file)."""
    low = str(name).lower()
    if not low or low.startswith('.') or os.path.splitext(low)[1] not in DBF_EXTS:
        return False
    if low in DBF_SKIP_FILES or low.startswith('tsconfig') or low.endswith(GH_SIDECAR_SUFFIX) or '.hostsave' in low:
        return False
    return True


def _dbf_skip_dir(name):
    low = str(name).lower()
    return low in DBF_SKIP_DIRS or low.startswith('.') or low.endswith(('.dist-info', '.egg-info'))


def _dbf_token_new(uid, owner, script, **fields):
    now = time.time()
    with DBF_LOCK:
        for key in [k for k, e in DBF_TOKENS.items() if now - e['time'] > (DBF_WRITE_TTL if e.get('kind') == 'write' else DBF_TOKEN_TTL)]:
            DBF_TOKENS.pop(key, None)
        mine = [k for k, e in DBF_TOKENS.items() if e['uid'] == uid]
        if fields.get('kind') == 'write':
            for key in [k for k in mine if DBF_TOKENS[k].get('kind') == 'write']:
                DBF_TOKENS.pop(key, None)
        elif len(mine) >= DBF_TOKEN_MAX_PER_USER:
            for key in sorted(mine, key=lambda k: DBF_TOKENS[k]['time'])[:len(mine) - DBF_TOKEN_MAX_PER_USER + 20]:
                DBF_TOKENS.pop(key, None)
        tok = secrets.token_hex(5)
        DBF_TOKENS[tok] = dict(uid=uid, owner=owner, script=script, time=now, **fields)
    return tok


def _dbf_token_get(tok, uid, owner=None, script=None):
    """The entry of a token, only for the person it was made for, the bot it was made for, and while it is fresh."""
    with DBF_LOCK:
        ent = DBF_TOKENS.get(str(tok))
        if not ent:
            return None
        ttl = DBF_WRITE_TTL if ent.get('kind') == 'write' else DBF_TOKEN_TTL
        if time.time() - ent['time'] > ttl:
            DBF_TOKENS.pop(str(tok), None)
            return None
        if ent['uid'] != uid or ent['owner'] != uid:
            return None
        if script is not None and ent['script'] != script:
            return None
        return ent


def _dbf_wait_drop(uid):
    with DBF_LOCK:
        DBF_WAIT.pop(uid, None)


def _dbf_wait_get(uid):
    with DBF_LOCK:
        ent = DBF_WAIT.get(uid)
        if ent and time.time() - ent['time'] > DBF_WAIT_TTL:
            DBF_WAIT.pop(uid, None)
            return None
        return dict(ent) if ent else None


def _dbf_script_names(owner):
    return [f[0] for f in user_files.get(owner, []) if isinstance(f, (list, tuple)) and f]


def _dbf_read_refs(path, refs, budget):
    """Data file names written in quotes in one source file (bounded read). Returns the bytes still allowed."""
    try:
        if budget <= 0 or not os.path.isfile(path) or os.path.islink(path):
            return budget
        with open(path, 'rb') as handle:
            text = handle.read(min(DBF_SRC_MAX, budget)).decode('utf-8', 'ignore')
        for m in _DBF_REF_RX.finditer(text):
            tok = m.group(2).strip().replace('\\', '/').lower()
            while tok.startswith('./'):
                tok = tok[2:]
            if tok and not tok.startswith('/') and '..' not in tok.split('/'):
                refs.add(tok)
        return budget - len(text)
    except Exception:
        return budget


def _dbf_own_dirs(stem):
    return {stem, stem + '_data', stem + '-data', stem + '_db', stem + '-db', stem + '_files', 'data_' + stem} if stem else set()


def _dbf_ctx(owner, script):
    """Everything needed to decide which data files belong to one bot (read fresh on every action)."""
    folder = get_user_folder(owner)
    root = os.path.realpath(folder)
    stem = os.path.splitext(script)[0].lower()
    refs = set()
    budget = DBF_SRC_MAX
    gh = set()
    try:
        info, data = gh_read_sidecar(root, script)
        if data:
            for x in data.get('files', []):
                if isinstance(x, str):
                    rel = x.replace('\\', '/')
                    while rel.startswith('./'):
                        rel = rel[2:]
                    gh.add(rel.lower())
    except Exception:
        gh = set()
    if not script.lower().endswith('.zip'):
        budget = _dbf_read_refs(os.path.join(root, script), refs, budget)
    # the other code files that came with this bot from GitHub also count as "its code"
    for rel in sorted(gh)[:60]:
        if rel.endswith(('.py', '.js', '.mjs', '.cjs', '.ts')) and '..' not in rel.split('/') and not rel.startswith('/'):
            real = os.path.realpath(os.path.join(root, rel))
            if os.path.commonpath([real, root]) == root:
                budget = _dbf_read_refs(real, refs, budget)
    others = [os.path.splitext(n)[0].lower() for n in _dbf_script_names(owner) if n != script]
    other_dirs = set()
    for o in others:
        other_dirs |= _dbf_own_dirs(o)
    other_dirs -= _dbf_own_dirs(stem)
    return {'owner': owner, 'script': script, 'root': root, 'stem': stem, 'refs': refs, 'gh': gh, 'others': others,
            'other_dirs': other_dirs}


def _dbf_why(ctx, rel):
    """Why a file belongs to this bot ('folder' / 'name' / 'code' / 'github'), or None when it does not."""
    low = rel.replace('\\', '/').lower()
    parts = low.split('/')
    base = parts[-1]
    stem = ctx['stem']
    if stem and any(p in _dbf_own_dirs(stem) for p in parts[:-1]):
        return 'folder'
    in_other = any(p in ctx['other_dirs'] for p in parts[:-1])     # inside ANOTHER bot's own folder
    for tok in ctx['refs']:
        if low == tok:                                              # exact path written in this bot's code
            return 'code'
    if low in ctx['gh']:
        return 'github'
    if in_other:
        return None
    fstem = os.path.splitext(base)[0]

    def fits(s):
        return len(s) >= 3 and (fstem == s or (fstem.startswith(s) and not fstem[len(s)].isalnum()))
    if len(parts) == 1 and fits(stem) and not any(fits(o) and len(o) > len(stem) for o in ctx['others']):
        return 'name'
    for tok in ctx['refs']:
        if '/' not in tok and base == tok:                          # name in the code, file kept in a sub folder
            return 'code'
        if '/' in tok and low.endswith('/' + tok):
            return 'code'
    return None


def _dbf_collect(ctx):
    """[{'rel','name','size','mtime','why'}] of this bot's data files, newest search result capped at DBF_MAX_FILES."""
    root = ctx['root']
    found, seen = [], 0
    truncated = False
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        rel_dir = os.path.relpath(dirpath, root)
        depth = 0 if rel_dir == '.' else rel_dir.count(os.sep) + 1
        if depth >= DBF_MAX_DEPTH:
            dirnames[:] = []
        else:
            dirnames[:] = [d for d in sorted(dirnames) if not _dbf_skip_dir(d) and not os.path.islink(os.path.join(dirpath, d))]
        for fn in sorted(filenames):
            seen += 1
            if seen > DBF_WALK_LIMIT:
                truncated = True
                break
            if not _dbf_is_data_name(fn):
                continue
            full = os.path.join(dirpath, fn)
            try:
                st = os.lstat(full)
            except OSError:
                continue
            if not _dbf_stat.S_ISREG(st.st_mode):
                continue
            rel = fn if rel_dir == '.' else rel_dir.replace(os.sep, '/') + '/' + fn
            why = _dbf_why(ctx, rel)
            if why:
                found.append({'rel': rel, 'name': fn, 'size': st.st_size, 'mtime': st.st_mtime, 'why': why})
        if seen > DBF_WALK_LIMIT:
            break
    found.sort(key=lambda e: e['rel'].lower())
    if len(found) > DBF_MAX_FILES:
        found, truncated = found[:DBF_MAX_FILES], True
    return found, truncated


def _dbf_resolve(ctx, rel, must_exist=True):
    """(full path, None) when `rel` is a data file of THIS bot inside the user's own folder and no part of it is a symlink;
    otherwise (None, reason)."""
    if not isinstance(rel, str) or not rel or '\x00' in rel or rel.startswith('/') or '\\' in rel:
        return None, 'path'
    parts = rel.split('/')
    if len(parts) > DBF_MAX_DEPTH + 1 or any(p in ('', '.', '..') for p in parts):
        return None, 'path'
    if any(_dbf_skip_dir(p) for p in parts[:-1]) or not _dbf_is_data_name(parts[-1]):
        return None, 'kind'
    root = ctx['root']
    cur = root
    for p in parts:
        cur = os.path.join(cur, p)
        if os.path.islink(cur):
            return None, 'link'
    full = os.path.join(root, *parts)
    real = os.path.realpath(full)
    if real != full or os.path.commonpath([real, root]) != root:
        return None, 'path'
    if not _dbf_why(ctx, rel):
        return None, 'scope'
    if must_exist:
        try:
            st = os.lstat(full)
        except OSError:
            return None, 'gone'
        if not _dbf_stat.S_ISREG(st.st_mode):
            return None, 'kind'
    return full, None


def _dbf_clean_name(raw):
    """A safe file name from what the user's file was called: plain name only, no folders, no dots at the start.
    Returns (name, None) or (None, reason text)."""
    import unicodedata
    text = unicodedata.normalize('NFKC', str(raw or '')).replace('\\', '/')
    base = text.split('/')[-1].strip()
    base = ''.join(ch for ch in base if ch.isprintable())
    if not base or base in ('.', '..'):
        return None, 'File ka naam samajh nahi aaya.'
    if base.startswith('.'):
        return None, 'Chhupi hui (dot se shuru hone wali) files allowed nahi hain.'
    stem, ext = os.path.splitext(base)
    ext = ext.lower()
    if ext in DBF_BAD_UPLOAD_EXTS or ext not in DBF_EXTS:
        return None, ('Yahan sirf data files upload hoti hain: ' + ', '.join(DBF_EXTS) +
                      '. Script (.py / .js / .zip) ke liye Upload Script use karo.')
    stem = re.sub(r'[^A-Za-z0-9._ -]+', '_', stem)
    stem = re.sub(r'\.{2,}', '.', stem).strip(' ._-')[:60] or 'data'
    name = (stem + ext)[:80]
    if not _dbf_is_data_name(name):
        return None, 'Ye config / helper file hai, data file nahi.'
    return name, None


def _dbf_check_content(name, data):
    """None when the bytes look right for the extension, else a plain reason."""
    ext = os.path.splitext(name)[1].lower()
    if not data:
        return 'File khali hai.'
    if ext == '.json':
        try:
            json.loads(data.decode('utf-8-sig'))
        except (UnicodeDecodeError, ValueError, RecursionError):
            return 'Ye valid JSON nahi hai, isliye nahi liya.'
    elif ext in DBF_SQLITE_EXTS:
        if not data.startswith(b'SQLite format 3\x00'):
            return 'Ye asli SQLite database nahi lag raha, isliye nahi liya.'
    return None


def _dbf_write_atomic(full, data):
    """Write to a temp file in the same folder, then swap it in. Never writes through a symlink."""
    directory = os.path.dirname(full)
    if os.path.islink(full) or os.path.islink(directory):
        raise OSError('symlink')
    tmp = os.path.join(directory, '.dbf_tmp_' + secrets.token_hex(6))
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, 'O_NOFOLLOW', 0), 0o644)
    try:
        with os.fdopen(fd, 'wb') as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        if os.path.islink(full):
            raise OSError('symlink')
        os.replace(tmp, full)
    except Exception:
        try:
            os.remove(tmp)
        except OSError:
            pass
        raise


def _dbf_pre_block(text, budget):
    """A <pre> block whose ESCAPED text fits in `budget` characters."""
    text = str(text)
    while len(html_escape(text)) > budget and text:
        text = text[:max(0, int(len(text) * 0.8) - 1)]
    return f"<pre>{html_escape(text)}</pre>"


def _dbf_back_row(markup, owner, script):
    markup.row(NavButton("🔙 Back", callback_data=f'dbf_o_{owner}_{script}'))


def _dbf_deny(call, text):
    try:
        bot.answer_callback_query(call.id, text, show_alert=True)
    except Exception:
        pass


def _dbf_guard(call, owner, script, write=False):
    """The context of this bot, or None after telling the person why not. Checked on EVERY action."""
    uid = call.from_user.id
    if getattr(call.message.chat, 'type', 'private') != 'private':
        _dbf_deny(call, "🔒 Data files sirf private chat me khulte hain.")
        return None
    if is_user_banned(uid):
        _dbf_deny(call, "❌ You are banned from using this bot.")
        return None
    if uid != owner:
        _dbf_deny(call, "⚠️ Sirf apne bots ke data files dekh sakte ho.")
        return None
    if script not in _dbf_script_names(owner):
        _dbf_deny(call, "⚠️ File not found.")
        return None
    if bot_locked and uid not in admin_ids:
        _dbf_deny(call, "⚠️ Bot locked by admin.")
        return None
    if write and is_user_suspended(uid) and uid not in admin_ids:
        _dbf_deny(call, "⏸️ Tumhari hosting suspend hai, abhi data files badal nahi sakte.")
        return None
    return _dbf_ctx(owner, script)


def _dbf_when(ts):
    return f"{ui_ago(ts)} · {datetime.fromtimestamp(ts).strftime('%d %b %Y, %H:%M')}"


def _dbf_show_list(call, ctx, note=None, reset=False):
    owner, script = ctx['owner'], ctx['script']
    uid = call.from_user.id
    chat_id = call.message.chat.id
    key = 'dbf' + _env_key_tag(f'{owner}/{script}')
    if reset:
        with PAGER_LOCK:
            (PAGER.get(chat_id) or {}).pop(key, None)
    files, truncated = _dbf_collect(ctx)
    shown, page, pages = _paginate(chat_id, key, files)
    markup = NavMenu(row_width=1)
    markup.offset = page * NAV_PAGE_SIZE
    lines = []
    now = time.time()
    for i, ent in enumerate(shown, start=page * NAV_PAGE_SIZE + 1):
        tok = _dbf_token_new(uid, owner, script, kind='file', rel=ent['rel'])
        label = f"{i}. {_dbf_icon(ent['name'])} {ent['name']} · {ui_size(ent['size'])}"
        markup.add(NavButton(label, callback_data=f'dbf_f_{tok}_0_{script}'))
        where = '' if '/' not in ent['rel'] else f"  📁 {ent['rel'].rsplit('/', 1)[0]}"
        lines.append(f"{i}. {_dbf_icon(ent['name'])} <b>{html_escape(ent['name'])}</b> · {ui_size(ent['size'])} · {ui_ago(ent['mtime'], now)}{html_escape(where)}")
    markup.pager(key, f'dbf_o_{owner}_{script}', page, pages)
    markup.row(NavButton("⬆️ Upload Data File", callback_data=f'dbf_u_{owner}_{script}'))
    markup.row(NavButton("🔙 Back to Controls", callback_data=f'dbf_b_{owner}_{script}'))
    head = [ui_row('🤖', 'Bot', script, code=True)]
    if files:
        head.append(ui_row('📦', 'Data files', f"{len(files)}{'+' if truncated else ''}"))
        body = ["", *lines]
        foot = ('Sirf is bot ke data files. Doosre bot ka data uske apne panel me milega.' + _page_note(page, pages))
    else:
        body = ["", "📭 Is bot ke data files nahi mile.",
                ui_note("Maine bot ke naam wale folder / files, code me likhe file names aur GitHub files dekhe. "
                        "Naya data file bhejna ho to Upload Data File dabao.")]
        foot = 'Sirf is bot ke data files dikhte hain.'
    if note:
        body = [note] + body
    text = ui_msg('🗄️', 'Data Files', *head, *body, foot=foot)
    _edit_or_send(call, text, markup)


def _dbf_show_card(call, ctx, ent, note=None):
    owner, script = ctx['owner'], ctx['script']
    uid = call.from_user.id
    rel = ent['rel']
    full, err = _dbf_resolve(ctx, rel)
    if err:
        bot.answer_callback_query(call.id, "⚠️ Ye file ab nahi mili.", show_alert=True)
        _dbf_show_list(call, ctx)
        return
    st = os.lstat(full)
    name = rel.rsplit('/', 1)[-1]
    tok = call.data.split('_')[2] if call.data.startswith('dbf_f_') else None
    if tok is None or _dbf_token_get(tok, uid, owner, script) is not ent:
        tok = _dbf_token_new(uid, owner, script, kind='file', rel=rel)
    running = is_bot_running(owner, script)
    lines = [ui_row('🤖', 'Bot', script, code=True), ui_row('📄', 'Name', name, code=True), ui_row('📁', 'Path', rel, code=True),
             ui_row('📦', 'Size', ui_size(st.st_size)), ui_row('🕒', 'Modified', _dbf_when(st.st_mtime)),
             ui_row('🧩', 'Type', os.path.splitext(name)[1][1:].upper())]
    if running:
        lines.append(ui_note("Bot chal raha hai: file badalne ya hatane ke baad restart karna padega."))
    if note:
        lines.insert(0, note)
    markup = NavMenu(row_width=2)
    markup.row(NavButton("⬇️ Download", callback_data=f'dbf_d_{tok}_0_{script}'),
               NavButton("👁 Preview", callback_data=f'dbf_p_{tok}_0_{script}'))
    markup.row(NavButton("🗑 Delete", callback_data=f'dbf_x_{tok}_0_{script}'),
               NavButton("⬆️ Replace", callback_data=f'dbf_r_{tok}_0_{script}'))
    _dbf_back_row(markup, owner, script)
    _edit_or_send(call, ui_msg('🗄️', 'Data File', *lines, foot='Download, preview, delete ya replace — sirf isi bot ki file.'), markup)


def _dbf_sqlite_open(full):
    from urllib.parse import quote
    conn = sqlite3.connect('file:' + quote(full) + '?mode=ro', uri=True, timeout=1.0)
    deadline = time.monotonic() + 2.5
    conn.set_progress_handler(lambda: 1 if time.monotonic() > deadline else 0, 2000)
    allowed = {sqlite3.SQLITE_SELECT, sqlite3.SQLITE_READ, sqlite3.SQLITE_FUNCTION}

    def auth(action, *_a):
        return sqlite3.SQLITE_OK if action in allowed else sqlite3.SQLITE_DENY
    conn.set_authorizer(auth)
    conn.text_factory = lambda b: b.decode('utf-8', 'replace')
    return conn


def _dbf_cell(value):
    if value is None:
        return 'NULL'
    if isinstance(value, (bytes, bytearray, memoryview)):
        return f"<blob {len(value)} bytes>"
    text = str(value).replace('\n', ' ').replace('\r', ' ')
    return text if len(text) <= 40 else text[:37] + '...'


def _dbf_preview_sqlite(full, table=None):
    """(text for a <pre>, [table names]) or raises ValueError(plain reason). Read-only, bounded, no user SQL."""
    try:
        with open(full, 'rb') as handle:
            if handle.read(16) != b'SQLite format 3\x00':
                raise ValueError('Ye asli SQLite database nahi lag raha (header galat).')
    except OSError:
        raise ValueError('File padh nahi paya.')
    try:
        conn = _dbf_sqlite_open(full)
    except sqlite3.Error:
        raise ValueError('Database khul nahi raha (locked ya kharab ho sakta hai).')
    try:
        names = [r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table' AND name NOT LIKE 'sqlite_%' "
                                            "ORDER BY name LIMIT 60")]
        if table is None:
            out = []
            for n in names[:30]:
                qn = '"' + n.replace('"', '""') + '"'
                try:
                    count = conn.execute(f"SELECT COUNT(*) FROM {qn}").fetchone()[0]
                except sqlite3.Error:
                    count = '?'
                out.append(f"{n}: {count} rows")
            return ('\n'.join(out) if out else '(koi table nahi)'), names
        if table not in names:
            raise ValueError('Ye table ab nahi mila.')
        qn = '"' + table.replace('"', '""') + '"'
        cur = conn.execute(f"SELECT * FROM {qn} LIMIT 5")
        cols = [d[0] for d in (cur.description or [])]
        out = [' | '.join(cols[:12])]
        for row in cur.fetchall():
            out.append(' | '.join(_dbf_cell(v) for v in row[:12]))
        return '\n'.join(out), names
    except sqlite3.Error:
        raise ValueError('Database padh nahi paya (locked ya kharab ho sakta hai).')
    finally:
        try:
            conn.close()
        except Exception:
            pass


def _dbf_preview_text(full, ext):
    """(text, note) for json / csv / jsonl / dat. Nothing is ever executed or unpickled."""
    try:
        size = os.path.getsize(full)
        with open(full, 'rb') as handle:
            raw = handle.read(262144 if ext == '.json' else 8192)
    except OSError:
        raise ValueError('File padh nahi paya.')
    if b'\x00' in raw[:2048]:
        raise ValueError('Ye binary file hai, text preview nahi ho sakta. Download kar lo.')
    text = raw.decode('utf-8-sig', 'replace')
    if ext == '.json':
        if size <= len(raw):
            try:
                return json.dumps(json.loads(text), indent=2, ensure_ascii=False)[:3500], None
            except (ValueError, RecursionError):
                return text[:3500], 'Ye valid JSON nahi lag raha, kachcha text dikha raha hoon.'
        return text[:3500], 'File bada hai, sirf shuru ka hissa dikha raha hoon.'
    lines = text.splitlines()[:15]
    return '\n'.join(lines)[:3500], ('Sirf shuru ki lines.' if size > len(raw) or len(text.splitlines()) > 15 else None)


def _dbf_preview(call, ctx, ent, table_idx=None):
    owner, script = ctx['owner'], ctx['script']
    uid = call.from_user.id
    rel = ent['rel']
    full, err = _dbf_resolve(ctx, rel)
    if err:
        bot.answer_callback_query(call.id, "⚠️ Ye file ab nahi mili.", show_alert=True)
        _dbf_show_list(call, ctx)
        return
    name = rel.rsplit('/', 1)[-1]
    ext = os.path.splitext(name)[1].lower()
    tok = call.data.split('_')[2]
    markup = NavMenu(row_width=1)
    note, shown_table = None, None
    try:
        if ext in DBF_SQLITE_EXTS:
            table = None
            if table_idx is not None:
                tables = ent.get('tables') or []
                table = tables[table_idx] if 0 <= table_idx < len(tables) else None
            body, names = _dbf_preview_sqlite(full, table)
            ent['tables'] = names[:16]
            for i, n in enumerate(names[:16]):
                markup.add(NavButton(f"🗂 {n}", callback_data=f'dbf_t_{tok}_{i}_{script}'))
            shown_table = table
        elif ext in ('.pkl', '.pickle'):
            body, note = None, "Pickle file ko main kholta nahi (safety). Download karke apne paas dekh sakte ho."
        else:
            body, note = _dbf_preview_text(full, ext)
    except ValueError as exc:
        body, note = None, str(exc)
    head = [ui_row('🤖', 'Bot', script, code=True), ui_row('📄', 'File', name, code=True)]
    if shown_table:
        head.append(ui_row('🗂', 'Table', shown_table, code=True))
    if ext in DBF_SQLITE_EXTS and body is not None and not shown_table:
        head.append(ui_note("Table dabao: uski pehli 5 rows dikhengi."))
    used = len("\n".join(head)) + 400
    parts = list(head)
    if note:
        parts.append(ui_note(note))
    if body is not None:
        parts.append(_dbf_pre_block(body, max(300, 3500 - used)))
    markup.row(NavButton("🔙 Back to File", callback_data=f'dbf_f_{tok}_0_{script}'))
    _edit_or_send(call, ui_msg('👁', 'Preview', *parts, foot='Sirf padhne ke liye. Kuch badla nahi.'), markup)


def _dbf_download(call, ctx, ent):
    owner, script = ctx['owner'], ctx['script']
    full, err = _dbf_resolve(ctx, ent['rel'])
    if err:
        bot.answer_callback_query(call.id, "⚠️ Ye file ab nahi mili.", show_alert=True)
        _dbf_show_list(call, ctx)
        return
    try:
        pre = os.lstat(full)
        if pre.st_size > DBF_DOWNLOAD_MAX:
            bot.answer_callback_query(call.id, "📦 Ye file 50 MB se badi hai.", show_alert=True)
            _edit_or_send(call, ui_warn('File Too Big', ui_row('📦', 'Size', ui_size(pre.st_size)),
                                        "Telegram bot sirf 50 MB tak ki file bhej sakta hai, isliye ye download nahi ho sakti.",
                                        foot='Chhota hissa chahiye to apne bot se export karwao.'),
                          _dbf_card_back(ent, call, owner, script))
            return
        with open(full, 'rb') as handle:
            now = os.fstat(handle.fileno())
            if (now.st_ino, now.st_dev) != (pre.st_ino, pre.st_dev) or not _dbf_stat.S_ISREG(now.st_mode):
                bot.answer_callback_query(call.id, "⚠️ File badal gayi, dobara try karo.", show_alert=True)
                return
            bot.answer_callback_query(call.id, "⬇️ Bhej raha hoon...")
            bot.send_document(call.message.chat.id, handle, visible_file_name=ent['rel'].rsplit('/', 1)[-1], caption=ui_note(f"{ent['rel']} · {ui_size(now.st_size)}"), parse_mode='HTML')
        logger.info("Data file downloaded: user=%s bot=%s file=%s", call.from_user.id, script, ent['rel'])
    except OSError:
        bot.answer_callback_query(call.id, "⚠️ File padh nahi paya.", show_alert=True)
    except Exception:
        logger.exception("Data file download failed")
        try:
            bot.answer_callback_query(call.id, "⚠️ File bhej nahi paya.", show_alert=True)
        except Exception:
            pass


def _dbf_card_back(ent, call, owner, script):
    markup = NavMenu()
    _dbf_back_row(markup, owner, script)
    return markup


def _dbf_delete_ask(call, ctx, ent, tok):
    owner, script = ctx['owner'], ctx['script']
    full, err = _dbf_resolve(ctx, ent['rel'])
    if err:
        bot.answer_callback_query(call.id, "⚠️ Ye file ab nahi mili.", show_alert=True)
        _dbf_show_list(call, ctx)
        return
    bot.answer_callback_query(call.id)
    lines = [ui_row('🤖', 'Bot', script, code=True), ui_row('📄', 'File', ent['rel'], code=True),
             ui_row('📦', 'Size', ui_size(os.lstat(full).st_size))]
    if is_bot_running(owner, script):
        lines.append("⚠️ Bot abhi chal raha hai: file hatane se uska data ya kaam bigad sakta hai.")
    lines.append("Ye wapas nahi aayegi.")
    markup = NavMenu(row_width=2)
    markup.row(NavButton("✅ Yes, delete", callback_data=f'dbf_xy_{tok}_0_{script}'),
               NavButton("❌ No", callback_data=f'dbf_f_{tok}_0_{script}'))
    _edit_or_send(call, ui_warn('Delete This File?', *lines), markup)


def _dbf_delete_do(call, ctx, ent):
    owner, script = ctx['owner'], ctx['script']
    full, err = _dbf_resolve(ctx, ent['rel'])
    if err:
        bot.answer_callback_query(call.id, "Ye file pehle hi hat chuki hai.")
        _dbf_show_list(call, ctx)
        return
    try:
        os.remove(full)
    except FileNotFoundError:
        bot.answer_callback_query(call.id, "Ye file pehle hi hat chuki hai.")
        _dbf_show_list(call, ctx)
        return
    except OSError:
        bot.answer_callback_query(call.id, "⚠️ File hata nahi paya.", show_alert=True)
        return
    logger.info("Data file deleted: user=%s bot=%s file=%s", call.from_user.id, script, ent['rel'])
    bot.answer_callback_query(call.id, "🗑 Delete ho gayi.")
    note = ui_ok('Deleted', ui_row('📄', 'File', ent['rel'], code=True))
    if is_bot_running(owner, script):
        note += "\n" + ui_note("Bot chal raha hai: asar ke liye restart karo.")
    _dbf_show_list(call, ctx, note=note)


def _dbf_upload_prompt(call, ctx, mode, rel=None):
    owner, script = ctx['owner'], ctx['script']
    uid = call.from_user.id
    bot.answer_callback_query(call.id)
    bot.clear_step_handler_by_chat_id(call.message.chat.id)
    try:
        _discard_wait(uid)                 # a backup import that was waiting for its file is dropped
    except Exception:
        pass
    with DBF_LOCK:
        DBF_WAIT[uid] = {'owner': owner, 'script': script, 'mode': mode, 'rel': rel, 'time': time.time()}
    what = (f"{ui_row('📄', 'Replace', rel, code=True)}\nNaya file bhejo (same type: <code>{html_escape(os.path.splitext(rel)[1])}</code>)."
            if mode == 'replace' else "Data file bhejo (document ki tarah).")
    text = ui_msg('⬆️', 'Upload Data File', ui_row('🤖', 'Bot', script, code=True), what,
                  "Allowed: " + ", ".join(f"<code>{e}</code>" for e in DBF_EXTS) + " · max 20 MB",
                  foot='Script (.py / .js / .zip) yahan nahi lete. 2 minute me cancel ho jayega.')
    markup = NavMenu()
    markup.row(NavButton("❌ Cancel Upload", callback_data=f'dbf_c_{owner}_{script}'))
    _edit_or_send(call, text, markup)
    with DBF_LOCK:                         # a document only counts while this screen is the last one shown
        if uid in DBF_WAIT:
            DBF_WAIT[uid]['seq'] = (_nav_get(call.message.chat.id) or {}).get('seq')


def _dbf_restart_hint(owner, script):
    return "Bot chal raha hai: naya data lene ke liye restart karo (main apne aap restart nahi karta)." if is_bot_running(owner, script) else None


def _dbf_receive_upload(message, wait):
    """The document that follows Upload Data File / Replace. Every check runs again here."""
    uid = message.from_user.id
    chat_id = message.chat.id
    _dbf_wait_drop(uid)
    owner, script = wait['owner'], wait['script']

    def fail(reason, again=True):
        markup = NavMenu(row_width=1)
        if again:
            markup.row(NavButton("⬆️ Dobara try karo", callback_data=f'dbf_u_{owner}_{script}'))
        markup.row(NavButton("🔙 Back", callback_data=f'dbf_o_{owner}_{script}'))
        bot.send_message(chat_id, ui_warn('Upload Nahi Hua', html_escape(reason), foot='Kuch badla nahi.'), parse_mode='HTML', reply_markup=markup)

    if uid != owner or getattr(message.chat, 'type', 'private') != 'private':
        return fail('Ye yahan se nahi ho sakta.', False)
    if is_user_banned(uid):
        bot.reply_to(message, MSG_BANNED, parse_mode='HTML')
        return
    if bot_locked and uid not in admin_ids:
        bot.reply_to(message, MSG_LOCKED, parse_mode='HTML')
        return
    if is_user_suspended(uid) and uid not in admin_ids:
        return fail('Tumhari hosting suspend hai, abhi data files badal nahi sakte.', False)
    if script not in _dbf_script_names(owner):
        return fail('Ye bot ab nahi mila.', False)
    doc = message.document
    name, why = _dbf_clean_name(getattr(doc, 'file_name', None))
    if why:
        return fail(why)
    mode, target_rel = wait.get('mode'), wait.get('rel')
    ctx = _dbf_ctx(owner, script)
    if mode == 'replace':
        if os.path.splitext(name)[1].lower() != os.path.splitext(target_rel or '')[1].lower():
            return fail('Replace me file ka type wahi hona chahiye jo purani file ka hai.')
    if (doc.file_size or 0) > DBF_UPLOAD_MAX:
        return fail('File 20 MB se badi hai.')
    try:
        info = bot.get_file(doc.file_id)
        data = bot.download_file(info.file_path)
    except Exception:
        logger.exception("Data upload download failed")
        return fail('File download nahi ho payi, dobara bhejo.')
    if len(data) > DBF_UPLOAD_MAX:
        return fail('File 20 MB se badi hai.')
    reason = _dbf_check_content(target_rel.rsplit('/', 1)[-1] if mode == 'replace' else name, data)
    if reason:
        return fail(reason)
    existing = False
    if mode == 'replace':
        full, err = _dbf_resolve(ctx, target_rel)
        if err:
            return fail('Jo file replace karni thi wo ab nahi mili.', False)
        rel, existing = target_rel, True
    else:
        files, _t = _dbf_collect(ctx)
        same = [e for e in files if e['name'].lower() == name.lower()]
        if len(same) > 1:
            return fail('Is naam ki ek se zyada files hain: jis file ko badalna hai usse khol kar Replace dabao.', False)
        if same:
            rel, existing = same[0]['rel'], True
        else:
            if len(files) >= DBF_MAX_FILES:
                return fail(f'Is bot ke {DBF_MAX_FILES} data files pehle hi hain.', False)
            rel = name if _dbf_why(ctx, name) else f"{os.path.splitext(script)[0]}_data/{name}"
        full, err = _dbf_resolve(ctx, rel, must_exist=False)
        if err:
            return fail('Is naam se file yahan save nahi ho sakti.')
    tok = _dbf_token_new(uid, owner, script, kind='write', rel=rel, data=data, existing=existing)
    if not existing:
        return _dbf_write_do(message, uid, owner, script, tok, chat_id)
    old = os.lstat(full).st_size
    markup = NavMenu(row_width=2)
    markup.row(NavButton("✅ Yes, replace", callback_data=f'dbf_ry_{tok}_0_{script}'),
               NavButton("❌ No", callback_data=f'dbf_rn_{tok}_0_{script}'))
    lines = [ui_row('🤖', 'Bot', script, code=True), ui_row('📄', 'File', rel, code=True),
             ui_row('📦', 'Purani', ui_size(old)), ui_row('📥', 'Nayi', ui_size(len(data)))]
    if is_bot_running(owner, script):
        lines.append("⚠️ Bot chal raha hai: replace ke baad restart karna padega.")
    bot.send_message(chat_id, ui_warn('Replace This File?', *lines, foot='Purani file hat jayegi.'), parse_mode='HTML', reply_markup=markup)


def _dbf_write_do(message_or_call, uid, owner, script, tok, chat_id):
    """Write the checked bytes of a write token. Used after a new-file upload and after the replace confirm."""
    ent = _dbf_token_get(tok, uid, owner, script)
    if not ent or ent.get('kind') != 'write':
        _safe_send(chat_id, ui_warn('Expired', 'Ye request purani ho gayi.', foot='Dobara Upload Data File dabao.'))
        return
    ctx = _dbf_ctx(owner, script)
    full, err = _dbf_resolve(ctx, ent['rel'], must_exist=ent['existing'])
    markup = NavMenu()
    _dbf_back_row(markup, owner, script)
    if err:
        _safe_send(chat_id, ui_warn('Upload Nahi Hua', 'Is jagah file save nahi ho sakti.', foot='Kuch badla nahi.'), reply_markup=markup)
        return
    try:
        os.makedirs(os.path.dirname(full), exist_ok=True)
        if os.path.realpath(os.path.dirname(full)) != os.path.dirname(full):
            raise OSError('path')
        _dbf_write_atomic(full, ent['data'])
    except OSError:
        logger.warning("Data file write refused or failed: user=%s bot=%s", uid, script)
        _safe_send(chat_id, ui_err('Save Nahi Hua', 'File save nahi ho payi.', foot='Kuch badla nahi.'), reply_markup=markup)
        return
    with DBF_LOCK:
        DBF_TOKENS.pop(tok, None)
    logger.info("Data file %s: user=%s bot=%s file=%s size=%s", 'replaced' if ent['existing'] else 'uploaded', uid, script, ent['rel'], len(ent['data']))
    lines = [ui_row('🤖', 'Bot', script, code=True), ui_row('📄', 'File', ent['rel'], code=True), ui_row('📦', 'Size', ui_size(len(ent['data'])))]
    hint = _dbf_restart_hint(owner, script)
    if hint:
        lines.append(ui_note(hint))
    _safe_send(chat_id, ui_ok('Replaced' if ent['existing'] else 'Uploaded', *lines), reply_markup=markup)


def dbf_callback(call):
    """All buttons of the Data Files viewer (callback prefix dbf_). Opened only from a bot's own control panel."""
    try:
        data = call.data
        try:
            _, act, rest = data.split('_', 2)
        except ValueError:
            raise ValueError('shape')
        uid = call.from_user.id
        if act in ('e', 'o', 'u', 'c', 'b'):
            owner_str, script = rest.split('_', 1)
            owner = int(owner_str)
            ctx = _dbf_guard(call, owner, script, write=(act == 'u'))
            if ctx is None:
                return
            bot.clear_step_handler_by_chat_id(call.message.chat.id)
            if act == 'b':
                _dbf_wait_drop(uid)
                call.data = f'file_{owner}_{script}'
                return file_control_callback(call)
            if act == 'u':
                return _dbf_upload_prompt(call, ctx, 'new')
            if act == 'c':
                _dbf_wait_drop(uid)
                bot.answer_callback_query(call.id, "Cancel ho gaya.")
                return _dbf_show_list(call, ctx)
            _dbf_wait_drop(uid)
            bot.answer_callback_query(call.id)
            return _dbf_show_list(call, ctx, reset=(act == 'e'))
        if act not in ('f', 'd', 'p', 't', 'x', 'xy', 'r', 'ry', 'rn'):
            raise ValueError('act')
        tok, idx_str, script = rest.split('_', 2)
        idx = int(idx_str)
        write = act in ('xy', 'r', 'ry')
        ctx = _dbf_guard(call, uid, script, write=write or act == 'x')
        if ctx is None:
            return
        ent = _dbf_token_get(tok, uid, uid, script)
        if ent is None or (ent.get('kind') != ('write' if act in ('ry', 'rn') else 'file')):
            bot.answer_callback_query(call.id, "⌛ Ye button purana ho gaya. Data Files dobara kholo.", show_alert=True)
            return
        bot.clear_step_handler_by_chat_id(call.message.chat.id)
        _dbf_wait_drop(uid)
        if act == 'f':
            bot.answer_callback_query(call.id)
            return _dbf_show_card(call, ctx, ent)
        if act == 'd':
            return _dbf_download(call, ctx, ent)
        if act == 'p':
            bot.answer_callback_query(call.id)
            return _dbf_preview(call, ctx, ent)
        if act == 't':
            bot.answer_callback_query(call.id)
            return _dbf_preview(call, ctx, ent, table_idx=idx)
        if act == 'x':
            return _dbf_delete_ask(call, ctx, ent, tok)
        if act == 'xy':
            return _dbf_delete_do(call, ctx, ent)
        if act == 'r':
            full, err = _dbf_resolve(ctx, ent['rel'])
            if err:
                bot.answer_callback_query(call.id, "⚠️ Ye file ab nahi mili.", show_alert=True)
                return _dbf_show_list(call, ctx)
            return _dbf_upload_prompt(call, ctx, 'replace', ent['rel'])
        if act == 'rn':
            with DBF_LOCK:
                DBF_TOKENS.pop(tok, None)
            bot.answer_callback_query(call.id, "Kuch badla nahi.")
            return _dbf_show_list(call, ctx, note=ui_note("Replace cancel: purani file waisi hi hai."))
        if act == 'ry':
            bot.answer_callback_query(call.id)
            return _dbf_write_do(call, uid, uid, script, tok, call.message.chat.id)
    except (ValueError, IndexError):
        try:
            bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
        except Exception:
            pass
    except Exception as exc:
        logger.error("Error in dbf_callback for '%s': %s", call.data, redact_secrets(exc), exc_info=True)
        try:
            bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)
        except Exception:
            pass


def file_control_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id

        # Allow owner/admin to control any file, or user to control their own
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            logger.warning(f"User {requesting_user_id} tried to access file '{file_name}' of user {script_owner_id} without permission.")
            bot.answer_callback_query(call.id, "⚠️ You can only manage your own files.", show_alert=True)
            check_files_callback(call) # Show their own files
            return

        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == file_name for f in user_files_list):
            logger.warning(f"File '{file_name}' not found for user {script_owner_id} during control.")
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True)
            # If admin was viewing, this might be confusing. For now, just show their own.
            check_files_callback(call) 
            return

        bot.answer_callback_query(call.id) 
        is_running = is_bot_running(script_owner_id, file_name)
        status_text = '🟢 Running' if is_running else '🔴 Stopped'
        file_type = next((f[1] for f in user_files_list if f[0] == file_name), '?') 
        try:
            source_info = gh_read_sidecar(get_user_folder(script_owner_id), file_name)[0]
            bot.edit_message_text(
                _control_panel_text(script_owner_id, file_name, file_type, status_text, source_info['url'] if source_info else None),
                call.message.chat.id, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, is_running),
                parse_mode='HTML'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified (controls for {file_name})")
             else: raise 
    except (ValueError, IndexError) as ve:
        logger.error(f"Error parsing file control callback: {ve}. Data: '{call.data}'")
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in file_control_callback for data '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)

def _gate_button_start(call, owner_id, file_name, file_type):
    """Launch check for the Start / Restart buttons. Returns True when the file may start. Otherwise the
    panel is edited in place to show why (a running bot is left alone)."""
    allowed, note = launch_gate(owner_id, file_name, file_type, call.from_user.id)
    if allowed:
        return True
    try:
        bot.answer_callback_query(call.id, '🛡 Not started')
    except Exception as exc:
        logger.debug('answer_callback_query: %s', type(exc).__name__)
    running = is_bot_running(owner_id, file_name)
    try:
        bot.edit_message_text(ui_cap(f"{note}\n{ui_row('📄', 'File', file_name, code=True)}"), call.message.chat.id, call.message.message_id,
                              parse_mode='HTML', reply_markup=create_control_buttons(owner_id, file_name, running))
    except Exception as exc:
        logger.debug('Could not edit gate note: %s', type(exc).__name__)
        _safe_send(call.message.chat.id, note)
    return False


def start_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id # Where the admin/user gets the reply

        logger.info(f"Start request: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")

        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied to start this script.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == file_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        file_type = file_info[1]
        user_folder = get_user_folder(script_owner_id)
        file_path = os.path.join(user_folder, file_name)

        if not os.path.exists(file_path):
            bot.answer_callback_query(call.id, f"⚠️ File '{file_name}' is missing. Please upload it again.", show_alert=True)
            remove_user_file_db(script_owner_id, file_name); check_files_callback(call); return

        if is_bot_running(script_owner_id, file_name):
            bot.answer_callback_query(call.id, f"⚠️ Script '{file_name}' already running.", show_alert=True)
            try: bot.edit_message_reply_markup(chat_id_for_reply, call.message.message_id, reply_markup=create_control_buttons(script_owner_id, file_name, True))
            except Exception as e: logger.error(f"Error updating buttons (already running): {e}")
            return

        if not _gate_button_start(call, script_owner_id, file_name, file_type):
            return

        RESTART_STATE[_script_key(script_owner_id, file_name)] = {"attempts": 0, "manual_stop": False}
        bot.answer_callback_query(call.id, f"⏳ Attempting to start {file_name} for user {script_owner_id}...")

        # Pass call.message as message_obj_for_reply so feedback goes to the person who clicked
        if file_type == 'py':
            launcher = threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        elif file_type == 'js':
            launcher = threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        else:
             bot.send_message(chat_id_for_reply, ui_err('Unsupported File', ui_row('📄', 'File', file_name, code=True),
                                                        ui_row('🧩', 'Type', file_type)), parse_mode='HTML'); return 
        launcher.start()

        # The launcher first test-runs the script for about 5 seconds, so wait for it to finish.
        # Otherwise the panel keeps showing "Starting" with a Start button after the script is already up.
        launcher.join(timeout=LAUNCH_WAIT_SECONDS)
        time.sleep(0.5)
        is_now_running = is_bot_running(script_owner_id, file_name) 
        if is_now_running:
            status_text = '🟢 Running'
        elif launcher.is_alive():
            status_text = '🟡 Still starting (installing modules?). Open Check Files again in a moment'
        else:
            status_text = '🔴 Not running. See the message above or the logs'
        try:
            bot.edit_message_text(
                _control_panel_text(script_owner_id, file_name, file_type, status_text),
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, is_now_running), parse_mode='HTML'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified after starting {file_name}")
             else: raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing start callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid start command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in start_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error starting script.", show_alert=True)
        try: # Attempt to reset buttons to 'stopped' state on error
            _, script_owner_id_err_str, file_name_err = call.data.split('_', 2)
            script_owner_id_err = int(script_owner_id_err_str)
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=create_control_buttons(script_owner_id_err, file_name_err, False))
        except Exception as e_btn: logger.error(f"Failed to update buttons after start error: {e_btn}")

def scheduled_restart_toggle_callback(call):
    """Owner or admin: switch the scheduled restart on or off for one script."""
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True); return
    if not (call.from_user.id == script_owner_id or call.from_user.id in admin_ids):
        bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return
    if not any(f[0] == file_name for f in user_files.get(script_owner_id, [])):
        bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return
    key = _script_key(script_owner_id, file_name)
    set_scheduled_restart_optout(key, key not in SCHEDULED_RESTART_OPTOUT, call.from_user.id)
    file_control_callback(call)   # shows the control panel again with the new ON/OFF label


def stop_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Stop request: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == file_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        file_type = file_info[1] 
        script_key = f"{script_owner_id}_{file_name}"
        RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        autostart_clear(script_key)      # stopped by hand: it must not come back after a restart

        if not is_bot_running(script_owner_id, file_name): 
            bot.answer_callback_query(call.id, f"⚠️ Script '{file_name}' already stopped.", show_alert=True)
            try:
                 bot.edit_message_text(
                     _control_panel_text(script_owner_id, file_name, file_type, '🔴 Stopped'),
                     chat_id_for_reply, call.message.message_id,
                     reply_markup=create_control_buttons(script_owner_id, file_name, False), parse_mode='HTML')
            except Exception as e: logger.error(f"Error updating buttons (already stopped): {e}")
            return

        bot.answer_callback_query(call.id, f"⏳ Stopping {file_name} for user {script_owner_id}...")
        process_info = bot_scripts.get(script_key)
        if process_info:
            kill_process_tree(process_info)
            _forget_script(script_key); logger.info(f"Removed {script_key} from running after stop.")
        else: logger.warning(f"Script {script_key} running by psutil but not in bot_scripts dict.")

        try:
            bot.edit_message_text(
                _control_panel_text(script_owner_id, file_name, file_type, '🔴 Stopped'),
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, False), parse_mode='HTML'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified after stopping {file_name}")
             else: raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing stop callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid stop command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in stop_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error stopping script.", show_alert=True)

def restart_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Restart: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        file_info = next((f for f in user_files_list if f[0] == file_name), None)
        if not file_info:
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        file_type = file_info[1]; user_folder = get_user_folder(script_owner_id)
        file_path = os.path.join(user_folder, file_name); script_key = f"{script_owner_id}_{file_name}"

        if not os.path.exists(file_path):
            bot.answer_callback_query(call.id, f"⚠️ File '{file_name}' is missing. Please upload it again.", show_alert=True)
            remove_user_file_db(script_owner_id, file_name)
            _forget_script(script_key)
            check_files_callback(call); return

        if not _gate_button_start(call, script_owner_id, file_name, file_type):
            return

        bot.answer_callback_query(call.id, f"⏳ Restarting {file_name} for user {script_owner_id}...")
        # Mark it as manually stopped while the old process is killed, so the watchdog does not see the
        # kill as a crash (extra "stopped unexpectedly" message, possible second launch).
        RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        if is_bot_running(script_owner_id, file_name):
            logger.info(f"Restart: Stopping existing {script_key}...")
            process_info = bot_scripts.get(script_key)
            if process_info: kill_process_tree(process_info)
            _forget_script(script_key)
            time.sleep(1.5) 
        _reset_restart_state(script_owner_id, file_name)

        logger.info(f"Restart: Starting script {script_key}...")
        if file_type == 'py':
            launcher = threading.Thread(target=run_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        elif file_type == 'js':
            launcher = threading.Thread(target=run_js_script, args=(file_path, script_owner_id, user_folder, file_name, call.message))
        else:
             bot.send_message(chat_id_for_reply, ui_err('Unsupported File', ui_row('📄', 'File', file_name, code=True),
                                                        ui_row('🧩', 'Type', file_type)), parse_mode='HTML'); return
        launcher.start()

        launcher.join(timeout=LAUNCH_WAIT_SECONDS)
        time.sleep(0.5)
        is_now_running = is_bot_running(script_owner_id, file_name) 
        if is_now_running:
            status_text = '🟢 Running'
        elif launcher.is_alive():
            status_text = '🟡 Still starting (installing modules?). Open Check Files again in a moment'
        else:
            status_text = '🔴 Not running. See the message above or the logs'
        try:
            bot.edit_message_text(
                _control_panel_text(script_owner_id, file_name, file_type, status_text),
                chat_id_for_reply, call.message.message_id,
                reply_markup=create_control_buttons(script_owner_id, file_name, is_now_running), parse_mode='HTML'
            )
        except telebot.apihelper.ApiTelegramException as e:
             if "message is not modified" in str(e): logger.warning(f"Msg not modified (restart {file_name})")
             else: raise
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing restart callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid restart command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in restart_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error restarting.", show_alert=True)
        try:
            _, script_owner_id_err_str, file_name_err = call.data.split('_', 2)
            script_owner_id_err = int(script_owner_id_err_str)
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=create_control_buttons(script_owner_id_err, file_name_err, False))
        except Exception as e_btn: logger.error(f"Failed to update buttons after restart error: {e_btn}")

def delete_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Delete: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == file_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        bot.answer_callback_query(call.id, f"🗑️ Deleting {file_name} for user {script_owner_id}...")
        deleted_disk = _delete_user_file_core(script_owner_id, file_name, exclude_chat=chat_id_for_reply)
        if requesting_user_id != script_owner_id and requesting_user_id in admin_ids:
            _notify_owner_file_removed(script_owner_id, file_name)
        deleted_str = ", ".join(f"<code>{html_escape(f)}</code>" for f in deleted_disk) if deleted_disk else "associated files"
        try:
            bot.edit_message_text(
                ui_ok('File Deleted', ui_row('📄', 'File', file_name, code=True), ui_row('👤', 'Owner', script_owner_id, code=True),
                      ui_row('🗑️', 'Removed', ui_raw(deleted_str), bold=False)),
                chat_id_for_reply, call.message.message_id, reply_markup=create_main_menu_inline(call.from_user.id), parse_mode='HTML'
            )
        except Exception as e:
            logger.error(f"Error editing msg after delete: {e}")
            bot.send_message(chat_id_for_reply, ui_ok('File Deleted', ui_row('📄', 'File', file_name, code=True)), parse_mode='HTML',
                             reply_markup=create_main_menu_inline(call.from_user.id))
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing delete callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid delete command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in delete_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error deleting.", show_alert=True)

def logs_bot_callback(call):
    try:
        _, script_owner_id_str, file_name = call.data.split('_', 2)
        script_owner_id = int(script_owner_id_str)
        requesting_user_id = call.from_user.id
        chat_id_for_reply = call.message.chat.id

        logger.info(f"Logs: Requester={requesting_user_id}, Owner={script_owner_id}, File='{file_name}'")
        if not (requesting_user_id == script_owner_id or requesting_user_id in admin_ids):
            bot.answer_callback_query(call.id, "⚠️ Permission denied.", show_alert=True); return

        user_files_list = user_files.get(script_owner_id, [])
        if not any(f[0] == file_name for f in user_files_list):
            bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True); check_files_callback(call); return

        user_folder = get_user_folder(script_owner_id)
        log_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
        if not os.path.exists(log_path):
            bot.answer_callback_query(call.id, f"⚠️ No logs for '{file_name}'.", show_alert=True); return

        bot.answer_callback_query(call.id) 
        try:
            log_content = ""; file_size = os.path.getsize(log_path)
            max_log_kb = 100; max_tg_msg = 3500
            if file_size == 0: log_content = "(Log empty)"
            elif file_size > max_log_kb * 1024:
                 with open(log_path, 'rb') as f: f.seek(-max_log_kb * 1024, os.SEEK_END); log_bytes = f.read()
                 log_content = log_bytes.decode('utf-8', errors='ignore')
                 log_content = f"(Last {max_log_kb} KB)\n...\n" + log_content
            else:
                 with open(log_path, 'r', encoding='utf-8', errors='ignore') as f: log_content = f.read()

            if len(log_content) > max_tg_msg:
                log_content = log_content[-max_tg_msg:]
                first_nl = log_content.find('\n')
                if first_nl != -1: log_content = "...\n" + log_content[first_nl+1:]
                else: log_content = "...\n" + log_content 
            if not log_content.strip(): log_content = "(No visible content)"

            while len(html_escape(log_content)) > max_tg_msg:      # escaping can make the text longer
                log_content = log_content[int(len(log_content) * 0.8):]
            bot.send_message(chat_id_for_reply,
                             ui_msg('📜', 'Script Logs', ui_row('📄', 'File', file_name, code=True),
                                    ui_row('👤', 'Owner', script_owner_id, code=True),
                                    f"📡 Status: {ui_tag('active') if is_bot_running(script_owner_id, file_name) else ui_tag('stopped')}",
                                    ui_row('🕒', 'Last write', ui_ago(os.path.getmtime(log_path))),
                                    "👇 Tap to open the latest lines:",
                                    ui_expand(log_content, 2800),
                                    foot='Logs show what your script printed.'), parse_mode='HTML')
        except Exception as e:
            logger.error(f"Error reading/sending log {log_path}: {e}", exc_info=True)
            bot.send_message(chat_id_for_reply, ui_err('Logs Unavailable', ui_row('📄', 'File', file_name, code=True),
                                                       'Could not read the log right now.'), parse_mode='HTML')
    except (ValueError, IndexError) as e:
        logger.error(f"Error parsing logs callback '{call.data}': {e}")
        bot.answer_callback_query(call.id, "Error: Invalid logs command.", show_alert=True)
    except Exception as e:
        logger.error(f"Error in logs_bot_callback for '{call.data}': {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error fetching logs.", show_alert=True)

# --- Environment (.env) button: per-bot control panel ----------------------------
def _env_panel(owner_id, file_name, reveal=False):
    """Text + buttons of the Environment panel for one bot."""
    user_folder = get_user_folder(owner_id)
    env = load_bot_env(user_folder, file_name)
    lines = [ui_head('🔑', 'Environment'), ui_row('📄', 'File', file_name, code=True), ui_row('👤', 'Owner', owner_id, code=True),
             ui_row('📦', 'Saved variables', f"{len(env)}/{ENV_MAX_VARS}"), ""]
    if env:
        shown = []
        for key in sorted(env):
            shown.append(f"<code>{html_escape(key)}</code> = <code>{html_escape(_env_display_value(key, env[key], reveal))}</code>")
        text_tail = ("\n\nValues that look secret are partly hidden. Tap <b>Show Values</b> to see everything."
                     if not reveal else "\n\nShowing full values. Do not forward this message.")
        footer = text_tail + "\nChanges are used the next time this bot starts or restarts."
        body = "\n".join(shown)
        limit = 3800 - len("\n".join(lines)) - len(footer)
        if len(body) > limit:
            cut = body[:limit].rsplit("\n", 1)[0]
            body = cut + "\n…(more not shown)"
        lines.append(body)
        lines.append(footer)
    else:
        lines.append("No variables yet. Tap <b>Add / Update</b> and send them like a .env file, for example <code>BOT_TOKEN=123:abc</code>.")
    markup = NavMenu(row_width=2)
    markup.row(NavButton("➕ Add / Update", callback_data=f'enva_{owner_id}_{file_name}'),
               NavButton("🗑 Delete One", callback_data=f'envd_{owner_id}_{file_name}') if env else
               NavButton("🔄 Refresh", callback_data=f'envm_{owner_id}_{file_name}'))
    if env:
        view_btn = (NavButton("🙈 Hide Values", callback_data=f'envm_{owner_id}_{file_name}') if reveal
                    else NavButton("👁 Show Values", callback_data=f'envv_{owner_id}_{file_name}'))
        markup.row(view_btn, NavButton("🧹 Clear All", callback_data=f'envc_{owner_id}_{file_name}'))
    if is_bot_running(owner_id, file_name):
        markup.row(NavButton("🔄 Restart Now (apply changes)", callback_data=f'restart_{owner_id}_{file_name}'))
    markup.row(NavButton("🔙 Back to Controls", callback_data=f'file_{owner_id}_{file_name}'))
    return "\n".join(lines), markup


def _env_show_panel(call, owner_id, file_name, reveal=False):
    text, markup = _env_panel(owner_id, file_name, reveal)
    _edit_or_send(call, text, markup)


def _env_access_ok(call, owner_id, file_name):
    """Same rule as the other per-bot buttons: the bot's owner or an admin, and the bot must exist."""
    uid = call.from_user.id
    if not (uid == owner_id or uid in admin_ids):
        bot.answer_callback_query(call.id, "⚠️ You can only manage the environment of your own bots.", show_alert=True)
        return False
    if not any(item[0] == file_name for item in user_files.get(owner_id, [])):
        bot.answer_callback_query(call.id, "⚠️ File not found.", show_alert=True)
        return False
    if getattr(call.message.chat, 'type', 'private') != 'private':
        bot.answer_callback_query(call.id, "🔒 Open this in a private chat with me, so your secrets stay private.", show_alert=True)
        return False
    return True


def env_callback(call):
    """All buttons of the Environment panel (callback prefixes envm_ envv_ enva_ envd_ envk_ envc_ envy_)."""
    try:
        action = call.data.split('_', 1)[0]
        key_tag = None
        if action == 'envk':
            _, owner_str, key_tag, file_name = call.data.split('_', 3)
        else:
            _, owner_str, file_name = call.data.split('_', 2)
        owner_id = int(owner_str)
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, "Error: Invalid action data.", show_alert=True)
        return
    try:
        if not _env_access_ok(call, owner_id, file_name):
            return
        chat_id = call.message.chat.id
        user_folder = get_user_folder(owner_id)
        bot.clear_step_handler_by_chat_id(chat_id)   # leaving a half-finished "send variables" step
        if action in ('envm', 'envv'):
            bot.answer_callback_query(call.id)
            _env_show_panel(call, owner_id, file_name, reveal=(action == 'envv'))
        elif action == 'enva':
            bot.answer_callback_query(call.id)
            prompt = (f"➕ <b>Add / update variables</b> for <code>{html_escape(file_name)}</code>\n\n"
                      "Send me one line:\n<pre>KEY=VALUE</pre>"
                      "or several lines, like the inside of a .env file (you can also upload the .env file itself):\n"
                      "<pre>BOT_TOKEN=123456:abcdef\nADMIN_ID=12345\nDEBUG=true</pre>"
                      "A name that already exists is updated, new names are added. Lines starting with # are ignored. "
                      "If a value has spaces, put it in quotes.\n"
                      "I delete your message after saving so the secrets do not stay in the chat.")
            markup = NavMenu().add(
                NavButton("❌ Cancel", callback_data=f'envm_{owner_id}_{file_name}'))
            _edit_or_send(call, prompt, markup)
            bot.register_next_step_handler(call.message, _env_receive_input, owner_id, file_name, call.from_user.id)
        elif action == 'envd':
            env = load_bot_env(user_folder, file_name)
            bot.answer_callback_query(call.id)
            if not env:
                _env_show_panel(call, owner_id, file_name)
                return
            markup = NavMenu(row_width=2)
            shown, page, pages = _paginate(chat_id, 'envd' + _env_key_tag(f'{owner_id}/{file_name}'), sorted(env))
            markup.add(*[NavButton(f"🗑 {key}", callback_data=f'envk_{owner_id}_{_env_key_tag(key)}_{file_name}')
                         for key in shown])
            markup.pager('envd' + _env_key_tag(f'{owner_id}/{file_name}'), f'envd_{owner_id}_{file_name}', page, pages)
            markup.row(NavButton("🔙 Back", callback_data=f'envm_{owner_id}_{file_name}'))
            _edit_or_send(call, f"🗑 Which variable of <code>{html_escape(file_name)}</code> should be deleted?" + _page_note(page, pages), markup)
        elif action == 'envk':
            env = load_bot_env(user_folder, file_name)
            key = next((k for k in env if _env_key_tag(k) == key_tag), None)
            if key and delete_bot_env_key(user_folder, file_name, key):
                bot.answer_callback_query(call.id, f"🗑 {key} deleted.")
            else:
                bot.answer_callback_query(call.id, "That variable is already gone.")
            _env_show_panel(call, owner_id, file_name)
        elif action == 'envc':
            bot.answer_callback_query(call.id)
            markup = NavMenu()
            markup.row(NavButton("✅ Yes, delete all", callback_data=f'envy_{owner_id}_{file_name}'),
                       NavButton("❌ No", callback_data=f'envm_{owner_id}_{file_name}'))
            _edit_or_send(call, f"🧹 Delete <b>all</b> variables of <code>{html_escape(file_name)}</code>?", markup)
        elif action == 'envy':
            count = clear_bot_env(user_folder, file_name)
            bot.answer_callback_query(call.id, f"🧹 {count} variable(s) deleted.")
            _env_show_panel(call, owner_id, file_name)
        else:
            bot.answer_callback_query(call.id, "Unknown action.")
    except Exception as exc:
        logger.error("Error in env_callback for '%s': %s", call.data, redact_secrets(exc), exc_info=True)
        try:
            bot.answer_callback_query(call.id, "An error occurred.", show_alert=True)
        except Exception:
            pass


def _env_forget_message(message):
    """Best effort: remove the message that carried the secrets (works in private chats)."""
    try:
        bot.delete_message(message.chat.id, message.message_id)
        return True
    except Exception:
        return False


def _env_receive_input(message, owner_id, file_name, expected_uid):
    """Next message after Add / Update: text lines, or an uploaded .env file."""
    chat_id = message.chat.id
    uid = message.from_user.id if message.from_user else None
    try:
        if uid != expected_uid:
            return
        text = message.text if message.content_type == 'text' else None
        # A command or a menu button means the user moved on: hand it back to the normal handlers.
        if text and (text.startswith('/') or text in BUTTON_TEXT_TO_LOGIC):
            bot.process_new_messages([message])
            return
        if is_user_banned(uid) or not (uid == owner_id or uid in admin_ids) \
                or not any(item[0] == file_name for item in user_files.get(owner_id, [])):
            bot.send_message(chat_id, ui_warn('Not Available', 'That bot is not available for you any more.', foot='Nothing was changed.'), parse_mode='HTML')
            return
        if message.content_type == 'document':
            doc = message.document
            if (doc.file_size or 0) > ENV_MAX_FILE_BYTES:
                bot.send_message(chat_id, f"❌ That file is too big for an environment file (max {ENV_MAX_FILE_BYTES // 1024} KB). Nothing was changed.")
                return
            raw = bot.download_file(bot.get_file(doc.file_id).file_path)
            if len(raw) > ENV_MAX_FILE_BYTES:
                bot.send_message(chat_id, ui_err('File Too Big', 'That file is too big for an environment file.', foot='Nothing was changed.'), parse_mode='HTML')
                return
            try:
                text = raw.decode('utf-8-sig')
            except UnicodeDecodeError:
                bot.send_message(chat_id, ui_err('Could Not Read', 'I could not read that file as text. Send a plain text .env file.', foot='Nothing was changed.'), parse_mode='HTML')
                return
        elif text is None:
            bot.send_message(chat_id, ui_err('Text Needed', 'Please send text like KEY=VALUE, or a .env file.', foot='Nothing was changed.'), parse_mode='HTML')
            return
        if len(text) > ENV_MAX_FILE_BYTES:
            bot.send_message(chat_id, ui_err('Too Much Text', 'That is too much text.', foot='Nothing was changed.'), parse_mode='HTML')
            return

        pairs, problems = parse_env_text(text)
        result = []
        if pairs:
            try:
                added, updated, unchanged = update_bot_env(get_user_folder(owner_id), file_name, pairs)
            except ValueError as exc:
                bot.send_message(chat_id, f"❌ {html_escape(str(exc))} Nothing was changed.", parse_mode='HTML',
                                 reply_markup=_env_back_markup(owner_id, file_name))
                _env_forget_message(message)
                return
            if added:
                result.append("Added: " + ", ".join(f"<code>{html_escape(k)}</code>" for k in added))
            if updated:
                result.append("Updated: " + ", ".join(f"<code>{html_escape(k)}</code>" for k in updated))
            if unchanged:
                result.append("Already the same: " + ", ".join(f"<code>{html_escape(k)}</code>" for k in unchanged))
            head = f"✅ Saved {len(added) + len(updated)} change(s) for <code>{html_escape(file_name)}</code>."
        else:
            head = "❌ I found no valid KEY=VALUE line, so nothing was changed."
        if problems:
            result.append("Skipped lines:")
            for number, label, reason in problems[:10]:
                who = f" (<code>{html_escape(label)}</code>)" if label else ""
                result.append(f"• line {number}{who}: {html_escape(reason)}")
            if len(problems) > 10:
                result.append(f"• …and {len(problems) - 10} more")
        removed = _env_forget_message(message)
        tail = "\nYour message was deleted so the secrets do not stay in the chat." if removed else \
               "\nTip: delete your message yourself so the secrets do not stay in the chat."
        if pairs:
            tail += "\nRestart the bot to use the new values."
        bot.send_message(chat_id, head + ("\n" + "\n".join(result) if result else "") + tail, parse_mode='HTML',
                         reply_markup=_env_back_markup(owner_id, file_name))
    except Exception as exc:
        logger.error("Error saving environment for %s: %s", file_name, redact_secrets(exc), exc_info=True)
        try:
            bot.send_message(chat_id, ui_warn('Something Went Wrong', 'Something went wrong while saving.', foot='Please try again.'), parse_mode='HTML')
        except Exception:
            pass


def _env_back_markup(owner_id, file_name):
    return NavMenu().add(
        NavButton("🔑 Open Environment", callback_data=f'envm_{owner_id}_{file_name}'))


def speed_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, chat_id, call.message.message_id, reply_markup=markup, parse_mode='HTML')
        except Exception:
            bot.send_message(chat_id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    start_cb_ping_time = time.time() 
    try:
        bot.edit_message_text("🏃 Testing speed...", chat_id, call.message.message_id)
        bot.send_chat_action(chat_id, 'typing') 
        response_time = round((time.time() - start_cb_ping_time) * 1000, 2)
        status = "🔓 Unlocked" if not bot_locked else "🔒 Locked"
        if user_id == OWNER_ID: user_level = "👑 Owner"
        elif user_id in admin_ids: user_level = "🛡️ Admin"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > datetime.now(): user_level = "⭐ Premium"
        else: user_level = "🆓 Free User"
        speed_msg = (f"⚡ Bot Speed & Status:\n\n⏱️ API Response Time: {response_time} ms\n"
                     f"🚦 Bot Status: {status}\n"
                     f"👤 Your Level: {user_level}")
        bot.answer_callback_query(call.id) 
        bot.edit_message_text(speed_msg, chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id))
    except Exception as e:
         logger.error(f"Error during speed test (cb): {e}", exc_info=True)
         bot.answer_callback_query(call.id, "Error in speed test.", show_alert=True)
         try: bot.edit_message_text("〽️ Main Menu", chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id))
         except Exception: pass

def back_to_main_callback(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    
    # Check if user is banned
    if is_user_banned(user_id):
        bot.answer_callback_query(call.id, "❌ You are banned from using this bot.", show_alert=True)
        return
    
    # Check mandatory subscription first
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    if not is_subscribed and user_id not in admin_ids:
        subscription_message, markup = create_subscription_check_message(not_joined)
        bot.answer_callback_query(call.id)
        try:
            bot.edit_message_text(subscription_message, chat_id, call.message.message_id, reply_markup=markup, parse_mode='HTML')
        except Exception:
            bot.send_message(chat_id, subscription_message, reply_markup=markup, parse_mode='HTML')
        return
        
    file_limit = get_user_file_limit(user_id)
    current_files = get_user_file_count(user_id)
    limit_str = ui_limit(file_limit)
    days_left = None
    if user_id == OWNER_ID: user_status = "👑 Owner"
    elif user_id in admin_ids: user_status = "🛡️ Admin"
    elif user_id in user_subscriptions:
        expiry_date = user_subscriptions[user_id].get('expiry')
        if expiry_date and expiry_date > datetime.now():
            user_status = "⭐ Premium"; days_left = (expiry_date - datetime.now()).days
        else: user_status = "🆓 Free User (Expired Sub)" # Will be cleaned up by welcome if not already
    else: user_status = "🆓 Free User"
    main_menu_text = _main_menu_text(call.from_user.first_name, user_id, user_status, days_left, current_files, limit_str, back=True)
    try:
        bot.answer_callback_query(call.id)
        bot.edit_message_text(main_menu_text, chat_id, call.message.message_id,
                              reply_markup=create_main_menu_inline(user_id), parse_mode='HTML')
    except telebot.apihelper.ApiTelegramException as e:
         if "message is not modified" in str(e): logger.warning("Msg not modified (back_to_main).")
         else: logger.error(f"API error on back_to_main: {e}")
    except Exception as e: logger.error(f"Error handling back_to_main: {e}", exc_info=True)

# --- Admin Callback Implementations (for Inline Buttons) ---
def subscription_management_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(ui_msg('💳', 'Subscription Management', '💎 Add, remove or check premium access.', foot='Pick an action below.'),
                              call.message.chat.id, call.message.message_id, reply_markup=create_subscription_menu(), parse_mode='HTML')
    except Exception as e: logger.error(f"Error showing sub menu: {e}")

def stats_callback(call): # Called by user and admin
    bot.answer_callback_query(call.id)
    _logic_statistics(call.message) 
    try:
        bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id,
                                      reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception as e:
        logger.error(f"Error updating menu after stats_callback: {e}")

def lock_bot_callback(call):
    global bot_locked; bot_locked = True
    logger.warning(f"Bot locked by Admin {call.from_user.id}")
    bot.answer_callback_query(call.id, "🔒 Bot locked.")
    bot.send_message(call.message.chat.id, ui_ok('Bot Locked', ui_row('🔒', 'Status', 'Locked'),
                                                 foot='Ab sirf admins use kar sakte hain.'),
                     parse_mode='HTML', reply_markup=create_main_menu_inline(call.from_user.id))

def unlock_bot_callback(call):
    global bot_locked; bot_locked = False
    logger.warning(f"Bot unlocked by Admin {call.from_user.id}")
    bot.answer_callback_query(call.id, "🔓 Bot unlocked.")
    bot.send_message(call.message.chat.id, ui_ok('Bot Unlocked', ui_row('🔓', 'Status', 'Unlocked'),
                                                 foot='Sab users ab bot use kar sakte hain.'),
                     parse_mode='HTML', reply_markup=create_main_menu_inline(call.from_user.id))

def run_all_scripts_callback(call): # Added
    _logic_run_all_scripts(call) # Pass the call object

def broadcast_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "📢 Send message to broadcast.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_broadcast_message)

BROADCAST_PENDING = {}          # (chat_id, original message id) -> the admin's message to send; a key press has no reply_to_message
BROADCAST_PENDING_MAX = 20


def process_broadcast_message(message):
    user_id = message.from_user.id
    if user_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, ui_info('Cancelled', 'Broadcast cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML'); return

    broadcast_content = message.text # Can also handle photos, videos etc. if message.content_type is checked
    if not broadcast_content and not (message.photo or message.video or message.document or message.sticker or message.voice or message.audio): # If no text and no other media
         bot.reply_to(message, ui_warn('Not Allowed', 'Cannot broadcast empty message.', foot='Send text or media, or /cancel.'), parse_mode='HTML')
         msg = bot.send_message(message.chat.id, "📢 Send broadcast message or /cancel.")
         bot.register_next_step_handler(msg, process_broadcast_message)
         return

    target_count = len(active_users)
    BROADCAST_PENDING[(message.chat.id, message.message_id)] = message
    while len(BROADCAST_PENDING) > BROADCAST_PENDING_MAX:
        BROADCAST_PENDING.pop(next(iter(BROADCAST_PENDING)), None)
    markup = NavMenu()
    markup.row(NavButton("✅ Confirm & Send", callback_data=f"confirm_broadcast_{message.message_id}"),
               NavButton("❌ Cancel", callback_data="cancel_broadcast"))

    preview_text = broadcast_content[:1000].strip().replace('`' * 3, "'" * 3) if broadcast_content else "(Media message)"
    bot.reply_to(message, ui_msg('📢', 'Confirm Broadcast',
                                 ui_row('👥', 'Target users', ui_num(target_count)),
                                 f"📡 Status: {ui_tag('warn', 'WAITING FOR CONFIRM')}",
                                 ui_section('👁️', 'Preview'),
                                 ui_expand(preview_text, 900, tail=False),
                                 foot='Tap Confirm & Send to go ahead, or Cancel.'),
                 reply_markup=markup, parse_mode='HTML')

def handle_confirm_broadcast(call):
    user_id = call.from_user.id
    chat_id = call.message.chat.id
    if user_id not in admin_ids: bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True); return
    try:
        original_message = call.message.reply_to_message
        if not original_message:
            try:
                key = (chat_id, int(call.data.rsplit('_', 1)[1]))
            except (ValueError, IndexError, AttributeError):
                key = None
            original_message = BROADCAST_PENDING.pop(key, None) if key else None
        if not original_message: raise ValueError("Could not retrieve original message.")

        # Check content type and get content
        broadcast_text = None
        broadcast_photo_id = None
        broadcast_video_id = None
        broadcast_document_id = None
        broadcast_audio_id = None
        broadcast_voice_id = None
        broadcast_sticker_id = None

        if original_message.text:
            broadcast_text = original_message.text
        elif original_message.photo:
            broadcast_photo_id = original_message.photo[-1].file_id # Get highest quality
        elif original_message.video:
            broadcast_video_id = original_message.video.file_id
        elif original_message.document:
            broadcast_document_id = original_message.document.file_id
        elif original_message.audio:
            broadcast_audio_id = original_message.audio.file_id
        elif original_message.voice:
            broadcast_voice_id = original_message.voice.file_id
        elif original_message.sticker:
            broadcast_sticker_id = original_message.sticker.file_id
        else:
            raise ValueError("Message has no text or supported media for broadcast.")

        bot.answer_callback_query(call.id, "🚀 Starting broadcast...")
        status = bot.edit_message_text(ui_wait('Broadcasting', f'Sending to {len(active_users)} users, please wait...'),
                                       chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id), parse_mode='HTML')
        status_id = getattr(status, 'message_id', None)
        bc_pm = None
        if isinstance(status_id, int) and status_id > 0:       # animate the status message that is now on screen
            try:
                bc_pm = ui_anim(chat_id, 'Broadcasting', f'Sending to {len(active_users)} users, please wait...',
                                message_id=status_id, done=0, total=len(active_users))
            except Exception:
                logger.exception("Could not start the broadcast progress message")
                bc_pm = None
        # Pass all potential content types to execute_broadcast
        thread = threading.Thread(name='broadcast', daemon=True, target=execute_broadcast, args=(
            broadcast_text, broadcast_photo_id, broadcast_video_id,
            original_message.caption if (broadcast_photo_id or broadcast_video_id or broadcast_document_id or broadcast_audio_id or broadcast_voice_id) else None,
            chat_id, broadcast_document_id, broadcast_audio_id, broadcast_voice_id, broadcast_sticker_id, bc_pm))
        thread.start()
    except ValueError as ve: 
        logger.error(f"Error retrieving msg for broadcast confirm: {ve}")
        bot.edit_message_text(ui_err('Broadcast Not Started', 'The message to send could not be found. Please start the broadcast again.'), chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id))
    except Exception as e:
        logger.error(f"Error in handle_confirm_broadcast: {e}", exc_info=True)
        bot.edit_message_text(ui_err('Broadcast Not Sent', 'An unexpected error stopped the broadcast.', foot='Nothing was sent. Please try again.'), chat_id, call.message.message_id, reply_markup=create_main_menu_inline(user_id), parse_mode='HTML')

def handle_cancel_broadcast(call):
    bot.answer_callback_query(call.id, "Broadcast cancelled.")
    try:
        BROADCAST_PENDING.pop((call.message.chat.id, int(getattr(call, 'data', '').rsplit('_', 1)[1])), None)
    except Exception:
        pass
    bot.delete_message(call.message.chat.id, call.message.message_id)
    try:
        bot.send_message(call.message.chat.id, "❎ Broadcast cancelled.", reply_markup=create_main_menu_inline(call.from_user.id))
    except Exception:
        logger.exception("Could not restore the menu after cancelling a broadcast")
    # Optionally delete the original message too if call.message.reply_to_message exists
    if call.message.reply_to_message:
        try: bot.delete_message(call.message.chat.id, call.message.reply_to_message.message_id)
        except Exception as exc: logger.debug(f"Could not delete the original message: {exc}")

def _broadcast_send_one(user_id_bc, broadcast_text, photo_id, video_id, caption, document_id, audio_id, voice_id, sticker_id):
    """Send one broadcast item. Rate limits and bad formatting are handled inside SafeTeleBot."""
    cap = caption[:1024] if caption else None  # Telegram caption limit
    pm = 'Markdown' if cap else None
    if broadcast_text:
        bot.send_message(user_id_bc, broadcast_text[:4096], parse_mode='Markdown', ui_raw=True)
    elif photo_id:
        bot.send_photo(user_id_bc, photo_id, caption=cap, parse_mode=pm)
    elif video_id:
        bot.send_video(user_id_bc, video_id, caption=cap, parse_mode=pm)
    elif document_id:
        bot.send_document(user_id_bc, document_id, caption=cap, parse_mode=pm)
    elif audio_id:
        bot.send_audio(user_id_bc, audio_id, caption=cap, parse_mode=pm)
    elif voice_id:
        bot.send_voice(user_id_bc, voice_id, caption=cap, parse_mode=pm)
    elif sticker_id:
        bot.send_sticker(user_id_bc, sticker_id)
    else:
        raise ValueError("Nothing to broadcast")


def execute_broadcast(broadcast_text, photo_id, video_id, caption, admin_chat_id, document_id=None, audio_id=None, voice_id=None, sticker_id=None, progress=None):
    sent_count = 0; failed_count = 0; blocked_count = 0
    start_exec_time = time.time()
    with STATE_LOCK:
        users_to_broadcast = list(active_users)
    total_users = len(users_to_broadcast)
    if progress is not None:
        progress.update(0, total_users, f'Sending to {total_users} users, please wait...')
    logger.info("Executing broadcast to %s users.", total_users)
    batch_size = 25; delay_batches = 1.5
    blocked_markers = ("bot was blocked", "user is deactivated", "chat not found", "kicked from", "restricted",
                       "have no rights", "forbidden")

    for i, user_id_bc in enumerate(users_to_broadcast):
        if SHUTDOWN_EVENT.is_set():
            logger.warning("Broadcast interrupted by shutdown at %s/%s", i, total_users)
            break
        try:
            _broadcast_send_one(user_id_bc, broadcast_text, photo_id, video_id, caption,
                                document_id, audio_id, voice_id, sticker_id)
            sent_count += 1
        except telebot.apihelper.ApiTelegramException as e:
            err_desc = str(e).lower()
            if any(m in err_desc for m in blocked_markers):
                logger.warning("Broadcast failed to %s: user blocked/inactive.", user_id_bc)
                blocked_count += 1
            else:
                logger.error("Broadcast failed to %s: %s", user_id_bc, e)
                failed_count += 1
        except Exception as e:
            logger.error("Unexpected error broadcasting to %s: %s", user_id_bc, e)
            failed_count += 1

        if progress is not None:
            progress.update(i + 1, total_users, f"Sent {sent_count}  |  Failed {failed_count}  |  Blocked {blocked_count}")
        if (i + 1) % batch_size == 0 and i < total_users - 1:
            logger.info("Broadcast batch %s sent. Sleeping %ss...", i // batch_size + 1, delay_batches)
            SHUTDOWN_EVENT.wait(delay_batches)
        elif i % 5 == 0:
            SHUTDOWN_EVENT.wait(0.2)

    duration = round(time.time() - start_exec_time, 2)
    logger.info("Broadcast complete | sent %s | failed %s | blocked %s | targets %s | %ss",
                sent_count, failed_count, blocked_count, total_users, duration)
    result_msg = ui_ok('Broadcast Complete',
                       f"📡 Status: {ui_tag('ok', 'DELIVERED') if sent_count and not failed_count else ui_tag('warn', 'PARTIAL' if sent_count else 'NOT DELIVERED')}",
                       ui_row('✅', 'Sent', sent_count),
                       ui_row('❌', 'Failed', failed_count),
                       ui_row('🚫', 'Blocked / inactive', blocked_count),
                       ui_row('👥', 'Targets', total_users),
                       f"<code>{ui_bar(sent_count, total_users)}</code> delivered",
                       ui_row('⏱️', 'Duration', f'{duration}s'),
                       foot='Failed or blocked users are skipped, nothing to redo.' if (failed_count or blocked_count) else 'Everyone active got your message.',
                       progress=(sent_count / total_users) if total_users else None)
    try:
        menu = None
        try:                                     # fresh keyboard, so the numbers on it are the real ones after the broadcast
            menu = _nav_live_markup(admin_chat_id, admin_chat_id, force=True)
        except Exception:
            logger.exception("Could not build the menu for the broadcast result")
        _say_via(progress, admin_chat_id, result_msg, menu)
    except Exception as e:
        logger.error("Failed to send broadcast result to admin %s: %s", admin_chat_id, e)
    finally:
        if progress is not None and not progress._done:
            progress.fail()

def admin_panel_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(ui_msg('👑', 'Admin Panel', '🛡️ Manage admins.', foot='Some owner actions may be restricted.'),
                              call.message.chat.id, call.message.message_id, reply_markup=create_admin_panel(), parse_mode='HTML')
    except Exception as e: logger.error(f"Error showing admin panel: {e}")

# --- Shared admin screen helper ---
def _adm_show(call, text, kb):
    try:
        bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=kb)
    except Exception:
        _safe_send(call.message.chat.id, text, reply_markup=kb)


def add_admin_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, ui_msg('👑', 'Add Admin', 'Send the numeric user ID to promote.', foot='Send /cancel to abort.'), parse_mode='HTML')
    bot.register_next_step_handler(msg, process_add_admin_id)

def process_add_admin_id(message):
    owner_id_check = message.from_user.id 
    if owner_id_check != OWNER_ID: bot.reply_to(message, ui_warn('Owner Only', 'Only the owner can do this.', foot='Ask the owner if you need it.'), parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, ui_info('Cancelled', 'Admin promotion cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML'); return
    try:
        new_admin_id = int(message.text.strip())
        if new_admin_id <= 0 or new_admin_id >= 2 ** 63: raise ValueError("ID must be positive")
        if new_admin_id == OWNER_ID: bot.reply_to(message, ui_warn('Already Done', 'That user is already the Owner.', foot='Nothing to change.'), parse_mode='HTML'); return
        if new_admin_id in admin_ids: bot.reply_to(message, ui_warn('Already Admin', ui_row('👤', 'User', new_admin_id, code=True), f"🛡️ Role: {ui_tag('admin')}", foot='Nothing to change.'), parse_mode='HTML'); return
        add_admin_db(new_admin_id, owner_id_check) 
        logger.warning(f"Admin {new_admin_id} added by Owner {owner_id_check}.")
        bot.reply_to(message, ui_ok('Admin Added', ui_row('👤', 'User', new_admin_id, code=True), f"🛡️ Role: {ui_tag('admin')}", foot='The user has been told about it.'), parse_mode='HTML')
        try: bot.send_message(new_admin_id, ui_ok('You Are Now An Admin', f"🛡️ Role: {ui_tag('admin')}", foot='Open the Admin Panel from the menu.'), parse_mode='HTML')
        except Exception as e: logger.error(f"Failed to notify new admin {new_admin_id}: {e}")
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'Send a numeric user ID.', foot='or send /cancel'), parse_mode='HTML')
        msg = bot.send_message(message.chat.id, ui_msg('👑', 'Add Admin', 'Send the numeric user ID to promote.', foot='Or send /cancel.'), parse_mode='HTML')
        bot.register_next_step_handler(msg, process_add_admin_id)
    except Exception as e: logger.error(f"Error processing add admin: {e}", exc_info=True); bot.reply_to(message, ui_err('Something Went Wrong', 'That did not work. Nothing was changed, please try again.'), parse_mode='HTML')

def remove_admin_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, ui_msg('👑', 'Remove Admin', 'Send the numeric user ID of the admin to remove.', foot='Send /cancel to abort.'), parse_mode='HTML')
    bot.register_next_step_handler(msg, process_remove_admin_id)

def process_remove_admin_id(message):
    owner_id_check = message.from_user.id
    if owner_id_check != OWNER_ID: bot.reply_to(message, ui_warn('Owner Only', 'Only the owner can do this.', foot='Ask the owner if you need it.'), parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, ui_info('Cancelled', 'Admin removal cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML'); return
    try:
        admin_id_remove = int(message.text.strip()) # Renamed
        if admin_id_remove <= 0: raise ValueError("ID must be positive")
        if admin_id_remove == OWNER_ID: bot.reply_to(message, ui_warn('Not Allowed', 'The owner cannot remove themselves.', foot='Pick a different admin.'), parse_mode='HTML'); return
        if admin_id_remove not in admin_ids: bot.reply_to(message, ui_warn('Not An Admin', ui_row('👤', 'User', admin_id_remove, code=True), foot='Nothing to remove.'), parse_mode='HTML'); return
        if remove_admin_db(admin_id_remove): 
            logger.warning(f"Admin {admin_id_remove} removed by Owner {owner_id_check}.")
            bot.reply_to(message, ui_ok('Admin Removed', ui_row('👤', 'User', admin_id_remove, code=True), f"🛡️ Role: {ui_tag('free', 'USER')}", foot='The user has been told about it.'), parse_mode='HTML')
            try: bot.send_message(admin_id_remove, ui_info('Admin Role Ended', f"🛡️ Role: {ui_tag('free', 'USER')}", foot='You can still use the bot as a normal user.'), parse_mode='HTML')
            except Exception as e: logger.error(f"Failed to notify removed admin {admin_id_remove}: {e}")
        else: bot.reply_to(message, ui_err('Action Failed', ui_row('👤', 'User', admin_id_remove, code=True), 'Failed to remove this admin. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'Send a numeric user ID.', foot='or send /cancel'), parse_mode='HTML')
        msg = bot.send_message(message.chat.id, ui_msg('👑', 'Remove Admin', 'Send the numeric ID of the admin to remove.', foot='Or send /cancel.'), parse_mode='HTML')
        bot.register_next_step_handler(msg, process_remove_admin_id)
    except Exception as e: logger.error(f"Error processing remove admin: {e}", exc_info=True); bot.reply_to(message, ui_err('Something Went Wrong', 'That did not work. Nothing was changed, please try again.'), parse_mode='HTML')

def list_admins_callback(call):
    bot.answer_callback_query(call.id)
    try:
        admin_list_str = "\n".join(f"- <code>{aid}</code> {'(Owner)' if aid == OWNER_ID else ''}" for aid in sorted(list(admin_ids)))
        if not admin_list_str: admin_list_str = "(No Owner/Admins configured!)"
        text = f"👑 Current Admins ({len(admin_ids)}):\n\n{admin_list_str}"
        if len(text) <= 3900:
            bot.edit_message_text(text, call.message.chat.id, call.message.message_id,
                                  reply_markup=create_admin_panel(), parse_mode='HTML')
        else:                                    # very long list: several messages, the keyboard on the last one
            _send_long(call.message.chat.id, text, reply_markup=create_admin_panel(), parse_mode='HTML')
    except Exception as e: logger.error(f"Error listing admins: {e}")

def add_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID & days (e.g., `12345678 30`).\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_add_subscription_details)

def process_add_subscription_details(message):
    admin_id_check = message.from_user.id 
    if admin_id_check not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, ui_info('Cancelled', 'Sub add cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML'); return
    try:
        parts = message.text.split();
        if len(parts) != 2: raise ValueError("Incorrect format")
        sub_user_id = int(parts[0].strip()); days = int(parts[1].strip())
        if sub_user_id <= 0 or days <= 0: raise ValueError("User ID/days must be positive")

        current_expiry = user_subscriptions.get(sub_user_id, {}).get('expiry')
        start_date_new_sub = datetime.now() # Renamed
        if current_expiry and current_expiry > start_date_new_sub: start_date_new_sub = current_expiry
        new_expiry = start_date_new_sub + timedelta(days=days)
        save_subscription(sub_user_id, new_expiry)

        logger.info(f"Sub for {sub_user_id} by admin {admin_id_check}. Expiry: {new_expiry:%Y-%m-%d}")
        bot.reply_to(message, ui_ok('Subscription Added', ui_row('👤', 'User', sub_user_id, code=True), f"⭐ Plan: {ui_tag('premium')}", ui_row('➕', 'Added', f'{days} days'), ui_row('📅', 'New expiry', f'{new_expiry:%Y-%m-%d}'), foot='The user has been told about it.'), parse_mode='HTML')
        try: bot.send_message(sub_user_id, ui_ok('Premium Activated', f"⭐ Plan: {ui_tag('premium')}", ui_row('➕', 'Added', f'{days} days'), ui_row('📅', 'Expires', f'{new_expiry:%Y-%m-%d}'), ui_row('⏳', 'Days left', ui_num(max(0, (new_expiry - datetime.now()).days))), foot='Enjoy more slots. Open My Files to upload.'), parse_mode='HTML')
        except Exception as e: logger.error(f"Failed to notify {sub_user_id} of new sub: {e}")
    except ValueError as e:
        bot.reply_to(message, ui_warn('Invalid Input', 'Please send a user ID and a number of days.', ui_row('✍️', 'Format', 'ID days', code=True), foot='or send /cancel'), parse_mode='HTML')
        msg = bot.send_message(message.chat.id, "💳 Enter User ID & days, or /cancel.")
        bot.register_next_step_handler(msg, process_add_subscription_details)
    except Exception as e: logger.error(f"Error processing add sub: {e}", exc_info=True); bot.reply_to(message, ui_err('Something Went Wrong', 'That did not work. Nothing was changed, please try again.'), parse_mode='HTML')

def remove_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID to remove sub.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_remove_subscription_id)

def process_remove_subscription_id(message):
    admin_id_check = message.from_user.id
    if admin_id_check not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, ui_info('Cancelled', 'Sub removal cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML'); return
    try:
        sub_user_id_remove = int(message.text.strip()) # Renamed
        if sub_user_id_remove <= 0: raise ValueError("ID must be positive")
        if sub_user_id_remove not in user_subscriptions:
            bot.reply_to(message, ui_warn('No Subscription', ui_row('👤', 'User', sub_user_id_remove, code=True), 'No active subscription found.'), parse_mode='HTML'); return
        remove_subscription_db(sub_user_id_remove) 
        logger.warning(f"Sub removed for {sub_user_id_remove} by admin {admin_id_check}.")
        bot.reply_to(message, ui_ok('Subscription Removed', ui_row('👤', 'User', sub_user_id_remove, code=True)), parse_mode='HTML')
        try: bot.send_message(sub_user_id_remove, ui_info('Premium Ended', f"⭐ Plan: {ui_tag('free')}", 'Your Premium was removed by an admin.', foot='Your files are safe. Contact the owner to renew.'), parse_mode='HTML')
        except Exception as e: logger.error(f"Failed to notify {sub_user_id_remove} of sub removal: {e}")
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'Send a numeric user ID.', foot='or send /cancel'), parse_mode='HTML')
        msg = bot.send_message(message.chat.id, "💳 Enter User ID to remove sub from, or /cancel.")
        bot.register_next_step_handler(msg, process_remove_subscription_id)
    except Exception as e: logger.error(f"Error processing remove sub: {e}", exc_info=True); bot.reply_to(message, ui_err('Something Went Wrong', 'That did not work. Nothing was changed, please try again.'), parse_mode='HTML')

def check_subscription_init_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "💳 Enter User ID to check sub.\n/cancel to abort.")
    bot.register_next_step_handler(msg, process_check_subscription_id)

def process_check_subscription_id(message):
    admin_id_check = message.from_user.id
    if admin_id_check not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel': bot.reply_to(message, ui_info('Cancelled', 'Sub check cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML'); return
    try:
        sub_user_id_check = int(message.text.strip()) # Renamed
        if sub_user_id_check <= 0: raise ValueError("ID must be positive")
        if sub_user_id_check in user_subscriptions:
            expiry_dt = user_subscriptions[sub_user_id_check].get('expiry')
            if expiry_dt:
                if expiry_dt > datetime.now():
                    days_left = (expiry_dt - datetime.now()).days
                    bot.reply_to(message, ui_ok('Active Subscription', ui_row('👤', 'User', sub_user_id_check, code=True), f"⭐ Plan: {ui_tag('premium')}", ui_row('📅', 'Expires', f'{expiry_dt:%Y-%m-%d %H:%M}'), ui_row('⏳', 'Days left', ui_num(days_left))), parse_mode='HTML')
                else:
                    bot.reply_to(message, ui_warn('Subscription Expired', ui_row('👤', 'User', sub_user_id_check, code=True), f"⌛ Plan: {ui_tag('expired')}", ui_row('📅', 'Expired on', f'{expiry_dt:%Y-%m-%d %H:%M}')), parse_mode='HTML')
                    remove_subscription_db(sub_user_id_check) # Clean up
            else: bot.reply_to(message, ui_warn('Expiry Missing', ui_row('👤', 'User', sub_user_id_check, code=True), 'In the subscription list, but no expiry date. Re-add if needed.'), parse_mode='HTML')
        else: bot.reply_to(message, ui_info('No Subscription', ui_row('👤', 'User', sub_user_id_check, code=True), 'No active subscription record.'), parse_mode='HTML')
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'Send a numeric user ID.', foot='or send /cancel'), parse_mode='HTML')
        msg = bot.send_message(message.chat.id, "💳 Enter User ID to check, or /cancel.")
        bot.register_next_step_handler(msg, process_check_subscription_id)
    except Exception as e: logger.error(f"Error processing check sub: {e}", exc_info=True); bot.reply_to(message, ui_err('Something Went Wrong', 'That did not work. Nothing was changed, please try again.'), parse_mode='HTML')

# --- User Management Callbacks ---
def user_management_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(ui_msg('👥', 'User Management', 'Select an action below.'), call.message.chat.id,
                              call.message.message_id, reply_markup=create_user_management_menu(), parse_mode='HTML')
    except Exception as e: logger.error(f"Error showing user management menu: {e}")

def ban_user_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, ui_msg('🚫', 'Ban User', 'Send the user ID and a reason.', 'Example: <code>12345678 Spamming</code>', foot='Send /cancel to cancel.'), parse_mode='HTML')
    bot.register_next_step_handler(msg, process_ban_user)

def process_ban_user(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Ban cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    
    try:
        parts = message.text.split()
        if len(parts) < 2:
            bot.reply_to(message, ui_warn('Invalid Format', ui_row('✍️', 'Format', 'user_id reason', code=True), ui_row('💡', 'Example', '12345678 Spamming', code=True)), parse_mode='HTML')
            return
        
        user_id = int(parts[0])
        reason = ' '.join(parts[1:])
        
        if user_id <= 0: raise ValueError("ID must be positive")
        if user_id == OWNER_ID: bot.reply_to(message, ui_warn('Not Allowed', 'Cannot ban owner.', foot='Pick a different user.'), parse_mode='HTML'); return
        if user_id in admin_ids: bot.reply_to(message, ui_warn('Not Allowed', 'Cannot ban admin.', foot='Pick a different user.'), parse_mode='HTML'); return
        
        if ban_user_db(user_id, reason, admin_id):
            bot.reply_to(message, ui_ok('User Banned', ui_row('👤', 'User', user_id, code=True), ui_row('📝', 'Reason', reason)), parse_mode='HTML')
            # Stop all scripts for banned user
            autostart_clear(owner_id=user_id)
            for file_name, _ in user_files.get(user_id, []):
                script_key = f"{user_id}_{file_name}"
                stopped_info = _forget_script(script_key)
                if stopped_info:
                    kill_process_tree(stopped_info)
            
            try:
                bot.send_message(user_id, ui_err('Account Banned', f"🚫 Status: {ui_tag('banned')}", 'You can no longer use this bot.', ui_row('📝', 'Reason', reason), foot='Think this is a mistake? Contact the owner.'), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Failed to notify banned user {user_id}: {e}")
        else:
            bot.reply_to(message, ui_err('Action Failed', 'Failed to ban user. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
            
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error banning user: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Action Failed', ui_user_error(e)), parse_mode='HTML')

def unban_user_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, ui_msg('✅', 'Unban User', 'Send the user ID to unban.', foot='Send /cancel to cancel.'), parse_mode='HTML')
    bot.register_next_step_handler(msg, process_unban_user)

def process_unban_user(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Unban cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        
        if user_id not in banned_users:
            bot.reply_to(message, ui_info('Not Banned', ui_row('👤', 'User', user_id, code=True), 'This user is not banned.'), parse_mode='HTML')
            return
        
        if unban_user_db(user_id):
            bot.reply_to(message, ui_ok('User Unbanned', ui_row('👤', 'User', user_id, code=True)), parse_mode='HTML')
            try:
                bot.send_message(user_id, ui_ok('Ban Lifted', 'You can now use the bot again.'), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Failed to notify unbanned user {user_id}: {e}")
        else:
            bot.reply_to(message, ui_err('Action Failed', 'Failed to unban user. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
            
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error unbanning user: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Action Failed', ui_user_error(e)), parse_mode='HTML')

def user_info_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "👤 Enter User ID to get info\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_user_info)

def process_user_info(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Info request cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        
        # Gather user information
        rows = [ui_row('🆔', 'User ID', user_id, code=True)]
        if user_id == OWNER_ID:
            rows.append(ui_row('👑', 'Status', 'Owner'))
        elif user_id in admin_ids:
            rows.append(ui_row('🛡️', 'Status', 'Admin'))
        elif user_id in banned_users:
            rows.append(ui_row('🚫', 'Status', 'Banned'))
        elif user_id in user_subscriptions:
            expiry = user_subscriptions[user_id].get('expiry')
            if expiry and expiry > datetime.now():
                days_left = (expiry - datetime.now()).days
                rows.append(ui_row('⭐', 'Status', f'Premium (expires in {days_left} days)'))
            else:
                rows.append(ui_row('🆓', 'Status', 'Free user (subscription expired)'))
        else:
            rows.append(ui_row('🆓', 'Status', 'Free user'))
        if user_id in temp_bans:
            rows.append(ui_row('⏳', 'Temp ban until', temp_bans[user_id].strftime('%Y-%m-%d %H:%M'), code=True))
        if user_id in suspended_users:
            rows.append(ui_row('⏸️', 'Hosting', 'Suspended'))
        file_count = get_user_file_count(user_id)
        file_limit = get_user_file_limit(user_id)
        rows.append(ui_row('📁', 'Files', f"{ui_num(file_count)} / {ui_num(file_limit)}"))
        if user_id in user_limits:
            rows.append(ui_row('⚙️', 'Custom limit', ui_num(user_limits[user_id])))
        running_scripts = 0
        for file_name, _ in user_files.get(user_id, []):
            if is_bot_running(user_id, file_name):
                running_scripts += 1
        rows.append(ui_row('🤖', 'Running scripts', ui_num(running_scripts)))
        if user_id in active_users:
            rows.append(ui_row('🟢', 'Active', 'Yes'))
        bot.reply_to(message, ui_msg('👤', 'User Info', *rows), parse_mode='HTML')
        
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error getting user info: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Action Failed', ui_user_error(e)), parse_mode='HTML')

USERS_PAGE_SIZE = 20


def _users_view(chat_id=None):
    """Active users list, USERS_PAGE_SIZE per page: (text, menu). The text carries the users, so the page is long."""
    users_list = sorted(active_users)
    back = NavButton("🔙 Back to User Management", callback_data='user_management')
    if not users_list:
        return "👥 No active users yet.", NavMenu(row_width=1).add(back)
    shown, page, pages = _paginate(chat_id, 'users', users_list, size=USERS_PAGE_SIZE)
    start = page * USERS_PAGE_SIZE
    lines = [f"👥 <b>Active Users</b> ({len(users_list)}) - Page {page + 1}/{pages}", ""]
    now = datetime.now()
    for i, user_id in enumerate(shown, start + 1):
        if user_id == OWNER_ID: status = "👑"
        elif user_id in admin_ids: status = "🛡️"
        elif user_id in temp_bans: status = "⏳"
        elif user_id in banned_users: status = "🚫"
        elif user_id in user_subscriptions and user_subscriptions[user_id].get('expiry', datetime.min) > now:
            status = "⭐"
        else: status = "🆓"
        if user_id in suspended_users: status += "⏸️"
        lines.append(f"{i}. <code>{user_id}</code> {status}")
    markup = NavMenu(row_width=1)
    markup.pager('users', 'all_users', page, pages)
    markup.row(back)
    markup.live = lambda cid=chat_id: _users_view(cid)[1]
    return "\n".join(lines), markup


def all_users_callback(call):
    bot.answer_callback_query(call.id)
    try:
        text, markup = _users_view(call.message.chat.id)
        _adm_show(call, text, markup)
    except Exception as e:
        logger.error(f"Error displaying all users: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error displaying users.", show_alert=True)


def handle_users_page(call):
    """Old inline 'users_page_N' button (an old message still on screen): show that page of the list."""
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "⚠️ Admin only.", show_alert=True)
        return
    try:
        page = max(0, int(call.data.split('_')[2]))
        bot.answer_callback_query(call.id)
        with PAGER_LOCK:
            PAGER.setdefault(call.message.chat.id, {})['users'] = {'page': page, 'time': time.time()}
        all_users_callback(call)
    except Exception as e:
        logger.error(f"Error handling users page: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error.", show_alert=True)

def set_user_limit_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🔧 Enter User ID and new limit (e.g., `12345678 50`)\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_set_user_limit)

def process_set_user_limit(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Limit set cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    
    try:
        parts = message.text.split()
        if len(parts) != 2: raise ValueError("Format: user_id limit")
        
        user_id = int(parts[0])
        limit = int(parts[1])
        
        if user_id <= 0 or limit <= 0: raise ValueError("ID and limit must be positive")
        
        if set_user_limit_db(user_id, limit, admin_id):
            bot.reply_to(message, ui_ok('File Limit Set', ui_row('👤', 'User', user_id, code=True), ui_row('📁', 'New limit', f'{limit} files'), foot='Applies right away.'), parse_mode='HTML')
            try:
                bot.send_message(user_id, f"⚙️ Your file upload limit has been set to {limit}")
            except Exception as e:
                logger.error(f"Failed to notify user {user_id}: {e}")
        else:
            bot.reply_to(message, ui_err('Action Failed', 'Failed to set limit. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
            
    except ValueError as e:
        bot.reply_to(message, ui_warn('Invalid Input', 'Please send a user ID and a limit (numbers only).', ui_row('✍️', 'Format', 'user_id limit', code=True)), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error setting user limit: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Action Failed', ui_user_error(e)), parse_mode='HTML')

def remove_user_limit_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "🗑️ Enter User ID to remove custom limit\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_remove_user_limit)

def process_remove_user_limit(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Limit removal cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    
    try:
        user_id = int(message.text.strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        
        if user_id not in user_limits:
            bot.reply_to(message, ui_info('No Custom Limit', ui_row('👤', 'User', user_id, code=True), 'This user already uses the standard limit.', foot='Nothing to remove.'), parse_mode='HTML')
            return
        
        if remove_user_limit_db(user_id):
            bot.reply_to(message, ui_ok('Limit Removed', ui_row('👤', 'User', user_id, code=True), 'The standard file limit applies now.', foot='The user has been told about it.'), parse_mode='HTML')
            try:
                bot.send_message(user_id, ui_info('File Limit Reset', 'Your custom file limit was removed.', foot='The standard limit applies now.'), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Failed to notify user {user_id}: {e}")
        else:
            bot.reply_to(message, ui_err('Action Failed', 'Failed to remove limit. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
            
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error removing user limit: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Action Failed', ui_user_error(e)), parse_mode='HTML')


# =============================================================================
# Admin User Management extras: temp ban, hosting suspension, bulk actions, user files,
# running bots, file preview, delete + owner notice, keyword search
# =============================================================================
BULK_PENDING = {}          # admin id -> {'ids': [...], 'time': t}: the IDs of a bulk action waiting for its action key
BULK_TTL = 600
BULK_MAX_LIMIT = 100000


def _um_back_button():
    return NavButton('🔙 Back to User Management', callback_data='user_management')


def _um_protected(user_id):
    """The owner and the admins are never banned, suspended or limited by these tools."""
    return user_id == OWNER_ID or user_id in admin_ids


def _um_user_mark(user_id):
    if user_id == OWNER_ID: return '👑'
    if user_id in admin_ids: return '🛡️'
    if user_id in temp_bans: return '⏳'
    if user_id in banned_users: return '🚫'
    if user_id in suspended_users: return '⏸️'
    return '👤'


def _um_find_file(owner_id, file_name):
    """(file_name, file_type) when this user really has this file in his list, else None."""
    for name, ftype in user_files.get(owner_id, []):
        if name == file_name:
            return name, ftype
    return None


def _um_parse_file(data):
    """'um_x_<uid>_<file name>' -> (uid, file_name, file_type) or None. The name may hold underscores, and it must be a
    file the user really has, so nothing typed into a button can point outside his own folder."""
    parts = data.split('_', 3)
    if len(parts) != 4:
        return None
    try:
        uid = int(parts[2])
    except ValueError:
        return None
    found = _um_find_file(uid, parts[3])
    if not found:
        return None
    return uid, found[0], found[1]


def _um_file_path(owner_id, file_name):
    return os.path.join(get_user_folder(owner_id), os.path.basename(file_name))


def _um_fmt_size(num):
    num = float(num)
    for unit in ('B', 'KB', 'MB', 'GB'):
        if num < 1024 or unit == 'GB':
            return f"{num:.0f} {unit}" if unit == 'B' else f"{num:.1f} {unit}"
        num /= 1024


def _um_clean_text(text, limit=200):
    """Admin-typed free text that goes into a message to a user: one line, bounded."""
    return re.sub(r'\s+', ' ', str(text or '')).strip()[:limit]


def _um_gone(call, text="⚠️ File not found (maybe deleted)."):
    bot.answer_callback_query(call.id, text, show_alert=True)


# ---- 1. Temp ban -------------------------------------------------------------------------------------
def um_tempban_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           f"⏳ Enter User ID, number of days (1-{TEMP_BAN_MAX_DAYS}) and a reason\n"
                           "Example: <code>12345678 3 Spamming</code>\n"
                           "The ban lifts by itself when the days are over.\n/cancel to cancel", parse_mode='HTML')
    bot.register_next_step_handler(msg, process_um_tempban)


def _um_do_ban(user_id, reason, admin_id, until=None, exclude_chat=None):
    """Ban (temporary when `until` is given), stop the user's scripts and tell him.
    Returns an error text, or '' when it worked."""
    if _um_protected(user_id):
        return "owner/admin cannot be banned"
    if user_id in banned_users and user_id not in temp_bans:
        return "already banned permanently"
    if not ban_user_db(user_id, reason, admin_id, until=until):
        return "database error"
    try:
        _stop_user_scripts(user_id)
    except Exception:
        logger.exception("Could not stop scripts of banned user %s", user_id)
    try:
        if until is not None:
            bot.send_message(user_id, ui_err('Temporary Ban', f"🚫 Status: {ui_tag('banned', 'TEMP BAN')}",
                                             ui_row('⏳', 'Lifts on', f"{until.strftime('%Y-%m-%d %H:%M')}"), ui_row('📝', 'Reason', reason),
                                             foot='The ban lifts by itself, nothing for you to do.'), parse_mode='HTML')
        else:
            bot.send_message(user_id, ui_err('Account Banned', f"🚫 Status: {ui_tag('banned')}", 'You can no longer use this bot.', ui_row('📝', 'Reason', reason), foot='Think this is a mistake? Contact the owner.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Failed to notify banned user {user_id}: {e}")
    return ''


def process_um_tempban(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Temp ban cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    try:
        parts = (message.text or '').split(None, 2)
        if len(parts) < 2:
            bot.reply_to(message, "⚠️ Format: <code>user_id days reason</code>\nExample: <code>12345678 3 Spamming</code>",
                         parse_mode='HTML')
            return
        user_id = int(parts[0])
        days = int(parts[1])
        if user_id <= 0: raise ValueError("ID must be positive")
        if not 1 <= days <= TEMP_BAN_MAX_DAYS:
            bot.reply_to(message, ui_warn('Check The Days', f'Days must be between 1 and {TEMP_BAN_MAX_DAYS}.', foot='Send user_id days reason again, or /cancel.'), parse_mode='HTML')
            return
        reason = _um_clean_text(parts[2]) if len(parts) > 2 else ''
        reason = reason or 'Temporary ban by admin'
        until = datetime.now() + timedelta(days=days)
        error = _um_do_ban(user_id, reason, admin_id, until=until, exclude_chat=message.chat.id)
        if error:
            bot.reply_to(message, ui_warn('Ban Not Applied', ui_row('👤', 'User', user_id, code=True), ui_row('📝', 'Reason', error)), parse_mode='HTML')
            return
        bot.reply_to(message,
                     f"⏳ <b>Temp Ban Applied</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\n"
                     f"👤 User: <code>{user_id}</code>\n📅 Days: <b>{days}</b>\n"
                     f"🕒 Until: <code>{until.strftime('%Y-%m-%d %H:%M')}</code>\n"
                     f"📝 Reason: {html_escape(reason)}\n\nThe user is unbanned automatically when the time is over.",
                     parse_mode='HTML')
    except ValueError:
        bot.reply_to(message, "⚠️ Invalid input. User ID and days must be numbers.\nFormat: <code>user_id days reason</code>",
                     parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error in temp ban: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Something Went Wrong', 'The ban could not be completed. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')


# ---- 2. Suspend / unsuspend hosting -------------------------------------------------------------------
def um_suspend_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           "⏸️ Enter User ID to suspend hosting, with an optional reason\n"
                           "Example: <code>12345678 Abuse review</code>\n"
                           "The user keeps the bot and chat, but nothing of theirs runs and nothing can be started.\n"
                           "/cancel to cancel", parse_mode='HTML')
    bot.register_next_step_handler(msg, process_um_suspend)


def process_um_suspend(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Suspend cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    try:
        parts = (message.text or '').split(None, 1)
        if not parts: raise ValueError("empty")
        user_id = int(parts[0])
        if user_id <= 0: raise ValueError("ID must be positive")
        reason = _um_clean_text(parts[1]) if len(parts) > 1 else ''
        reason = reason or 'Suspended by admin'
        if _um_protected(user_id):
            bot.reply_to(message, ui_warn('Not Allowed', 'Cannot suspend the owner or an admin.', foot='Pick a different user.'), parse_mode='HTML')
            return
        if user_id in suspended_users:
            bot.reply_to(message, ui_info('Already Suspended', ui_row('👤', 'User', user_id, code=True), f"⏸️ Status: {ui_tag('suspended')}", foot='Use Unsuspend to lift it.'), parse_mode='HTML')
            return
        if not suspend_user_db(user_id, reason, admin_id):
            bot.reply_to(message, ui_err('Action Failed', 'Failed to suspend hosting. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
            return
        stopped = _stop_user_scripts(user_id)
        bot.reply_to(message,
                     ui_warn('Hosting Suspended', ui_row('👤', 'User', user_id, code=True), f"⏸️ Status: {ui_tag('suspended')}",
                             ui_row('🛑', 'Scripts stopped', stopped), ui_row('📝', 'Reason', reason),
                             foot='New starts are refused until you unsuspend this user.'),
                     parse_mode='HTML')
        try:
            bot.send_message(user_id, ui_warn('Hosting Suspended', f"⏸️ Status: {ui_tag('suspended')}", ui_row('📝', 'Reason', reason),
                                              'Your files are safe and you can still use the bot, but nothing can run or start until an admin lifts this.',
                                              foot='Contact the owner if you want this reviewed.'), parse_mode='HTML')
        except Exception as e:
            logger.error(f"Failed to notify suspended user {user_id}: {e}")
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error suspending user: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Something Went Wrong', 'The suspension could not be completed. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')


def um_unsuspend_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           f"▶️ Enter User ID to unsuspend hosting ({len(suspended_users)} suspended now)\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_um_unsuspend)


def process_um_unsuspend(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Unsuspend cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    try:
        user_id = int((message.text or '').strip())
        if user_id <= 0: raise ValueError("ID must be positive")
        if user_id not in suspended_users:
            bot.reply_to(message, ui_info('Not Suspended', ui_row('👤', 'User', user_id, code=True), f"▶️ Status: {ui_tag('active')}", foot='Nothing to lift.'), parse_mode='HTML')
            return
        if not unsuspend_user_db(user_id):
            bot.reply_to(message, ui_err('Action Failed', 'Failed to unsuspend. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')
            return
        bot.reply_to(message, ui_ok('Hosting Restored', ui_row('👤', 'User', user_id, code=True), f"▶️ Status: {ui_tag('active')}",
                                    foot='The user can start scripts again.'), parse_mode='HTML')
        try:
            bot.send_message(user_id, ui_ok('Hosting Restored', f"▶️ Status: {ui_tag('active')}", 'Your suspension has been lifted.', foot='Open My Files and start your scripts again.'), parse_mode='HTML')
        except Exception as e:
            logger.error(f"Failed to notify unsuspended user {user_id}: {e}")
    except ValueError:
        bot.reply_to(message, ui_warn('Invalid User ID', 'The user ID must be a number.'), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error unsuspending user: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Something Went Wrong', 'Could not lift the suspension. Nothing was changed.', foot='Please try again in a moment.'), parse_mode='HTML')


# ---- 3. Bulk actions ---------------------------------------------------------------------------------
def um_bulk_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           f"📦 Paste the User IDs (one per line or separated by spaces, up to {BULK_MAX_IDS}).\n"
                           "Next you pick one action for all of them: ban, unban or set file limit.\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_um_bulk_ids)


def _um_parse_ids(text):
    """(ids without repeats in typed order, number of pieces that were not a valid ID)."""
    ids, seen, bad = [], set(), 0
    for token in re.split(r'[\s,;]+', (text or '').strip()):
        if not token:
            continue
        if token.isdigit() and 0 < int(token) < 2 ** 52:
            uid = int(token)
            if uid not in seen:
                seen.add(uid)
                ids.append(uid)
        else:
            bad += 1
    return ids, bad


def process_um_bulk_ids(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Bulk action cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    try:
        ids, bad = _um_parse_ids(message.text)
        if not ids:
            bot.reply_to(message, ui_warn('Nothing Found', 'No valid User IDs found.', foot='Paste numbers only, then try Bulk Actions again.'), parse_mode='HTML')
            return
        cut = max(0, len(ids) - BULK_MAX_IDS)
        ids = ids[:BULK_MAX_IDS]
        BULK_PENDING[admin_id] = {'ids': ids, 'time': time.time()}
        for key in [k for k, v in BULK_PENDING.items() if time.time() - v['time'] > BULK_TTL]:
            BULK_PENDING.pop(key, None)
        notes = []
        if bad: notes.append(f"⚠️ {bad} piece(s) were not valid IDs and were ignored.")
        if cut: notes.append(f"⚠️ Only the first {BULK_MAX_IDS} IDs are used ({cut} cut).")
        menu = NavMenu(row_width=1)
        menu.row(NavButton('🚫 Ban All Listed', callback_data='um_bk_ban'))
        menu.row(NavButton('✅ Unban All Listed', callback_data='um_bk_unban'))
        menu.row(NavButton('🔧 Set Limit For All', callback_data='um_bk_limit'))
        menu.row(_um_back_button())
        sample = ', '.join(str(i) for i in ids[:10]) + (' ...' if len(ids) > 10 else '')
        bot.send_message(message.chat.id,
                         f"📦 <b>Bulk Actions</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\n👥 IDs ready: <b>{len(ids)}</b>\n"
                         f"<code>{html_escape(sample)}</code>\n" + ("\n".join(notes) + "\n" if notes else "") +
                         "\nPick the action for all of them. Owner and admins are always skipped.",
                         parse_mode='HTML', reply_markup=menu)
    except Exception as e:
        logger.error(f"Error reading bulk IDs: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Could Not Read', 'Could not read that list.', foot='Try again.'), parse_mode='HTML')


def _um_bulk_ids(admin_id):
    entry = BULK_PENDING.get(admin_id)
    if not entry or time.time() - entry['time'] > BULK_TTL:
        BULK_PENDING.pop(admin_id, None)
        return None
    return list(entry['ids'])


def _um_bulk_summary(title, ok, failed):
    lines = [f"📦 <b>Bulk {html_escape(title)} Done</b>", "💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰",
             f"✅ Succeeded: <b>{len(ok)}</b>", f"❌ Failed: <b>{len(failed)}</b>"]
    if ok:
        lines.append("")
        lines.append("✅ " + ', '.join(f"<code>{u}</code>" for u in ok[:30]) + (f" ...(+{len(ok) - 30})" if len(ok) > 30 else ''))
    if failed:
        lines.append("")
        for uid, why in failed[:15]:
            lines.append(f"• <code>{uid}</code> - {html_escape(why)}")
        if len(failed) > 15:
            lines.append(f"• ...and {len(failed) - 15} more")
    return "\n".join(lines)


def _um_bulk_expired(call):
    bot.answer_callback_query(call.id, "⚠️ That list expired. Open Bulk Actions and paste the IDs again.", show_alert=True)


def um_bulk_ban_callback(call):
    admin_id = call.from_user.id
    ids = _um_bulk_ids(admin_id)
    if ids is None: _um_bulk_expired(call); return
    BULK_PENDING.pop(admin_id, None)
    bot.answer_callback_query(call.id, f"⏳ Banning {len(ids)} user(s)...")
    ok, failed = [], []
    for uid in ids:
        error = _um_do_ban(uid, 'Bulk ban by admin', admin_id, exclude_chat=call.message.chat.id)
        (failed.append((uid, error)) if error else ok.append(uid))
        time.sleep(0.05)
    _um_send_summary(call, _um_bulk_summary('Ban', ok, failed))


def um_bulk_unban_callback(call):
    admin_id = call.from_user.id
    ids = _um_bulk_ids(admin_id)
    if ids is None: _um_bulk_expired(call); return
    BULK_PENDING.pop(admin_id, None)
    bot.answer_callback_query(call.id, f"⏳ Unbanning {len(ids)} user(s)...")
    ok, failed = [], []
    for uid in ids:
        if uid not in banned_users:
            failed.append((uid, "not banned"))
        elif unban_user_db(uid):
            ok.append(uid)
            try:
                bot.send_message(uid, ui_ok('Ban Lifted', f"✅ Status: {ui_tag('active')}", 'Your ban has been lifted.', foot='Send /start to continue.'), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Failed to notify unbanned user {uid}: {e}")
            time.sleep(0.05)
        else:
            failed.append((uid, "database error"))
    _um_send_summary(call, _um_bulk_summary('Unban', ok, failed))


def um_bulk_limit_callback(call):
    admin_id = call.from_user.id
    ids = _um_bulk_ids(admin_id)
    if ids is None: _um_bulk_expired(call); return
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           f"🔧 Enter the new file limit for these {len(ids)} user(s) (a number from 1 to {BULK_MAX_LIMIT})\n"
                           "/cancel to cancel")
    bot.register_next_step_handler(msg, process_um_bulk_limit)


def process_um_bulk_limit(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Bulk limit cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    try:
        limit = int((message.text or '').strip())
        if not 1 <= limit <= BULK_MAX_LIMIT: raise ValueError("limit out of range")
    except ValueError:
        bot.reply_to(message, ui_warn('Check The Number', f'The limit must be a number from 1 to {BULK_MAX_LIMIT}.', foot='Open Bulk Actions to try again.'), parse_mode='HTML')
        return
    ids = _um_bulk_ids(admin_id)
    if ids is None:
        bot.reply_to(message, ui_warn('Session Expired', 'That list expired.', foot='Open Bulk Actions and paste the IDs again.'), parse_mode='HTML')
        return
    BULK_PENDING.pop(admin_id, None)
    ok, failed = [], []
    for uid in ids:
        if _um_protected(uid):
            failed.append((uid, "owner/admin has no limit"))
        elif set_user_limit_db(uid, limit, admin_id):
            ok.append(uid)
            try:
                bot.send_message(uid, f"⚙️ Your file upload limit has been set to {limit}")
            except Exception as e:
                logger.error(f"Failed to notify user {uid}: {e}")
            time.sleep(0.05)
        else:
            failed.append((uid, "database error"))
    _um_send_summary(message, _um_bulk_summary(f'Limit ({limit})', ok, failed))


def _um_send_summary(call_or_message, text):
    chat_id = call_or_message.message.chat.id if hasattr(call_or_message, 'message') and hasattr(call_or_message.message, 'chat') \
        else call_or_message.chat.id
    menu = NavMenu(row_width=1)
    menu.row(NavButton('📦 Bulk Actions', callback_data='um_bulk'))
    menu.row(_um_back_button())
    bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=menu)


# ---- 5. View user files (users list -> files of one user -> inspect / preview / delete) ----------------
def _um_users_view(chat_id=None):
    users = sorted(uid for uid, files in user_files.items() if files)
    back = _um_back_button()
    if not users:
        return "📂 <b>User Files</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\nNo user has any file yet.", NavMenu(row_width=1).add(back)
    shown, page, pages = _paginate(chat_id, 'um_files', users)
    markup = NavMenu(row_width=1)
    markup.offset = page * NAV_PAGE_SIZE
    for uid in shown:
        count = len(user_files.get(uid, []))
        markup.add(NavButton(f"{_um_user_mark(uid)} {uid} ({count} file{'s' if count != 1 else ''})", callback_data=f'um_u_{uid}'))
    markup.pager('um_files', 'um_files', page, pages)
    markup.row(back)
    markup.live = lambda cid=chat_id: _um_users_view(cid)[1]
    text = (f"📂 <b>User Files</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\n👥 Users with files: <b>{len(users)}</b>\n\n"
            "Tap a user to see and manage their files." + _page_note(page, pages))
    return text, markup


def um_files_callback(call):
    bot.answer_callback_query(call.id)
    text, markup = _um_users_view(call.message.chat.id)
    _adm_show(call, text, markup)


def _um_status_line(uid):
    bits = []
    if uid == OWNER_ID: bits.append('👑 Owner')
    elif uid in admin_ids: bits.append('🛡️ Admin')
    if uid in temp_bans: bits.append(f"⏳ Temp banned until {temp_bans[uid].strftime('%Y-%m-%d %H:%M')}")
    elif uid in banned_users: bits.append('🚫 Banned')
    if uid in suspended_users: bits.append('⏸️ Hosting suspended')
    return ' | '.join(bits) if bits else '✅ Normal'


def _um_user_files_view(chat_id, uid):
    files = sorted(user_files.get(uid, []), key=lambda f: f[0].lower())
    back = NavButton('🔙 Back to Users', callback_data='um_files')
    head = f"👤 <b>User</b> <code>{uid}</code>\n📌 {html_escape(_um_status_line(uid))}\n"
    if not files:
        return head + "\n📂 This user has no files.", NavMenu(row_width=1).add(back)
    key = f'umf_{uid}'
    shown, page, pages = _paginate(chat_id, key, files)
    markup = NavMenu(row_width=1)
    markup.offset = page * NAV_PAGE_SIZE
    for name, _ftype in shown:
        icon = '🟢' if is_bot_running(uid, name) else '🔴'
        markup.add(NavButton(f"{icon} {name}", callback_data=f'um_f_{uid}_{name}'))
    markup.pager(key, f'um_u_{uid}', page, pages)
    markup.row(back)
    markup.live = lambda cid=chat_id, u=uid: _um_user_files_view(cid, u)[1]
    return head + f"📁 Files: <b>{len(files)}</b>\n\nTap a file to inspect, preview or delete it." + _page_note(page, pages), markup


def um_user_callback(call):
    try:
        uid = int(call.data.split('_', 2)[2])
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, "⚠️ Invalid user.", show_alert=True); return
    bot.answer_callback_query(call.id)
    text, markup = _um_user_files_view(call.message.chat.id, uid)
    _adm_show(call, text, markup)


def _um_file_detail(chat_id, uid, file_name, file_type):
    path = _um_file_path(uid, file_name)
    try:
        size = _um_fmt_size(os.path.getsize(path))
    except OSError:
        size = 'missing on disk'
    running = is_bot_running(uid, file_name)
    lines = ["📄 <b>File Details</b>", "💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰",
             f"👤 Owner: <code>{uid}</code>", f"📄 File: <code>{html_escape(file_name)}</code>",
             f"🏷️ Type: <b>{html_escape(str(file_type))}</b>", f"💾 Size: <b>{html_escape(size)}</b>",
             f"🤖 Status: {'🟢 Running' if running else '🔴 Stopped'}"]
    markup = NavMenu(row_width=2)
    markup.row(NavButton('👁️ Preview File', callback_data=f'um_p_{uid}_{file_name}'),
               NavButton('🗑️ Delete File', callback_data=f'um_d_{uid}_{file_name}'))
    if running:
        markup.row(NavButton('🔴 Stop Script', callback_data=f'um_fs_{uid}_{file_name}'))
    markup.row(NavButton('🔙 Back to Files', callback_data=f'um_u_{uid}'))
    return "\n".join(lines), markup


def um_file_callback(call):
    parsed = _um_parse_file(call.data)
    if not parsed: _um_gone(call); return
    uid, file_name, file_type = parsed
    bot.answer_callback_query(call.id)
    text, markup = _um_file_detail(call.message.chat.id, uid, file_name, file_type)
    _adm_show(call, text, markup)


def um_file_stop_callback(call):
    """Stop button of the file detail screen (the running-bots screen has its own, um_rs_)."""
    parsed = _um_parse_file(call.data)
    if not parsed: _um_gone(call); return
    uid, file_name, file_type = parsed
    _um_stop_script(uid, file_name)
    bot.answer_callback_query(call.id, f"🔴 Stopped {file_name}")
    text, markup = _um_file_detail(call.message.chat.id, uid, file_name, file_type)
    _adm_show(call, text, markup)


# ---- 7. File preview ---------------------------------------------------------------------------------
UM_PREVIEW_READ_BYTES = 256 * 1024


def _um_fit_html(lines, budget):
    """Escaped lines joined so that the result stays within `budget` characters. Returns (html, lines shown, cut)."""
    out, used, shown, cut = [], 0, 0, False
    for line in lines:
        esc = html_escape(line)
        if used + len(esc) + 1 > budget:
            room = budget - used - 1
            if room > 20:                                    # part of a long line is still better than nothing
                piece = line[:room]
                esc = html_escape(piece)
                while len(esc) > room and piece:
                    piece = piece[:int(len(piece) * 0.8)]
                    esc = html_escape(piece)
                if esc:
                    out.append(esc + ' …')
                    shown += 1
            cut = True
            break
        out.append(esc)
        used += len(esc) + 1
        shown += 1
    return "\n".join(out), shown, cut


def _um_read_text(path, limit=UM_PREVIEW_READ_BYTES):
    """(text or None, file is bigger than what was read, problem text). Binary files are refused."""
    with open(path, 'rb') as handle:
        raw = handle.read(limit + 1)
    if b'\x00' in raw[:4096]:
        return None, False, "This looks like a binary file, so there is no text to preview."
    big = len(raw) > limit
    return raw[:limit].decode('utf-8', errors='replace'), big, ''


def um_preview_callback(call):
    parsed = _um_parse_file(call.data)
    if not parsed: _um_gone(call); return
    uid, file_name, file_type = parsed
    back = NavMenu(row_width=1).add(NavButton('🔙 Back to File', callback_data=f'um_f_{uid}_{file_name}'))
    path = _um_file_path(uid, file_name)
    if not os.path.isfile(path):
        bot.answer_callback_query(call.id, "⚠️ The file is missing on disk.", show_alert=True); return
    if os.path.basename(file_name).lower().startswith('.env') or file_name.lower().endswith('.env'):
        bot.answer_callback_query(call.id, "⚠️ Environment files are not previewed (they hold secrets).", show_alert=True); return
    bot.answer_callback_query(call.id)
    try:
        text, big, problem = _um_read_text(path)
    except OSError as e:
        logger.error(f"Preview read failed for {path}: {e}")
        bot.send_message(call.message.chat.id, "❌ Could not read that file.", reply_markup=back)
        return
    head = f"👁️ <b>Preview</b> <code>{html_escape(file_name)}</code> (User <code>{uid}</code>)\n"
    if problem:
        _adm_show(call, head + f"\n⚠️ {html_escape(problem)}", back)
        return
    all_lines = text.splitlines()
    first = all_lines[:FILE_PREVIEW_LINES]
    body, shown, cut = _um_fit_html(first, FILE_PREVIEW_CHARS)
    notes = []
    if not all_lines:
        notes.append("(the file is empty)")
    elif len(all_lines) > FILE_PREVIEW_LINES or big:
        notes.append(f"Showing the first {shown} line(s)." if cut else f"Showing the first {shown} line(s); the rest of the file is not shown.")
    if cut:
        notes.append("The text was cut to fit Telegram's message size limit.")
    _adm_show(call, head + f"<pre>{body}</pre>" + ("\n" + "\n".join(f"ℹ️ {html_escape(n)}" for n in notes) if notes else ''), back)


# ---- 8. Delete a user's file (admin) and tell the owner ---------------------------------------------
def _delete_user_file_core(owner_id, file_name, exclude_chat=None):
    """Stop the script, remove the file, its log, env file and GitHub sidecar, forget the record.
    Returns the names that were removed from disk. Shared by the owner's delete button and the admin tools."""
    script_key = f"{owner_id}_{file_name}"
    RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
    autostart_clear(script_key)
    if is_bot_running(owner_id, file_name):
        logger.info(f"Delete: Stopping {script_key}...")
        process_info = bot_scripts.get(script_key)
        if process_info: kill_process_tree(process_info)
        _forget_script(script_key)
        time.sleep(0.5)
    user_folder = get_user_folder(owner_id)
    file_path = os.path.join(user_folder, file_name)
    log_path = os.path.join(user_folder, f"{os.path.splitext(file_name)[0]}.log")
    env_path = bot_env_path(user_folder, file_name)
    deleted_disk = []
    if os.path.exists(file_path):
        try: os.remove(file_path); deleted_disk.append(file_name); logger.info(f"Deleted file: {file_path}")
        except OSError as e: logger.error(f"Error deleting {file_path}: {e}")
    if os.path.exists(log_path):
        try: os.remove(log_path); deleted_disk.append(os.path.basename(log_path)); logger.info(f"Deleted log: {log_path}")
        except OSError as e: logger.error(f"Error deleting log {log_path}: {e}")
    if env_path and os.path.isfile(env_path):
        try: os.remove(env_path); deleted_disk.append(os.path.basename(env_path)); logger.info(f"Deleted environment file: {env_path}")
        except OSError as e: logger.error(f"Error deleting {env_path}: {e}")
    side_path = gh_sidecar_path(user_folder, file_name)
    if side_path and os.path.isfile(side_path):
        _remove_quietly(side_path)
    remove_user_file_db(owner_id, file_name)
    return deleted_disk


def _notify_owner_file_removed(owner_id, file_name):
    """Tell the owner that an admin removed his file (neutral wording, no accusation)."""
    try:
        bot.send_message(owner_id,
                         f"🗑️ Your file <code>{html_escape(file_name)}</code> was removed by an admin.\n"
                         "If you have questions, please contact an admin.", parse_mode='HTML')
    except Exception as e:
        logger.error(f"Failed to notify user {owner_id} about the removed file: {e}")


def um_delete_ask_callback(call):
    parsed = _um_parse_file(call.data)
    if not parsed: _um_gone(call); return
    uid, file_name, _ftype = parsed
    bot.answer_callback_query(call.id)
    markup = NavMenu(row_width=1)
    markup.row(NavButton('✅ Yes, Delete File', callback_data=f'um_dy_{uid}_{file_name}'))
    markup.row(NavButton('📁 Keep File', callback_data=f'um_f_{uid}_{file_name}'))
    _adm_show(call, f"🗑️ <b>Delete this file?</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\n👤 Owner: <code>{uid}</code>\n"
                    f"📄 File: <code>{html_escape(file_name)}</code>\n\n"
                    "The script is stopped and the file, its log and settings are removed. "
                    "The owner is told it was removed by an admin.", markup)


def um_delete_do_callback(call):
    parsed = _um_parse_file(call.data)
    if not parsed: _um_gone(call); return
    uid, file_name, _ftype = parsed
    bot.answer_callback_query(call.id, f"🗑️ Deleting {file_name}...")
    deleted = _delete_user_file_core(uid, file_name, exclude_chat=call.message.chat.id)
    logger.info(f"Admin {call.from_user.id} deleted {file_name} of user {uid} ({len(deleted)} items)")
    _notify_owner_file_removed(uid, file_name)
    text, markup = _um_user_files_view(call.message.chat.id, uid)
    _adm_show(call, f"🗑️ <code>{html_escape(file_name)}</code> deleted and the owner was notified.\n\n" + text, markup)


# ---- 6. Running bots browser -------------------------------------------------------------------------
def _um_running_rows():
    with STATE_LOCK:
        items = list(bot_scripts.items())
    rows = []
    for key, info in items:
        try:
            owner = int(info.get('script_owner_id'))
            name = info.get('file_name') or key.split('_', 1)[1]
            proc = info.get('process')
            if proc is not None and proc.poll() is None:
                rows.append((owner, str(name)))
        except Exception:
            continue
    rows.sort(key=lambda r: (r[0], r[1].lower()))
    return rows


def _um_running_view(chat_id=None):
    rows = _um_running_rows()
    back = _um_back_button()
    if not rows:
        return "🟢 <b>Running Bots</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\nNo script is running right now.", NavMenu(row_width=1).add(back)
    shown, page, pages = _paginate(chat_id, 'um_run', rows)
    markup = NavMenu(row_width=1)
    markup.offset = page * NAV_PAGE_SIZE
    for owner, name in shown:
        markup.add(NavButton(f"🟢 {name} ({owner})", callback_data=f'um_r_{owner}_{name}'))
    markup.pager('um_run', 'um_run', page, pages)
    markup.row(back)
    markup.live = lambda cid=chat_id: _um_running_view(cid)[1]
    text = (f"🟢 <b>Running Bots</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\n🤖 Running now: <b>{len(rows)}</b>\n\n"
            "Tap one to see its live log and stop it." + _page_note(page, pages))
    return text, markup


def um_run_callback(call):
    bot.answer_callback_query(call.id)
    text, markup = _um_running_view(call.message.chat.id)
    _adm_show(call, text, markup)


def _um_parse_running(data):
    """'um_r_<uid>_<file>' -> (uid, file_name, info) for a script that is running right now, else None."""
    parts = data.split('_', 3)
    if len(parts) != 4:
        return None
    try:
        uid = int(parts[2])
    except ValueError:
        return None
    name = parts[3]
    with STATE_LOCK:
        info = bot_scripts.get(f"{uid}_{name}")
    if not info or not is_bot_running(uid, name):
        return None
    return uid, name, info


def _um_log_tail(uid, name, info, lines=25, max_chars=3000):
    folder = info.get('user_folder') or get_user_folder(uid)
    log_path = os.path.join(folder, f"{os.path.splitext(os.path.basename(name))[0]}.log")
    if not os.path.isfile(log_path):
        return "(no log file yet)"
    try:
        size = os.path.getsize(log_path)
        with open(log_path, 'rb') as handle:
            if size > 64 * 1024:
                handle.seek(-64 * 1024, os.SEEK_END)
            raw = handle.read()
    except OSError:
        return "(the log could not be read)"
    tail = raw.decode('utf-8', errors='replace').splitlines()[-lines:]
    if not tail:
        return "(log is empty)"
    body, _shown, _cut = _um_fit_html(tail[::-1], max_chars)     # newest lines are kept when the log is too long
    kept = body.split("\n")[::-1]
    return "\n".join(kept)


def um_running_log_callback(call):
    parsed = _um_parse_running(call.data)
    if not parsed:
        bot.answer_callback_query(call.id, "⚠️ That script is not running any more.", show_alert=True)
        um_run_callback(call)
        return
    uid, name, info = parsed
    bot.answer_callback_query(call.id)
    started = info.get('start_time')
    up = ''
    if isinstance(started, datetime):
        secs = int((datetime.now() - started).total_seconds())
        up = f"\n⏱️ Running for: <b>{secs // 3600}h {(secs % 3600) // 60}m</b>"
    log_html = _um_log_tail(uid, name, info)
    markup = NavMenu(row_width=2)
    markup.row(NavButton('🔄 Refresh Log', callback_data=f'um_r_{uid}_{name}'),
               NavButton('🔴 Stop Script', callback_data=f'um_rs_{uid}_{name}'))
    markup.row(NavButton('🔙 Back to Running Bots', callback_data='um_run'))
    _adm_show(call, f"🟢 <b>{html_escape(name)}</b>\n👤 Owner: <code>{uid}</code>{up}\n\n📜 <b>Live log</b> (last lines)\n<pre>{log_html}</pre>",
              markup)


def _um_stop_script(uid, name):
    """Same as the Stop button of the file controls: no automatic restart, process tree killed, record removed."""
    script_key = f"{uid}_{name}"
    RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
    autostart_clear(script_key)
    process_info = bot_scripts.get(script_key)
    if process_info:
        kill_process_tree(process_info)
        _forget_script(script_key)
        logger.info(f"Admin stopped {script_key}")
        return True
    return False


def um_running_stop_callback(call):
    parts = call.data.split('_', 3)
    try:
        uid, name = int(parts[2]), parts[3]
    except (ValueError, IndexError):
        bot.answer_callback_query(call.id, "⚠️ Invalid script.", show_alert=True); return
    if not is_bot_running(uid, name):
        bot.answer_callback_query(call.id, "⚠️ That script is already stopped.", show_alert=True)
    else:
        _um_stop_script(uid, name)
        bot.answer_callback_query(call.id, f"🔴 Stopped {name} (user {uid})")
    um_run_callback(call)


# ---- 9. Keyword search across all users --------------------------------------------------------------
def um_search_callback(call):
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id,
                           f"🔍 Enter the word or text to search for in all hosted files ({SEARCH_MIN_CHARS}-{SEARCH_MAX_CHARS} characters).\n"
                           "It is a plain text search (not a pattern), case does not matter.\n/cancel to cancel")
    bot.register_next_step_handler(msg, process_um_search)


def _um_search_files(needle):
    """Plain, case-insensitive substring search over every user's hosted files (not a regex, so no pattern can hang the bot).
    Binary files are skipped, only the first SEARCH_MAX_FILE_BYTES of a file is read, and the number of hits per file,
    in total and the running time are all capped. Returns (hits, files searched, stopped early reason)."""
    needle = needle.lower()
    deadline = time.time() + SEARCH_MAX_SECONDS
    hits, searched, stop = [], 0, ''
    entries = [(uid, name) for uid, files in sorted(list(user_files.items())) for name, _t in list(files)]
    for uid, name in entries:
        if time.time() > deadline:
            stop = f"stopped after {SEARCH_MAX_SECONDS} seconds"
            break
        path = os.path.join(UPLOAD_BOTS_DIR, str(uid), os.path.basename(name))
        try:
            if not os.path.isfile(path) or os.path.islink(path):
                continue
            with open(path, 'rb') as handle:
                raw = handle.read(SEARCH_MAX_FILE_BYTES)
        except OSError:
            continue
        if b'\x00' in raw[:4096]:
            continue
        searched += 1
        per_file = 0
        for number, line in enumerate(raw.decode('utf-8', errors='replace').splitlines(), 1):
            low = line.lower()
            pos = low.find(needle)
            if pos < 0:
                continue
            start = max(0, pos - 40)
            snippet = line[start:start + 120].strip()
            hits.append((uid, name, number, snippet))
            per_file += 1
            if len(hits) >= SEARCH_MAX_HITS_TOTAL:
                return hits, searched, f"stopped at {SEARCH_MAX_HITS_TOTAL} hits"
            if per_file >= SEARCH_MAX_HITS_PER_FILE:
                break
    return hits, searched, stop


def process_um_search(message):
    admin_id = message.from_user.id
    if admin_id not in admin_ids: bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML'); return
    if message.text and message.text.lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Search cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    term = (message.text or '').strip()
    if not SEARCH_MIN_CHARS <= len(term) <= SEARCH_MAX_CHARS:
        bot.reply_to(message, ui_warn('Check The Search', f'The search text must be {SEARCH_MIN_CHARS} to {SEARCH_MAX_CHARS} characters.', foot='Open Search Files to try again.'), parse_mode='HTML')
        return
    try:
        bot.reply_to(message, "🔍 Searching all hosted files...")
        hits, searched, stop = _um_search_files(term)
        menu = NavMenu(row_width=1)
        menu.row(NavButton('🔍 Search Files', callback_data='um_search'))
        menu.row(_um_back_button())
        head = (f"🔍 <b>Search Results</b>\n💎 ▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰▰\n🔎 Text: <code>{html_escape(term)}</code>\n"
                f"📂 Files searched: <b>{searched}</b>\n🎯 Hits: <b>{len(hits)}</b>")
        if stop:
            head += f"\n⚠️ Search {html_escape(stop)}; there may be more."
        if not hits:
            bot.send_message(message.chat.id, head + "\n\nNothing found.", parse_mode='HTML', reply_markup=menu)
            return
        blocks = []
        for uid, name, number, snippet in hits:
            blocks.append(f"👤 <code>{uid}</code> - <code>{html_escape(name)}</code> (line {number})\n   <code>{html_escape(snippet)}</code>")
        chunks, current, size = [], [], 0
        for block in blocks:
            if size + len(block) + 2 > 3600 and current:
                chunks.append("\n\n".join(current))
                current, size = [], 0
            current.append(block)
            size += len(block) + 2
        if current:
            chunks.append("\n\n".join(current))
        bot.send_message(message.chat.id, head, parse_mode='HTML')
        for i, chunk in enumerate(chunks):
            last = i == len(chunks) - 1
            bot.send_message(message.chat.id, chunk, parse_mode='HTML', reply_markup=menu if last else None, ui_raw=True)
    except Exception as e:
        logger.error(f"Error in file search: {e}", exc_info=True)
        bot.reply_to(message, ui_err('Something Went Wrong', 'Something went wrong during the search.', foot='Check the logs.'), parse_mode='HTML')


# --- Hosting Health & Crash Recovery ---
def _script_key(owner_id, file_name):
    return f"{int(owner_id)}_{file_name}"

def _reset_restart_state(owner_id, file_name):
    """A fresh user-initiated launch clears an old manual stop / used-up retries, so auto-restart works again."""
    RESTART_STATE[_script_key(owner_id, file_name)] = {"attempts": 0, "manual_stop": False}

def _read_cgroup_value(paths):
    """Read the first available cgroup metric without touching /proc."""
    for path in paths:
        try:
            with open(path, "r", encoding="utf-8") as handle:
                value = handle.read().strip()
            if value:
                return value
        except (OSError, ValueError):
            continue
    return None

def _safe_cpu_health():
    # Many container hosts deny /proc/stat. Use cgroup v2 accounting first.
    stat_text = _read_cgroup_value(("/sys/fs/cgroup/cpu.stat",))
    if stat_text and "usage_usec" in stat_text:
        try:
            usage1 = next(int(line.split()[1]) for line in stat_text.splitlines() if line.startswith("usage_usec "))
            time.sleep(0.12)
            later = _read_cgroup_value(("/sys/fs/cgroup/cpu.stat",))
            usage2 = next(int(line.split()[1]) for line in later.splitlines() if line.startswith("usage_usec "))
            quota_text = _read_cgroup_value(("/sys/fs/cgroup/cpu.max",))
            parts = quota_text.split() if quota_text else []
            cores = (float(parts[0]) / float(parts[1])) if len(parts) == 2 and parts[0] != "max" else float(os.cpu_count() or 1)
            pct = max(0.0, (usage2 - usage1) / 1200.0 / max(cores, 0.01))
            return f"{pct:.1f}% (container)"
        except Exception:
            pass
    try:
        return f"Load {os.getloadavg()[0]:.2f} (CPU % restricted)"
    except (AttributeError, OSError):
        return "Unavailable (host restricts CPU metrics)"

def _safe_memory_health():
    current = _read_cgroup_value(("/sys/fs/cgroup/memory.current", "/sys/fs/cgroup/memory/memory.usage_in_bytes"))
    limit = _read_cgroup_value(("/sys/fs/cgroup/memory.max", "/sys/fs/cgroup/memory/memory.limit_in_bytes"))
    try:
        if current and limit and limit != "max":
            used, total = int(current), int(limit)
            if 0 < total < (1 << 60):
                return f"{used / total * 100:.1f}% ({used // 1048576}/{total // 1048576} MB, container)"
    except (TypeError, ValueError):
        pass
    try:
        mem = psutil.virtual_memory()
        return f"{mem.percent:.1f}% ({mem.used // 1048576}/{mem.total // 1048576} MB)"
    except Exception:
        return "Unavailable (host restricts memory metrics)"

def _res_bar(text):
    """Real usage bar for a resource text that starts with a percent ('42.5% (...)'); None when no percent is known."""
    try:
        match = re.match(r'\s*(\d+(?:\.\d+)?)%', str(text))
        if not match:
            return None
        return f"<code>{ui_bar(min(float(match.group(1)), 100.0), 100)}</code>"
    except Exception:
        return None


def build_hosting_health_report():
    # Isolate each metric so a restricted /proc mount cannot break the report.
    try:
        try:
            disk = shutil.disk_usage(BASE_DIR)
            disk_text = f"{disk.used / disk.total * 100:.1f}% ({disk.used // 1048576}/{disk.total // 1048576} MB)"
        except Exception:
            disk_text = "Unavailable"
        try:
            running = sum(1 for info in list(bot_scripts.values())
                          if info.get("process") and info["process"].poll() is None)
        except Exception:
            running = "Unknown"
        exhausted = sum(1 for st in RESTART_STATE.values()
                        if st.get("attempts", 0) >= MAX_AUTO_RESTARTS)
        cpu_text, ram_text = _safe_cpu_health(), _safe_memory_health()
        up = max(0, int(time.time() - HOST_START_TIME))
        sched = (f"every {SCHEDULED_RESTART_HOURS}h ({len(SCHEDULED_RESTART_OPTOUT)} script(s) opted out)"
                 if SCHEDULED_RESTART_HOURS > 0 else "off")
        try:
            backup_lines = [ui_row('💾', 'Auto backup', re.sub(r'^Auto backup:\s*', '', ln.lstrip('•- ').strip())) for ln in auto_backup_status_lines()]
        except Exception:
            backup_lines = []
        return ui_msg('🩺', 'HOSTING HEALTH',
                      f"🤖 Hosting bot: {ui_tag('online')}",
                      f"🛡️ Overall: {ui_tag('warn', 'ATTENTION') if exhausted else ui_tag('ok', 'ALL GOOD')}",
                      ui_section('⚙️', 'Scripts'),
                      ui_row('🚀', 'Running now', running),
                      ui_row('📦', 'Stored scripts', sum(len(v) for v in user_files.values())),
                      ui_row('🔁', 'Restart-exhausted', exhausted),
                      ui_row('👥', 'Registered users', len(active_users)),
                      ui_section('🧠', 'Resources'),
                      ui_row('🧠', 'CPU', cpu_text), _res_bar(cpu_text),
                      ui_row('💾', 'RAM', ram_text), _res_bar(ram_text),
                      ui_row('💿', 'Disk', disk_text), _res_bar(disk_text),
                      ui_row('⏱️', 'Host uptime', ui_uptime(up)),
                      ui_section('🛡️', 'Protection'),
                      ui_row('🛡️', 'Auto-restart', f"maximum {MAX_AUTO_RESTARTS} attempts"),
                      ui_row('⏰', 'Scheduled restart', sched),
                      *backup_lines,
                      brand=True)
    except Exception as exc:
        logger.exception("Health report failed")
        return ui_warn('Health Report', 'Some health details could not be read right now.', foot='Details are in the server log.')

def _watchdog_restart(info, script_key, attempt_no):
    try:
        owner_id = int(info["script_owner_id"])
        file_name = info["file_name"]
        folder = info["user_folder"]
        path = os.path.join(folder, file_name)
        state = RESTART_STATE.get(script_key, {})
        if state.get("manual_stop"):
            logger.info("Watchdog restart for %s cancelled: stopped manually.", script_key)
            return
        if is_bot_running(owner_id, file_name):
            logger.info("Watchdog restart for %s skipped: already running again.", script_key)
            return
        if not os.path.isfile(path):
            logger.error("Watchdog cannot restart missing script: %s", script_key)
            return
        target = info.get("reply_target")
        if target is None:
            logger.error("No Telegram reply target stored for %s", script_key)
            return
        runner = run_js_script if info.get("type") == "js" else run_script
        try:
            gate_ok = launch_gate(owner_id, file_name, info.get("type", "py"), owner_id, queue=False, admin_override=False)[0]
        except Exception:
            gate_ok = True
        _run_auto(runner, path, owner_id, folder, file_name, target)
        if not gate_ok:
            return              # suspended / security hold: not a crash, so no more tries (the runner told the user why)
        _watchdog_check_started(info, script_key)
    except Exception:
        logger.exception("Watchdog restart worker failed: %s", script_key)
        _watchdog_check_started(info, script_key, failed=True)


def _wait_until_running(owner_id, file_name, seconds):
    """True as soon as the script is running; False when it did not come up within `seconds`."""
    end = time.time() + seconds
    while True:
        if is_bot_running(owner_id, file_name):
            return True
        if time.time() >= end or SHUTDOWN_EVENT.is_set():
            return False
        SHUTDOWN_EVENT.wait(2)


def _watchdog_check_started(info, script_key, failed=False):
    """After a restart: if the script never came up (pre-check exit, sandbox error, start error) nothing watches it any more,
    so it is handed back to the watchdog loop, which counts it as one more failed try and plans the next one."""
    try:
        if not failed and _wait_until_running(info["script_owner_id"], info["file_name"], RESTART_START_WAIT):
            return
        if SHUTDOWN_EVENT.is_set() or RESTART_STATE.get(script_key, {}).get("manual_stop"):
            return
        with STATE_LOCK:
            if script_key in bot_scripts:
                return          # registered (maybe already dead again): the loop handles it like any exit
        WATCHDOG_START_FAILED[script_key] = info
    except Exception:
        logger.exception("Could not check the restart of %s", script_key)


def _trim_script_log(info):
    """Keep a running script's log file from growing without limit (the script keeps appending to the same file)."""
    try:
        log_path = os.path.join(info["user_folder"], f"{os.path.splitext(info['file_name'])[0]}.log")
        if os.path.exists(log_path) and os.path.getsize(log_path) > MAX_SCRIPT_LOG_MB * 1024 * 1024:
            os.truncate(log_path, 0)
            logger.info("Log %s passed %s MB and was cleared.", log_path, MAX_SCRIPT_LOG_MB)
    except Exception as exc:
        logger.debug("Could not trim log for %s: %s", info.get("script_key"), exc)


def _log_tail(info, lines=8, limit=900):
    """The last few lines of a script's log as plain text ('' when there is none). Never raises."""
    try:
        path = os.path.join(info["user_folder"], f"{os.path.splitext(info['file_name'])[0]}.log")
        if not os.path.isfile(path) or os.path.getsize(path) == 0:
            return ''
        with open(path, 'rb') as fh:
            fh.seek(max(0, os.path.getsize(path) - 6000))
            raw = fh.read().decode('utf-8', errors='ignore')
        tail = '\n'.join([ln for ln in raw.splitlines() if ln.strip()][-lines:])
        return tail[-limit:]
    except Exception:
        return ''


def _crash_card(kind, info, rows, foot):
    """A crash / restart notice: status badge, short rows and (when there is a log) the last lines in a collapsed quote."""
    tail = _log_tail(info)
    parts = [f"📡 Status: {ui_tag('stopped')}", ui_row('📄', 'File', info.get('file_name', '?'), code=True), *rows]
    if tail:
        parts += ["👇 Last log lines:", ui_expand(tail, 800)]
    fn = ui_err if kind == 'err' else ui_warn
    return fn('Script Stopped', *parts, foot=foot)


def _notify_owner(info, text):
    try:
        bot.send_message(int(info["script_owner_id"]), text, parse_mode="HTML")
    except Exception as exc:
        logger.warning("Could not notify user %s: %s", info.get("script_owner_id"), exc)


def _watchdog_plan_retry(key, info, rc, scheduled):
    """A script ended (or its restart never came up): plan the next try, or tell the owner that we stopped trying.
    Quick tries first (RESTART_BACKOFF), then slow ones (every RESTART_SLOW_DELAY seconds) before giving up."""
    state = RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})
    name = html_escape(str(info['file_name']))
    attempts = int(state.get("attempts", 0))
    if attempts >= MAX_AUTO_RESTARTS:
        slow = int(state.get("slow", 0))
        if MAX_AUTO_RESTARTS > 0 and slow < RESTART_SLOW_RETRIES:
            slow += 1
            state["slow"] = slow
            state["last_error"] = f"exit={rc}"
            logger.warning("%s exited (%s); slow retry %s/%s in %ss", key, rc, slow, RESTART_SLOW_RETRIES, RESTART_SLOW_DELAY)
            if slow == 1:
                _notify_owner(info, _crash_card('warn', info,
                              [f"🔁 {MAX_AUTO_RESTARTS} baar restart karne par bhi nahi chala.",
                               ui_row('⏱️', 'Next try', f"every {RESTART_SLOW_DELAY // 60} min")],
                              'Main phir try karta rahunga. Logs check karo, shayad code me error hai.'))
            scheduled[key] = (time.time() + RESTART_SLOW_DELAY, info, attempts)
            return
        state["last_error"] = f"exit={rc}; retry limit reached"
        logger.error("Restart limit reached for %s (exit=%s)", key, rc)
        if not SHUTDOWN_EVENT.is_set():
            autostart_clear(key)       # given up: a reboot does not start a script that crashes every time
        _notify_owner(info, _crash_card('err', info,
                      [ui_row('🔁', 'Auto-restart', f"limit ({MAX_AUTO_RESTARTS}) reached")],
                      'Fix the error from the log, then tap Start in My Files.'))
        return
    attempts += 1
    state["attempts"] = attempts
    state["last_error"] = f"exit={rc}"
    delay = RESTART_BACKOFF[min(attempts - 1, len(RESTART_BACKOFF) - 1)]
    logger.warning("%s exited (%s); retry %s/%s in %ss", key, rc, attempts, MAX_AUTO_RESTARTS, delay)
    _notify_owner(info, _crash_card('warn', info,
                  ["Stopped unexpectedly.", ui_row('🔁', 'Auto-restart', f"{attempts}/{MAX_AUTO_RESTARTS} in {delay}s")],
                  'No action needed, it comes back by itself.'))
    scheduled[key] = (time.time() + delay, info, attempts)


def watchdog_loop():
    """Checks running scripts. A script that exits is restarted after a growing delay (RESTART_BACKOFF).
    The wait is tracked per script, so one failing script never delays the checks for the others."""
    logger.info("Crash watchdog started (max %s retries)", MAX_AUTO_RESTARTS)
    scheduled = {}  # script_key -> (time when the restart is due, info, attempt number)
    loops = 0
    while not SHUTDOWN_EVENT.is_set():
        try:
            loops += 1
            now = time.time()
            with STATE_LOCK:
                snapshot = list(bot_scripts.items())
            for key, info in snapshot:
                proc = info.get("process")
                if proc is None:
                    continue
                try:
                    rc = proc.poll()
                except Exception:
                    logger.exception("Could not inspect child process %s", key)
                    continue
                if rc is None:
                    started = info.get("start_time")
                    if started and (datetime.now() - started).total_seconds() >= 120:
                        _st = RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})
                        _st["attempts"] = 0
                        _st["slow"] = 0
                    if loops % 8 == 0:
                        _trim_script_log(info)
                    continue
                state = RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})
                with STATE_LOCK:
                    if bot_scripts.get(key) is not info:
                        continue
                    bot_scripts.pop(key, None)
                release_process_resources(info)  # close the log file and pipes of the finished process
                if state.get("manual_stop"):
                    continue
                _watchdog_plan_retry(key, info, rc, scheduled)

            for key, info in list(WATCHDOG_START_FAILED.items()):       # restarts that never came up
                WATCHDOG_START_FAILED.pop(key, None)
                if key not in bot_scripts and key not in scheduled and not RESTART_STATE.get(key, {}).get("manual_stop"):
                    _watchdog_plan_retry(key, info, 'start failed', scheduled)

            for key, (due, info, attempts) in list(scheduled.items()):
                if due > time.time():
                    continue
                del scheduled[key]
                if RESTART_STATE.get(key, {}).get("manual_stop"):
                    continue
                threading.Thread(target=_watchdog_restart, args=(info, key, attempts),
                                 name=f"watchdog-{key}", daemon=True).start()
        except Exception:
            logger.exception("Watchdog loop error; continuing")
        SHUTDOWN_EVENT.wait(1 if scheduled else WATCHDOG_INTERVAL)
    logger.info("Crash watchdog stopped.")

def start_watchdog():
    global WATCHDOG_STARTED
    if WATCHDOG_STARTED: return
    WATCHDOG_STARTED = True
    threading.Thread(target=watchdog_loop, name="script-watchdog", daemon=True).start()

# --- Scheduled restart (separate from the crash watchdog above) ---
def set_scheduled_restart_optout(script_key, opt_out, actor_id):
    """Save whether a script is left out of the scheduled restart."""
    with DB_LOCK:
        conn = db_connect()
        try:
            if opt_out:
                conn.execute('INSERT OR REPLACE INTO scheduled_restart_optout (script_key, set_by, set_date) VALUES (?, ?, ?)',
                             (script_key, actor_id, datetime.now().isoformat()))
            else:
                conn.execute('DELETE FROM scheduled_restart_optout WHERE script_key = ?', (script_key,))
            conn.commit()
            if opt_out: SCHEDULED_RESTART_OPTOUT.add(script_key)
            else: SCHEDULED_RESTART_OPTOUT.discard(script_key)
            logger.info("Scheduled restart for %s turned %s by %s", script_key, 'OFF' if opt_out else 'ON', actor_id)
        except sqlite3.Error as e: logger.error(f"❌ SQLite error saving scheduled restart setting for {script_key}: {e}")
        finally: conn.close()


def _scheduled_restart_worker(info, script_key):
    """Clean stop, then start again with the same launcher the watchdog uses (files and .env stay as they are)."""
    try:
        owner_id = int(info["script_owner_id"])
        file_name = info["file_name"]
        folder = info["user_folder"]
        path = os.path.join(folder, file_name)
        if not os.path.isfile(path):
            logger.error("Scheduled restart cannot find the script: %s", script_key)
            return
        target = info.get("reply_target")
        if target is None:
            logger.error("No Telegram reply target stored for %s; scheduled restart skipped", script_key)
            return
        file_type = info.get("type", "py")
        allowed, _note = launch_gate(owner_id, file_name, file_type, owner_id, queue=False, admin_override=False)
        if not allowed:
            logger.warning("Scheduled restart of %s skipped: the launch gate does not allow a start now.", script_key)
            return
        _notify_owner(info, f"🔄 <code>{html_escape(str(file_name))}</code> ka scheduled restart ho raha hai "
                            f"(har {SCHEDULED_RESTART_HOURS} ghante).")
        # Marked as a manual stop while the old process is killed, so the watchdog does not count it as a crash.
        RESTART_STATE.setdefault(script_key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
        kill_process_tree(info)
        with STATE_LOCK:
            if bot_scripts.get(script_key) is info:
                bot_scripts.pop(script_key, None)
        time.sleep(1.5)
        _reset_restart_state(owner_id, file_name)
        runner = run_js_script if file_type == "js" else run_script
        _run_auto(runner, path, owner_id, folder, file_name, target)
        up = _wait_until_running(owner_id, file_name, RESTART_START_WAIT)
        for delay in SCHEDULED_RESTART_RETRY_DELAYS:     # the old process is already gone: never leave the script down silently
            if up or script_key in bot_scripts or SHUTDOWN_EVENT.is_set() or RESTART_STATE.get(script_key, {}).get("manual_stop"):
                break
            logger.warning("Scheduled restart of %s did not come up; trying again in %ss", script_key, delay)
            SHUTDOWN_EVENT.wait(delay)
            if SHUTDOWN_EVENT.is_set() or RESTART_STATE.get(script_key, {}).get("manual_stop"):
                return
            _run_auto(runner, path, owner_id, folder, file_name, target)
            up = _wait_until_running(owner_id, file_name, RESTART_START_WAIT)
        if not up and script_key not in bot_scripts and not SHUTDOWN_EVENT.is_set() \
                and not RESTART_STATE.get(script_key, {}).get("manual_stop"):
            logger.error("Scheduled restart of %s failed after %s tries; handed to the crash watchdog.",
                         script_key, 1 + len(SCHEDULED_RESTART_RETRY_DELAYS))
            WATCHDOG_START_FAILED[script_key] = info
            _notify_owner(info, f"❌ <code>{html_escape(str(file_name))}</code> scheduled restart ke baad "
                                f"{1 + len(SCHEDULED_RESTART_RETRY_DELAYS)} baar try karke bhi start nahi hua. "
                                f"Main aur try karta rahunga; na chale to Files se Start dabao ya logs dekho.")
    except Exception:
        logger.exception("Scheduled restart worker failed: %s", script_key)
        try:
            if not is_bot_running(info["script_owner_id"], info["file_name"]) and script_key not in bot_scripts:
                WATCHDOG_START_FAILED[script_key] = info
                _notify_owner(info, f"❌ <code>{html_escape(str(info.get('file_name')))}</code> scheduled restart me problem aayi. "
                                    f"Main phir try karta rahunga; na chale to Files se Start dabao.")
        except Exception:
            pass


def scheduled_restart_loop():
    """Restarts each running script once SCHEDULED_RESTART_HOURS have passed since it started (or was last restarted),
    whether or not it crashed. Scripts that opted out, were stopped by hand or are not running are left alone."""
    interval = SCHEDULED_RESTART_HOURS * 3600
    logger.info("Scheduled restart started (every %s h)", SCHEDULED_RESTART_HOURS)
    while not SHUTDOWN_EVENT.is_set():
        try:
            now = time.time()
            with STATE_LOCK:
                snapshot = list(bot_scripts.items())
            due = []
            for key, info in snapshot:
                if key in SCHEDULED_RESTART_OPTOUT or RESTART_STATE.get(key, {}).get("manual_stop"):
                    continue
                proc = info.get("process")
                try:
                    if proc is None or proc.poll() is not None:
                        continue      # not running: the crash watchdog handles it
                except Exception:
                    continue
                started = info.get("start_time")
                since = started.timestamp() if started else now
                since = max(since, SCHEDULED_RESTART_LAST.get(key, 0))
                if now - since >= interval:
                    due.append((since, key, info))
            due.sort(key=lambda item: item[0])
            for _since, key, info in due[:SCHEDULED_RESTART_MAX_PER_CYCLE]:
                SCHEDULED_RESTART_LAST[key] = now
                threading.Thread(target=_scheduled_restart_worker, args=(info, key),
                                 name=f"sched-restart-{key}", daemon=True).start()
            alive_keys = {k for k, _i in snapshot}
            for key in [k for k in SCHEDULED_RESTART_LAST if k not in alive_keys]:
                if now - SCHEDULED_RESTART_LAST[key] > interval:
                    SCHEDULED_RESTART_LAST.pop(key, None)    # forget scripts that are gone
        except Exception:
            logger.exception("Scheduled restart loop error; continuing")
        SHUTDOWN_EVENT.wait(SCHEDULED_RESTART_CHECK_SECONDS)
    logger.info("Scheduled restart stopped.")


def start_scheduled_restart():
    global SCHEDULED_RESTART_STARTED
    if SCHEDULED_RESTART_STARTED: return
    if SCHEDULED_RESTART_HOURS <= 0:
        logger.info("Scheduled restart is off (SCHEDULED_RESTART_HOURS=0).")
        return
    SCHEDULED_RESTART_STARTED = True
    threading.Thread(target=scheduled_restart_loop, name="scheduled-restart", daemon=True).start()


def retry_failed_scripts(admin_id, chat_id):
    if admin_id not in admin_ids:
        bot.send_message(chat_id, MSG_NO_ADMIN, parse_mode='HTML')
        return
    retryable = []
    for owner_id, files_list in list(user_files.items()):
        folder = get_user_folder(owner_id)
        for file_name, file_type in list(files_list):
            key = _script_key(owner_id, file_name)
            state = RESTART_STATE.get(key, {})
            if state.get("attempts", 0) >= MAX_AUTO_RESTARTS and os.path.isfile(os.path.join(folder, file_name)):
                retryable.append((owner_id, file_name, file_type, folder))
    if not retryable:
        bot.send_message(chat_id, ui_ok('All Clear', 'No failed scripts are waiting for retry.'), parse_mode='HTML')
        return
    pm = ui_anim(chat_id, 'Retry Failed Bots', 'Starting the failed scripts again...', done=0, total=len(retryable))
    try:
        for index, (owner_id, file_name, file_type, folder) in enumerate(retryable):
            pm.update(index, len(retryable), UIRaw(f"Now: <code>{html_escape(file_name)}</code>"))
            key = _script_key(owner_id, file_name)
            RESTART_STATE[key] = {"attempts": 0, "manual_stop": False}
            msg = bot.send_message(chat_id, f"🔄 Retrying <code>{file_name}</code> for <code>{owner_id}</code>...")
            runner = run_js_script if file_type == "js" else run_script
            threading.Thread(target=runner, args=(os.path.join(folder, file_name), owner_id,
                             folder, file_name, msg), daemon=True).start()
            time.sleep(0.2)
    except BaseException:
        pm.fail()
        raise
    _say_via(pm, chat_id, f"✅ Manual retry queued for {len(retryable)} script(s).")

RESTART_ALL_LOCK = threading.Lock()   # only one "Restart All" at a time (a double tap must not restart everything twice)

def restart_all_scripts(admin_id, chat_id):
    """Admin: stop and start EVERY hosted script of every user again (retry_failed_scripts only touches failed ones).
    Covers running scripts and registered scripts that are down but were not stopped on purpose.
    Uses the same pieces as the scheduled restart: manual_stop mark, kill_process_tree, _reset_restart_state, run_script."""
    if admin_id not in admin_ids:
        bot.send_message(chat_id, MSG_NO_ADMIN, parse_mode='HTML')
        return
    if not RESTART_ALL_LOCK.acquire(blocking=False):
        bot.send_message(chat_id, "⏳ A restart of all bots is already running. Wait for its summary.")
        return
    pm = None
    try:
        targets = []      # (owner_id, file_name, file_type, folder, running_info or None)
        seen = set()
        for owner_id, files_list in list(user_files.items()):
            folder = get_user_folder(owner_id)
            for file_name, file_type in list(files_list):
                key = _script_key(owner_id, file_name)
                if key in seen or not os.path.isfile(os.path.join(folder, file_name)):
                    continue
                with STATE_LOCK:
                    info = bot_scripts.get(key)
                if info is not None and is_bot_running(owner_id, file_name):
                    targets.append((owner_id, file_name, file_type, folder, info))
                elif not RESTART_STATE.get(key, {}).get("manual_stop"):
                    targets.append((owner_id, file_name, file_type, folder, None))   # down, but not stopped by hand
                else:
                    continue
                seen.add(key)
        if not targets:
            bot.send_message(chat_id, ui_info('Nothing To Restart', 'No hosted scripts found to restart.'), parse_mode='HTML')
            return
        logger.info("Admin %s started 'restart all' for %s script(s)", admin_id, len(targets))
        pm = ui_anim(chat_id, 'Restart All Bots', f"Restarting {len(targets)} script(s) of all users. Please wait...",
                     done=0, total=len(targets) + 1)
        admin_msg = _ReplyTarget(chat_id, pm.message_id, admin_id) if pm.message_id is not None \
            else bot.send_message(chat_id, f"🔁 Restarting {len(targets)} script(s) of all users. Please wait...")
        launchers, held, failed = [], 0, 0
        was_running = 0
        for index, (owner_id, file_name, file_type, folder, info) in enumerate(targets):
            pm.update(index, len(targets) + 1, UIRaw(f"Now: <code>{html_escape(file_name)}</code>"))
            key = _script_key(owner_id, file_name)
            path = os.path.join(folder, file_name)
            try:
                allowed, _note = launch_gate(owner_id, file_name, file_type, admin_id, queue=False, admin_override=False)
                if not allowed:       # checked BEFORE stopping, so a script that may not start again is not killed for nothing
                    held += 1
                    continue
                if info is not None:
                    was_running += 1
                    RESTART_STATE.setdefault(key, {"attempts": 0, "manual_stop": False})["manual_stop"] = True
                    kill_process_tree(info)
                    with STATE_LOCK:
                        if bot_scripts.get(key) is info:
                            bot_scripts.pop(key, None)
                    time.sleep(1.5)
                _reset_restart_state(owner_id, file_name)
                target = (info or {}).get("reply_target") or admin_msg
                runner = run_js_script if file_type == "js" else run_script
                thread = threading.Thread(target=runner, args=(path, owner_id, folder, file_name, target), daemon=True)
                thread.start()
                launchers.append((owner_id, file_name, thread))
                time.sleep(0.7)
            except Exception:
                failed += 1
                logger.exception("Restart all: could not restart %s", key)
        pm.update(len(targets), len(targets) + 1, 'Waiting for the scripts to come back up...')
        deadline = time.time() + 90
        for _owner, _name, thread in launchers:
            thread.join(timeout=max(0.1, deadline - time.time()))
        up = sum(1 for owner_id, file_name, _t in launchers if is_bot_running(owner_id, file_name))
        lines = ["✅ Restart All finished.",
                 f"🔁 Restarted: {up} of {len(launchers)} script(s) are running again.",
                 f"▶️ Were running before: {was_running}"]
        if held:
            lines.append(f"🚫 Skipped (suspended or start blocked, not touched): {held}")
        if failed:
            lines.append(f"⚠️ Errors: {failed} (see logs)")
        if len(launchers) - up > 0:
            lines.append(f"❌ Not running after restart: {len(launchers) - up} (the watchdog / Retry Failed Bots can try again)")
        _say_via(pm, chat_id, "\n".join(lines))
        logger.info("Restart all done by %s: targets=%s running=%s held=%s failed=%s", admin_id, len(targets), up, held, failed)
    finally:
        if pm is not None and not pm._done:
            pm.fail()
        RESTART_ALL_LOCK.release()

def hosting_health_callback(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "Admin only", show_alert=True); return
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(build_hosting_health_report(), call.message.chat.id,
                              call.message.message_id, parse_mode="HTML",
                              reply_markup=create_admin_settings_menu())
    except Exception: logger.exception("Unable to show hosting health")

def retry_failed_callback(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "Admin only", show_alert=True); return
    bot.answer_callback_query(call.id, "Retry queue started")
    threading.Thread(target=retry_failed_scripts,
                     args=(call.from_user.id, call.message.chat.id), daemon=True).start()

def restart_all_callback(call):
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, "Admin only", show_alert=True); return
    bot.answer_callback_query(call.id, "Restarting all bots")
    threading.Thread(target=restart_all_scripts,
                     args=(call.from_user.id, call.message.chat.id), daemon=True).start()


# --- Admin Settings Callbacks ---
def admin_settings_callback(call):
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(ui_msg('⚙️', 'ADMIN SETTINGS', '🛠️ Pick an action from the buttons below.', foot='Admin tools only.', brand=True), call.message.chat.id,
                              call.message.message_id, reply_markup=create_admin_settings_menu(), parse_mode='HTML')
    except Exception as e: logger.error(f"Error showing admin settings: {e}")

def system_info_callback(call):
    bot.answer_callback_query(call.id)
    try:
        import platform
        up = max(0, int(time.time() - HOST_START_TIME))
        lines = [ui_section('🤖', 'Bot Information'),
                 ui_row('✨', 'Version', f"{BOT_VERSION} Premium"),
                 ui_row('🐍', 'Python', platform.python_version()),
                 ui_row('🖥️', 'Platform', platform.platform()),
                 ui_row('⏱️', 'Bot uptime', ui_uptime(up)),
                 ui_section('💻', 'System')]
        try:
            cpu_text, ram_text = _safe_cpu_health(), _safe_memory_health()
            lines.append(ui_row('🧠', 'CPU', cpu_text))
            if _res_bar(cpu_text):
                lines.append(_res_bar(cpu_text))
            lines.append(ui_row('💾', 'Memory', ram_text))
            if _res_bar(ram_text):
                lines.append(_res_bar(ram_text))
            disk = shutil.disk_usage(BASE_DIR)
            lines.append(ui_row('💿', 'Disk', f"{disk.used / disk.total * 100:.1f}% used ({disk.used//1024//1024}MB/{disk.total//1024//1024}MB)"))
            lines.append(f"<code>{ui_bar(disk.used, disk.total)}</code>")
        except Exception as e:
            logger.warning("System stats failed: %s", e)
            lines.append(ui_warn_line('System stats are not available right now'))
        lines += [ui_section('📊', 'Bot Statistics'),
                  ui_row('👥', 'Active users', len(active_users)),
                  ui_row('🚀', 'Running scripts', len(bot_scripts)),
                  ui_row('📦', 'Total files', sum(len(files) for files in user_files.values())),
                  f"🔐 Bot status: {ui_tag('locked') if bot_locked else ui_tag('unlocked')}"]
        try:
            for line in auto_backup_status_lines():
                lines.append(ui_row('💾', 'Auto backup', re.sub(r'^Auto backup:\s*', '', line.lstrip('•- ').strip())))
        except Exception as exc:
            logger.warning("Auto backup status not shown: %s", exc)
        bot.edit_message_text(ui_msg('💻', 'SYSTEM INFO', *lines, brand=True), call.message.chat.id,
                              call.message.message_id, reply_markup=create_admin_settings_menu(), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error showing system info: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "😕 System info is not available right now.", show_alert=True)

def bot_performance_callback(call):
    bot.answer_callback_query(call.id)
    try:
        running_scripts = len(bot_scripts)
        total_files = sum(len(files) for files in user_files.values())
        lines = [f"📡 Engine: {ui_tag('active') if running_scripts else ui_tag('off', 'IDLE')}",
                 ui_section('🚀', 'Scripts'),
                 ui_row('⚡', 'Running', running_scripts),
                 ui_row('📦', 'Total', total_files),
                 ui_row('📈', 'Running ratio', f"{running_scripts}/{total_files} ({running_scripts / total_files * 100:.1f}%)" if total_files else "0/0 (N/A)")]
        if total_files:
            lines.append(f"<code>{ui_bar(running_scripts, total_files)}</code>")
        try:
            bot_process = psutil.Process()
            memory_usage = bot_process.memory_info().rss / 1024 / 1024
            cpu_usage = bot_process.cpu_percent(interval=0.5)
            lines += [ui_section('💾', 'Resource Usage'),
                      ui_row('💾', 'Memory', f"{memory_usage:.1f} MB"),
                      ui_row('🧠', 'CPU', f"{cpu_usage:.1f}%"),
                      f"<code>{ui_bar(min(cpu_usage, 100), 100)}</code>",
                      f"🚦 Load: {ui_tag('ok', 'LIGHT') if cpu_usage < 60 else (ui_tag('warn', 'BUSY') if cpu_usage < 85 else ui_tag('stopped', 'HEAVY'))}"]
        except Exception as e:
            logger.warning("Resource stats failed: %s", e)
            lines.append(ui_warn_line('Resource stats are not available right now'))
        lines += [ui_section('🗄️', 'Database'),
                  ui_row('👥', 'Active users', len(active_users)),
                  ui_row('💎', 'Subscriptions', len(user_subscriptions)),
                  ui_row('🚫', 'Banned users', len(banned_users)),
                  ui_row('🎚️', 'Custom limits', len(user_limits))]
        bot.edit_message_text(ui_msg('📈', 'BOT PERFORMANCE', *lines, brand=True), call.message.chat.id,
                              call.message.message_id, reply_markup=create_admin_settings_menu(), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error showing performance: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "😕 Performance stats are not available right now.", show_alert=True)

def cleanup_files_callback(call):
    bot.answer_callback_query(call.id, "🧹 Cleaning up temporary files...")
    pm = None
    try:
        # Clean up empty user directories
        cleaned_dirs = 0
        cleaned_files = 0
        entries = os.listdir(UPLOAD_BOTS_DIR)
        pm = _call_anim(call, 'Cleanup', 'Removing empty folders and old logs', done=0, total=max(len(entries), 1))
        
        for n_done, user_dir in enumerate(entries, 1):
            if pm is not None:
                pm.update(n_done - 1, max(len(entries), 1), f"Folders: {cleaned_dirs} removed  |  Logs: {cleaned_files} cleared")
            if user_dir.startswith('.'):
                continue  # temporary restore folders (.restore_in_*, .restore_old_*) must not be touched
            user_path = os.path.join(UPLOAD_BOTS_DIR, user_dir)
            if os.path.isdir(user_path):
                # Check if directory is empty
                if not os.listdir(user_path):
                    try:
                        os.rmdir(user_path)
                        cleaned_dirs += 1
                    except Exception as e:
                        logger.error(f"Error removing empty dir {user_path}: {e}")
                
                # Clean old log files (older than 7 days)
                else:
                    for file_name in os.listdir(user_path):
                        if file_name.endswith('.log'):
                            file_path = os.path.join(user_path, file_name)
                            try:
                                file_age = time.time() - os.path.getmtime(file_path)
                                if file_age > 7 * 24 * 3600:  # 7 days
                                    os.remove(file_path)
                                    cleaned_files += 1
                            except Exception as e:
                                logger.error(f"Error cleaning log file {file_path}: {e}")
        
        result_msg = f"🧹 **Cleanup Complete:**\n• Removed empty directories: {cleaned_dirs}\n• Cleared old log files: {cleaned_files}"
        
        if pm is not None and not pm._done:
            pm.finish(result_msg, parse_mode='Markdown', reply_markup=create_admin_settings_menu())
        else:
            bot.edit_message_text(result_msg, call.message.chat.id, call.message.message_id,
                                  reply_markup=create_admin_settings_menu(), parse_mode='Markdown')
        
    except Exception as e:
        logger.error(f"Error during cleanup: {e}", exc_info=True)
        failed = ui_err('Cleanup Failed', ui_user_error(e))
        if pm is not None and not pm._done:
            pm.finish(failed)
        else:
            bot.edit_message_text(failed, call.message.chat.id, call.message.message_id, parse_mode='HTML')

def install_logs_callback(call):
    bot.answer_callback_query(call.id)
    try:
        with DB_LOCK:
            conn = db_connect()
            c = conn.cursor()
            c.execute('SELECT user_id, module_name, package_name, status, install_date FROM install_logs ORDER BY install_date DESC LIMIT 20')
            logs = c.fetchall()
            conn.close()
        
        if not logs:
            bot.edit_message_text("📋 **No installation logs found**", call.message.chat.id, 
                                  call.message.message_id, reply_markup=create_admin_settings_menu())
            return
        
        log_text = "📋 **Recent Installation Logs (Last 20):**\n\n"
        for user_id, module_name, package_name, status, install_date in logs:
            status_icon = "✅" if status == "success" else "❌" if status == "failed" else "⚠️"
            log_text += f"{status_icon} `{user_id}`: {module_name} -> {package_name}\n"
            log_text += f"   📅 {install_date[:19]}\n\n"
        
        bot.edit_message_text(log_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_admin_settings_menu(), parse_mode='Markdown')
        
    except Exception as e:
        logger.error(f"Error showing install logs: {e}", exc_info=True)
        bot.answer_callback_query(call.id, "Error showing logs.", show_alert=True)

def admin_install_callback(call):
    bot.answer_callback_query(call.id)
    _logic_admin_install(call.message)

# --- Mandatory Channels Callbacks ---
def manage_mandatory_channels_callback(call):
    """Handle mandatory channels management request"""
    bot.answer_callback_query(call.id)
    try:
        bot.edit_message_text(_channels_card(),
                              call.message.chat.id, call.message.message_id,
                              reply_markup=create_mandatory_channels_menu(), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error showing channel management menu: {e}")

def add_mandatory_channel_callback(call):
    """Start the mandatory-channel setup flow."""
    if call.from_user.id not in admin_ids:
        bot.answer_callback_query(call.id, ui_toast('err', 'Admin permissions required.'), show_alert=True)
        return
    bot.answer_callback_query(call.id)
    prompt = ui_msg('📢', 'Add Force-Join Channel',
                    'Send one of these: <code>@public_channel</code>, <code>https://t.me/public_channel</code>, '
                    'or numeric channel ID such as <code>-1001234567890</code>.',
                    "🟡 <b>Important:</b> Add this bot as an administrator in the channel first.",
                    'Private channels require their numeric ID; the invite link is asked next.',
                    foot='Send /cancel to stop.')
    msg = bot.send_message(call.message.chat.id, prompt, parse_mode='HTML')
    bot.register_next_step_handler(msg, process_add_channel)

def _normalize_channel_identifier(raw_value):
    """Normalize common Telegram channel username/link/ID formats."""
    value = (raw_value or '').strip()
    if not value:
        raise ValueError('Channel ID or username is empty.')
    value = value.split('?')[0].rstrip('/')
    value = re.sub(r'^https?://(?:www\.)?(?:t\.me|telegram\.me)/', '', value, flags=re.I)
    if value.startswith('s/'):
        value = value[2:]
    # A t.me/c/<internal-id>/<message-id> link maps to a -100 channel ID.
    private_match = re.match(r'^c/(\d+)(?:/\d+)?$', value)
    if private_match:
        return '-100' + private_match.group(1)
    if value.startswith('@'):
        return value
    if re.fullmatch(r'-?\d+', value):
        return value
    if re.fullmatch(r'[A-Za-z0-9_]{5,}', value):
        return '@' + value
    raise ValueError('Invalid format. Send @username, a t.me channel link, or a numeric -100 channel ID.')

def process_add_channel(message):
    """Validate bot permissions and save a force-join channel."""
    admin_id = message.from_user.id
    if admin_id not in admin_ids:
        bot.reply_to(message, MSG_NO_ADMIN, parse_mode='HTML')
        return
    if not message.text:
        bot.reply_to(message, ui_warn('Text Needed', 'Please send the channel username, link, or numeric ID as text.', foot='Send /cancel to cancel.'), parse_mode='HTML')
        return
    if message.text.strip().lower() == '/cancel':
        bot.reply_to(message, ui_info('Cancelled', 'Channel addition cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return

    try:
        channel_identifier = _normalize_channel_identifier(message.text)
        chat = bot.get_chat(channel_identifier)
        if getattr(chat, 'type', None) not in ('channel', 'supergroup'):
            bot.reply_to(message, ui_warn('Not A Channel', 'This is not a Telegram channel or supergroup.', foot='Send a channel username or channel ID.'), parse_mode='HTML')
            return

        channel_id = str(chat.id)
        channel_username = f"@{chat.username}" if getattr(chat, 'username', None) else ""
        channel_name = getattr(chat, 'title', None) or channel_username or channel_id

        try:
            bot_member = bot.get_chat_member(channel_id, bot.get_me().id)
        except Exception as permission_error:
            logger.warning('Cannot inspect bot membership in channel %s: %s', channel_id, permission_error, exc_info=True)
            bot.reply_to(
                message,
                ui_err('Bot Cannot Access This Channel',
                       ui_steps('Add the bot to the channel', 'Promote it to administrator', "Retry using the channel's @username or -100 channel ID"),
                       ui_row('💬', 'Telegram says', str(permission_error)[:350], code=True, bold=False)),
                parse_mode='HTML'
            )
            return

        if getattr(bot_member, 'status', None) not in ('administrator', 'creator'):
            bot.reply_to(message, ui_warn('Bot Is Not Admin', 'The bot is not an administrator in this channel.', foot='Promote the bot to admin there and try again.'), parse_mode='HTML')
            return

        if not channel_username:
            # Private channels have no public t.me/username URL. Ask for a real invite link.
            pending_channel_add[admin_id] = {
                'channel_id': channel_id,
                'username': '',
                'name': channel_name,
                'added_by': admin_id
            }
            prompt = bot.reply_to(
                message,
                ui_info('Private Channel Detected', 'Send its invite link now (<code>https://t.me/+...</code> or <code>https://t.me/joinchat/...</code>).',
                        foot='Send /cancel to abort.'),
                parse_mode='HTML'
            )
            bot.register_next_step_handler(prompt, process_private_channel_invite)
            return

        if save_mandatory_channel(channel_id, channel_username, channel_name, admin_id):
            bot.reply_to(
                message,
                ui_ok('Channel Added', f"🔒 Join gate: {ui_tag('active', 'ENFORCED')}", ui_row('📢', 'Channel', channel_name),
                      ui_row('🆔', 'ID', channel_id, code=True), ui_row('🔗', 'Link', channel_username),
                      foot='New users must join it before using the bot.'),
                parse_mode='HTML',
                reply_markup=create_mandatory_channels_menu()
            )
        else:
            bot.reply_to(message, ui_err('Could Not Save', 'The database could not save this channel.', foot='Check hosting logs and database write permissions.'), parse_mode='HTML')
    except ValueError as exc:
        bot.reply_to(message, ui_warn('Check The Channel', html_escape(str(exc)), foot='Send the channel again or /cancel.'), parse_mode='HTML')
    except Exception as exc:
        logger.error('Error adding mandatory channel: %s', exc, exc_info=True)
        error_text = str(exc)
        if 'chat not found' in error_text.lower():
            hint = 'Channel not found. Check the username/ID and make sure the bot is already added to the channel.'
        elif 'not enough rights' in error_text.lower() or 'administrator' in error_text.lower():
            hint = 'Bot needs administrator access in that channel.'
        else:
            hint = 'Could not add this channel. Verify the channel ID/username and bot admin permissions.'
        bot.reply_to(message, ui_err('Channel Not Added', hint, ui_row('💬', 'Telegram says', error_text[:350], code=True, bold=False), foot='Fix it and try Channel Add again.'), parse_mode='HTML')

def process_private_channel_invite(message):
    admin_id = message.from_user.id
    pending = pending_channel_add.get(admin_id)
    if admin_id not in admin_ids or not pending:
        bot.reply_to(message, ui_warn('Setup Expired', 'This channel setup has expired.', foot='Start again from Channel Add.'), parse_mode='HTML')
        return
    if not message.text:
        bot.reply_to(message, ui_warn('Text Needed', 'Send the private invite URL as text.', foot='Or send /cancel to stop.'), parse_mode='HTML')
        bot.register_next_step_handler(message, process_private_channel_invite)
        return
    value = message.text.strip()
    if value.lower() == '/cancel':
        pending_channel_add.pop(admin_id, None)
        bot.reply_to(message, ui_info('Cancelled', 'Private channel setup cancelled. Nothing was changed.', foot='Use the menu to continue.'), parse_mode='HTML')
        return
    if not re.match(r'^https?://(?:www\.)?t\.me/(?:\+[^/\s]+|joinchat/[^/\s]+)(?:\?.*)?$', value, re.I):
        bot.reply_to(message, ui_warn('Invalid Invite Link', 'That does not look like an invite link.', foot='Use https://t.me/+... or https://t.me/joinchat/... or send /cancel.'), parse_mode='HTML')
        bot.register_next_step_handler(message, process_private_channel_invite)
        return
    pending_channel_add.pop(admin_id, None)
    if save_mandatory_channel(pending['channel_id'], '', pending['name'], admin_id, invite_link=value):
        bot.reply_to(
            message,
            ui_ok('Private Channel Added', f"🔒 Join gate: {ui_tag('active', 'ENFORCED')}", ui_row('📢', 'Channel', pending['name']),
                  ui_row('🆔', 'ID', pending['channel_id'], code=True), ui_row('🔗', 'Invite', value),
                  foot='New users must join it before using the bot.'),
            parse_mode='HTML', reply_markup=create_mandatory_channels_menu()
        )
    else:
        bot.reply_to(message, ui_err('Could Not Save', 'The database could not save this channel.', foot='Check hosting logs and try again.'), parse_mode='HTML')


def remove_mandatory_channel_callback(call):
    """Remove mandatory channel"""
    if not mandatory_channels:
        bot.answer_callback_query(call.id, "❌ No mandatory channels.", show_alert=True)
        return
        
    bot.answer_callback_query(call.id)
    
    markup = NavMenu()
    shown, page, pages = _paginate(call.message.chat.id, 'rmchan', list(mandatory_channels.items()))
    markup.offset = page * NAV_PAGE_SIZE
    for channel_id, channel_info in shown:
        channel_name = channel_info.get('name', 'Unknown')
        button_text = f"🗑️ {channel_name}"
        markup.add(NavButton(button_text, callback_data=f'remove_channel_{channel_id}'), row_width=1)
    markup.pager('rmchan', 'remove_mandatory_channel', page, pages)
    markup.add(NavButton("🔙 Back", callback_data='manage_mandatory_channels'))
    
    try:
        bot.edit_message_text(ui_msg('🗑️', 'Remove Channel', ui_row('📢', 'Channels', ui_num(len(mandatory_channels))),
                                     foot='Tap a channel below to remove it from the join gate.' + _page_note(page, pages)),
                              call.message.chat.id, call.message.message_id,
                              reply_markup=markup, parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error showing remove channel menu: {e}")

def process_remove_channel(call):
    """Process channel removal"""
    channel_id = call.data.replace('remove_channel_', '')
    
    if channel_id in mandatory_channels:
        channel_name = mandatory_channels[channel_id].get('name', 'Unknown')
        if remove_mandatory_channel_db(channel_id):
            bot.answer_callback_query(call.id, f"✅ Channel deleted: {channel_name}")
            try:
                bot.edit_message_text(ui_ok('Channel Removed', ui_row('📢', 'Channel', channel_name), ui_row('📢', 'Left', ui_num(len(mandatory_channels))),
                                            foot='Users no longer need to join it.'),
                                      call.message.chat.id, call.message.message_id,
                                      reply_markup=create_mandatory_channels_menu(), parse_mode='HTML')
            except Exception as e:
                logger.error(f"Error updating message after channel removal: {e}")
        else:
            bot.answer_callback_query(call.id, "❌ Failed to delete channel.", show_alert=True)
    else:
        bot.answer_callback_query(call.id, "❌ Channel not found.", show_alert=True)

def list_mandatory_channels_callback(call):
    """Show list of mandatory channels"""
    bot.answer_callback_query(call.id)
    
    if not mandatory_channels:
        message_text = ui_msg('📢', 'Mandatory Channels', f"🔒 Join gate: {ui_tag('off', 'NOT SET')}",
                              '🌱 No mandatory channels yet.', foot='Tap Add Channel to require users to join one.')
    else:
        items = list(mandatory_channels.items())
        lines = []
        for channel_id, channel_info in items[:20]:
            channel_name = channel_info.get('name', 'Unknown')
            channel_username = channel_info.get('username') or channel_id
            lines.append(f"📢 <b>{ui_esc(str(channel_name)[:60])}</b>\n    <code>{ui_esc(str(channel_username)[:60])}</code>")
        if len(items) > 20:
            lines.append(f"<i>+{len(items) - 20} more</i>")
        message_text = ui_msg('📢', 'Mandatory Channels', f"🔒 Join gate: {ui_tag('active', 'ENFORCED')}",
                              ui_row('📢', 'Channels', ui_num(len(items))), *lines, foot='Users must join all of these to use the bot.')

    try:
        bot.edit_message_text(message_text, call.message.chat.id, call.message.message_id,
                              reply_markup=create_mandatory_channels_menu(), parse_mode='HTML')
    except Exception as e:
        logger.error(f"Error listing channels: {e}")

def check_subscription_status_callback(call):
    """Check subscription status"""
    user_id = call.from_user.id
    is_subscribed, not_joined = check_mandatory_subscription(user_id)
    
    if is_subscribed or user_id in admin_ids:
        bot.answer_callback_query(call.id, "✅ You are subscribed to all required channels!", show_alert=True)
        # Show main menu
        try:
            _logic_send_welcome(call.message)
        except Exception:
            back_to_main_callback(call)
    else:
        bot.answer_callback_query(call.id, "❌ You haven't joined all required channels yet!", show_alert=True)
        # Update the subscription message
        subscription_message, markup = create_subscription_check_message(not_joined)
        try:
            bot.edit_message_text(subscription_message, call.message.chat.id, 
                                  call.message.message_id, reply_markup=markup, parse_mode='HTML')
        except Exception as e:
            logger.error(f"Error updating subscription message: {e}")

# --- Auto-resume after a restart or redeploy -------------------------------------------------------------------------
class _ResumeMessage(_NavMessage):
    """Stand-in 'message' for a script started by the boot auto-resume: replies go to the owner's private chat.
    quiet=True hides the per-script 'started' reply (the owner gets one summary instead)."""
    quiet = True


from types import SimpleNamespace as _SimpleNamespace


def _resume_target(owner_id):
    who = _SimpleNamespace(id=int(owner_id), is_bot=False, first_name='', username=None)
    chat = _SimpleNamespace(id=int(owner_id), type='private')
    return _ResumeMessage(chat, who, '')


def _resume_skip_reason(owner_id, file_name, file_type):
    """Why a remembered script must NOT start again now ('' = go on). Returns (reason, forget) where forget means the
    memory entry is useless and is deleted."""
    if owner_id in banned_users:
        return 'banned', True
    if owner_id in suspended_users and owner_id not in admin_ids:
        return 'suspended', True
    if not any(f[0] == file_name for f in user_files.get(owner_id, [])):
        return 'file no longer registered', True
    if not os.path.isfile(os.path.join(get_user_folder(owner_id), file_name)):
        return 'file missing on disk', True
    if RESTART_STATE.get(_script_key(owner_id, file_name), {}).get('manual_stop'):
        return 'stopped by hand', True
    if is_bot_running(owner_id, file_name):
        return 'already running', False
    return '', False


def resume_scripts_on_boot(gap_seconds=None):
    """Start again the scripts that were running when the bot last stopped (restart, redeploy, crash of the host).
    Not started: scripts stopped on purpose (their memory entry is gone), files of banned or suspended users, deleted
    files, and anything the launch gate does not allow. Starts are spread out by a few seconds.
    Returns a summary dict (also logged)."""
    summary = {'started': 0, 'skipped': 0, 'failed': 0}
    if not AUTO_RESUME_ON_BOOT:
        logger.info("Auto-resume on boot is OFF (AUTO_RESUME_ON_BOOT=0); hosted scripts stay stopped until started.")
        return summary
    gap = AUTO_RESUME_GAP_SECONDS if gap_seconds is None else gap_seconds
    try:
        rows = autostart_rows()
    except Exception:
        logger.exception("Auto-resume: could not read the was-running list")
        return summary
    if not rows:
        logger.info("Auto-resume: no scripts were running before this start.")
        return summary
    logger.info("Auto-resume: %s script(s) were running before; starting them one by one.", len(rows))
    per_owner = {}
    first = True
    for key, owner_id, file_name, saved_type in rows:
        if SHUTDOWN_EVENT.is_set():
            break
        try:
            file_type = next((f[1] for f in user_files.get(owner_id, []) if f[0] == file_name), saved_type or 'py')
            reason, forget = _resume_skip_reason(owner_id, file_name, file_type)
            if not reason:
                allowed, _note = launch_gate(owner_id, file_name, file_type, owner_id, queue=False, admin_override=False)
                if not allowed:
                    reason, forget = 'launch gate does not allow a start', False
            if reason:
                summary['skipped'] += 1
                logger.info("Auto-resume: %s not started (%s).", key, reason)
                if forget:
                    autostart_clear(key)
                continue
            if not first and gap > 0:
                SHUTDOWN_EVENT.wait(gap)
                if SHUTDOWN_EVENT.is_set():
                    break
            first = False
            folder = get_user_folder(owner_id)
            target = _resume_target(owner_id)
            _reset_restart_state(owner_id, file_name)
            runner = run_js_script if file_type == 'js' else run_script
            runner(os.path.join(folder, file_name), owner_id, folder, file_name, target)
            if is_bot_running(owner_id, file_name):
                summary['started'] += 1
                per_owner.setdefault(owner_id, []).append(file_name)
                with STATE_LOCK:      # later watchdog restarts talk to the owner normally again
                    info = bot_scripts.get(key)
                    if info is not None and info.get('reply_target') is target:
                        info['reply_target'] = _NavMessage(target.chat, target.from_user, '')
            else:
                summary['failed'] += 1
                logger.warning("Auto-resume: %s did not come up.", key)
        except Exception:
            summary['failed'] += 1
            logger.exception("Auto-resume failed for %s; going on with the next one", key)
    for owner_id, names in per_owner.items():
        try:
            listed = ', '.join(f"<code>{html_escape(n)}</code>" for n in names[:10])
            more = f" (+{len(names) - 10} aur)" if len(names) > 10 else ''
            bot.send_message(owner_id, f"🔁 Bot restart hua tha, isliye teri chal rahi script(s) wapas start kar di: {listed}{more}",
                             parse_mode='HTML')
        except Exception as exc:
            logger.debug("Auto-resume notice to %s not sent: %s", owner_id, exc)
    logger.info("Auto-resume finished: %(started)s started, %(skipped)s skipped, %(failed)s failed.", summary)
    return summary


_RESUME_LOCK = threading.Lock()
_resume_scripts_inner = resume_scripts_on_boot


def resume_scripts_on_boot(gap_seconds=None):
    """One resume at a time (the normal boot one and the one after a late automatic restore must not overlap)."""
    with _RESUME_LOCK:
        return _resume_scripts_inner(gap_seconds)


for _ab_name in ('autostart_mark', 'autostart_clear'):
    _ab_wrap_change(_ab_name)


def start_auto_resume():
    """Run the auto-resume in the background a few seconds after the bot is up."""
    def _worker():
        try:
            SHUTDOWN_EVENT.wait(6)
            if not SHUTDOWN_EVENT.is_set():
                resume_scripts_on_boot()
        except Exception:
            logger.exception("Auto-resume thread crashed")
    threading.Thread(target=_worker, name="auto-resume", daemon=True).start()


# --- Cleanup Function ---
_CLEANUP_DONE = False

def cleanup():
    """Stop every hosted script. Safe to call more than once."""
    global _CLEANUP_DONE
    if _CLEANUP_DONE:
        return
    _CLEANUP_DONE = True
    SHUTDOWN_EVENT.set()
    logger.warning("Shutdown. Cleaning up processes...")
    with STATE_LOCK:
        infos = list(bot_scripts.items())
    if not infos:
        logger.info("No scripts running. Exiting.")
        return
    logger.info("Stopping %s scripts...", len(infos))
    for key, info in infos:
        try:
            logger.info("Stopping: %s", key)
            kill_process_tree(info)
        except Exception:
            logger.exception("Could not stop %s", key)
    logger.warning("Cleanup finished.")
atexit.register(cleanup)


def _handle_signal(signum, _frame):
    logger.warning("Received signal %s; shutting down gracefully.", signum)
    SHUTDOWN_EVENT.set()
    try:
        bot.stop_polling()
    except Exception as exc:
        logger.debug("stop_polling: %s", exc)


def run_polling_forever():
    """Run polling; if it ever stops or fails, restart with a growing delay (max 60s).
    Old updates are skipped only on the very first start (after a deploy); after a polling restart the messages that
    arrived meanwhile are kept, so nobody's button press or upload is lost during a short network problem."""
    delay = 3
    first_run = True
    while not SHUTDOWN_EVENT.is_set():
        started = time.time()
        HEALTH_STATE['last_poll_start'] = datetime.now().isoformat(timespec='seconds')
        try:
            bot.infinity_polling(logger_level=logging.INFO, timeout=60, long_polling_timeout=30,
                                 skip_pending=first_run)
            first_run = False
        except requests.exceptions.ReadTimeout:
            logger.warning("Polling read timeout.")
        except requests.exceptions.ConnectionError as ce:
            logger.error("Polling connection error: %s", ce)
            HEALTH_STATE['last_error'] = 'connection error'
        except Exception as exc:
            logger.exception("Polling crashed: %s", exc)
            HEALTH_STATE['last_error'] = str(exc)[:200]
        first_run = False
        if SHUTDOWN_EVENT.is_set():
            break
        HEALTH_STATE['poll_restarts'] += 1
        # A run that lasted a while means the network was fine: start the backoff over.
        delay = 3 if time.time() - started > 120 else min(delay * 2, 60)
        logger.warning("Polling stopped. Restarting in %ss (restart #%s).", delay, HEALTH_STATE['poll_restarts'])
        SHUTDOWN_EVENT.wait(delay)


_INSTANCE_LOCK = None


def acquire_instance_lock(path=None):
    """Only one copy of the bot may poll Telegram: two copies answer every key press twice. Returns True when this
    process got the lock (it is held until the process ends); on a system without fcntl nothing is enforced."""
    global _INSTANCE_LOCK
    try:
        import fcntl
    except ImportError:
        return True
    handle = open(path or os.path.join(IROTECH_DIR, 'bot.lock'), 'a+')
    try:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        handle.close()
        return False
    _INSTANCE_LOCK = handle
    return True


# --- Main Execution ---
@bot.message_handler(func=lambda m: m.chat.type == 'private' and bool(m.text) and not m.text.startswith('/'),
                     content_types=['text'])
def handle_stale_text(message):
    """Registered last: any other text brings the current keyboard back."""
    _nav_stale(message)


if __name__ == '__main__':
    logger.info("Starting up. Bot version %s | Python %s | data dir: %s | owner: %s | admins: %s | banned: %s | channels: %s",
                BOT_VERSION, sys.version.split()[0], IROTECH_DIR, OWNER_ID, len(admin_ids), len(banned_users),
                len(mandatory_channels))
    for _sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(_sig, _handle_signal)
        except (ValueError, OSError) as exc:
            logger.warning("Could not install handler for %s: %s", _sig, exc)
    if not acquire_instance_lock():
        logger.error("Another copy of this bot is already running (same data folder). Stopping this one.")
        logging.shutdown()
        os._exit(1)                  # not sys.exit: the exit hook would stop scripts that belong to the running copy
    try:
        sandbox_log_startup()        # find out (by really trying) how strong the isolation of hosted scripts can be here
    except Exception:
        logger.exception("Sandbox check failed; hosted scripts will run with the basic protections only")
    keep_alive()
    start_watchdog()
    start_scheduled_restart()
    start_temp_ban()
    auto_restore_on_boot()       # a wiped install (redeploy without a Volume) gets its data back from the pinned Telegram backup
    start_auto_resume()
    start_auto_backup()
    logger.info("Starting polling...")
    try:
        run_polling_forever()
    finally:
        cleanup()
        logging.shutdown()
