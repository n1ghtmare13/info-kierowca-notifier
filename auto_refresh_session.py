#!/usr/bin/env python3
"""Auto-heals an expired info-kierowca.pl session.

Launches Chrome (in its own throwaway profile, separate from your regular
browsing) pointed at the login page, waits for you to scan the mObywatel QR
code in the app, then captures the resulting session cookies the moment
they appear and writes session.json — no manual "launch Chrome, log in, run
a script" dance required.

Run by hand:

    python auto_refresh_session.py

or invoked automatically by notifier.py (see trigger_auto_refresh() in
notifier.py) whenever a check comes back auth_expired. A lock file at
~/.local/state/info-kierowca-notifier/auto-refresh.lock stops it firing
more than once concurrently — delete that file if a previous run crashed
without cleaning up.

Nothing but the two info-kierowca.pl session cookies is read or sent
anywhere; see cdp_client.py's docstring for the debug-port security note.
"""

import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

import cdp_client

from paths import AUTO_REFRESH_COOLDOWN_FILE  # noqa: E402
from paths import AUTO_REFRESH_LOCK as LOCK_FILE  # noqa: E402
from paths import CONFIG_FILE, STATE_DIR  # noqa: E402,F401

PROFILE_DIR = STATE_DIR / "chrome-relogin-profile"

# Deliberately distinct from pull_session_cookies.py's manual default (9222)
# so this never fights over the port with a Chrome you started by hand.
DEFAULT_PORT = 9333
DEFAULT_URL = "https://info-kierowca.pl/login"
# No default timeout: you'll log back in eventually regardless, and the lock
# file already stops this from being relaunched while one is in flight — so
# just wait for the QR to be scanned, however long that takes. Pass --timeout
# to bound it (e.g. for testing).
DEFAULT_TIMEOUT = None

# Edge is Chromium-based and supports the same --remote-debugging-port CDP
# flag, so it's included as a fallback — it's preinstalled on all Windows
# machines, unlike Chrome, which matters for a "no setup needed" install.
CHROME_CANDIDATES = [
    "google-chrome",
    "google-chrome-stable",
    "chromium",
    "chromium-browser",
    "msedge",
    "microsoft-edge",
    "microsoft-edge-stable",
]
CHROME_MAC_PATH = Path("/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
# CHROME_MAC_PATH only covers the common system-wide install location — the
# same class of gap CHROME_WIN_PATHS had on Windows before the registry
# lookup below existed, and by the same reasoning it would miss Chrome
# installed to ~/Applications (no-admin-rights install) or anywhere else.
# _chrome_from_macos_spotlight() is checked first for exactly that reason.
# UNVERIFIED as of 2026-07-22 — written without a live Mac to test on;
# CHROME_MAC_PATH remains as a fallback for the common case if this doesn't
# pan out or mdfind is unavailable/disabled.
# CHROME_CANDIDATES' PATH-based names ("google-chrome" etc.) are a Linux/Mac
# convention — a Windows Chrome install never puts chrome.exe on PATH under
# any of those names, so without these explicit paths find_chrome() always
# fell through to EDGE_WIN_PATHS below even on a machine with Chrome
# installed (confirmed live: Edge opened instead of the user's own Chrome).
# %LOCALAPPDATA% covers the common non-admin/per-user install; the two
# Program Files paths cover a machine-wide install (matching EDGE_WIN_PATHS'
# own x86/64 pair).
CHROME_WIN_PATHS = [
    Path(os.environ.get("LOCALAPPDATA", ""))
    / "Google"
    / "Chrome"
    / "Application"
    / "chrome.exe",
    Path(r"C:\Program Files\Google\Chrome\Application\chrome.exe"),
    Path(r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe"),
]
EDGE_WIN_PATHS = [
    Path(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"),
    Path(r"C:\Program Files\Microsoft\Edge\Application\msedge.exe"),
]


def _chrome_from_windows_registry():
    """Look up Chrome's install path via the "App Paths" registry key —
    the same mechanism Windows itself uses to resolve a bare "chrome.exe"
    (e.g. from the Run dialog or `start chrome`). Every normal Chrome
    installer (per-user or per-machine) writes this key regardless of which
    drive/folder it installed to, so it's more robust than guessing fixed
    paths like CHROME_WIN_PATHS above — those only cover the default
    locations and silently miss anything installed elsewhere. winreg only
    exists on Windows; the ImportError there makes this a clean no-op on
    Linux/Mac.
    """
    try:
        import winreg
    except ImportError:
        return None
    key_path = r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\chrome.exe"
    for hive in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
        try:
            with winreg.OpenKey(hive, key_path) as key:
                path, _ = winreg.QueryValueEx(key, None)
        except OSError:
            continue
        if path and Path(path).exists():
            return path
    return None


# The login click-path: info-kierowca.pl -> (maybe) "Zaloguj się" -> a PWPW
# identity-provider chooser with a "gov.pl" tile -> a login.gov.pl chooser
# with an "Aplikacja mObywatel" tile -> QR code. Checked in this order (most
# specific/downstream first) so whichever screen is showing gets exactly one
# click; harmless no-op once the QR page itself is showing, since nothing
# there matches. Site markup could change and break this — if it stops
# matching, you can still click through by hand while the script waits.
AUTO_CLICK_TARGETS = ["Aplikacja mObywatel", "gov.pl", "Zaloguj się"]

# Shared by both scripts below: find the smallest element anywhere on the
# page whose text contains one of `targets` (checked in that order) and
# click the nearest real clickable ancestor — login-page rows are often a
# plain <div> wrapping an icon + label, not a bare <button>/<a>. Once
# targets[0] (the most specific/downstream one, "Aplikacja mObywatel" — the
# tile that lands on the QR page itself) gets clicked, a sessionStorage flag
# is set so neither this function nor its callers try again: sessionStorage
# survives same-origin navigations (including the browser back button), so
# if you back out of the QR page to pick a different login method, this
# won't force you straight back to it. Origin-scoped only — it resets on a
# genuine cross-origin hop, which matches the one place that's actually
# wanted: a fresh run of this script (new profile) should auto-click again.
# The "is this thing clickable" heuristic, shared verbatim with
# open_logged_in_browser.py's own click-by-text helper. This is the most
# site-fragile code in the project — when info-kierowca.pl reshuffles its
# markup it gets edited under pressure, so it lives in exactly one place
# rather than in two copies that can silently drift apart.
CLICKABLE_HELPERS_JS = """
function __ikw_isVisible(el) {
  var style = window.getComputedStyle(el);
  if (style.display === 'none' || style.visibility === 'hidden' || style.opacity === '0') return false;
  return el.offsetWidth > 0 || el.offsetHeight > 0 || el.getClientRects().length > 0;
}
function __ikw_isClickable(el) {
  if (!el) return false;
  var style = window.getComputedStyle(el);
  return el.tagName === 'BUTTON' || el.tagName === 'A' ||
    el.getAttribute('role') === 'button' || style.cursor === 'pointer';
}
function __ikw_clickableAncestor(el) {
  var cur = el;
  for (var i = 0; i < 6 && cur; i++) {
    if (__ikw_isClickable(cur)) return cur;
    cur = cur.parentElement;
  }
  return el;
}
"""

CLICK_LOGIC_JS = (
    """
var __IKW_STOP_KEY = '__ikw_auto_click_stopped';
function __ikw_stopped() {
  try { return !!sessionStorage.getItem(__IKW_STOP_KEY); } catch (e) { return false; }
}
"""
    + CLICKABLE_HELPERS_JS
    + """
function __ikw_findAndClick(targets) {
  if (__ikw_stopped()) return null;
  var bodyText = (document.body ? document.body.innerText : '').toLowerCase();
  if (document.querySelector('.alertPage, [class*="alertPage"], .wkProcessUsed') || bodyText.indexOf('wkprocessused') !== -1 || bodyText.indexOf('alertpage') !== -1) {
    return null;
  }
  var all = document.querySelectorAll('button, a, [role="button"], li, div, span');
  for (var ti = 0; ti < targets.length; ti++) {
    var text = targets[ti];
    var best = null;
    for (var i = 0; i < all.length; i++) {
      var el = all[i];
      if (!__ikw_isVisible(el)) continue;

      // Skip header, footer, logo, language switcher, go-back, and external links
      var ancestor = el;
      var skip = false;
      for (var k = 0; k < 6 && ancestor; k++) {
        var tag = (ancestor.tagName || '').toLowerCase();
        var cls = (ancestor.className || '').toString().toLowerCase();
        var href = (ancestor.href || '').toString().toLowerCase();
        if (tag === 'header' || tag === 'footer' || tag === 'app-logo' || tag === 'app-wk-footer' || tag === 'app-wk-language-switcher') {
          skip = true; break;
        }
        if (cls.indexOf('logo') !== -1 || cls.indexOf('footer') !== -1 || cls.indexOf('go-back') !== -1) {
          skip = true; break;
        }
        if (href.indexOf('www.gov.pl') !== -1 && href.indexOf('login') === -1) {
          skip = true; break;
        }
        ancestor = ancestor.parentElement;
      }
      if (skip) continue;

      var t = (el.innerText || el.textContent || '').trim();
      var tLower = t.toLowerCase();
      if (tLower.indexOf('załóż') !== -1 || tLower.indexOf('zaloz') !== -1) continue;
      if (tLower.indexOf('przypomnij') !== -1) continue;
      if (tLower.indexOf('polityka') !== -1 || tLower.indexOf('pomoc') !== -1) continue;

      if (t && t.length < 200 && tLower.indexOf(text.toLowerCase()) !== -1) {
        if (!best || t.length <= best[1].length) best = [el, t];
      }
    }
    if (best) {
      var targetEl = __ikw_clickableAncestor(best[0]);
      targetEl.click();
      if (text === targets[0]) {
        try { sessionStorage.setItem(__IKW_STOP_KEY, '1'); } catch (e) {}
      }
      return JSON.stringify({
        target: text,
        matched_text: best[1],
        tag: targetEl.tagName,
        id: targetEl.id || '',
        class: targetEl.className || '',
        href: targetEl.href || ''
      });
    }
  }
  return null;
}
"""
)

# One-shot version: used as a slow Python-polled fallback (see try_auto_click).
AUTO_CLICK_JS = CLICK_LOGIC_JS + (
    "(function(targets) { return __ikw_findAndClick(targets); })(%s)"
    % json.dumps(AUTO_CLICK_TARGETS)
)

# Persistent version: registered via Page.addScriptToEvaluateOnNewDocument
# (see cdp_client.inject_and_navigate) so it's already watching the DOM
# before the first paint of *every* document in this tab — including
# cross-origin OAuth redirects — and clicks the instant a target appears,
# instead of waiting on our next poll tick. This is what makes the
# click-through effectively instant rather than bounded by a sleep interval.
#
# Watches `attributes` as well as `childList`/`characterData`: some chooser
# screens reveal the next tile by toggling a class/hidden attribute on an
# already-present element rather than inserting a new node, which this
# observer used to miss entirely — the click then only happened on the next
# Python-side fallback poll (try_auto_click, see wait_for_cookies), which is
# exactly the ~1s-ish hang reported right before the QR page. Disconnects
# itself once targets[0] is clicked (see __ikw_findAndClick's sessionStorage
# flag above) so a same-document re-render that brings the chooser back
# (e.g. picking a different login method) doesn't get auto-clicked forward
# again.
#
# Confirmed live 2026-07-18: on the podmiotyzewnetrzne.login.gov.pl tile
# chooser specifically, this observer's callback (and a setInterval placed
# alongside it, tried and discarded) never fires at all even though the
# tiles are fully rendered and clickable within ~1s — the MutationObserver
# and any in-page timers registered via this
# Page.addScriptToEvaluateOnNewDocument-injected script go silently inert on
# that one page. A *fresh* Runtime.evaluate call from Python-side (i.e.
# try_auto_click, called on its own separate CDP connection) always finds
# and clicks the tile instantly regardless. So the reliable fix isn't a
# better in-page watcher — it's not leaving that fallback 3s idle; see
# wait_for_cookies's poll interval.
AUTO_CLICK_OBSERVER_JS = CLICK_LOGIC_JS + ("""
(function(targets) {
  if (__ikw_stopped()) return;
  var scheduled = false;
  var observer = new MutationObserver(schedule);
  function schedule() {
    if (scheduled) return;
    scheduled = true;
    requestAnimationFrame(function() {
      scheduled = false;
      var clicked = __ikw_findAndClick(targets);
      if (clicked === targets[0]) observer.disconnect();
    });
  }
  var clicked = __ikw_findAndClick(targets);
  if (clicked === targets[0]) return;
  observer.observe(
    document, {childList: true, subtree: true, characterData: true, attributes: true}
  );
})(%s)
""" % json.dumps(AUTO_CLICK_TARGETS))


def try_auto_click(host, port, targets=None):
    if targets is None:
        targets = AUTO_CLICK_TARGETS
    js = CLICK_LOGIC_JS + (
        "(function(targets) { return __ikw_findAndClick(targets); })(%s)"
        % json.dumps(targets)
    )
    try:
        raw_res = cdp_client.evaluate_in_page(host, port, js)
        if raw_res:
            try:
                info = json.loads(raw_res)
                target = info.get("target")
                matched = info.get("matched_text")
                tag = info.get("tag")
                el_id = info.get("id")
                el_cls = info.get("class")
                href = info.get("href")
                print(f"[AUTO-CLICK LOG] Target='{target}' (matched='{matched}') -> Clicked <{tag} id='{el_id}' class='{el_cls}' href='{href}'>")
                return target
            except Exception:
                print(f"[AUTO-CLICK LOG] Clicked element: {raw_res!r}")
                return str(raw_res)
        return None
    except Exception as e:
        print(f"[AUTO-CLICK LOG] try_auto_click error: {e!r}")
        return None


def _chrome_from_macos_spotlight():
    """macOS analog of _chrome_from_windows_registry() above: `mdfind`
    (Spotlight) looks Chrome up by bundle identifier, which finds it
    regardless of install location — /Applications, ~/Applications, or
    anywhere else — unlike the fixed CHROME_MAC_PATH guess. Returns None on
    any failure (wrong OS, mdfind missing/disabled, nothing indexed) so
    CHROME_MAC_PATH stays a working fallback for the common case.

    UNVERIFIED as of 2026-07-22 — written without a live Mac to test on.
    """
    if sys.platform != "darwin":
        return None
    try:
        out = subprocess.check_output(
            ["mdfind", "kMDItemCFBundleIdentifier == 'com.google.Chrome'"],
            text=True,
            stderr=subprocess.DEVNULL,
            timeout=5,
        )
    except Exception:
        return None
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        binary = Path(line) / "Contents" / "MacOS" / "Google Chrome"
        if binary.exists():
            return str(binary)
    return None


def find_chrome():
    for name in CHROME_CANDIDATES:
        path = shutil.which(name)
        if path:
            return path
    macos_path = _chrome_from_macos_spotlight()
    if macos_path:
        return macos_path
    if CHROME_MAC_PATH.exists():
        return str(CHROME_MAC_PATH)
    registry_path = _chrome_from_windows_registry()
    if registry_path:
        return registry_path
    for path in CHROME_WIN_PATHS:
        if path.exists():
            return str(path)
    for path in EDGE_WIN_PATHS:
        if path.exists():
            return str(path)
    raise SystemExit("Couldn't find a Chrome/Chromium/Edge binary on PATH.")


def chrome_available():
    """Whether find_chrome() would succeed, without raising. Used by
    notifier.trigger_auto_refresh()/trigger_open_browser() to detect a
    missing Chromium browser (e.g. a Mac with only Safari installed)
    synchronously, before spawning the detached subprocess whose own
    find_chrome() failure would otherwise be invisible — its stdout/stderr
    go to DEVNULL since the launch is fire-and-forget.
    """
    try:
        find_chrome()
        return True
    except SystemExit:
        return False


def notify_desktop(summary, body, urgency="normal"):
    """Best-effort local desktop notification — the ntfy phone push is the
    primary alert, this is a secondary one for whoever's at the machine.

    notify-send is Linux-only; osascript is macOS's always-available
    equivalent (no third-party notifier needed, matching this project's
    zero-dependency stance). json.dumps() quotes summary/body as AppleScript
    string literals safely rather than interpolating them raw into the
    -e script text. UNVERIFIED as of 2026-07-22 — written without a live Mac
    to test on; worst case it silently no-ops there, same as before.
    """
    if sys.platform == "darwin":
        script = (
            f"display notification {json.dumps(body)} with title {json.dumps(summary)}"
        )
        try:
            subprocess.run(["osascript", "-e", script], check=False)
        except FileNotFoundError:
            pass
        return
    try:
        subprocess.run(
            [
                "notify-send",
                "-u",
                urgency,
                "-a",
                "info-kierowca-notifier",
                summary,
                body,
            ],
            check=False,
        )
    except FileNotFoundError:
        pass


import ssl


def open_google_messages_pairing(port=DEFAULT_PORT):
    """Launch or attach Chrome with persistent PROFILE_DIR to let user pair Google Messages Web."""
    if cdp_client.debug_port_open("127.0.0.1", port):
        try:
            cdp_client.create_tab("127.0.0.1", port, "https://messages.google.com/web")
            cdp_client.bring_to_front("127.0.0.1", port)
            return True, "Opened Google Messages Web in existing Chrome window"
        except Exception:
            pass

    chrome = find_chrome()
    if not chrome:
        return False, "No Chrome, Edge, or Chromium browser found on this machine."
    PROFILE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        subprocess.Popen(
            [
                chrome,
                f"--remote-debugging-port={port}",
                f"--user-data-dir={PROFILE_DIR}",
                "--no-first-run",
                "--no-default-browser-check",
                "--window-size=900,850",
                "https://messages.google.com/web",
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return True, "Chrome opened for Google Messages pairing"
    except Exception as e:
        return False, f"Could not launch Chrome: {e}"


def push_ntfy(title, message, priority="default", tags=None):
    try:
        config = json.loads(CONFIG_FILE.read_text())
    except Exception:
        return
    topic = config.get("ntfy_topic")
    if not topic or not config.get("phone_alerts_relogin", True):
        return
    headers = {"Title": title, "Priority": priority}
    if tags:
        headers["Tags"] = ",".join(tags)
    req = urllib.request.Request(
        f"https://ntfy.sh/{topic}",
        data=message.encode("utf-8"),
        headers=headers,
        method="POST",
    )
    try:
        ctx = ssl.create_default_context()
        with urllib.request.urlopen(req, timeout=15, context=ctx):
            pass
    except Exception:
        try:
            unverified_ctx = ssl._create_unverified_context()
            with urllib.request.urlopen(req, timeout=15, context=unverified_ctx):
                pass
        except Exception:
            pass


def acquire_lock():
    if LOCK_FILE.exists():
        try:
            pid = int(LOCK_FILE.read_text().strip())
        except ValueError:
            pid = None
        if pid is not None:
            try:
                os.kill(pid, 0)
                return False  # a refresh is already in progress
            except OSError:
                pass  # stale lock — the owning process is gone
    LOCK_FILE.parent.mkdir(parents=True, exist_ok=True)
    LOCK_FILE.write_text(str(os.getpid()))
    return True


def release_lock():
    try:
        LOCK_FILE.unlink()
    except FileNotFoundError:
        pass


def dev_pause(step_name, dev_mode=False):
    if dev_mode:
        print(
            f"[DEV-MODE] Pausing 5s before step: '{step_name}'... (Close Chrome window now to abort)"
        )
        time.sleep(5)


def check_pz_form_present(host, port):
    """Check if Profil Zaufany login/password fields are present on page."""
    js = """
    (function() {
      var l = document.querySelector('input#username, input[formcontrolname="login"], input[data-testid="username-input"] input, input[name="login"], input[id="login"], #login');
      var p = document.querySelector('input#password, input[formcontrolname="password"], input[data-testid="password-input"] input, input[name="password"], input[id="password"], #password');
      return !!(l && p);
    })()
    """
    try:
        return cdp_client.evaluate_in_page(host, port, js)
    except Exception:
        return False


def wait_for_cookies(
    host,
    port,
    timeout,
    chrome_proc,
    login_method="mobywatel",
    pz_login="",
    pz_password="",
    targets=None,
    dev_mode=False,
):
    deadline = None if timeout is None else time.monotonic() + timeout
    pz_submitted_at = None
    state = "CHOOSER"  # States: CHOOSER, CREDENTIALS, SMS_WAITING, SUBMITTED_SMS

    while deadline is None or time.monotonic() < deadline:
        if chrome_proc and chrome_proc.poll() is not None and not cdp_client.debug_port_open(host, port):
            return None
        try:
            raw = cdp_client.fetch_cookies(host, port)
            cookies = cdp_client.extract_info_kierowca_cookies(raw)
            if cdp_client.COOKIE_NAMES <= cookies.keys():
                return cookies
        except Exception:
            pass  # Chrome may be mid-navigation; just retry

        if login_method == "profil_zaufany":
            # State Machine transition checks
            if check_sms_modal_present(host, port):
                if state != "SMS_WAITING" and state != "SUBMITTED_SMS":
                    print("[PZ-LOGIN LOG] SMS Modal detected. Transitioning to SMS_WAITING (Auto-clicker disabled).")
                    state = "SMS_WAITING"
            elif check_pz_form_present(host, port):
                if state == "CHOOSER":
                    print("[PZ-LOGIN LOG] PZ Credential form detected. Transitioning to CREDENTIALS.")
                    state = "CREDENTIALS"

            if state == "CREDENTIALS":
                if fill_pz_credentials(host, port, pz_login, pz_password, dev_mode=dev_mode):
                    if pz_submitted_at is None:
                        pz_submitted_at = time.time()
                    state = "SMS_WAITING"

            elif state == "SMS_WAITING":
                # AUTO-CLICKER IS STRICTLY DISABLED IN SMS_WAITING
                sms_code = fetch_sms_code_from_google_messages(
                    host, port, min_timestamp=pz_submitted_at
                )
                if sms_code:
                    print(f"Captured SMS code: {sms_code}")
                    dev_pause(f"submitting SMS code {sms_code}", dev_mode)
                    cdp_client.bring_to_front(host, port, url_pattern="gov.pl")
                    inject_sms_code_and_submit(host, port, sms_code)
                    state = "SUBMITTED_SMS"

            elif state == "CHOOSER":
                clicked = try_auto_click(host, port, targets=targets)
                if clicked:
                    print(f"auto-clicked: {clicked!r}")
        else:
            clicked = try_auto_click(host, port, targets=targets)
            if clicked:
                print(f"auto-clicked: {clicked!r}")

        time.sleep(0.5)
    return None


def fill_pz_credentials(host, port, login, password, dev_mode=False):
    """Fill credentials into the Profil Zaufany login form and click submit."""
    check_js = """
    (function() {
      if (window.__ikw_pz_submitted) return false;
      var l = document.querySelector('input#username, input[formcontrolname="login"], input[data-testid="username-input"] input, input[name="login"], input[id="login"], #login');
      var p = document.querySelector('input#password, input[formcontrolname="password"], input[data-testid="password-input"] input, input[name="password"], input[id="password"], #password');
      return !!(l && p);
    })()
    """
    try:
        if cdp_client.evaluate_in_page(host, port, check_js):
            dev_pause("submitting Profil Zaufany credentials", dev_mode)
    except Exception:
        pass

    js = f"""
    (function() {{
      if (window.__ikw_pz_submitted) return null;
      var errEl = document.querySelector('.alertPage, [class*="alertPage"], .wkProcessUsed');
      var bodyText = (document.body ? document.body.innerText : '').toLowerCase();
      if (errEl || bodyText.indexOf('wkprocessused') !== -1 || bodyText.indexOf('został już użyty') !== -1 || bodyText.indexOf('zostal juz uzyty') !== -1) {{
        return JSON.stringify({{ error: 'wk_process_used', message: 'Profil Zaufany process expired or already used.' }});
      }}
      var l = document.querySelector('input#username, input[formcontrolname="login"], input[data-testid="username-input"] input, input[name="login"], input[id="login"], #login');
      var p = document.querySelector('input#password, input[formcontrolname="password"], input[data-testid="password-input"] input, input[name="password"], input[id="password"], #password');
      if (l && p) {{
        if (!l.value || !p.value) {{
          l.value = {json.dumps(login)};
          l.dispatchEvent(new Event('input', {{ bubbles: true }}));
          l.dispatchEvent(new Event('change', {{ bubbles: true }}));
          p.value = {json.dumps(password)};
          p.dispatchEvent(new Event('input', {{ bubbles: true }}));
          p.dispatchEvent(new Event('change', {{ bubbles: true }}));
        }}
        var btn = document.querySelector('[data-testid="login-confirm-btn"] button, button[aria-label="Zaloguj się"], button[type="submit"].gds-button--primary');
        if (!btn) {{
          var form = l.form || l.closest('form');
          if (form) {{
            var candidates = Array.from(form.querySelectorAll('button, input[type="submit"]'));
            btn = candidates.find(b => {{
              var t = (b.innerText || b.value || '').toLowerCase();
              return t.includes('zaloguj') && !t.includes('załóż') && !t.includes('zaloz');
            }}) || form.querySelector('button[type="submit"], input[type="submit"]');
          }}
        }}
        if (!btn) {{
          var allBtns = Array.from(document.querySelectorAll('button, input[type="submit"]'));
          btn = allBtns.find(b => {{
            var t = (b.innerText || b.value || '').toLowerCase();
            return t.includes('zaloguj') && !t.includes('załóż') && !t.includes('zaloz');
          }});
        }}
        window.__ikw_pz_submitted = true;
        if (btn) {{
          btn.click();
          return JSON.stringify({{ action: 'clicked_button', btn: btn.tagName + (btn.className ? '.' + btn.className : ''), text: (btn.innerText || btn.value || '').trim() }});
        }} else if (l.form) {{
          if (typeof l.form.requestSubmit === 'function') {{
            l.form.requestSubmit();
          }} else {{
            l.form.submit();
          }}
          return JSON.stringify({{ action: 'form_submit' }});
        }}
      }}
      return null;
    }})()
    """
    try:
        raw_res = cdp_client.evaluate_in_page(host, port, js)
        if raw_res:
            print(f"[PZ-LOGIN LOG] Form handled -> {raw_res}")
            return True
        return False
    except Exception as e:
        print(f"[PZ-LOGIN LOG] fill_pz_credentials error: {e!r}")
        return False


def check_sms_modal_present(host, port):
    """Check if the SMS code input modal is visible on the PZ page."""
    js = """
    (function() {
      var input = document.querySelector('input[data-testid="sms-code-input"], #smsInput');
      return !!input;
    })()
    """
    try:
        return cdp_client.evaluate_in_page(host, port, js)
    except Exception:
        return False


_GM_TAB_CREATED = False


def fetch_sms_code_info_from_google_messages(host, port):
    """Scan Google Messages Web for PZePUAP SMS code and return info dict or None."""
    try:
        targets = cdp_client.get_all_targets(host, port)
    except Exception:
        return None

    msg_target = None
    for t in targets:
        url = t.get("url", "")
        title = t.get("title", "")
        if "messages.google.com" in url or "Google Messages" in title or "Messages" in title:
            msg_target = t
            break

    if msg_target:
        ws_url = msg_target.get("webSocketDebuggerUrl")
    else:
        return None

    js = r"""
    (function() {
      function queryDeep(sel, root) {
        root = root || document;
        var res = Array.from(root.querySelectorAll(sel));
        var tw = document.createTreeWalker(root, NodeFilter.SHOW_ELEMENT, null, false);
        while (tw.nextNode()) {
          var n = tw.currentNode;
          if (n.shadowRoot) {
            var sub = queryDeep(sel, n.shadowRoot);
            for (var i = 0; i < sub.length; i++) res.push(sub[i]);
          }
        }
        return res;
      }

      var headerTitleEl = queryDeep('[data-e2e-header-title] h2, [data-e2e-header-title], mws-header h2')[0];
      var headerTitle = (headerTitleEl ? headerTitleEl.innerText : '').trim();
      var isPzActive = headerTitle.toLowerCase().indexOf('pzepuap') !== -1 || headerTitle.toLowerCase().indexOf('profil zaufany') !== -1;

      // 1. If PZePUAP is not currently active, trigger Angular router navigation or click
      var convItems = queryDeep('mws-conversation-list-item, a[data-e2e-conversation]');
      var pzItem = convItems.find(function(el) {
        var nameEl = el.querySelector('[data-e2e-conversation-name], .name');
        var name = (nameEl ? nameEl.innerText : el.innerText) || '';
        return name.toLowerCase().indexOf('pzepuap') !== -1 || name.toLowerCase().indexOf('profil zaufany') !== -1;
      });

      if (!isPzActive && pzItem) {
        var target = pzItem.querySelector('a[data-e2e-conversation]') || (pzItem.tagName === 'A' ? pzItem : null);
        if (target) {
          var href = target.getAttribute('href');
          if (href && window.location.pathname !== href) {
            window.location.href = href;
          } else {
            target.scrollIntoView({ block: 'center', behavior: 'instant' });
            target.click();
            target.dispatchEvent(new MouseEvent('mousedown', { bubbles: true, cancelable: true }));
            target.dispatchEvent(new MouseEvent('mouseup', { bubbles: true, cancelable: true }));
            target.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true }));
          }
          return JSON.stringify({ action: 'switching_to_pz', is_pz_active: false });
        }
      }

      // 2. Scan both active message pane and sidebar conversation list items (deep Shadow DOM query)
      var items = queryDeep('mws-message-wrapper, [data-e2e-message-content], mws-conversation-list-item, a[data-e2e-conversation], mws-text-message-part');
      var matches = [];
      var seen = {};
      for (var i = 0; i < items.length; i++) {
        var item = items[i];
        var isPzItem = false;
        var nameEl = item.querySelector('[data-e2e-conversation-name], .name');
        if (nameEl) {
          var name = (nameEl.innerText || nameEl.textContent || '').toLowerCase();
          if (name.indexOf('pzepuap') !== -1 || name.indexOf('profil zaufany') !== -1) {
            isPzItem = true;
          }
        }
        var isMessageWrapper = item.tagName === 'MWS-MESSAGE-WRAPPER' || item.hasAttribute('data-e2e-message-content') || item.tagName === 'MWS-TEXT-MESSAGE-PART';
        
        if (isPzItem || isMessageWrapper || isPzActive) {
          var text = item.innerText || item.textContent || '';
          var m = text.match(/(\d{2}\.\d{2}\.\d{4}),?\s*godz\.\s*(\d{2}:\d{2}:\d{2}).*?Kod:\s*(\d{8})/i);
          if (m) {
            var dateParts = m[1].split('.');
            var timeParts = m[2].split(':');
            var d = parseInt(dateParts[0], 10);
            var mo = parseInt(dateParts[1], 10) - 1;
            var y = parseInt(dateParts[2], 10);
            var h = parseInt(timeParts[0], 10);
            var mi = parseInt(timeParts[1], 10);
            var s = parseInt(timeParts[2], 10);
            var ts = new Date(y, mo, d, h, mi, s).getTime() / 1000;
            var key = m[3] + '_' + ts;
            if (!seen[key]) {
              seen[key] = true;
              matches.push({ code: m[3], timestamp: ts, date_str: m[1], time_str: m[2] });
            }
          }
        }
      }

      if (matches.length > 0) {
        matches.sort(function(a, b) { return b.timestamp - a.timestamp; });
        return JSON.stringify(matches[0]);
      }
      return JSON.stringify({ debug_items: items.length, is_pz_active: isPzActive, pz_item_found: !!pzItem });
    })()
    """
    try:
        raw_res = cdp_client.evaluate_in_target_ws(ws_url, js)
        if raw_res:
            res_dict = json.loads(raw_res)
            return res_dict
    except Exception as e:
        print(f"[PZ-SMS LOG] fetch_sms_code_info error: {e!r}")
    return None


def fetch_sms_code_from_google_messages(host, port, min_timestamp=None):
    """Open or switch to Google Messages Web tab, ensure PZePUAP conversation is active via header inspection,
    and extract the latest valid PZePUAP SMS code matching the timestamp condition."""
    global _GM_TAB_CREATED
    messages_url = "https://messages.google.com/web"
    try:
        targets = cdp_client.get_all_targets(host, port)
    except Exception:
        return None

    msg_target = None
    for t in targets:
        url = t.get("url", "")
        title = t.get("title", "")
        if "messages.google.com" in url or "Google Messages" in title or "Messages" in title:
            msg_target = t
            break

    if not msg_target:
        if not _GM_TAB_CREATED:
            _GM_TAB_CREATED = True
            cdp_client.create_tab(host, port, messages_url)
        else:
            return None

    # Focus Google Messages tab to prevent Chromium background tab throttling
    cdp_client.bring_to_front(host, port, url_pattern="messages.google.com")

    info = fetch_sms_code_info_from_google_messages(host, port)
    if info:
        if info.get("action") == "switching_to_pz":
            print("[PZ-SMS LOG] Switching to PZePUAP conversation in Google Messages tab... Waiting for Angular render.")
            time.sleep(1.0)
            info = fetch_sms_code_info_from_google_messages(host, port)

        if info and "code" in info:
            code = info.get("code")
            sms_ts = info.get("timestamp", 0)
            date_str = info.get("date_str", "")
            time_str = info.get("time_str", "")

            now = time.time()
            if min_timestamp and sms_ts < (min_timestamp - 30):
                print(
                    f"[PZ-SMS LOG] Found SMS code {code} from {date_str} {time_str}, but it is older than login attempt (min ts: {min_timestamp}). Waiting for new SMS..."
                )
                return None

            if now - sms_ts > 300:  # Older than 5 minutes overall
                print(
                    f"[PZ-SMS LOG] Found SMS code {code} from {date_str} {time_str}, but it is too old ({int(now - sms_ts)}s). Waiting for new SMS..."
                )
                return None

            print(
                f"[PZ-SMS LOG] Fresh SMS code captured: {code} (sent at {date_str} {time_str})"
            )
            return code
        else:
            print(f"[PZ-SMS LOG] Debug DOM scan -> {info}")
    return None


def inject_sms_code_and_submit(host, port, code):
    """Inject the SMS code into the PZ input field and click confirm."""
    js = f"""
    (function(code) {{
      var input = document.querySelector('input[data-testid="sms-code-input"], #smsInput');
      if (input) {{
        input.value = code;
        input.dispatchEvent(new Event('input', {{ bubbles: true }}));
        input.dispatchEvent(new Event('change', {{ bubbles: true }}));
        var btn = document.querySelector('button[data-testid="sms-code-submit-btn"], button[aria-label="Potwierdź"]');
        if (btn) {{
          btn.click();
          return true;
        }}
      }}
      return false;
    }})({json.dumps(code)})
    """
    try:
        return cdp_client.evaluate_in_page(host, port, js)
    except Exception:
        return False


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--url",
        default=DEFAULT_URL,
        help="Page to open Chrome to (default: %(default)s)",
    )
    parser.add_argument("--port", type=int, default=DEFAULT_PORT)
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help="Seconds to wait for the QR to be scanned before giving up (default: wait indefinitely)",
    )
    parser.add_argument(
        "--no-phone-push",
        action="store_true",
        help="Skip the ntfy push notification — used when a person just clicked a "
        "button and is already watching Chrome, so a 'scan the QR' push to their "
        "phone would be redundant. The desktop notification still fires.",
    )
    parser.add_argument(
        "--keep-open",
        action="store_true",
        help="Leave Chrome open after capturing cookies",
    )
    args = parser.parse_args()

    # notifier.trigger_auto_refresh(force=True) — the "Open browser" button's
    # path for clearing a forgotten QR window — SIGTERMs whoever holds the
    # lock. Without a handler Python dies immediately, skipping the finally
    # below: the lock got cleared but our Chrome child survived as an orphan
    # still holding PROFILE_DIR, so the *replacement* Chrome launched against
    # the same --user-data-dir would delegate to it and exit instantly,
    # tripping the "Chrome closed before logging in" bail-out on every retry.
    # Translating the signal into SystemExit lets the finally run normally.
    def _terminate(signum, _frame):
        raise SystemExit(f"terminated by signal {signum}")

    signal.signal(signal.SIGTERM, _terminate)

    # stdout/stderr are redirected to a plain file (AUTO_REFRESH_LOG_FILE) when
    # launched via notifier.trigger_auto_refresh(), which fully-buffers by
    # default for a non-tty — without this, prints below (including
    # try_auto_click's failure logging) wouldn't actually land in the file
    # until the process exits, which could be hours into an unattended wait.
    try:
        sys.stdout.reconfigure(line_buffering=True)
        sys.stderr.reconfigure(line_buffering=True)
    except AttributeError:
        pass  # older Python without reconfigure(); harmless to skip

    if not acquire_lock():
        print("A refresh is already in progress (lock file present) — exiting.")
        return

    # Load login configuration
    try:
        config = json.loads(CONFIG_FILE.read_text())
    except Exception:
        config = {}

    login_method = config.get("login_method", "mobywatel")
    pz_login = config.get("pz_login", "")
    pz_password = config.get("pz_password", "")
    dev_mode = bool(config.get("dev_mode", False))

    if login_method == "profil_zaufany":
        targets = ["Profil zaufany", "gov.pl", "Zaloguj się"]
    else:
        targets = ["Aplikacja mObywatel", "gov.pl", "Zaloguj się"]

    observer_js = CLICK_LOGIC_JS + ("""
(function(targets) {
  if (__ikw_stopped()) return;
  var scheduled = false;
  var observer = new MutationObserver(schedule);
  function schedule() {
    if (scheduled) return;
    scheduled = true;
    requestAnimationFrame(function() {
      scheduled = false;
      var clicked = __ikw_findAndClick(targets);
      if (clicked === targets[0]) observer.disconnect();
    });
  }
  var clicked = __ikw_findAndClick(targets);
  if (clicked === targets[0]) return;
  observer.observe(
    document, {childList: true, subtree: true, characterData: true, attributes: true}
  );
})(%s)
""" % json.dumps(targets))

    chrome_proc = None
    try:
        chrome = find_chrome()
        print(f"using browser: {chrome}")
        PROFILE_DIR.mkdir(parents=True, exist_ok=True)
        chrome_proc = subprocess.Popen(
            [
                chrome,
                f"--remote-debugging-port={args.port}",
                f"--user-data-dir={PROFILE_DIR}",
                "--no-first-run",
                "--no-default-browser-check",
                "--window-size=900,850",
                args.url,
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

        notify_desktop(
            "info-kierowca: relogin needed",
            "Chrome opened — scan the QR in the app to log back in",
            "critical",
        )
        if not args.no_phone_push:
            push_ntfy(
                "info-kierowca: relogin needed",
                "Chrome opened on your desktop — scan the QR in the app to log back in",
                priority="default",
            )

        cdp_client.wait_for_debug_port("127.0.0.1", args.port, timeout=20)
        cdp_client.inject_and_navigate("127.0.0.1", args.port, args.url, observer_js)
        cdp_client.bring_to_front("127.0.0.1", args.port)

        cookies = wait_for_cookies(
            "127.0.0.1",
            args.port,
            args.timeout,
            chrome_proc,
            login_method=login_method,
            pz_login=pz_login,
            pz_password=pz_password,
            targets=targets,
            dev_mode=dev_mode,
        )

        if cookies is None:
            try:
                AUTO_REFRESH_COOLDOWN_FILE.write_text(str(time.time()))
            except Exception:
                pass
            if chrome_proc.poll() is not None:
                print("Chrome exited before logging in (crashed or was closed).")
                notify_desktop(
                    "info-kierowca: relogin failed",
                    "Chrome closed before logging in — run auto_refresh_session.py again",
                    "critical",
                )
            else:
                print(f"No login detected within {args.timeout}s.")
                notify_desktop(
                    "info-kierowca: relogin timed out",
                    f"No login detected within {args.timeout}s — run auto_refresh_session.py again when ready",
                    "critical",
                )
            sys.exit(1)

        AUTO_REFRESH_COOLDOWN_FILE.unlink(missing_ok=True)
        cdp_client.write_session_file(cookies)
        print(f"Wrote {len(cookies)} cookie(s) to {cdp_client.SESSION_FILE}")
        notify_desktop(
            "info-kierowca: session refreshed",
            "Logged back in — the notifier will pick it up on the next check",
        )
    finally:
        if chrome_proc and not args.keep_open:
            chrome_proc.terminate()
            try:
                chrome_proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                chrome_proc.kill()
        release_lock()


if __name__ == "__main__":
    main()
