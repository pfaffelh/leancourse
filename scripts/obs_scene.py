#!/usr/bin/env python3
"""Switch the OBS program scene over obs-websocket (protocol v5).

    scripts/obs_scene.py camera     -> "Nur Kamera"
    scripts/obs_scene.py slides     -> "Vortrag"
    scripts/obs_scene.py code       -> "Blatt lösen (VS Code)"
    scripts/obs_scene.py "<scene>"  -> any scene by its exact name

Bound to F1/F2/F3 by scripts/recording_keys.sh. Standard library only
(plus `xprop`), so it needs nothing installed. Port and password are
read from OBS's own websocket settings, so they cannot drift apart.

Before switching to the slides or the VS Code scene, the script looks
up the current window by its X11 class and points the window capture
at it. OBS on its own finds a window again after a restart only if
title *and* class match exactly, and VS Code changes its title with
every file; the desktop portal, the other way to pick a window, asks
in a dialog at every start and crashes if OBS quits while it is open.
"""
import base64
import configparser
import hashlib
import json
import os
import re
import socket
import struct
import subprocess
import sys

SCENES = {
    "camera": "Nur Kamera",
    "slides": "Vortrag",
    "code": "Blatt lösen (VS Code)",
}
# scene -> (window-capture input, regex on the window's WM_CLASS instance)
WINDOWS = {
    "Vortrag": ("Folien (Fenster)", r"^localhost__slides_"),
    # the snap package of VS Code reports `code_code`
    "Blatt lösen (VS Code)": ("VS Code (Fenster)", r"^code(_code)?$"),
}
# obs-websocket up to 5.4 (OBS 30) keeps its settings in OBS's
# global.ini; from 5.5 (OBS 31) in a JSON file of its own.
GLOBAL_INI = os.path.expanduser("~/.config/obs-studio/global.ini")
CONFIG = os.path.expanduser(
    "~/.config/obs-studio/plugin_config/obs-websocket/config.json")


def read_config():
    """Port and password, from wherever this OBS version keeps them."""
    if os.path.exists(CONFIG):
        with open(CONFIG) as f:
            cfg = json.load(f)
        return cfg.get("server_port", 4455), cfg.get("server_password", "")
    ini = configparser.ConfigParser(interpolation=None)
    ini.read(GLOBAL_INI, encoding="utf-8")
    sec = ini["OBSWebSocket"]
    return int(sec.get("ServerPort", "4455")), sec.get("ServerPassword", "")


def find_window(pattern):
    """The topmost window whose WM_CLASS instance matches, as the
    `id\\r\\ntitle\\r\\ninstance` string xcomposite capture stores."""
    def prop(*args):
        return subprocess.run(["xprop", *args], capture_output=True,
                              text=True).stdout
    stack = re.findall(r"0x[0-9a-f]+", prop("-root", "_NET_CLIENT_LIST_STACKING"))
    for wid in reversed(stack):  # last is topmost
        m = re.search(r'= "([^"]*)"', prop("-id", wid, "WM_CLASS"))
        if m and re.search(pattern, m.group(1)):
            t = re.search(r'= "(.*)"', prop("-id", wid, "_NET_WM_NAME"))
            title = t.group(1).encode().decode("unicode_escape").encode(
                "latin-1").decode("utf-8") if t else ""
            return "%d\r\n%s\r\n%s" % (int(wid, 16), title, m.group(1))
    return None


def send(sock, obj):
    data = json.dumps(obj).encode()
    mask = os.urandom(4)
    head = bytes([0x81])  # FIN + text frame
    n = len(data)
    if n < 126:
        head += bytes([0x80 | n])
    elif n < 1 << 16:
        head += bytes([0x80 | 126]) + struct.pack(">H", n)
    else:
        head += bytes([0x80 | 127]) + struct.pack(">Q", n)
    sock.sendall(head + mask + bytes(b ^ mask[i % 4] for i, b in enumerate(data)))


def recv_exact(sock, n):
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise ConnectionError("OBS closed the connection")
        buf += chunk
    return buf


def recv(sock):
    b0, b1 = recv_exact(sock, 2)
    n = b1 & 0x7F
    if n == 126:
        n = struct.unpack(">H", recv_exact(sock, 2))[0]
    elif n == 127:
        n = struct.unpack(">Q", recv_exact(sock, 8))[0]
    payload = recv_exact(sock, n)  # server frames are not masked
    if b0 & 0x0F == 0x8:
        raise ConnectionError("OBS closed the connection: %r" % payload[2:])
    return json.loads(payload)


def connect():
    port, password = read_config()
    sock = socket.create_connection(("127.0.0.1", port), timeout=3)
    key = base64.b64encode(os.urandom(16)).decode()
    sock.sendall((
        "GET / HTTP/1.1\r\nHost: localhost:%d\r\nUpgrade: websocket\r\n"
        "Connection: Upgrade\r\nSec-WebSocket-Key: %s\r\n"
        "Sec-WebSocket-Version: 13\r\n"
        "Sec-WebSocket-Protocol: obswebsocket.json\r\n\r\n" % (port, key)
    ).encode())
    resp = b""
    while b"\r\n\r\n" not in resp:
        resp += sock.recv(1024)
    if b" 101 " not in resp.split(b"\r\n")[0]:
        sys.exit("websocket handshake failed: %r" % resp.split(b"\r\n")[0])

    hello = recv(sock)["d"]
    # no event subscriptions: otherwise a scene change sends its event
    # before the reply to the request that caused it
    identify = {"rpcVersion": 1, "eventSubscriptions": 0}
    if "authentication" in hello:
        a = hello["authentication"]
        secret = base64.b64encode(hashlib.sha256(
            (password + a["salt"]).encode()).digest())
        identify["authentication"] = base64.b64encode(hashlib.sha256(
            secret + a["challenge"].encode()).digest()).decode()
    send(sock, {"op": 1, "d": identify})
    while recv(sock)["op"] != 2:  # Identified
        pass
    return sock


def request(sock, rtype, data, _n=[0]):
    _n[0] += 1
    rid = str(_n[0])
    send(sock, {"op": 6, "d": {"requestType": rtype, "requestId": rid,
                               "requestData": data}})
    while True:
        msg = recv(sock)
        if msg["op"] == 7 and msg["d"]["requestId"] == rid:
            return msg["d"]


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    scene = SCENES.get(sys.argv[1], sys.argv[1])
    sock = connect()

    if scene in WINDOWS:
        inp, pattern = WINDOWS[scene]
        # no matching window: capture nothing rather than whatever
        # window the source pointed at last time
        target = find_window(pattern) or ""
        if not target:
            print("no window for %s open -- switching anyway" % inp,
                  file=sys.stderr)
        cur = request(sock, "GetInputSettings", {"inputName": inp})
        if cur.get("responseData", {}).get("inputSettings", {}) \
                .get("capture_window") != target:
            request(sock, "SetInputSettings", {
                "inputName": inp,
                "inputSettings": {"capture_window": target}})

    status = request(sock, "SetCurrentProgramScene",
                     {"sceneName": scene})["requestStatus"]
    sock.close()
    if not status["result"]:
        sys.exit("OBS: %s" % status.get("comment", status))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ConnectionError) as e:
        sys.exit("OBS not reachable (%s) -- is OBS running?" % e)
