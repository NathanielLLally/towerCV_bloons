#!/usr/bin/env python
# Import required packages
import os
#  Gnome sessions are wayland, where PyQt5 falls back with a warning; must be set
#  before Qt loads.  setdefault so QT_QPA_PLATFORM=... on the command line still wins
os.environ.setdefault("QT_QPA_PLATFORM", "xcb")
#  run on wayland anyway, Qt's own window activation (shown windows, popups) isn't allowed
#  there and logs "Wayland does not support QWindow::requestActivate()": harmless, hidden
os.environ.setdefault("QT_LOGGING_RULES", "qt.qpa.wayland.warning=false")

#  the phone being played: an Android device on adb (adb devices) comes first, else an iPhone
#  (idevice_id -l: its UDID).  GUEST_OS=android|ios in the environment decides it instead.
#  Every device command goes through guest_shell(), which runs adb on Android and maps the
#  same Android commands onto WebDriverAgent (WDA_URL) on iOS
#
GUEST_OS_ANDROID = "android"
GUEST_OS_IOS = "ios"

def detect_guest_os():
    import subprocess as sp
    forced = os.environ.get("GUEST_OS", "").lower()
    if forced in (GUEST_OS_ANDROID, GUEST_OS_IOS):
        return forced
    try:
        out = sp.run(["adb", "devices"], capture_output=True, text=True, timeout=10).stdout
        if any(l.strip().endswith("device") for l in out.splitlines()[1:]):
            return GUEST_OS_ANDROID
    except (OSError, sp.TimeoutExpired):
        pass
    try:
        for flag in ("-l", "-n"):
            if sp.run(["idevice_id", flag], capture_output=True, text=True, timeout=10).stdout.strip():
                return GUEST_OS_IOS
    except (OSError, sp.TimeoutExpired):
        pass
    return GUEST_OS_ANDROID

GUEST_OS = detect_guest_os()
import cv2 as cv
import cv2 as cv2
import pytesseract
import sys
import optparse
import shutil
import subprocess
import os
import time
import threading
import queue
import signal
import re
import difflib
from pathlib import Path
import numpy as np
import math
import inspect #pass frame to sig handler
from skimage.feature import hog
import imutils
from imutils.object_detection import non_max_suppression
from PyQt5 import QtGui
from PyQt5 import QtCore
#from PyQt5.QtWidgets import QWidget, QApplication, QLabel, QVBoxLayout, QTable, QTableItem
from PyQt5.QtWidgets import * 
from PyQt5.QtGui import QPixmap
from PyQt5.QtCore import *
from PyQt5 import QtTest
#pyqtSignal, pyqtSlot, Qt, QThread
import json
import webbrowser
import requests
import urllib
from ppretty import ppretty
import bloons_build_chars as chars_lib
import bloons_place as place_lib
import bloons_path as path_lib
import bloons_upgrade as upgrade_lib
import bloons_strategy as strategy_lib
import traceback
import atexit
from datetime import datetime
from datetime import timedelta

#
page = 1

# Adaptive threshold levels
BKG_THRESH = 30
CARD_THRESH = 30
SERIAL = ""


#  Code derived and adapted from optical character recognition based playing card software that I wrote 
#   in order to aid in managing and trading tangible collectible cards
#

BUTTON_TEXT='EXIT'

BUTTONS = { 'EXIT': 'tap', 'HOLD TO SPAR': 'hold', 'HOLD SPAR': "hold", 'CONTINUE': 'tap', 'HOLD BATTLE': 'hold', 'HOLD TO BATTLE': 'hold'}
#BUTTON_TEXT='HOLD TO SPAR'

#"self.tap(961,1110)","self.tap(1200,980)"]
#this is on 7 spells
BTNCOORDS = { 1: (260,860), 2: (950,860), 3: (1200, 860), 4: (1656, 860), 5:(260, 966), 6:(720, 966), 7:(1673,966),
        20: (1200,980), 21:(961,1110), 22: (500,500), 23: (500,500) 
        }

#9 spells
BTNCOORDS = { 
        1: (260,650), 2: (730,650), 3: (1200, 650), 4: (1656, 650), 
        5: (260,750), 6: (730,750), 7: (1200, 750), 8: (1656, 750), 
        9:(260, 860), 10:(730, 860), 11: {1200, 860}, 12:(1673,860), 
        13:(260,960), 
        20: (960,1100), #(X)
        21:(1200,975),  #Offhand
        22: (1400,1100), #Item
        49: (1180,650), #19th item (currently large mana) of 31
        23: (270, 850), #potion
        24: (500,500) 
        }

BTNMAP = {
'Arena': { "summon": 3, "summon2": 3, "stun": 10, "diffuse": 11, "heal": 4, "ward": 5, "mend": 5, "shock": 7, "blind": 8, "freeze": 9, "stun": 10, "offhand": [20,21] },
'Raid1': { "summon": {"n":1, "t":2}, "mimic": 2, "mend": 4, "ward": 5, "heal": 7, "offhand": [20,21], "potion": [20,23], "set potion 19": [20,22,49], "greater elixir":[20,21,23] },
'Raid': { "summon": {"n": 1, "t":2}, "summon2": 12, "mend": 4, "ward": 5, "balor": 9, "heal": 7, "db": 4, "dc": 3, "rhada":10, "offhand": [20,21], "potion": [20,23], "set potion 19": [20,22,49], "greater elixir":[20,21,23] },
}
            #2nd of 7 spells (or of 8
#            self.tap(950,860)

            #3rd of 7 spells (or of 8
#            self.tap(1200,860)

            #4th of 7 spells (or of 8
#            self.tap(1656,860)

            #5th of 7 spells (or 5th of 8)
#            self.tap(260,966)

            #6th of 7 spells (or 6th of 8)
#            self.tap(720,966)

            #7th of 7 spells (or 8th of 8
#            self.tap(1673,966)



def stdout_reader(proc, q):
    for line in iter(proc.stdout.readline, b''):
        q.put(line.decode('utf-8'))

def stderr_reader(proc, q):
    for line in iter(proc.stderr.readline, b''):
        q.put(line.decode('utf-8'))

#  counts the lines written to the console, so the HUD's header can be repeated every half
#  screen: every = the terminal's rows (tput lines) / 2
#
class LineCounter:
    lines = 0
    every = 12

    def __init__(self, stream):
        self.stream = stream
        try:
            rows = int(subprocess.run(["tput", "lines"], capture_output=True, text=True).stdout.strip())
        except (ValueError, OSError):
            rows = 24
        LineCounter.every = max(2, rows // 2)

    #  everything printed also goes to bloons_adventure/runs/<start time>.log, so a run started
    #  from a terminal can be looked over afterwards
    log = None

    def write(self, s):
        LineCounter.lines += s.count("\n")
        if LineCounter.log is None:
            d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "runs")
            os.makedirs(d, exist_ok=True)
            LineCounter.log = open(os.path.join(d, datetime.now().strftime("%Y%m%d_%H%M%S") + ".log"), "a", buffering=1)
        LineCounter.log.write(s)
        return self.stream.write(s)

    def __getattr__(self, name):
        return getattr(self.stream, name)

sys.stdout = LineCounter(sys.stdout)

#  ---- the guest phone -----------------------------------------------------------------
#  guest_shell(serial, cmd): an Android shell command (a string, or a list of words) on the
#  phone; popen=True starts it and returns without waiting.  The result has .stdout and
#  .returncode, like subprocess's.
#
#  iOS has no shell to run them in: WebDriverAgent (WDA_URL, default http://localhost:8100;
#  started on the phone with go-ios / tidevice / Xcode) does the touches, and the Android
#  commands the bot sends are mapped onto it:
#     input tap / swipe / motionevent DOWN..MOVE..UP   taps and drags (pixels -> WDA points)
#     input keyevent KEYCODE_WAKEUP                    unlock
#     dumpsys ...                                      mScreenOn / mScreenLocked / mDisplayPolicy
#     wm size                                          Physical size: WxH (pixels, portrait)
#  anything else (settings, monkey, getevent, pidof) does nothing on iOS
#
class GuestResult:
    def __init__(self, stdout="", returncode=0):
        self.stdout = stdout
        self.returncode = returncode

    def poll(self):
        return self.returncode

    def wait(self, timeout=None):
        return self.returncode


class WDA:
    url = os.environ.get("WDA_URL", "http://localhost:8100").rstrip("/")
    session = None
    scale = None            # device pixels per WDA point

    downUntil = 0           # unreachable: not tried again until then
    downSaid = False

    @classmethod
    def call(cls, method, path, body=None, timeout=15):
        import json as js
        import urllib.request
        if time.time() < cls.downUntil:
            raise ConnectionError("WebDriverAgent not reachable")
        req = urllib.request.Request(cls.url + path, method=method,
                                     data=None if body is None else js.dumps(body).encode(),
                                     headers={"Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                out = js.loads(r.read().decode() or "{}")
        except OSError as e:
            #  not running (connection refused): said once, tried again every 30 s
            cls.downUntil = time.time() + 30
            cls.session = None
            if not cls.downSaid:
                print("IOS WebDriverAgent not reachable at %s (%s): start it on the phone" % (cls.url, e))
                cls.downSaid = True
            raise ConnectionError("WebDriverAgent not reachable")
        if cls.downSaid:
            print("IOS WebDriverAgent reachable again at %s" % cls.url)
            cls.downSaid = False
        return out

    #  True / False, or None when WebDriverAgent can't say
    @classmethod
    def locked(cls):
        try:
            return bool(cls.call("GET", "/session/%s/wda/locked" % cls.sid()).get("value"))
        except Exception:
            return None

    @classmethod
    def sid(cls):
        if cls.session is None:
            out = cls.call("POST", "/session", {"capabilities": {}})
            cls.session = out.get("sessionId") or out.get("value", {}).get("sessionId")
        return cls.session

    @classmethod
    def points(cls):
        if cls.scale is None:
            v = cls.call("GET", "/session/%s/wda/screen" % cls.sid())["value"]
            cls.scale = float(v.get("scale") or 1)
            cls.size = (int(v["screenSize"]["width"] * cls.scale), int(v["screenSize"]["height"] * cls.scale))
        return cls.scale

    @classmethod
    def gesture(cls, pts, pause_ms=0, hold_ms=100):
        #  pts: [(x, y)] in device pixels, the finger down at the first, moved along, up at the last
        s = cls.points()
        acts = [{"type": "pointerMove", "duration": 0, "x": pts[0][0] / s, "y": pts[0][1] / s},
                {"type": "pointerDown", "button": 0}, {"type": "pause", "duration": 50}]
        for x, y in pts[1:]:
            acts.append({"type": "pointerMove", "duration": max(50, pause_ms), "x": x / s, "y": y / s})
        acts += [{"type": "pause", "duration": hold_ms}, {"type": "pointerUp", "button": 0}]
        cls.call("POST", "/session/%s/actions" % cls.sid(),
                 {"actions": [{"type": "pointer", "id": "finger1", "parameters": {"pointerType": "touch"},
                               "actions": acts}]})

    #  a "DOWN; sleep; MOVE; sleep; MOVE ...; sleep; UP" line played in order: a sleep straight
    #  after DOWN or before UP is the finger held still, one between moves the next move's time
    @classmethod
    def motion(cls, cmd):
        s = cls.points()
        acts, wait, moved = [], 0.0, False
        for part in cmd.split(";"):
            w = part.split()
            if len(w) == 2 and w[0] == "sleep":
                wait += float(w[1])
                continue
            if len(w) < 5 or w[:2] != ["input", "motionevent"]:
                continue
            x, y = float(w[3]) / s, float(w[4]) / s
            if w[2] == "DOWN":
                acts += [{"type": "pointerMove", "duration": 0, "x": x, "y": y},
                         {"type": "pointerDown", "button": 0}, {"type": "pause", "duration": 50}]
            elif w[2] == "MOVE":
                if not moved and wait:
                    acts.append({"type": "pause", "duration": int(wait * 1000)})
                    wait = 0.0
                acts.append({"type": "pointerMove", "duration": max(50, int(wait * 1000)), "x": x, "y": y})
                moved = True
            elif w[2] == "UP":
                acts += [{"type": "pause", "duration": int((wait or 0.1) * 1000)}, {"type": "pointerUp", "button": 0}]
            wait = 0.0
        cls.call("POST", "/session/%s/actions" % cls.sid(),
                 {"actions": [{"type": "pointer", "id": "finger1", "parameters": {"pointerType": "touch"},
                               "actions": acts}]})

    @classmethod
    def run(cls, cmd):
        words = cmd.replace(";", " ; ").split()
        try:
            if cmd.strip().startswith("input motionevent"):
                cls.motion(cmd)
            elif words[:2] == ["input", "tap"]:
                cls.gesture([(float(words[2]), float(words[3]))])
            elif words[:2] == ["input", "swipe"]:
                x1, y1, x2, y2 = (float(v) for v in words[2:6])
                ms = int(float(words[6])) if len(words) > 6 else 300
                cls.gesture([(x1, y1), (x2, y2)], pause_ms=ms)
            elif words[:2] == ["input", "keyevent"]:
                cls.call("POST", "/session/%s/wda/unlock" % cls.sid())
            elif words[:1] == ["dumpsys"]:
                locked = bool(cls.call("GET", "/session/%s/wda/locked" % cls.sid()).get("value"))
                return GuestResult("mScreenOn=true mScreenLocked=%s mDisplayPolicy=BRIGHT" % str(locked).lower())
            elif words[:2] == ["wm", "size"]:
                cls.points()
                w, h = sorted(cls.size)
                return GuestResult("Physical size: %dx%d\n" % (w, h))
            return GuestResult()
        except ConnectionError:
            return GuestResult("", 1)
        except Exception as e:
            print("IOS %s failed: %s" % (cmd[:60], e))
            cls.session = None
            return GuestResult("", 1)


#  (os, name, id) of the attached phone: on iOS the name ideviceinfo gives (DeviceName) and
#  the UDID; on Android the model (ro.product.model) and the adb serial
def guest_identity(serial):
    if GUEST_OS == GUEST_OS_IOS:
        try:
            info = subprocess.run(["ideviceinfo", "-u", serial], capture_output=True, text=True, timeout=10).stdout
        except (OSError, subprocess.TimeoutExpired):
            info = ""
        m = re.search(r"^DeviceName:\s*(.+)$", info, re.M)
        return "iOS", m.group(1).strip() if m else "?", serial
    name = guest_shell(serial, "getprop ro.product.model", timeout=10).stdout.strip()
    return "Android", name or "?", serial


GAME_PACKAGE = "com.ninjakiwi.btdadventuretime"     # the iOS bundle id is the same
APPLE_USB_VENDOR = "05ac"
#  USB vendor ids of Android phone makers (Samsung, Google, Motorola, Xiaomi, Huawei, HTC,
#  LG, OnePlus, Qualcomm, Sony, ZTE, MediaTek)
ANDROID_USB_VENDORS = {"04e8", "18d1", "22b8", "2717", "12d1", "0bb4", "1004", "2a70", "05c6",
                       "0fce", "19d2", "0e8d"}


def run_out(args, timeout=15):
    try:
        return subprocess.run(args, capture_output=True, text=True, timeout=timeout).stdout
    except (OSError, subprocess.TimeoutExpired):
        return ""


#  how the phone is connected: "USB", its IP over the network, or None when it isn't there
#  or doesn't check out.  USB is what lsusb sees, then confirmed by adb devices (Android) or
#  idevicepair validate (iOS); a network phone is one adb devices lists by ip:port (or
#  adb mdns), or idevice_id -n lists, its IP found by Bonjour from its Wi-Fi MAC
def device_connection(serial):
    vendors = set(re.findall(r"ID ([0-9a-f]{4}):[0-9a-f]{4}", run_out(["lsusb"])))
    if GUEST_OS == GUEST_OS_IOS:
        if APPLE_USB_VENDOR in vendors and serial in run_out(["idevice_id", "-l"]).split():
            if "SUCCESS" in run_out(["idevicepair", "-u", serial, "validate"]):
                return "USB"
        if serial in run_out(["idevice_id", "-n"]).split():
            if "SUCCESS" in run_out(["idevicepair", "-n", "-u", serial, "validate"]):
                return ios_network_address(serial)
        return None
    state = {}
    for line in run_out(["adb", "devices"]).splitlines()[1:]:
        w = line.split()
        if len(w) >= 2:
            state[w[0]] = w[1]
    if state.get(serial) != "device":
        return None
    if re.match(r"^[\d.]+:\d+$", serial):
        return serial.rsplit(":", 1)[0]
    if "._adb-tls-connect" in serial:
        m = re.search(r"^%s\s+\S+\s+([\d.]+):\d+" % re.escape(serial), run_out(["adb", "mdns", "services"]), re.M)
        return m.group(1) if m else serial
    #  serial with no address: USB, which lsusb should show (or an unknown maker's vendor id)
    if not vendors & ANDROID_USB_VENDORS:
        print("DEVICE %s is on adb by USB but lsusb shows no known Android maker" % serial)
    return "USB"


#  the iPhone's IP: Bonjour (_apple-mobdev2) names it by its Wi-Fi MAC, which lockdown has
def ios_network_address(udid):
    mac = run_out(["ideviceinfo", "-n", "-u", udid, "-k", "WiFiAddress"]).strip().lower()
    host = None
    for line in run_out(["avahi-browse", "-rtp", "_apple-mobdev2._tcp"], timeout=10).splitlines():
        f = line.split(";")
        if len(f) < 8 or f[0] != "=":
            continue
        name = re.sub(r"\\(\d{3})", lambda m: chr(int(m.group(1))), f[3]).lower()
        if mac and name.startswith(mac + "@"):
            if f[2] == "IPv4":
                return f[7]
            host = host or f[7]
    return host or mac or "network"


def guest_shell(serial, cmd, popen=False, timeout=None):
    if not isinstance(cmd, str):
        cmd = " ".join(str(c) for c in cmd)
    if GUEST_OS == GUEST_OS_IOS:
        if popen:
            threading.Thread(target=WDA.run, args=(cmd,), daemon=True).start()
            return GuestResult()
        return WDA.run(cmd)
    args = ["adb", "-s", serial, "shell", cmd]
    if popen:
        return subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return subprocess.run(args, capture_output=True, text=True, timeout=timeout)

#  Ctrl-C: stop the video thread, then exit (scrcpy runs detached and is left going)
#
def handler(signum, frame):
    try:
        main.thread.stop()
    except Exception:
        pass
    try:
        main.stop_ffmpeg()
    except Exception:
        pass
    sys.exit(130)

#  however the program ends (window closed, Ctrl-C, kill/hangup, an uncaught exception,
#  sys.exit): Private DNS back off, once.  Only SIGKILL gets past it
#
restoreActions = None
restored = False

def restore_device():
    global restored
    if restored or restoreActions is None:
        return
    restored = True
    try:
        restoreActions.disablePrivateDNS()
    except Exception as e:
        print("DNS couldn't turn private dns off: %s" % e)

atexit.register(restore_device)

#  PyQt aborts on an exception escaping a slot, skipping atexit: clean up first.  The
#  signal handlers' sys.exit comes through here too, from inside Qt's loop
def excepthook(kind, value, tb):
    code = value.code if kind is SystemExit and isinstance(value.code, int) else 1
    if kind is not SystemExit:
        traceback.print_exception(kind, value, tb)
    restore_device()
    os._exit(code)

def nothing(*arg):
    pass

class Actions(object):
    def __init__(self, *args, **kwargs):
        self.debug = 0
        if 'debug' in kwargs:
            self.debug = kwargs['debug']
        if self.debug > 3:
            print("Actions __init begin")
        self.currentAction = None
        self.currentActionStart = None
        self.waitForStart = None
        self.waitForEnd = None
        self.currentActionEnd = None
        self.timeout = 5
        self._scale = None
        self._device_width = None
        self._device_height = None
        self._X11_width = None
        self._X11_height = None
        self._mOption = None
        self._serial = None
        self.iActions = []
        self.cActions = []
        if 'serial' in kwargs:
            self._serial = kwargs['serial']
        if self.debug > 3:
            print("Actions __init end")

    #  ms
    def clock(self):
        return (cv.getTickCount() / cv.getTickFrequency()) * 1000

    def actions(self,Pactions=[]):
        if hasattr(Pactions,'__len__'):
            if len(Pactions) == 0:
                raise Exception("derive this class and override this method to provide a default action list")
            else:
                if (not self.iActions):
                    self.iActions = Pactions
                    self.cActions  = self.iActions
        else:
            raise Exception("invalid parameter to actions")

        return self.cActions

    def nextAction(self):
        actions = self.actions()
        if not len(actions):
            self.reset()
            actions = self.actions()

        self.currentAction = actions.pop(0)
        self.currentActionStart = None
        self.currentActionEnd = None
        return self.currentAction

    def action(self, Paction=[]):
        if (self.currentAction == None):
            self.nextAction()
        return self.currentAction

    def do(self):
        action = self.action()
        if self.currentActionStart == None or self.currentActionEnd == None:
            self.currentAction = None
            self.currentActionStart = self.clock()

        # only waitFor action can set waitForStart
            if self.waitForStart == None:
                if isinstance(action, dict):
                    if self.debug > -1:
                        print("do: %s - %s" % (action["name"], action["action"]))
                else:
                    if self.debug > -1:
                        print("self.currentAction: [%s]" % action)

            if isinstance(action, dict):
                exec(action["action"])
            else:
                exec(action)

        else:
            print("do(): doing nothing, action started at [%s]" % self.currentActionStart)
            raise Exception("action apparently did not handle start & end properly")

    def getResolutions(self):
        try:
            serial = self.serial()
        except:
            return (None, None, None, None)

    #  get android device physical size
        result = guest_shell(serial, "wm size")
        x = 0
        y = 0
        X11x = 0
        X11y = 0
        
        m = re.search(r"^(Physical size: )(?P<y>\d+)x(?P<x>\d+)\s", result.stdout or "", re.M)
        #  the phone's size is kept once read (bloons_adventure/screen_<serial>.json), for when
        #  it can't be asked (WebDriverAgent down or still starting): taps are never scaled by 0
        keep = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "screen_%s.json" % serial)
        if m:
            x = str(m.group('x'))
            y = str(m.group('y'))
            with open(keep, "w") as f:
                json.dump({"width": int(x), "height": int(y)}, f)
        elif os.path.exists(keep):
            with open(keep) as f:
                k = json.load(f)
            x, y = str(k["width"]), str(k["height"])
        self._kept = read = not m
        read = bool(m)

    #get X11 resolution
        cmd = "xrandr --current"
    # | grep '*' | uniq | awk '{print $1}' | cut -d 'x' -f1"
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        if (len(result.stdout) > 0):
            m = re.search(r".*?(?P<x>\d+)x(?P<y>\d+)\s+.*?\*", result.stdout, re.M)
            X11x = str(m.group('x'))
            X11y = str(m.group('y'))

        if self.debug > -1 and (x, y) != getattr(self, "_said", None):
            print("device %s has resolution (%s,%s)%s, X11 has resolution (%s, %s)" % (
                  serial, x, y, "" if read else " (kept from before, it didn't answer)" if int(x) else " (didn't answer)", X11x, X11y))
            self._said = (x, y)
        self._device_width = x
        self._device_height = y
        self._X11_width = X11x
        self._X11_height = X11y
        return (int(x),int(y),int(X11x),int(X11y))

    def resolutions(self):
        #  a size that didn't read (0: the phone or WebDriverAgent not answering yet), or one only
        #  kept from before, is asked again, at most every 5 s
        unsure = not self._device_width or not self._device_height or getattr(self, "_kept", False)
        if (unsure and time.time() - getattr(self, "_asked", 0) > 5) or self._X11_width == None or self._X11_height == None:
            self._asked = time.time()
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return (self._device_width,self._device_height,self._X11_width,self._X11_height)

    def device_width(self):
        if (self._device_width == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._device_width

    def device_height(self):
        if (self._device_height == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._device_height
    def X11_width(self):
        if (self._X11_width == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._X11_width

    def X11_height(self):
        if (self._X11_height == None):
            (self._device_width,self._device_height,self._X11_width,self._X11_height) = self.getResolutions()
        return self._X11_height

    def scale(self):
        (device_width,device_height,X11_width,X11_height) = self.resolutions()
        if ((device_width > X11_width) or (device_height > X11_height)):
            self._scale=0.5
        else:
            self._scale = 1

        return self._scale

    #  option that will be used to start video for linux
    #
    def mOption(self):
        if (self._mOption == None):
            print(self.device_width())
            print(self.scale())
            self._mOption = int(float(self.device_width()) * float(self.scale()))
        return self._mOption

    def adbShell(self, cmd):
        return guest_shell(self.serial(), cmd).stdout.strip()

    #  Private DNS, as in monkey_city.py: "on, specified hostname" while the program runs
    #  (ImageControl.__init__), off again however it exits (restore_device)
    #
    def enablePrivateDNS(self, dnsServer='dns.adguard.com'):
        if GUEST_OS == GUEST_OS_IOS:
            print("DNS private dns can't be set on iOS from here (set a DNS profile on the phone)")
            return
        self.adbShell("settings put global private_dns_specifier %s" % dnsServer)
        self.adbShell("settings put global private_dns_mode hostname")
        print("DNS private dns mode %s server %s" % (self.adbShell("settings get global private_dns_mode"),
                                                    self.adbShell("settings get global private_dns_specifier")))

    def disablePrivateDNS(self):
        if GUEST_OS == GUEST_OS_IOS:
            return
        self.adbShell("settings put global private_dns_mode off")
        print("DNS private dns mode %s" % self.adbShell("settings get global private_dns_mode"))

    def serial(self):
        if (not self._serial):
#len(self._serial) <= 0):
            self.getDeviceSerial()
        return self._serial

    def getDeviceSerial(self,Pserial=""):
        if (len(Pserial)):
            self._serial = Pserial
        if GUEST_OS == GUEST_OS_IOS:
            #  the iPhone's UDID
            udids = (subprocess.run(["idevice_id", "-l"], capture_output=True, text=True).stdout.split()
                     or subprocess.run(["idevice_id", "-n"], capture_output=True, text=True).stdout.split())
            if not udids:
                raise Exception("no connected iOS device!")
            self._serial = self._serial if self._serial in udids else udids[0]
            print("using connected iOS device [%s] through WebDriverAgent at %s" % (self._serial, WDA.url))
            return self._serial
        try:
            self._serial = os.environ['ANDROID_SERIAL']
        except:
            pass

        cmd = "adb devices"
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        
        if (len(result.stdout) > 0):
            m = re.search(r"^(?!(List|\s+))(?P<serial>.*?)\s", result.stdout, re.M)
            if m:
                if (self._serial):
                    if (str(m.group('serial')) == self._serial):
                        if self.debug > -1:
                            print("using connected device [%s]" % self.serial)
                        return self._serial
                else:
                    self._serial = str(m.group('serial'))
                    if self.debug > -1:
                        print("using connected device [%s]" % self._serial)
                    return self._serial
        raise Exception("no connected android device!") 

#  high level actions begin here
#
    def tap(self, x,y):
        cmd = "input tap %s %s" % (x / self.scale(), y / self.scale())
        if self.debug > 1:
            print(cmd)
        result = guest_shell(self.serial(), cmd)
        self.currentActionEnd = self.clock()
        if self.debug > 2:
            print(result)
        return result

    def hold(self, x,y, seconds):
        cmd = "input swipe %s %s %s %s %s" % (x / self.scale(), y / self.scale(), x / self.scale(), y / self.scale(), seconds * 1000)
        if self.debug > 1:
            print(cmd)
        result = guest_shell(self.serial(), cmd)
        self.currentActionEnd = self.clock()
        if self.debug > 2:
            print(result)
        return result

    def waitFor(self, seconds):
        #print("%s.waitFor(%s)"%(type(self), seconds))

        #re-entrant version
        if self.waitForStart:
            delta = self.clock() - self.waitForStart
           # print("delta: [%s]" % delta)
            if delta >= (seconds * 1000):
                self.currentAction = None
                self.currentActionEnd = self.clock()
                self.waitForStart = None
                print("action is ending, actual wait time was %s ms" % delta)
            else:
            #    print("action is ongoing, setting currentAction")
                self.currentAction = "self.waitFor(%s)" % (seconds)
        else:
            self.currentAction = "self.waitFor(%s)" % (seconds)
            self.waitForStart = self.currentActionStart

            #once set, let do() handle clearing
            self.waitForEnd = self.waitForStart + (seconds * 1000)
            #if self.waitForStart == None:
            #raise Exception("method not called with %s.do()" % type(self))

    def reset(self):
        if self.debug > 0:
            print("Actions.reset")
        self.waitForStart = None
        self.cActions = self.iActions
        self.currentAction = None
        self.currentActionStart = None
        self.currentActionEnd = None

class Aethric(Actions):
    def __init__(self, *args, **kwargs):
        super(Aethric, self).__init__(*args, **kwargs)
        if self.debug > 3:
            print("Aethic __init end")
        self.Arena = ["summon", "ward", "summon", "stun", "freeze", "blind", "ward", "summon", "mend" ]
        self.Raid = ["ward", "summon", "offhand", "summon", "summon", "offhand", "summon", "mend", "summon", "offhand", "mend", "mend", "offhand", "mend", "mend", "offhand", "mend", "mend","offhand", "mend", "heal", "offhand"]
        self.RaidHard = ["summon", "mend", "offhand", "summon", "mend", "offhand", "mend", "mend", "heal", "offhand", "mend", "mend", "heal", "offhand", "mend", "mend","heal", "offhand", "offhand", "offhand"]
        self.RaidQ = ["summon", "offhand", "offhand", "mend", "potion"]
        self.RaidHard2 = ["ward","summon","mend","offhand","mend","mend","offhand", "heal"]
        self.RaidHard3 = ["ward","summon","mend","offhand","mend","mend","offhand", "summon", "offhand", "potion", "potion"]
        self.mode = "Raid"
        self.Raid = self.RaidQ

        if "mode" in kwargs:
            if hasattr(self,kwargs["mode"]):
                self.mode = kwargs["mode"]
        self.modeSteps = getattr(self,self.mode)
        self.names = []
        self.sleep = 8
        self.doing = ""
        if self.debug > 3:
            print("Aethic __init end")

    def actions(self, actions=[]):
        if hasattr(actions, "__len__"):
            # get
            if (len(actions) == 0):
                #initialize
                if not self.iActions:
#                    self.iActions = self.make_button_taps(["summon", "summon", "ward", "summon", "heal", "summon", "buff", "debuff", "ward", "summon", "offhand"])
                    self.iActions = self.make_button_taps(self.modeSteps)
                    print(self.mode)
                    print(self.modeSteps)
                    print(self.iActions)
                    #let reset() handle this, otherwise when event loop calls do() it will begin
                    #self.cActions = self.iActions
            # set
            else:
                print("len of parameter to actions is %s" % len(actions))
                raise Exception("please use constructor for setting default actions")
        else:
            raise Exception("implement me. %s.actions() passed a %s, val [%s]" % (type(self), type(actions), actions))
        return self.cActions

    def disable_scale(self):
        self.scale_disabled = 1

    def enable_scale(self):
        self.scale_disabled = 0

    def scale(self):
        if hasattr(self, "scale_disabled") and self.scale_disabled:
            return 1
        return super(Aethric, self).scale()

    def do(self):
        #doesn't work
        self.disable_scale()
        super(Aethric,self).do()
        self.enable_scale()

    def doToken(self, token):
        self.disable_scale()
        print("do %s" % token)
        actions = self.make_button_taps([token], False)
        for action in actions:
            if isinstance(action, dict):
                print("%s - %s" % (action["name"], action["action"]))
                QtTest.QTest.qWait(100)
                exec(action["action"])
        self.enable_scale()
        return token

    def make_button_taps(self,maptokens,lastWait=True):
        taps = []
        bmap = BTNMAP[self.mode]
        self.names = []
        for t in maptokens:
            if t in bmap:
                el = bmap[t]
            else:
                raise Exception("BTNMAP[%s] missing token %s" % (self.mode,t))

            seq = []
            turn = []

            # if its a list, its a sequence of buttons
            if hasattr(el, "__len__"):
                seq = el
                #  apparently dict's have a __len__ attr
                if isinstance(el, dict):
                    seq = [el]
            else:
                seq = [el]

            s = self.sleep
            for n in seq:
                if isinstance(n, dict): #{'n': [button_number], 't': [turns]}
                    bn = n["n"]
                    s = (n["t"] * (self.sleep - 1))
                else:
                    bn = n

                if bn not in BTNCOORDS:
                    raise Exception("BTNCOORDS missing %s" % (bn))
                (x,y) = BTNCOORDS[bn]
                turn.append("self.tap(%s,%s)" % (x,y))
                if lastWait:
                    turn.append("self.waitFor(%s)" % 1)
                s -= 1

            if lastWait:
                turn.append("self.waitFor(%s)" % s)

            i = 1
            for el in turn:
                name = "%s[%s]" % (t, i)
                i+= 1
                taps.append({"action":el, "name":name})
        return taps

def rectContains(rect,pt):
    logic = rect[0] < pt[0] < rect[0]+rect[2] and rect[1] < pt[1] < rect[1]+rect[3]
    return logic

class VideoThread(QThread):
    change_pixmap_signal = pyqtSignal(np.ndarray)
    autoplay_stopped = pyqtSignal()
    map_changed = pyqtSignal(str)
    beacon_done = pyqtSignal(str)
    beacon_time_read = pyqtSignal(str)
    stats_changed = pyqtSignal(dict)
    hud_changed = pyqtSignal(dict)
    currencies_changed = pyqtSignal(dict)
    quests_read = pyqtSignal(list)
    quest_label = pyqtSignal(str)
    quest_play = pyqtSignal()
    change_text_signal = pyqtSignal(dict)
    canny_lower_signal = pyqtSignal(int)
    canny_upper_signal = pyqtSignal(int)
    thresh_lower_signal = pyqtSignal(int)
    thresh_upper_signal = pyqtSignal(int)
    battle_signal = pyqtSignal(tuple)

    def __init__(self,vdev=0,lower=None, upper=None, lowerT=None, upperT=None,debug=False, actions=None, hudShots=False, mapName=None):
        super().__init__()
        self._run_flag = True
        self.frame_count = 0
        self.vdev = vdev
        self.timeout = 5
        self.cardsByTile = {}
        self.show_tile_grid = False
        self.scale_percent = 100 # percent of original size
        if (actions):
            self.actions = actions
        else:
            self.actions = Actions()
        #self.scale = self.actions.scale()
        #self.device_width = int(self.actions.device_width())
        #self.device_height = int(self.actions.device_height())
        self.method="edge"
        self.debug = debug
        self.debug = 3
        self.image_options = None
        self.mode_options = None
        self.cannyLower = lower
        self.cannyUpper = upper
        self.threshLower = lowerT
        self.threshUpper = upperT
        self.worldThreshLower = 42 #great for high contrast mode balor
        self.bars_hpmpward = [((168,320),"red"),((168,332),"blue"), ((168,344), "purple")]
        self.barwh = (46,6)
        self.bars_hpsummons = [ (24,368), (24,272), (96,236), (240,248), (240,392) ]
        self.health_summons = []
        self.spell_menu = False
        self.battleStart = datetime.now()
        self.battleEnd = None
        self.ward_turns = 0
        self.health_percent = 0
        self.mana_percent = 0
        self.ward_percent = 0
        self.summons = 0
        self.turns = 0
        self.action = ""
        self.actionStack = ["db"]
        self.lastTurn = None
        self.xbtn_template = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates', 'x_btn_black_10px_border.png'), 0)
        self.origintown_template = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates', 'origin_town.png'), 0)
        self.balor_template = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates', 'balor.png'), 0)
        self.warpgate_template = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates', 'warp_gate.png'), 0)
        self.continuebtn_template = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates', 'continue_button.png'), 0)
        # load the pre-trained EAST text detector
        print("[INFO] loading EAST text detector...")
        self.net = cv.dnn.readNet("frozen_east_text_detection.pb")

        #  bloons: click script from bloons_build_replay.py, replayed in "Bloons" mode;
        #  its HUD boxes (lives, money, round) are OCR'd in every mode
        self.replay = None
        self.replayStep = 0
        self.replayHits = 0
        self.replayNextOk = 0
        self.replaySettle = 1.5     # seconds after an action before the next step may fire
        self.replayMinScore = 0.9
        self.replayNeedHits = 2     # consecutive frames the template must match
        self.hudLast = {}
        self.hudSeen = {}
        self.hudNext = 0
        self.hudSpent = 0
        self.hudHeader = False
        self.hudHeaderAt = 0
        #  money gained (any increase) during the current round
        self.hudGained = 0
        self.hudShots = hudShots
        self.hudDir = None
        self.hudCount = 1
        self.glyphLib = None
        self.glyphChars = []
        self.glyphSize = (10, 14)
        #  character panel: selected name and the 12 cost tags, from bloons_build_chars.py
        self.chars = None
        self.charSeen = None
        self.charLast = None
        self.load_replay()
        self.load_chars()
        #  set by the Record button; gets every captured frame, see ImageControl.ffmpeg_clicked
        self.recorder = None
        #  set by the Place button: a bloons_place.Placer driven one action at a time
        self.placer = None
        self.placeNext = 0
        self.placeDir = None
        self.placeCount = 0
        self.placeWhere = None
        self.placeTaken = []
        self.placedThisGame = []    # where our towers are this game, so plans keep clear of them
        #  set by the Play checkbox: auto_frame plays the game, see start_autoplay
        self.autoplay = False
        self.autoStage = None
        self.autoNext = 0
        self.autoOpens = 0
        self.autoAway = 0
        rd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        try:
            self.upgradeLib = upgrade_lib.load_lib(os.path.join(rd, "upgrade_tags.npz"))
            self.upgradeKeys = upgrade_lib.load_keys(rd)
        except (OSError, KeyError):
            self.upgradeLib = None
            self.upgradeKeys = {}
        self.sellKey = cv.imread(os.path.join(rd, "upgrade_sell.png"))
        #  newest frame, for blocking navigation (play_beacon_map) run off the frame loop
        self.lastRef = None
        self.lastRefTime = 0
        self.beaconRunning = False
        self.beaconAbort = False
        #  beacon gem, as drawn on the adventure list's thumbnails and on the map select cards,
        #  and the screens/buttons on the way to it; from the clicks in bloons_adventure/
        self.beaconKeys = {n: cv.imread(os.path.join(rd, "beacon_%s.png" % n)) for n in
                           ("list", "card", "adventures", "adventure_list", "go", "story_play", "map_play",
                            "fire_kingdom", "home", "activates", "clock")}
        self.beaconGems = [self.redness(self.beaconKeys[n]) for n in ("list", "card") if self.beaconKeys[n] is not None]
        self.playKey = cv.imread(os.path.join(rd, "play_idle.png"))
        #  the lock screen's padlock, and a watcher that unlocks while automation runs
        self.lockKey = cv.imread(os.path.join(rd, "lock_icon.png"))
        self.unlocking = False
        self.screenRaw = ""
        self.unlockLock = threading.Lock()
        threading.Thread(target=self.lock_watcher, daemon=True).start()
        self.lastInput = time.time()
        self.keepAlive = True
        threading.Thread(target=self.keepalive, name="keepalive", daemon=True).start()
        #  the map's bloon path, learned from the arrow intro of the first game seen on it
        self.mapName = None
        self.mapTitle = None
        self.path = None
        self.pathQueue = None
        self.pathRetry = True
        self.hudVisible = False
        self.titleNext = 0
        self.titleSeen = None
        #  read_banner_title saves its steps here for each new strip it reads
        self.titleDumpDir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "title_ocr")
        self.titleDumpLast = None
        self.titleCandidate = None
        self.mapInfoKey = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                 "bloons_adventure", "replay", "map_info_difficulty.png"))
        #  the account bar along the top of the menus: level, exp, gold, gems, shards
        self.menuKey = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                              "bloons_adventure", "replay", "menu_gold_icon.png"))
        self.menuNext = 0
        self.menuCandidate = {}
        self.menu = {}
        #  games played and resources gained, kept across runs in stats.json
        self.statsPath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "stats.json")
        self.stats = {"games": [], "gained": {"gold": 0, "gems": 0, "shards": 0}, "menu": {}}
        if os.path.exists(self.statsPath):
            with open(self.statsPath) as f:
                self.stats.update(json.load(f))
        self.statsNext = 0
        self.game = None
        #  a whole game recorded on this map (bloons_build_script.py), replayed by autoplay
        self.script = None
        self.scriptGame = None
        self.scriptStep = 0
        self.scriptNext = 0
        self.scriptEnd = 0
        self.scriptOffset = 0
        self.scriptStartMoney = None
        self.scriptDropAndLock = None
        self.endSeq = None          # a game's end being clicked through (end_worker)
        self.cloudKey = None
        self.rankKey = None
        self.placeFails = 0         # placements failed in a row: picks the drag speed
        self.infoCloseKey = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay", "info_close.png"))
        self.resultNext = 0
        self.resultSeen = None
        self.menuBefore = None
        #  Auto Start is turned off once per run so rounds start only when play is pressed
        self.autoStartChecked = False
        self.menuBusy = False
        self.cancelNext = 0
        self.placeResult = None
        self.scriptRetried = None
        self.lastPlaced = None
        #  the game's Drop & Lock setting (pause menu): off places a tower where its drag ends
        self.dropAndLock = False
        self.planStep = None
        self.planBlocked = True
        self.bannerKey = cv.imread(os.path.join(rd, place_lib.BANNER_KEY))
        self.pausedKey = self.white_letters(cv.imread(os.path.join(rd, "pause_paused.png")))
        #  quests (quests.md): what the current quest forbids or asks for, gating autoplay
        self.conditions = {}
        self.questOn = False
        self.beaconNext = None          # when the beacon activates, from beacon_activation
        self.campaignAttempt = 0
        self.questSelected = None
        self.quests = []
        self.noDifficulty = None
        self.diffKeys = {}
        for d in ("normal", "hard", "extreme", "impoppable"):
            k = cv.imread(os.path.join(rd, "diff_%s.png" % d))
            if k is not None:
                self.diffKeys[d] = self.white_letters(k)
        self.questDiscard = self.white_letters(cv.imread(os.path.join(rd, "quest_discard.png")))
        self.mapArrows = (cv.imread(os.path.join(rd, "map_prev.png")), cv.imread(os.path.join(rd, "map_next.png")))
        with open(os.path.join(rd, "chars.json")) as f:
            self.charNames = json.load(f)["chars"]
        #  the screens after a win, tapped through back to the map (end_frame)
        rd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        self.endKeys = {k: cv.imread(os.path.join(rd, "end_%s.png" % k)) for k, _ in self.END_SCREENS}
        for k in self.END_WHITE:
            if self.endKeys[k] is not None:
                self.endKeys[k] = self.white_letters(self.endKeys[k])
        if mapName:
            self.set_map(mapName)
        threading.Thread(target=self.end_worker, name="end", daemon=True).start()
        #  Navigate: the map to go to (the GUI's dropdown), worked by nav_worker
        self.navigateTo = None
        self.navNext = 0
        threading.Thread(target=self.nav_worker, name="navigate", daemon=True).start()


    def fast_east(self,image,min_confidence=0.5):
        orig = image.copy()
        (H, W) = image.shape[:2]

        # set the new width and height and then determine the ratio in change
        # for both the width and height
        (newW, newH) = (224, 64)
        rW = W / float(newW)
        rH = H / float(newH)

        # resize the image and grab the new image dimensions
        image = cv.resize(image, (newW, newH))
        (H, W) = image.shape[:2]

        # define the two output layer names for the EAST detector model that
        # we are interested -- the first is the output probabilities and the
        # second can be used to derive the bounding box coordinates of text
        layerNames = [
            "feature_fusion/Conv_7/Sigmoid",
            "feature_fusion/concat_3"]

        # construct a blob from the image and then perform a forward pass of
        # the model to obtain the two output layer sets
        blob = cv.dnn.blobFromImage(image, 1.0, (W, H),
            (123.68, 116.78, 103.94), swapRB=True, crop=False)
        start = time.time()
        self.net.setInput(blob)
        (scores, geometry) = self.net.forward(layerNames)
        end = time.time()

        # show timing information on text prediction
    #    print("[INFO] text detection took {:.6f} seconds".format(end - start))

        # grab the number of rows and columns from the scores volume, then
        # initialize our set of bounding box rectangles and corresponding
        # confidence scores
        (numRows, numCols) = scores.shape[2:4]
        rects = []
        confidences = []

        # loop over the number of rows
        for y in range(0, numRows):
            # extract the scores (probabilities), followed by the geometrical
            # data used to derive potential bounding box coordinates that
            # surround text
            scoresData = scores[0, 0, y]
            xData0 = geometry[0, 0, y]
            xData1 = geometry[0, 1, y]
            xData2 = geometry[0, 2, y]
            xData3 = geometry[0, 3, y]
            anglesData = geometry[0, 4, y]

            # loop over the number of columns
            for x in range(0, numCols):
                # if our score does not have sufficient probability, ignore it
                if scoresData[x] < min_confidence:
                    continue

                # compute the offset factor as our resulting feature maps will
                # be 4x smaller than the input image
                (offsetX, offsetY) = (x * 4.0, y * 4.0)

                # extract the rotation angle for the prediction and then
                # compute the sin and cosine
                angle = anglesData[x]
                cos = np.cos(angle)
                sin = np.sin(angle)

                # use the geometry volume to derive the width and height of
                # the bounding box
                h = xData0[x] + xData2[x]
                w = xData1[x] + xData3[x]

                # compute both the starting and ending (x, y)-coordinates for
                # the text prediction bounding box
                endX = int(offsetX + (cos * xData1[x]) + (sin * xData2[x])) 
                endY = int(offsetY - (sin * xData1[x]) + (cos * xData2[x]))
                startX = int(endX - w)
                startY = int(endY - h)

                # scale the bounding box coordinates based on the respective
                # ratios
                #startX = int(startX * rW)
                #startY = int(startY * rH)
                #endX = int(endX * rW) + 2
                #endY = int(endY * rH) + 2

                # add the bounding box coordinates and probability score to
                # our respective lists
                rects.append((startX, startY, endX, endY))
                confidences.append(scoresData[x])

        # apply non-maxima suppression to suppress weak, overlapping bounding
        # boxes
        boxes = non_max_suppression(np.array(rects), probs=confidences)

        rects = []
        for (startX, startY, endX, endY) in boxes:
            # scale the bounding box coordinates based on the respective
            # ratios
            startX = int(startX * rW)
            startY = int(startY * rH)
            endX = int(endX * rW) + 2
            endY = int(endY * rH) + 2

            rects.append((startX, startY, endX, endY))

        return rects

    def load_replay(self):
        d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        path = os.path.join(d, "replay.json")
        if not os.path.exists(path):
            print("no replay script at %s, run bloons_build_replay.py" % path)
            return
        with open(path) as f:
            self.replay = json.load(f)
        for s in self.replay["steps"]:
            s["tmpl"] = cv.imread(os.path.join(d, s["template"])) if s["template"] else None
        for h in self.replay["hud"]:
            h["keyImg"] = cv.imread(os.path.join(d, h["key"])) if h.get("key") else None
        print("loaded replay: %d steps, hud %s" % (len(self.replay["steps"]), [h["name"] for h in self.replay["hud"]]))
        gpath = os.path.join(d, "glyphs.npz")
        if os.path.exists(gpath):
            g = np.load(gpath)
            self.glyphChars = [str(c) for c in g["chars"]]
            self.glyphLib = [s.astype(np.float32) for s in g["glyphs"]]
            self.glyphSize = (self.glyphLib[0].shape[1], self.glyphLib[0].shape[0])
            print("loaded HUD glyphs: %d samples of %s" % (len(self.glyphChars), "".join(sorted(set(self.glyphChars)))))
        else:
            print("no HUD glyphs at %s, run bloons_build_glyphs.py" % gpath)

    def load_chars(self):
        d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        path = os.path.join(d, "chars.json")
        if not os.path.exists(path):
            print("no character panel data at %s, run bloons_build_chars.py" % path)
            return
        with open(path) as f:
            self.chars = json.load(f)
        for n in self.chars["names"]:
            n["keyImg"] = cv.imread(os.path.join(d, n["key"]))
        t = np.load(os.path.join(d, "tags.npz"))
        vecs = np.array([chars_lib.unit(g.astype(np.float32)) for g in t["glyphs"]])
        self.chars["lib"] = {red: (t["chars"][t["red"] == red], vecs[t["red"] == red]) for red in (False, True)}
        print("loaded character panel: %d names, %d tag samples" % (len(self.chars["names"]), len(t["chars"])))

    #  which character is selected and what each card costs; prints when it changes.
    #  Only runs when the panel's pixels change, the tags take ~20ms to read
    #
    def chars_frame(self, ref):
        x, y, w, h = self.chars["name_search"]
        panel = cv.cvtColor(ref[y:520, x:x + w], cv.COLOR_BGR2GRAY)
        if self.charSeen is not None and cv.countNonZero(cv.threshold(cv.absdiff(panel, self.charSeen), 40, 255, cv.THRESH_BINARY)[1]) < 30:
            return
        self.charSeen = panel
        strip = ref[y:y + h, x:x + w]
        selected = None
        best = 0.8
        for n in self.chars["names"]:
            if n["keyImg"] is None:
                continue
            score = cv.minMaxLoc(cv.matchTemplate(strip, n["keyImg"], cv.TM_CCOEFF_NORMED))[1]
            if score > best:
                best = score
                selected = n["name"]
        costs = [chars_lib.read_tag(ref[ty - 2:ty + 28, tx - 3:tx + 66], self.chars["lib"]) for (tx, ty) in self.chars["tags"]]
        if all(c is None for c in costs):
            #  panel isn't showing
            state = None
        else:
            state = (selected, tuple(costs))
        if state == self.charLast or state is None:
            self.charLast = state if state is not None else self.charLast
            return
        self.charLast = state

    #  frame at the size the script was recorded at, so templates and boxes line up
    #
    #  the bot's boxes are for the phone at ROTATION_90 (camera cutout's black strip on the
    #  left).  Upside down (270, strip on the right) the menus sit MENU_DX off, and a game
    #  wherever its pause button says.  The frame is shifted back here and taps shifted out
    #  again in replay_to_device
    PAUSE_X = 1043
    MENU_DX = -46
    pauseKey = None

    @staticmethod
    def shift_x(img, dx):
        pad = np.zeros((img.shape[0], abs(dx), 3), img.dtype)
        return np.hstack([img[:, dx:], pad]) if dx > 0 else np.hstack([pad, img[:, :dx]])

    def replay_ref(self, img):
        (fw, fh) = self.replay["frame_size"]
        if img.shape[1] != fw or img.shape[0] != fh:
            img = cv.resize(img, (fw, fh), interpolation=cv.INTER_AREA)
        left, right = img[:, :12].mean(), img[:, -12:].mean()
        if left < 8 and right > 15:
            self.rotated = False
        elif right < 8 and left > 15:
            self.rotated = True
        #  where a game sits varies from launch to launch: it's measured off the pause button
        #  (at x PAUSE_X when the bot's boxes fit)
        if VideoThread.pauseKey is None:
            VideoThread.pauseKey = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                          "bloons_adventure", "replay", "game_pause.png"))
        _, score, _, loc = cv.minMaxLoc(cv.matchTemplate(img[460:540, 850:], VideoThread.pauseKey, cv.TM_CCOEFF_NORMED))
        #  dimmed behind the pause menu it still scores ~0.89, but the menu keeps the menus' place
        if score > 0.93:
            self.layoutDx = loc[0] + 850 - self.PAUSE_X
        else:
            self.layoutDx = self.MENU_DX if getattr(self, "rotated", False) else 0
        if self.layoutDx:
            img = self.shift_x(img, self.layoutDx)
        return img

    def replay_to_device(self, x, y):
        (device_width, device_height, _X11_width, _X11_height) = self.actions.resolutions()
        (fw, fh) = self.replay["frame_size"]
        return (int((x + getattr(self, "layoutDx", 0)) * int(device_width) / fw), int(y * int(device_height) / fh))

    #  one step per call: fire it once its template has matched long enough
    #
    def replay_frame(self, ref, im2):
        steps = self.replay["steps"]
        if self.replayStep >= len(steps):
            return
        now = self.clock()
        if now < self.replayNextOk:
            return
        s = steps[self.replayStep]
        if s["tmpl"] is not None:
            res = cv.matchTemplate(ref, s["tmpl"], cv.TM_CCOEFF_NORMED)
            _minVal, maxVal, _minLoc, loc = cv.minMaxLoc(res)
            th, tw = s["tmpl"].shape[:2]
            if im2.shape[:2] == ref.shape[:2]:
                color = (0, 255, 0) if maxVal >= self.replayMinScore else (0, 0, 255)
                cv.rectangle(im2, loc, (loc[0] + tw, loc[1] + th), color, 2)
            if maxVal < self.replayMinScore:
                self.replayHits = 0
                return
            self.replayHits += 1
            if self.replayHits < self.replayNeedHits:
                return
            pt = (loc[0] + s["offset"][0], loc[1] + s["offset"][1])
        else:
            maxVal = 0
            pt = tuple(s["point"])
        self.replayHits = 0

        serial = self.actions.serial()
        (x, y) = self.replay_to_device(pt[0], pt[1])
        if s["kind"] == "tap":
            cmd = "input tap %d %d" % (x, y)
            busy = 0
        else:
            #  tower placement: pick up wherever the shape is, drop on the recorded map spot
            (ex, ey) = self.replay_to_device(s["end"][0], s["end"][1])
            cmd = "input swipe %d %d %d %d %d" % (x, y, ex, ey, s["ms"])
            busy = s["ms"] / 1000.0
        print("replay step %d/%d (click %04d) score %.2f: %s" % (self.replayStep + 1, len(steps), s["n"], maxVal, cmd))
        guest_shell(serial, cmd, popen=True)
        self.replayStep += 1
        self.replayNextOk = now + busy + self.replaySettle
        if self.replayStep >= len(steps):
            print("replay finished")

    #  (pause after each of the 5 drag steps, hold before lifting) in seconds, by failures in
    #  a row: the usual quick drag, then slower, much slower, and a fast flick
    DRAG_SPEEDS = [(0, 0.6), (0.08, 0.8), (0.2, 1.2), (0, 0.2)]
    DRAG_PRESS = 0.3            # s held on the card before it's pulled
    DRAG_EXIT_LEFT = 80         # frame px left of the panel the finger goes first, at the card's height

    #  start placing a character with its pending tower centred on target (frame coords)
    #
    def start_place(self, name, target, drop=None, card_key=None, ignore=(), drop_and_lock=None):
        d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        key = cv.imread(os.path.join(d, place_lib.BANNER_KEY))
        if key is None or (drop is None and card_key is None and not self.chars):
            print("place: needs replay/%s (bloons_place.py) and chars.json (bloons_build_chars.py)" % place_lib.BANNER_KEY)
            return
        card = place_lib.card_centre(self.chars, name) if drop is None and card_key is None else None
        if drop_and_lock is None:
            drop_and_lock = self.dropAndLock
        ranges = place_lib.load_placements(path_lib.map_dir(self.mapName))["ranges"] if self.mapName else {}
        self.placer = place_lib.Placer(name, card, target, key, drop=drop, card_key=card_key,
                                       ignore=ignore or self.placedThisGame, drop_and_lock=drop_and_lock,
                                       r_guess=ranges.get(name, 60))
        self.placeWhere = None
        self.placeNext = 0
        self.placeDir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure",
                                     "place_run_%s" % datetime.now().strftime("%Y%m%d_%H%M%S"))
        os.makedirs(self.placeDir, exist_ok=True)
        self.placeCount = 0
        print("place %s at %s, frames to %s" % (name, "a planned spot" if callable(target) else target, self.placeDir))

    #  place a character by a placement option (bloons_place.PLACE_OPTIONS, e.g. "near
    #  beginning", "range just outside beginning") worked out from the map's learned path
    #  once its range circle shows; it's dragged there and moved on to the next best spot
    #  whenever the circle is red.  The result, the circle size and the red spots seen go
    #  to maps/<map>/placements.json, and a spot that worked before is tried first.
    #  False if there's no learned path for the map yet
    #
    def place_character(self, name, where, drop_and_lock=None):
        if where not in place_lib.PLACE_OPTIONS:
            print("place: options are %s" % ", ".join(place_lib.PLACE_OPTIONS))
            return False
        if self.path is None:
            print("place: no learned path for %s" % (self.mapName or "this map"))
            return False
        store = place_lib.load_placements(path_lib.map_dir(self.mapName)) if self.mapName \
            else {"ranges": {}, "placed": [], "blocked": []}
        taken = list(self.placedThisGame)
        prior = next(((q["x"], q["y"]) for q in reversed(store["placed"])
                      if q["character"] == name and q["where"] == where
                      and all(np.hypot(q["x"] - tx, q["y"] - ty) > place_lib.TAKEN_R for tx, ty in taken)), None)
        blocked = [tuple(b) for b in store["blocked"]]

        def planner(r, avoid):
            if prior is not None and prior not in avoid:
                return prior
            return place_lib.plan_spot(self.path, where, r, list(avoid) + blocked, taken)

        #  by its card's art: the party's order on the panel changes
        art = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay",
                                     "card_%s.png" % name.lower().replace(" ", "_")), cv.IMREAD_GRAYSCALE)
        self.start_place(name, planner, drop_and_lock=drop_and_lock,
                         card_key=(art, (22, 52)) if art is not None else None)
        if self.placer is None:
            return False
        self.placeWhere = where
        self.placeTaken = taken
        print("place %s %s on %s%s" % (name, where, self.mapName, ", trying last good spot %s first" % (prior,) if prior else ""))
        return True

    #  one Placer action per settled frame; every frame it decides on is saved with
    #  the action in the filename, so a live run can be checked afterwards
    #
    def place_frame(self, ref):
        now = self.clock()
        if now < self.placeNext:
            return
        p = self.placer
        a = p.step(ref)
        self.placeCount += 1
        seen = "" if p.last is None else "_at%dx%d%s" % (p.last[0], p.last[1], "red" if p.last[3] else "")
        what = "_".join(str(v) for v in a)
        what = re.sub(r"[^A-Za-z0-9_,()-]+", "-", what)[:80]
        cv.imwrite(os.path.join(self.placeDir, "place_%02d_%s%s.png" % (self.placeCount, what, seen)),
                   ref, [cv.IMWRITE_PNG_COMPRESSION, 1])
        serial = self.actions.serial()
        if a[0] == "swipe":
            (x1, y1) = self.replay_to_device(a[1], a[2])
            (x2, y2) = self.replay_to_device(a[3], a[4])
            cmd = "input swipe %d %d %d %d %d" % (x1, y1, x2, y2, a[5])
            settle = a[5] / 1000.0 + 1.0
        elif a[0] == "tap":
            (x, y) = self.replay_to_device(a[1], a[2])
            cmd = "input tap %d %d" % (x, y)
            settle = 1.0
        elif a[0] == "drag":
            #  finger down, along, held a moment at the end so what's dragged catches up, up
            (x1, y1) = self.replay_to_device(a[1], a[2])
            (x2, y2) = self.replay_to_device(a[3], a[4])
            #  after failed placements the drag changes speed (DRAG_SPEEDS: pause per step,
            #  hold at the end), in case the game missed a drag too fast or too slow
            pause, hold = self.DRAG_SPEEDS[self.placeFails % len(self.DRAG_SPEEDS)]
            legs = [((x1, y1), (x2, y2), 5)]
            press = ""
            if a[1] >= place_lib.MAP_RIGHT > a[3]:
                #  off a card: pressed a moment, then straight left out of the panel before
                #  heading for the spot.  A short or mostly upward pull from the card reads as a
                #  tap or a panel scroll and opens the character's info instead
                (ex, ey) = self.replay_to_device(place_lib.MAP_RIGHT - self.DRAG_EXIT_LEFT, a[2])
                legs = [((x1, y1), (ex, ey), 4), ((ex, ey), (x2, y2), 5)]
                press = "sleep %.2f; " % self.DRAG_PRESS
            steps = [(sx + (tx - sx) * i // n, sy + (ty - sy) * i // n) for (sx, sy), (tx, ty), n in legs
                     for i in range(1, n + 1)]
            moves = ("; sleep %.2f; " % pause if pause else "; ").join("input motionevent MOVE %d %d" % m for m in steps)
            print("place %s: drag %d %d -> %s%d %d (step pause %.2fs, hold %.1fs)"
                  % (p.name, x1, y1, "%d %d -> " % legs[0][1] if len(legs) > 1 else "", x2, y2, pause, hold))
            self.lastInput = time.time()
            guest_shell(serial, "input motionevent DOWN %d %d; %s%s; sleep %.1f; input motionevent UP %d %d"
                        % (x1, y1, press, moves, hold, x2, y2), popen=True)
            self.placeNext = now + 3.5 + len(steps) * pause + hold - 0.6 + (self.DRAG_PRESS if press else 0)
            return
        elif a[0] == "wait":
            self.placeNext = now + 0.5
            return
        else:
            print("place %s: %s" % (p.name, " ".join(str(v) for v in a)))
            self.placeResult = a[0]
            #  "can't afford" isn't the drag's fault
            if a[0] == "done":
                self.placeFails = 0
            elif "afford" not in str(a[1:]):
                self.placeFails += 1
            self.placeWhy = a[1] if len(a) > 1 else None
            #  placed straight off the card drag, it was never seen held: it's where it was aimed
            at = p.final or (p.last[:2] if p.last is not None else p.target)
            self.lastPlaced = (int(at[0]), int(at[1])) if a[0] == "done" and at is not None else None
            if self.lastPlaced is not None:
                self.placedThisGame.append(self.lastPlaced)
            if self.placeWhere and self.mapName:
                place_lib.record_placement(path_lib.map_dir(self.mapName), p, self.placeWhere, self.placeTaken)
            self.placeLastTarget = tuple(int(v) for v in p.target[:2]) if p.target is not None else None
            self.placer = None
            return
        print("place %s: %s" % (p.name, cmd))
        self.lastInput = time.time()
        guest_shell(serial, cmd, popen=True)
        self.placeNext = now + settle

    #  auto play, one step a second off the live frames:
    #     wait while the arrow intro is being learned (learn_path)
    #     if the map has a learned path, place Finn "near beginning"
    #     press play whenever the round is idle
    #     keep Finn's upgrade panel open and buy the cheapest upgrade the money covers
    #  stops when lives hit 0, or after 15 s with no game on screen
    #
    PLAY_BTN = (988, 497)

    def start_autoplay(self):
        self.autoplay = True
        self.autoStage = "place"
        self.autoNext = 0
        self.autoOpens = 0
        self.autoAway = 0
        self.autoInfoWaits = 0
        print("PLAY started on %s" % (self.mapTitle or self.mapName or "an unknown map"))

    def stop_autoplay(self, why="stopped"):
        if self.autoplay:
            print("PLAY %s" % why)
            self.autoplay_stopped.emit()
        self.autoplay = False
        self.autoStage = None

    def adb_tap(self, x, y):
        self.lastInput = time.time()
        (dx, dy) = self.replay_to_device(x, y)
        guest_shell(self.actions.serial(), ["input", "tap", dx, dy], popen=True)

    def adb_swipe(self, x1, y1, x2, y2, ms):
        self.lastInput = time.time() + ms / 1000
        (a, b) = self.replay_to_device(x1, y1)
        (c, d) = self.replay_to_device(x2, y2)
        guest_shell(self.actions.serial(), ["input", "swipe", a, b, c, d, ms])

    #  ---- beacon maps --------------------------------------------------------------
    #  a map with a beacon shows a red gem over its thumbnail.  The gem is found on the
    #  redness channel (red minus the larger of green and blue), which drops the pink map
    #  art and the orange medals: gems score 0.74-1.0 against one template or the other,
    #  everything else seen 0.55 or less
    #
    BEACON_MIN = 0.68
    IMPOPPABLE_BTN = (840, 370)     # on the map info screen, always there
    LIST_SWIPE = ((620, 440), (620, 200))
    GO_DROP = 90                    # a row's GO is right of its gem and up to this much lower

    @staticmethod
    def redness(img):
        i = img.astype(np.int16)
        return np.clip(i[..., 2] - np.maximum(i[..., 1], i[..., 0]), 0, 255).astype(np.uint8)

    #  the beacon gem on screen: (x, y) of its centre, or None
    #
    def search_beacon(self, ref):
        r = self.redness(ref)
        best, at = self.BEACON_MIN, None
        for k in self.beaconGems:
            for s in np.arange(0.8, 1.25, 0.05):
                ks = cv.resize(k, None, fx=s, fy=s)
                _, v, _, (x, y) = cv.minMaxLoc(cv.matchTemplate(r, ks, cv.TM_CCOEFF_NORMED))
                if v > best:
                    best, at = v, (x + ks.shape[1] // 2, y + ks.shape[0] // 2)
        return at

    def key_score(self, ref, name):
        k = self.beaconKeys.get(name)
        if k is None:
            return 0.0
        return cv.minMaxLoc(cv.matchTemplate(ref, k, cv.TM_CCOEFF_NORMED))[1]

    #  centres of every match of a button template, best first
    #
    def find_buttons(self, ref, name, min_score=0.8):
        k = self.beaconKeys.get(name)
        if k is None:
            return []
        r = cv.matchTemplate(ref, k, cv.TM_CCOEFF_NORMED)
        kh, kw = k.shape[:2]
        out = []
        while True:
            _, v, _, (x, y) = cv.minMaxLoc(r)
            if v < min_score:
                return out
            out.append((x + kw // 2, y + kh // 2))
            cv.rectangle(r, (x - kw // 2, y - kh // 2), (x + kw // 2, y + kh // 2), -1, -1)

    #  a frame from after now + settle (the screen has caught up with the last action)
    #
    def next_frame(self, settle=0.8, timeout=5.0):
        t = time.time() + settle
        while time.time() < t + timeout and not self.beaconAbort:
            if self.lastRef is not None and self.lastRefTime >= t:
                return self.lastRef
            time.sleep(0.05)
        return None

    #  a frame once the screen has stopped moving (a flung list coasts on after the swipe)
    #
    def still_frame(self, timeout=4.0):
        prev = self.next_frame(0.3)
        end = time.time() + timeout
        while prev is not None and time.time() < end:
            ref = self.next_frame(0.25)
            if ref is None:
                return None
            if cv.absdiff(ref, prev).max(2).mean() < 1.0:
                return ref
            prev = ref
        return prev

    #  frames until check(ref) gives something truthy: (result, ref), or (None, last ref)
    #
    def wait_for(self, check, timeout=6.0):
        end = time.time() + timeout
        ref = None
        while time.time() < end:
            ref = self.next_frame(0.3)
            if ref is not None:
                v = check(ref)
                if v:
                    return v, ref
        return None, ref

    #  on the adventure list, scroll till a thumbnail shows the beacon gem with its row's GO
    #  button visible, right of the gem and a little lower; the nearest such GO is taken.  Goes down to the end, then back up to the top, so the whole list
    #  is seen wherever it starts.  Returns (gem, go button) or None
    #
    def find_beacon(self):
        for direction in (1, -1):
            prev = None
            for _ in range(40):
                ref = self.still_frame()
                if ref is None:
                    return None
                gem = self.search_beacon(ref)
                if gem is not None:
                    #  its own GO is right of the gem and a little lower (43 px in the clicks);
                    #  one above it or far below is another row's
                    gos = [g for g in self.find_buttons(ref, "go") if g[0] > gem[0] and 0 < g[1] - gem[1] < self.GO_DROP]
                    if gos:
                        return gem, min(gos, key=lambda g: np.hypot(g[0] - gem[0], g[1] - gem[1]))
                    #  its GO isn't on screen: nudge the gem's row into view
                    self.adb_swipe(620, 300, 620, 150 if gem[1] > 300 else 450, 700)
                    continue
                if prev is not None and cv.absdiff(ref, prev).max(2).mean() < 2:
                    break                   # didn't move: that end of the list
                prev = ref
                (x1, y1), (x2, y2) = self.LIST_SWIPE
                if direction > 0:
                    self.adb_swipe(x1, y1, x2, y2, 900)
                else:
                    self.adb_swipe(x2, y2, x1, y1, 900)
        return None

    #  from the home screen (or the adventure list), start the beacon map on Impoppable:
    #  open Adventures, find the beacon on the list and press its GO, PLAY through the story
    #  page if it shows, press the play button nearest the gem on the map select, then
    #  Impoppable.  Blocking (call it off the frame loop); returns "no beacon available",
    #  "started <map>", or what went wrong
    #
    def play_beacon_map(self):
        ref = self.next_frame(0)
        if ref is None:
            return "no video"
        if self.key_score(ref, "adventure_list") < 0.9:
            if self.key_score(ref, "adventures") < 0.9:
                return "not on the home screen"
            self.adb_tap(608, 446)
            ok, ref = self.wait_for(lambda r: self.key_score(r, "adventure_list") > 0.9)
            if not ok:
                return "adventure list didn't open"
        #  the area's story page (PLAY) may come first, then its map select
        #  the gem on the map select's cards is too small to find reliably, so the map is
        #  taken from its row on the list and picked there by its place in its chapter
        def area(r):
            if self.key_score(r, "story_play") > 0.9:
                return "story"
            if self.find_buttons(r, "map_play"):
                return "maps"
            return None
        name = None
        for attempt in range(2):
            found = self.find_beacon()
            if found is None:
                return "no beacon available"
            gem, go = found
            ref = self.still_frame()
            rows = self.list_maps(ref) if ref is not None else []
            name = min(rows, key=lambda m: np.hypot(m[1][0] - go[0], m[1][1] - go[1]))[0] if rows else None
            print("BEACON on the adventure list at %s, GO %s%s" % (gem, go, ", %s" % name if name else ""))
            self.adb_tap(*go)
            #  an area's world loads first, which can take well over 6 s
            what, ref = self.wait_for(area, timeout=15)
            if what or ref is None or self.key_score(ref, "adventure_list") < 0.9:
                break
            #  still on the list: the tap missed, look again

        if what == "story":
            self.adb_tap(*self.find_buttons(ref, "story_play")[0])
            what, ref = self.wait_for(lambda r: area(r) == "maps" and "maps", timeout=15)
        if what != "maps":
            return "beacon map select didn't show"
        still = self.still_frame()
        ref = still if still is not None else ref
        plays = sorted(self.find_buttons(ref, "map_play"))
        gem = self.search_beacon(ref)
        if name:
            play = plays[min(self.chapter_pos(name), len(plays) - 1)]
        elif gem:
            play = min(plays, key=lambda b: np.hypot(b[0] - gem[0], b[1] - gem[1]))
        else:
            play = plays[0]
        self.adb_tap(*play)

        ok, ref = self.wait_for(self.map_info_screen, timeout=15)
        if not ok:
            return "map info screen didn't show"
        if name and self.arrow_to_map(name) != "ready":
            return "%s's map screen not reached" % name
        #  read the title once the banner has stopped sliding in, and twice to be sure
        title = None
        for _ in range(4):
            ref = self.still_frame()
            t = self.read_map_title(ref) if ref is not None else None
            if t and t == title:
                break
            title = t
        if title:
            self.set_map(title)
        self.adb_tap(*self.IMPOPPABLE_BTN)
        ok, ref = self.wait_for(lambda r: not self.map_info_screen(r), timeout=10)
        if not ok:
            return "Impoppable didn't start"
        return "started %s" % (title or "the beacon map")

    #  the Find Beacon checkbox: play_beacon_map on a worker; beacon_done says how it went
    #
    def start_beacon(self):
        if self.beaconRunning:
            return
        self.beaconRunning = True
        self.beaconAbort = False
        threading.Thread(target=self.beacon_worker, daemon=True).start()

    def stop_beacon(self):
        if self.beaconRunning:
            self.beaconAbort = True

    def beacon_worker(self):
        try:
            if self.current_screen_state():
                print("LOCK %s" % self.unlock_screen())
            result = self.play_beacon_map()
        except Exception as e:
            result = "failed: %s" % e
        if self.beaconAbort:
            result = "stopped"
        self.beaconRunning = False
        self.beaconAbort = False
        print("BEACON %s" % result)
        self.beacon_done.emit(result)

    #  ---- quests (quests.md) ----------------------------------------------------------
    #
    DIFFICULTY_BTN = {"normal": (375, 370), "hard": (530, 370), "extreme": (685, 370), "impoppable": (840, 370)}
    QUESTS_BTN = (713, 465)         # main menu, the round button right of Adventures
    BACK_BTN = (87, 43)             # top left on most screens (the X on the quests list)
    MAP_ARROWS = ((308, 52), (913, 52))     # map info screen: previous, next map of the chapter
    QUEST_SWIPE = ((600, 480), (600, 296))
    QUEST_COUNT = 5
    #  the Home buttons on the screens a game can end on
    END_HOME = {"defeat": (470, 365), "no_more_orbs": (440, 467)}
    DEFAULT_MAP = "Apple Forest"

    #  an ally is any card past the panel's first 10 slots (BMO and Tiny Manticore show
    #  "ALLY" too); a card the builder couldn't find on the unscrolled panel is past them
    #
    def difficulty_offered(self, ref, difficulty):
        k = self.diffKeys.get(difficulty)
        if k is None:
            return True
        x, y = self.DIFFICULTY_BTN[difficulty]
        area = self.white_letters(ref[y - 30:y + 30, x - 75:x + 75])
        return cv.minMaxLoc(cv.matchTemplate(area, k, cv.TM_CCOEFF_NORMED))[1] > 0.7

    def place_allowed(self, name, slot):
        c = self.conditions
        if c.get("no_character") and name == c["no_character"]:
            return False
        if c.get("no_allies") and (slot is None or slot >= 10):
            return False
        return True

    def conditions_text(self, c=None):
        c = self.conditions if c is None else c
        out = []
        if c.get("no_character"):
            out.append("no %s" % c["no_character"])
        if c.get("no_allies"):
            out.append("no allies")
        return ", ".join(out) or "nothing special"

    #  a quest's details as conditions and the action they mean.  OCR glues words
    #  ("onHard"), so words are looked for with the spaces taken out
    #
    def parse_quest(self, text):
        t = re.sub(r"[^a-z0-9]", "", text.lower())
        c = {}
        m = re.search(r"normal|hard|extreme|impoppable", t)
        if m:
            c["difficulty"] = m.group(0)
        if re.search(r"(without|no)(placing|using)?(any)?all(y|ies)", t):
            c["no_allies"] = True
        for name in self.charNames:
            if re.search(r"without(placing|using)(any)?" + re.sub(r"[^a-z0-9]", "", name.lower()), t):
                c["no_character"] = name
        for low, title in self.MAP_NAMES.items():
            if re.sub(r"[^a-z0-9]", "", low) in t:
                c["map"] = title
        if c:
            action = "play %s on %s%s" % (c.get("map", self.DEFAULT_MAP), c.get("difficulty", "impoppable").capitalize(),
                                          ", %s" % self.conditions_text(c) if self.conditions_text(c) != "nothing special" else "")
            return c, action
        if "martian" in t:
            hours = re.search(r"(\d+)hour", t)
            return {"note": "win the Martian Throne and hold it%s" % (" %s hours" % hours.group(1) if hours else "")}, \
                "note it (Martian Throne), play %s on Impoppable" % self.DEFAULT_MAP
        if re.search(r"pop[0-9,]*.*bloons", t) or re.search(r"open[0-9]*wishorbs?", t) or re.fullmatch(r"win[0-9]+games?", t):
            return {}, "play %s on Impoppable" % self.DEFAULT_MAP
        return None, "unknown"

    #  quest cards on screen, top to bottom: (tier, details) of the ones fully showing.
    #  Each is found by its DISCARD button (grey or red, so by its white letters); the
    #  tier is in the banner above, the details in the white box left of it
    #
    def quest_cards(self, ref):
        w = self.white_letters(ref)
        r = cv.matchTemplate(w, self.questDiscard, cv.TM_CCOEFF_NORMED)
        out = []
        while True:
            _, v, _, (x, y) = cv.minMaxLoc(r)
            if v < 0.7:
                break
            r[max(0, y - 30):y + 30, :] = -1
            top = y - 4
            if top - 46 < 95 or top + 70 > ref.shape[0]:
                continue
            banner = cv.copyMakeBorder(w[top - 46:top - 10, 235:440], 15, 15, 15, 15, cv.BORDER_CONSTANT, value=0)
            tier = pytesseract.image_to_string(255 - banner, config="--psm 7").strip().lower()
            tier = next((k for k in ("diamond", "gold", "silver", "bronze") if k in tier.replace(" ", "")), tier or "?")
            box = cv.cvtColor(ref[top:top + 68, 358:822], cv.COLOR_BGR2GRAY)
            text = " ".join(pytesseract.image_to_string(box, config="--psm 6").split())
            out.append((top, tier, text))
        return [(tier, text) for _, tier, text in sorted(out)]

    #  any screen to a zone's world map (the "main menu" with Adventures and Quests)
    #
    def go_main_menu(self):
        prev = None
        for _ in range(12):
            ref = self.still_frame()
            if ref is None:
                return False
            if self.key_score(ref, "adventures") > 0.9:
                return True
            screen, at = self.end_screen(ref)
            if screen in self.END_HOME:
                self.adb_tap(*self.END_HOME[screen])
            elif screen in ("home", "shard_and_get"):
                #  the rewards' Home button, a wish orb's Shard and Get
                self.adb_tap(*at)
            elif screen == "level_complete":
                self.adb_tap(585, 270)
            elif self.paused(ref):
                #  in a game: quit it (Exit, then Yes on "Quit level?")
                self.adb_tap(*self.EXIT_BTN)
                self.next_frame(1.5)
                self.adb_tap(*self.QUIT_YES)
            elif self.hudVisible:
                self.adb_tap(*self.PAUSE_BTN)
            elif self.key_score(ref, "home") > 0.9:
                self.adb_tap(*self.HOME_BTN)
            elif prev is not None and cv.absdiff(ref, prev).max(2).mean() < 2:
                #  Back did nothing: a reward screen that wants a tap anywhere
                self.adb_tap(585, 270)
            else:
                self.adb_tap(*self.BACK_BTN)
            prev = ref
            self.next_frame(2)
        return False

    #  the 5 daily quests: main menu, Quests, read the cards while scrolling down, close.
    #  [{"tier", "text", "conditions", "action"}], or None if the list didn't open
    #
    def read_quests(self):
        if not self.go_main_menu():
            return None
        self.adb_tap(*self.QUESTS_BTN)
        ok, ref = self.wait_for(lambda r: self.quest_cards(r))
        if not ok:
            return None
        quests, prev = [], None
        for _ in range(8):
            ref = self.still_frame()
            if ref is None:
                break
            for tier, text in self.quest_cards(ref):
                if text and all(q["text"] != text for q in quests):
                    c, action = self.parse_quest(text)
                    quests.append({"tier": tier, "text": text, "conditions": c, "action": action})
                    print("QUEST %d %s: %s -> %s" % (len(quests), tier, text, action))
            if len(quests) >= self.QUEST_COUNT or (prev is not None and cv.absdiff(ref, prev).max(2).mean() < 1):
                break
            prev = ref
            (x1, y1), (x2, y2) = self.QUEST_SWIPE
            self.adb_swipe(x1, y1, x2, y2, 1500)
        self.adb_tap(*self.BACK_BTN)
        self.next_frame(1.5)
        self.quests = quests
        self.quests_read.emit(quests)
        return quests

    #  the adventure list's areas, in arrow order from Grasslands; the label between the
    #  arrows names the one the list is in (it reads "Canpy Kincpom", so it's snapped)
    AREAS = ["Grasslands", "Candy Kingdom", "Ice Kingdom", "Badlands", "Fire Kingdom", "Lemongrab",
             "Underwater City", "Haunted Swamp", "Lumpy Space"]
    AREA_PREV = (259, 105)
    AREA_LABEL = (270, 395, 86, 126)
    INDEX_SWIPE = ((620, 400), (620, 250))      # the swipe bloons_index_maps.py counted in

    @classmethod
    def snap_area(cls, t):
        low = [a.lower() for a in cls.AREAS]
        m = difflib.get_close_matches(t.lower(), low, 1, 0.6)
        return cls.AREAS[low.index(m[0])] if m else None

    def area_label(self, ref):
        x0, x1, y0, y1 = self.AREA_LABEL
        m = cv.copyMakeBorder(self.white_letters(ref[y0:y1, x0:x1]), 15, 15, 15, 15, cv.BORDER_CONSTANT, value=0)
        t = pytesseract.image_to_string(255 - m, config="--psm 6")
        t = " ".join(w for w in t.split() if sum(c.isalpha() for c in w) >= 2)
        return self.snap_area(t) or t.title()

    #  the map's place in its chapter (0 first) from the index: the maps before it under the
    #  same heading (read slightly differently from screen to screen, so compared loosely)
    #
    def chapter_pos(self, title):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "maps_index.json")
        if not os.path.exists(path):
            return 0
        with open(path) as f:
            maps = json.load(f)["maps"]
        if title not in maps:
            return 0
        order = sorted(maps, key=lambda m: (maps[m]["area_index"], maps[m]["slot"]))
        i = order.index(title)
        ch = (maps[title].get("chapter") or "").lower()
        pos = 0
        while i - pos - 1 >= 0 and difflib.SequenceMatcher(None, (maps[order[i - pos - 1]].get("chapter") or "").lower(), ch).ratio() > 0.7:
            pos += 1
        return pos

    #  where bloons_index_maps.py found the map: arrows to its area, its swipes down, its GO;
    #  None if it isn't indexed or isn't where the index says
    #
    def go_by_index(self, title):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "maps_index.json")
        if not os.path.exists(path):
            return None
        with open(path) as f:
            where = json.load(f)["maps"].get(title)
        if where is None:
            return None
        area = where["arrow_area"]
        moved = False
        for _ in range(len(self.AREAS) + 1):
            ref = self.still_frame()
            if ref is None or self.area_label(ref) == area:
                break
            self.adb_tap(*self.ZONE_NEXT)
            moved = True
        else:
            return None
        if not moved:
            #  the list may be part way down the area: an arrow round puts it at the start
            self.adb_tap(*self.AREA_PREV)
            self.still_frame()
            self.adb_tap(*self.ZONE_NEXT)
        (x1, y1), (x2, y2) = self.INDEX_SWIPE
        for i in range(where["scrolls"] + 3):
            ref = self.still_frame()
            go = next((at for name, at in self.list_maps(ref) if name == title), None) if ref is not None else None
            if go:
                return go
            if i >= where["scrolls"] + 2:
                break
            self.adb_swipe(x1, y1, x2, y2, 1000)
        return None

    #  the maps on the adventure list with their GO buttons: [(name, (x, y))]
    #
    def list_maps(self, ref):
        out = []
        for gx, gy in self.find_buttons(ref, "go"):
            if not 140 < gy < 505:
                continue
            crop = self.white_letters(ref[gy - 78:gy - 44, 440:680])
            crop = cv.copyMakeBorder(crop, 15, 15, 15, 15, cv.BORDER_CONSTANT, value=0)
            text = pytesseract.image_to_string(255 - crop, config="--psm 7").strip().lower().replace("’", "'")
            m = difflib.get_close_matches(text, self.MAP_NAMES, 1, 0.6)
            if m:
                out.append((self.MAP_NAMES[m[0]], (gx, gy)))
        return out

    #  the map's title on the map info screen, once two reads agree
    #
    def settled_title(self):
        title = None
        for _ in range(5):
            ref = self.still_frame()
            t = self.read_map_title(ref) if ref is not None else None
            if t and t == title:
                return t
            title = t
        return title

    #  any screen to the map info screen of a map: main menu, Adventures, each zone's list
    #  scrolled through for the map's name, its GO, PLAY on the story page if it shows, a
    #  play button on the chapter's map select, then the title's arrows to the map.
    #  Returns "ready" (and the map set), or what went wrong
    #
    def navigate_to_map(self, title):
        ref = self.still_frame()
        if ref is not None and self.map_info_screen(ref) and self.settled_title() == title:
            self.set_map(title)
            return "ready"
        if not self.go_main_menu():
            return "main menu not reached"
        self.adb_tap(608, 446)
        ok, ref = self.wait_for(lambda r: self.key_score(r, "adventure_list") > 0.9)
        if not ok:
            return "adventure list didn't open"
        go = self.go_by_index(title)
        (x1, y1), (x2, y2) = self.LIST_SWIPE
        for zone in range(0 if go else 16):
            for _ in range(3):
                self.adb_swipe(x2, y2, x1, y1, 300)
            prev = None
            for _ in range(15):
                ref = self.still_frame()
                if ref is None:
                    return "stopped"
                go = next((at for name, at in self.list_maps(ref) if name == title), None)
                if go or (prev is not None and cv.absdiff(ref, prev).max(2).mean() < 1):
                    break
                prev = ref
                self.adb_swipe(x1, y1, x2, y2, 900)
            if go:
                break
            self.adb_tap(*self.ZONE_NEXT)
        if not go:
            return "%s not found on the adventure list" % title
        print("NAV %s: GO %s" % (title, go))
        self.adb_tap(*go)

        def area(r):
            if self.key_score(r, "story_play") > 0.9:
                return "story"
            if self.find_buttons(r, "map_play"):
                return "maps"
            if self.map_info_screen(r):
                return "info"
            return None
        #  an area's world loads first: Lumpy Space's story page took over 6 s
        what, ref = self.wait_for(area, timeout=15)
        if what == "story":
            self.adb_tap(*self.find_buttons(ref, "story_play")[0])
            what, ref = self.wait_for(lambda r: area(r) in ("maps", "info") and area(r), timeout=15)
        if what == "maps":
            #  the map select slides in: only once it's still are all its play buttons there
            still = self.still_frame()
            ref = still if still is not None else ref
            plays = sorted(self.find_buttons(ref, "map_play"))
            self.adb_tap(*plays[min(self.chapter_pos(title), len(plays) - 1)])
            what, ref = self.wait_for(lambda r: self.map_info_screen(r) and "info", timeout=15)
        if what != "info":
            return "map info screen didn't show"
        return self.arrow_to_map(title)

    #  on a map info screen: the title's arrows to the chapter's map with this title
    #
    def arrow_to_map(self, title):
        tried = set()
        for _ in range(8):
            t = self.settled_title()
            if t == title:
                self.set_map(title)
                return "ready"
            tried.add(t)
            ref = self.still_frame()
            arrows = [a for a, k in zip(self.MAP_ARROWS, self.mapArrows)
                      if k is not None and cv.minMaxLoc(cv.matchTemplate(ref[a[1] - 30:a[1] + 30, a[0] - 30:a[0] + 30], k,
                                                                         cv.TM_CCOEFF_NORMED))[1] > 0.8]
            if not arrows:
                break
            self.adb_tap(*arrows[-1] if len(tried) % 2 or len(arrows) == 1 else arrows[0])
        return "%s's map screen not reached" % title

    #  the Quests checkbox: read the quests, take the first one understood, go to its map
    #  and autoplay it under its conditions; again after every game while it's ticked
    #
    TIERS = ["diamond", "gold", "silver", "bronze"]

    #  the quest picked in the GUI's dropdown if it's still on the list, else the best
    #  rewarded one that's understood
    def pick_quest(self, quests):
        ok = [q for q in quests if q["action"] != "unknown"]
        sel = next((q for q in ok if q["text"] == self.questSelected), None)
        if sel:
            return sel
        return min(ok, key=lambda q: self.TIERS.index(q["tier"]) if q["tier"] in self.TIERS else 9) if ok else None

    def start_quests(self):
        if self.questOn:
            return
        self.questOn = True
        threading.Thread(target=self.quest_worker, daemon=True).start()

    def stop_quests(self):
        self.questOn = False
        self.conditions = {}

    #  the bloon beacon comes before quests: if the adventure list shows its gem, its map is
    #  played on Impoppable with no quest conditions.  Returns True if a game was started
    #
    #  Once the beacon's been seen, a failed try is tried again rather than falling back to a
    #  quest.  With no beacon, Beacon time finds when it activates, and the list isn't
    #  searched again until then
    #
    def beacon_first(self):
        if self.beaconNext is not None and datetime.now() < self.beaconNext:
            return False
        result = None
        for attempt in range(3):
            if not self.questOn or not self.go_main_menu():
                return False
            result = self.play_beacon_map()
            print("BEACON %s" % result)
            if result.startswith("started") or result == "no beacon available":
                break
        if result == "no beacon available":
            self.go_main_menu()
            when = self.beacon_activation()
            if isinstance(when, datetime):
                self.beaconNext = when
                text = when.strftime("%a %I:%M:%S %p")
                print("BEACON activates %s, quests until then" % text)
                self.beacon_time_read.emit(text)
            else:
                print("BEACON time: %s" % when)
                self.beaconNext = datetime.now() + timedelta(minutes=30)
            return False
        if not result or not result.startswith("started"):
            return False
        self.beaconNext = None
        self.conditions = {}
        self.quest_label.emit("bloon beacon: %s on Impoppable (quests on hold)" % (self.mapTitle or "beacon map"))
        return True

    def wait_game(self):
        t = time.time()
        while self.questOn and (self.autoplay or time.time() - t < 5):
            time.sleep(1)

    def quest_worker(self):
        while self.questOn:
            try:
                if self.current_screen_state():
                    print("LOCK %s" % self.unlock_screen())
                if self.beacon_first():
                    self.quest_play.emit()
                    self.wait_game()
                    continue
                quests = self.read_quests()
            except Exception as e:
                print("QUEST read failed: %s" % e)
                quests = None
            if not self.questOn:
                break
            if quests is None:
                self.quest_label.emit("quests list didn't open")
                break
            pick = self.pick_quest(quests)
            if pick is None:
                self.quest_label.emit("current quests empty")
                print("QUEST current quests empty")
                break
            self.quest_label.emit("%s: %s -> %s" % (pick["tier"], pick["text"], pick["action"]))
            print("QUEST doing %s: %s -> %s" % (pick["tier"], pick["text"], pick["action"]))
            self.conditions = dict(pick["conditions"])
            result = self.navigate_to_map(self.conditions.get("map", self.DEFAULT_MAP))
            print("NAV %s" % result)
            if result != "ready" or not self.questOn:
                self.quest_label.emit("%s (%s)" % (pick["action"], result))
                break
            self.quest_play.emit()
            #  the game: autoplay runs from the map screen to the end screens and stops
            self.wait_game()
        self.conditions = {}
        self.questOn = False

    #  ---- campaign: win as many maps as the generic plan can --------------------------
    #  Every map on the adventure list in order, on Impoppable, with its recorded script or
    #  the generic plan.  campaign.json keeps each map's games: a win settles it, and after
    #  CAMPAIGN_FAILS losses it's given up (the strategy doesn't suit every map).  The
    #  beacon still comes first
    #
    CAMPAIGN_FAILS = 3

    def campaign_load(self):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "campaign.json")
        if os.path.exists(path):
            with open(path) as f:
                return path, json.load(f)
        return path, {}

    def campaign_next(self, camp):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "maps_index.json")
        with open(path) as f:
            maps = json.load(f)["maps"]
        for m in sorted(maps, key=lambda m: (maps[m]["area_index"], maps[m]["slot"])):
            c = camp.get(m, {})
            if c.get("wins", 0) == 0 and c.get("losses", 0) < self.CAMPAIGN_FAILS and not c.get("skip"):
                return m
        return None

    def start_campaign(self):
        if self.questOn:
            return
        self.questOn = True
        threading.Thread(target=self.campaign_worker, daemon=True).start()

    def campaign_worker(self):
        while self.questOn:
            try:
                if self.current_screen_state():
                    print("LOCK %s" % self.unlock_screen())
                if self.beacon_first():
                    self.campaignAttempt = 0
                    self.quest_play.emit()
                    self.wait_game()
                    continue
                path, camp = self.campaign_load()
                title = self.campaign_next(camp)
                if title is None:
                    self.quest_label.emit("campaign: every map won or given up")
                    print("CAMPAIGN every map won or given up")
                    break
                c = camp.setdefault(title, {"wins": 0, "losses": 0, "games": 0})
                self.campaignAttempt = c["losses"]
                self.conditions = {}
                self.quest_label.emit("campaign: %s on Impoppable, try %d of %d" % (title, c["losses"] + 1, self.CAMPAIGN_FAILS))
                print("CAMPAIGN %s, try %d" % (title, c["losses"] + 1))
                result = self.navigate_to_map(title)
                print("NAV %s" % result)
                if result != "ready":
                    c["losses"] += 1
                    c.setdefault("errors", []).append(result)
                else:
                    games = len(self.stats["games"])
                    self.noDifficulty = None
                    self.quest_play.emit()
                    self.wait_game()
                    if self.noDifficulty == title:
                        c["skip"] = "no Impoppable"
                        print("CAMPAIGN %s has no Impoppable, skipped" % title)
                        with open(path, "w") as f:
                            json.dump(camp, f, indent=1)
                        continue
                    new = self.stats["games"][games:]
                    won = any(g["result"] == "win" for g in new)
                    c["games"] += 1
                    c["wins" if won else "losses"] += 1
                    c["last"] = new[-1]["result"] if new else "no game recorded"
                    print("CAMPAIGN %s: %s (%d won, %d lost)" % (title, "won" if won else c["last"], c["wins"], c["losses"]))
                with open(path, "w") as f:
                    json.dump(camp, f, indent=1)
            except Exception as e:
                print("CAMPAIGN error: %s" % e)
                time.sleep(5)
        self.questOn = False

    #  ---- beacon timer ---------------------------------------------------------------
    #  Fire Kingdom's world map has a beacon crystal; tapping it opens a "Guarantees: /
    #  Activates in: HH:MM:SS" box.  Reached through the adventure list, as in the clicks
    #  in bloons_adventure/ (click_0009 to click_0017)
    #
    ZONE_NEXT = (407, 103)          # adventure list: right arrow to the next zone
    HOME_BTN = (85, 481)            # story page: back to the zone's world map
    FIRE_CRYSTAL = (180, 366)       # Fire Kingdom world map, as it opens from the story page
    TIMER_BOX = (680, 307)          # where the timer box shows once open

    #  time left on the "Activates in:" box if it's showing, as a timedelta, else None
    #
    def read_beacon_timer(self, ref):
        k = self.beaconKeys.get("activates")
        if k is None:
            return None
        _, v, _, (x, y) = cv.minMaxLoc(cv.matchTemplate(ref, k, cv.TM_CCOEFF_NORMED))
        if v < 0.8:
            return None
        g = cv.cvtColor(ref[y + 19:y + 44, max(x - 5, 0):x + 105], cv.COLOR_BGR2GRAY)
        g = cv.resize(g, None, fx=3, fy=3, interpolation=cv.INTER_CUBIC)
        _, b = cv.threshold(g, 0, 255, cv.THRESH_BINARY + cv.THRESH_OTSU)
        b = cv.copyMakeBorder(b, 20, 20, 20, 20, cv.BORDER_CONSTANT, value=255)
        text = pytesseract.image_to_string(b, config="--psm 7 -c tessedit_char_whitelist=0123456788:")
        m = re.fullmatch(r"(\d+):(\d\d):(\d\d)", text.strip())
        if not m:
            return None
        return timedelta(hours=int(m.group(1)), minutes=int(m.group(2)), seconds=int(m.group(3)))

    #  from the home screen (or the adventure list): Adventures, right arrow till Fire
    #  Kingdom, a GO, home on its story page, then the crystal for the timer box.
    #  Blocking; returns the local datetime the beacon activates, or a string saying what
    #  went wrong
    #
    def beacon_activation(self):
        ref = self.next_frame(0)
        if ref is None:
            return "no video"
        #  the world map often has the beacon's box up already (clock, "Activates in"):
        #  then there's nothing to navigate
        if self.key_score(ref, "clock") > 0.8:
            left, ref = self.wait_for(self.read_beacon_timer, timeout=3)
            if left:
                print("BEACON timer box already showing")
                return datetime.now() + left
        if self.key_score(ref, "adventure_list") < 0.9:
            if self.key_score(ref, "adventures") < 0.9:
                return "not on the home screen"
            self.adb_tap(608, 446)
            ok, ref = self.wait_for(lambda r: self.key_score(r, "adventure_list") > 0.9)
            if not ok:
                return "adventure list didn't open"
        for _ in range(15):
            ref = self.still_frame()
            if ref is None:
                return "stopped"
            if self.key_score(ref, "fire_kingdom") > 0.85:
                break
            self.adb_tap(*self.ZONE_NEXT)
        else:
            return "Fire Kingdom not found on the adventure list"
        gos = self.find_buttons(ref, "go")
        if not gos:
            return "no GO on Fire Kingdom"
        self.adb_tap(*gos[0])
        ok, ref = self.wait_for(lambda r: self.key_score(r, "home") > 0.9)
        if not ok:
            return "story page didn't show"
        self.adb_tap(*self.HOME_BTN)
        #  the world map zooms in for a while; the box may still be open from last time
        self.next_frame(2)
        left = None
        for tap in (None, self.FIRE_CRYSTAL, self.TIMER_BOX):
            if tap is not None:
                self.still_frame()
                self.adb_tap(*tap)
            left, ref = self.wait_for(self.read_beacon_timer, timeout=4)
            if left:
                break
        if not left:
            return "no Activates in: box"
        return datetime.now() + left

    #  the Beacon time checkbox: beacon_activation on a worker (sharing Find Beacon's flags,
    #  so only one drives the device); beacon_time_read gets the local time or "unknown"
    #
    def start_beacon_time(self):
        if self.beaconRunning:
            self.beacon_time_read.emit("busy")
            return
        self.beaconRunning = True
        self.beaconAbort = False
        threading.Thread(target=self.beacon_time_worker, daemon=True).start()

    def beacon_time_worker(self):
        try:
            if self.current_screen_state():
                print("LOCK %s" % self.unlock_screen())
            when = self.beacon_activation()
        except Exception as e:
            when = "failed: %s" % e
        if self.beaconAbort:
            when = "stopped"
        self.beaconRunning = False
        self.beaconAbort = False
        if isinstance(when, datetime):
            text = when.strftime("%a %I:%M:%S %p")
            print("BEACON activates %s" % text)
        else:
            print("BEACON time: %s" % when)
            text = "unknown"
        self.beacon_time_read.emit(text)

    #  ---- lock screen ----------------------------------------------------------------
    #  from the frames, when adb can't say (current_screen_state):
    #  "black": screen off (or no new frame for LOCK_STALE s, which is how scrcpy shows
    #  it off); "dim": the faded screen before it locks, every pixel dark (normal
    #  frames, loading screens included, all reach 255, dimmed ones ~60); "lock": the
    #  lock screen's padlock in the middle (0.98-1.0 there, 0.51 at most elsewhere)
    #
    LOCK_SWIPE = ((588, 294), (587, 40), 600)  # dragging the padlock up, as in click_0021
    #  the camera cutout's black strip beside the game: wakes without touching the game.
    #  Upside down it's on the right, at 1159 on screen before the layout shift
    @property
    def WAKE_TAP(self):
        return (1159 - self.layoutDx, 270) if getattr(self, "rotated", False) else (10, 270)
    LOCK_STALE = 5.0

    def screen_state(self, ref):
        if ref is None:
            return "black"
        g = cv.cvtColor(ref, cv.COLOR_BGR2GRAY)
        mx = int(g.max())
        if mx < 15:
            return "black"
        if self.lockKey is not None and \
                cv.minMaxLoc(cv.matchTemplate(ref[235:355, 525:645], self.lockKey, cv.TM_CCOEFF_NORMED))[1] > 0.8:
            return "lock"
        if mx < 100:
            return "dim"
        return None

    #  the same states as Android reports them: deviceidle's mScreenOn / mScreenLocked and
    #  the display's mDisplayPolicy (BRIGHT, DIM, OFF, DOZE); "unknown" if adb didn't say
    #
    def device_screen_state(self):
        if GUEST_OS == GUEST_OS_IOS:
            #  no dumpsys on iOS: WebDriverAgent says locked or not ("unknown" while it's down,
            #  and the frames decide)
            locked = WDA.locked()
            self.screenRaw = "WDA locked=%s" % locked
            return "unknown" if locked is None else ("lock" if locked else None)
        try:
            out = guest_shell(self.actions.serial(),
                              "dumpsys deviceidle | grep -E 'mScreenOn=|mScreenLocked='; "
                              "dumpsys display 2>/dev/null | grep -m1 'mDisplayPolicy='; "
                              "dumpsys window windows | grep -E 'Window #|isOnScreen=true'", timeout=5).stdout
        except subprocess.TimeoutExpired:
            return "unknown"
        v = dict(re.findall(r"(mScreenOn|mScreenLocked|mDisplayPolicy)=(\w+)", out))
        #  Samsung's Accidental touch protection (screen_off_pocket): a dark window over
        #  everything that swallows touches while the proximity sensor is covered.  Android
        #  counts the phone as on and unlocked meanwhile
        shown = re.findall(r"Window #\d+ Window\{\w+ u\d+ ([^}]+)\}:\s*\n\s*isOnScreen=true", out)
        protect = "TouchProtectionPresenter" in shown
        self.screenRaw = " ".join("%s=%s" % kv for kv in sorted(v.items())) + \
            (" TouchProtectionPresenter on screen" if protect else "")
        if len(v) < 3:
            return "unknown"
        if protect:
            return "covered"
        if v["mScreenOn"] != "true" or v["mDisplayPolicy"] in ("OFF", "DOZE"):
            return "black"
        if v["mScreenLocked"] == "true":
            return "lock"
        if v["mDisplayPolicy"] == "DIM":
            return "dim"
        return None

    #  Android's word on it, or the frames' when adb doesn't answer
    def current_screen_state(self):
        state = self.device_screen_state()
        if state != "unknown":
            return state
        if self.lastRef is None or time.time() - self.lastRefTime > self.LOCK_STALE:
            return "black"
        return self.screen_state(self.lastRef)

    #  wake the screen with a tap (KEYCODE_WAKEUP first if it's off, a tap doesn't wake
    #  that), then drag the padlock up if the lock screen shows.  Blocking; returns
    #  what it did
    #
    def unlock_screen(self):
        #  the watcher and a starting task may both get here: one at a time, and the
        #  second finds it already unlocked
        with self.unlockLock:
            return self.unlock_screen_locked()

    def unlock_screen_locked(self):
        state = self.current_screen_state()
        if state is None:
            return "not locked"
        if state == "covered":
            return "can't: Accidental touch protection is blocking touches"
        self.unlocking = True
        try:
            serial = self.actions.serial()
            if state == "black":
                guest_shell(serial, "input keyevent KEYCODE_WAKEUP")
            self.adb_tap(*self.WAKE_TAP)
            time.sleep(1.5)
            if self.current_screen_state() == "lock":
                (x1, y1), (x2, y2), ms = self.LOCK_SWIPE
                self.adb_swipe(x1, y1, x2, y2, ms)
                time.sleep(1.5)
            after = self.current_screen_state()
            return "unlocked (was %s)" % state if after is None else "still %s (was %s)" % (after, state)
        finally:
            self.unlocking = False

    #  from program start, once a second: unlock_screen as soon as Android says the
    #  screen is locked, dim or off.  When adb can't say, the frames' guess has to hold
    #  three seconds running, so a fade between screens doesn't count
    #
    SCREEN_WORDS = {"lock": "screen is locked", "dim": "screen is dimmed", "black": "screen is off",
                    None: "screen is on and unlocked", "unknown": "screen state unknown, adb didn't say",
                    "covered": "screen is blocked by Accidental touch protection: the proximity sensor at the "
                               "top of the phone is covered, uncover it (or turn the setting off); taps can't clear it"}

    #  keepalive: when nothing has been sent to the phone for KEEPALIVE s, tap the strip left
    #  of the game (WAKE_TAP, outside it) so the screen doesn't time out and lock
    #
    #  an iPhone dims and locks much sooner without touches: there, every 2 s
    KEEPALIVE = 2 if GUEST_OS == GUEST_OS_IOS else 20

    def keepalive(self):
        while True:
            time.sleep(min(2, self.KEEPALIVE / 2))
            if not self.keepAlive or time.time() - self.lastInput < self.KEEPALIVE or self.unlocking:
                continue
            if self.screenRaw and "mScreenOn=false" in self.screenRaw:
                continue
            self.adb_tap(*self.WAKE_TAP)

    def lock_watcher(self):
        seen = 0
        said = "never"
        while True:
            if not self.unlocking:
                state = self.device_screen_state()
                if state != said:
                    print("SCREEN %s (%s)" % (self.SCREEN_WORDS[state], self.screenRaw or "no answer"))
                    said = state
                if state == "unknown" and GUEST_OS == GUEST_OS_IOS:
                    #  WebDriverAgent down: nothing could unlock it anyway
                    seen = 0
                elif state == "unknown":
                    seen = seen + 1 if self.current_screen_state() else 0
                else:
                    seen = 3 if state in ("lock", "dim", "black") else 0
                if seen >= 3:
                    seen = 0
                    print("LOCK %s" % self.unlock_screen())
            time.sleep(1)

    def play_idle(self, ref):
        if self.playKey is None:
            return False
        return cv.minMaxLoc(cv.matchTemplate(ref[440:540, 930:1050], self.playKey, cv.TM_CCOEFF_NORMED))[1] > 0.9

    #  Play; the first press of a game is a double tap, the second switching to fast
    #  forward, which then stays on for the game
    def press_play(self):
        #  with Auto Start on (every tower placed) rounds start themselves; the play button
        #  shows idle for a moment between them, and a tap then only turns fast forward off
        #  (turning it on doesn't start the round that's waiting: one press still, for that)
        if getattr(self, "planAutoStart", False):
            if not self.autoStartPlay:
                return
            self.autoStartPlay = False
        self.adb_tap(*self.PLAY_BTN)
        if self.game is not None and not self.game.get("fast"):
            self.game["fast"] = True
            time.sleep(0.4)
            self.adb_tap(*self.PLAY_BTN)
            print("PLAY fast forward on")

    #  the map info screen's 10 portraits are the characters this game can place: which of
    #  the coming strategy's characters (not allies) aren't among them.  Portraits are known
    #  from replay/lineup_<name>.png; one without a portrait isn't checked
    LINEUP_BOX = (540, 910, 100, 260)       # x0, x1, y0, y1

    def lineup_missing(self, ref):
        strategy = strategy_lib.STRATEGIES[self.campaignAttempt % len(strategy_lib.STRATEGIES)]
        x0, x1, y0, y1 = self.LINEUP_BOX
        area = ref[y0:y1, x0:x1]
        rd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        out = []
        for name in dict.fromkeys(strategy.characters()):
            if strategy_lib.is_ally(name):
                continue
            k = cv.imread(os.path.join(rd, "lineup_%s.png" % name.lower().replace(" ", "_")))
            if k is not None and cv.minMaxLoc(cv.matchTemplate(area, k, cv.TM_CCOEFF_NORMED))[1] < 0.8:
                out.append(name)
        return out

    def auto_frame(self, ref):
        now = self.clock()
        if now < self.autoNext or self.unlocking or self.endSeq is not None or getattr(self, "navBusy", False):
            return
        #  a character's full upgrade tree (a tap on its panel header opens it) covers the
        #  whole game: close it with its X
        if self.infoCloseKey is not None:
            _, v, _, loc = cv.minMaxLoc(cv.matchTemplate(ref[0:120, 0:200], self.infoCloseKey, cv.TM_CCOEFF_NORMED))
            if v > 0.8:
                print("PLAY upgrade tree open, closing it")
                self.adb_tap(loc[0] + self.infoCloseKey.shape[1] // 2, loc[1] + self.infoCloseKey.shape[0] // 2)
                self.autoNext = now + 1.5
                return
        if self.placer is not None or self.pathQueue is not None:
            #  a game can end while a placement is being worked: the end screens come first
            if self.end_screen(ref)[0] in ("level_complete", "defeat"):
                print("PLAY game over, dropping the placement in progress")
                self.placer = None
            else:
                return
        self.autoNext = now + 1.0
        if self.map_info_screen(ref):
            #  give map_title_frame a few seconds to settle on the title first, so the
            #  game starts with the right map's path loaded
            title = self.read_map_title(ref)
            if (not title or title != self.mapTitle) and self.autoInfoWaits < 5:
                self.autoInfoWaits += 1
                return
            difficulty = self.conditions.get("difficulty", "impoppable")
            if not self.difficulty_offered(ref, difficulty):
                #  Tree Fort, the tutorial, only has Normal
                self.noDifficulty = self.mapTitle
                self.stop_autoplay("stopped, %s has no %s" % (self.mapTitle or "this map", difficulty.capitalize()))
                return
            missing = self.lineup_missing(ref)
            if missing:
                print("PLAY not in the lineup: %s (Characters on this screen)" % ", ".join(missing))
                if any(m in self.NEVER_SKIP for m in missing):
                    self.stop_autoplay("stopped, %s isn't in the lineup" % ", ".join(m for m in missing if m in self.NEVER_SKIP))
                    return
            print("PLAY %s on %s%s" % (difficulty.capitalize(), self.mapTitle or "an unknown map",
                  " (%s)" % self.conditions_text() if self.conditions else ""))
            self.adb_tap(*self.DIFFICULTY_BTN[difficulty])
            self.autoInfoWaits = 0
            self.autoAway = 0
            self.autoStage = "place"
            self.autoNext = now + 3.0
            return
        if self.end_frame(ref):
            self.autoNext = now + 1.5
            return
        side = upgrade_lib.panel_side(ref, self.sellKey) if self.sellKey is not None else None
        panel = side is not None
        self.panelDx = side or 0
        if not self.hudVisible and not panel:
            self.autoAway += 1
            if self.autoAway >= 15:
                self.stop_autoplay("stopped, no game on screen")
            return
        self.autoAway = 0
        if self.menuBusy:
            return
        if not self.autoStartChecked and self.placer is None:
            self.menuBusy = True
            threading.Thread(target=self.autostart_worker, daemon=True).start()
            return
        if not self.script and self.cancel_pending(ref):
            return
        lives = self.hudLast.get("lives")
        if lives is not None and int(lives) < 1:
            #  lost: the Defeat screen's on its way, end_step takes it from there
            return
        if self.script:
            #  the script presses play itself; only help once this round's steps are done
            self.autoStage = "run"
            rnd = self.hud_round()
            nxt = self.script[self.scriptStep] if self.scriptGame is self.game and self.scriptStep < len(self.script) else None
            #  between rounds no money comes in, so a step waiting on money waits for the next
            money = self.hudLast.get("money")
            broke = nxt is not None and nxt["round"] == rnd and nxt.get("money") is not None and money is not None \
                and money < nxt["money"] - self.scriptOffset
            if self.play_idle(ref) and self.scriptGame is self.game and (nxt is None or nxt["round"] > rnd or broke):
                self.press_play()
                self.autoNext = now + 1.5
            return
        if self.autoStage == "place":
            self.autoStage = "run"
            self.plan_start()
        #  the money is spent first: play only once the plan's next step can't be afforded
        #  (or there's nothing left to buy, or no path to place by)
        #  or the plan's got nowhere for a while (a panel it can't open): the game goes on
        #  a place step only goes between rounds, so the "nowhere for a while" rule mustn't
        #  press play then or it never gets its turn (it gives up by itself after its tries)
        steps = self.strategy.steps if self.planStep is not None else []
        placing = self.planStep is not None and self.planStep < len(steps) and steps[self.planStep][0] == "place"
        broke = self.planBlocked or (self.path is None and self.pathQueue is None) or \
            (not placing and time.time() - getattr(self, "planActed", 0) > 10)
        if self.planStep is not None and not self.planTowers and self.path is not None:
            broke = False
        if self.play_idle(ref) and broke:
            self.press_play()
            self.autoNext = now + 1.5
            return
        self.plan_frame(ref, now, panel)

    #  ---- the generic plan: maps without a recorded game -------------------------------
    #  (place, character, where) / (upgrade, character, upgrade) / (upgrade all, character)
    #  / (ability, name, round or None).  Allies (Monkey Farmer, Cobra, Dr Monkey, Super Fans)
    #  are found on the panel by their card art.  Steps the quest's conditions forbid are
    #  skipped, and so are upgrades of what wasn't placed
    #
    ALLY_CARDS = {c for c in strategy_lib.CHARACTERS if strategy_lib.is_ally(c)}
    #  around where the tower's thought to be, widening: the panel's name says when it's hit
    PANEL_TAPS = [(0, -15), (0, 0), (0, -30), (-25, -15), (25, -15), (0, 20), (-45, -15), (45, -15),
                  (0, -55), (0, 40), (-35, 25), (35, 25)]
    PANEL_CLOSE = (330, 300)        # open map just right of the upgrade panel (the bottom edge has the powers)
    PANEL_CLOSE_RIGHT = (590, 300)  # panel on the right: open map left of it and the ability column

    def panel_close(self):
        self.adb_tap(*(self.PANEL_CLOSE_RIGHT if getattr(self, "panelDx", 0) else self.PANEL_CLOSE))
    ABILITY_OPEN = (909, 500)       # the orange ! under the ability column
    ABILITY_BOX = (875, 0, 950, 480)

    #  damage towers' spot option per campaign attempt on a map, so a loss tries another layout
    NEVER_SKIP = ("Supermonkey",)
    SAVED_NUDGE = 17           # px left a saved spot is retried at when it goes red
    PLAN_VARIANTS = ["best coverage", "near beginning", "range just outside beginning", "near middle"]

    def plan_file(self):
        return os.path.join(path_lib.map_dir(self.mapName), "plan.json") if self.mapName else None

    #  a character placed again (the four Super Fans) is "Super Fans 2", ...: each has its spot
    def plan_key(self, name):
        key, n = name, 1
        while key in self.planTowers:
            n += 1
            key = "%s %d" % (name, n)
        return key

    #  every tower placed on a map, won or lost, so the next game there puts it straight back
    def spots_file(self):
        return os.path.join(path_lib.map_dir(self.mapName), "spots.json") if self.mapName else None

    def spots_save(self, key, at):
        f = self.spots_file()
        if not f:
            return
        spots = {}
        if os.path.exists(f):
            with open(f) as fh:
                spots = json.load(fh)
        spots[key] = [int(at[0]), int(at[1])]
        os.makedirs(os.path.dirname(f), exist_ok=True)
        with open(f, "w") as fh:
            json.dump(spots, fh, indent=1)

    #  ---- placements made by hand while touches are recorded (Record adb events) ----------
    #  a swipe off a character's card onto the map, then the card's check mark: that character
    #  stands where the finger last let go on the map (map swipes in between move it, with Drop &
    #  Lock), and goes into the map's spots.json for the plan to use next game
    RECORD_CONFIRM_S = 10       # s for the check mark after the last swipe
    RECORD_SETTLE = 10          # frame px a tower settles above where the finger lets go

    def record_touch(self, kind, action=None):
        if not hasattr(self, "touchQueue"):
            import collections
            self.touchQueue = collections.deque()
        self.touchQueue.append((kind, action))

    def touch_to_frame(self, x, y):
        (device_width, device_height, _X11_width, _X11_height) = self.actions.resolutions()
        (fw, fh) = self.replay["frame_size"]
        return (x * fw / int(device_width) - getattr(self, "layoutDx", 0), y * fh / int(device_height))

    def record_cards(self):
        if getattr(self, "recCards", None) is None:
            rd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
            self.recCards = {}
            for name in self.charNames + sorted(self.ALLY_CARDS):
                k = cv.imread(os.path.join(rd, "card_%s.png" % name.lower().replace(" ", "_")), cv.IMREAD_GRAYSCALE)
                if k is not None:
                    self.recCards[name] = k
        return self.recCards

    #  the character whose card is under (x, y) on the panel, and the card's slot (as the plan's)
    def record_card_at(self, ref, x, y):
        best = None
        for name, key in self.record_cards().items():
            at = place_lib.find_card(ref, key)
            if at is None:
                continue
            slot = (at[0] + 22, at[1] + 52)
            d = np.hypot(at[0] + key.shape[1] / 2 - x, at[1] + key.shape[0] / 2 - y)
            if d < 50 and (best is None or d < best[0]):
                best = (d, name, slot)
        return best[1:] if best else (None, None)

    def record_touch_frame(self, ref):
        q = getattr(self, "touchQueue", None)
        while q:
            kind, action = q.popleft()
            if kind == "down":
                self.recDownRef = ref.copy()
                continue
            m = re.fullmatch(r"swipe_(\d+)x(\d+)_(\d+)x(\d+)_\d+ms", action or "")
            if not m:
                continue
            (sx, sy) = self.touch_to_frame(int(m.group(1)), int(m.group(2)))
            (ex, ey) = self.touch_to_frame(int(m.group(3)), int(m.group(4)))
            onMap = 0 <= ex < place_lib.MAP_RIGHT and place_lib.MAP_TOP <= ey < ref.shape[0]
            if sx >= place_lib.MAP_RIGHT and onMap:
                name, slot = self.record_card_at(getattr(self, "recDownRef", ref), sx, sy)
                if name is None:
                    print("RECORD a card dragged onto the map, but which one couldn't be told")
                    continue
                self.recPending = {"name": name, "slot": slot, "at": (ex, ey), "until": time.time() + self.RECORD_CONFIRM_S}
            elif getattr(self, "recPending", None) and sx < place_lib.MAP_RIGHT and onMap:
                self.recPending["at"] = (ex, ey)
                self.recPending["until"] = time.time() + self.RECORD_CONFIRM_S
        p = getattr(self, "recPending", None)
        if not p:
            return
        if place_lib.slot_placed(ref, p["slot"]):
            self.recPending = None
            self.record_placed(p["name"], (int(p["at"][0]), int(p["at"][1]) - self.RECORD_SETTLE))
        elif time.time() > p["until"]:
            print("RECORD %s wasn't placed (no check mark on its card), not recorded" % p["name"])
            self.recPending = None

    def record_placed(self, name, at):
        if not self.mapName:
            print("RECORD %s placed at %s, but the map isn't known: not recorded" % (name, at))
            return
        #  this game's placements by character, for Super Fans 2, 3 ...; a new game (the round
        #  back down, or another map) starts them over
        rnd = self.hud_round()
        if getattr(self, "recGame", None) != self.mapName or rnd < getattr(self, "recRound", 0):
            self.recCount = {}
        self.recGame, self.recRound = self.mapName, rnd
        n = self.recCount.get(name, 0) + 1
        self.recCount[name] = n
        key = name if n == 1 else "%s %d" % (name, n)
        self.spots_save(key, at)
        d = path_lib.map_dir(self.mapName)
        store = place_lib.load_placements(d)
        store["placed"].append({"character": name, "where": "recorded", "x": at[0], "y": at[1],
                                "time": time.strftime("%Y-%m-%d %H:%M:%S")})
        with open(os.path.join(d, "placements.json"), "w") as f:
            json.dump(store, f, indent=1)
        print("RECORD %s at (%d,%d) on %s, saved as %s" % (name, at[0], at[1], self.mapTitle or self.mapName, key))

    def plan_start(self):
        self.planActed = time.time()
        self.planDud = {}
        self.planDudTries = 0
        self.planLastBuy = None
        self.planWaitRound = None
        f = self.plan_file()
        self.planSaved = {}
        #  spots towers were placed on here before; a won plan, then a recorded layout, over them
        sf = self.spots_file()
        if sf and os.path.exists(sf):
            with open(sf) as fh:
                self.planSaved = {k: tuple(v) for k, v in json.load(fh).items()}
        if f and os.path.exists(f):
            with open(f) as fh:
                saved = json.load(fh)
            if saved.get("result") == "win":
                self.planSaved.update({k: tuple(v) for k, v in saved["towers"].items()})
        #  a layout known to win the map (layout.json, from a recorded win) comes first
        lf = os.path.join(path_lib.map_dir(self.mapName), "layout.json") if self.mapName else None
        if lf and os.path.exists(lf):
            with open(lf) as fh:
                self.planSaved.update({k: tuple(v) for k, v in json.load(fh)["towers"].items()})
            print("PLAN layout for %s: %s" % (self.mapTitle, ", ".join(sorted(self.planSaved))))
        #  each try on a map takes the next strategy, and every round of strategies the next
        #  spot option for combat towers
        n = len(strategy_lib.STRATEGIES)
        self.strategy = strategy_lib.STRATEGIES[self.campaignAttempt % n]
        self.planVariant = self.PLAN_VARIANTS[self.campaignAttempt // n % len(self.PLAN_VARIANTS)]
        self.planStep = 0
        self.planBlocked = False
        self.planTowers = {}        # name: (x, y) of its circle centre
        self.planTries = 0
        self.planNext = 0
        self.planBuying = None      # (character, card name, cards seen) while a buy is checked
        self.planOpens = 0
        self.planRound = None
        self.planAbilities = {}     # ability: the round to use it on, None for every round
        self.planBadSpots = {}      # character: saved spots that failed this game
        self.planAutoStart = False  # Auto Start turned on once every tower is placed
        self.autoStartPlay = False  # the one Play press after that, for the round waiting
        self.abilityUsed = {}       # ability: round it was last used
        self.decreeOpened = None
        self.decreeScrolls = 0
        rd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
        self.planCards = {}
        for name in self.charNames + sorted(self.ALLY_CARDS):
            k = cv.imread(os.path.join(rd, "card_%s.png" % name.lower().replace(" ", "_")), cv.IMREAD_GRAYSCALE)
            if k is not None:
                self.planCards[name] = k
        self.abilityKeys = {}
        for s in self.strategy.steps:
            if s[0] == "ability":
                self.abilityKeys[s[1]] = cv.imread(os.path.join(rd, "ability_%s.png" % s[1].lower().replace(" ", "_")))
        self.warningKeys = (cv.imread(os.path.join(rd, "sungod_warning.png")), cv.imread(os.path.join(rd, "dialog_yes.png")))
        print("PLAN strategy %s on %s (%d steps, combat towers %s)" % (self.strategy.name, self.mapTitle or "this map",
              len(self.strategy.steps), self.planVariant))

    def plan_slot(self, name):
        return self.charNames.index(name) if name in self.charNames else None

    def plan_frame(self, ref, now, panel):
        self.planBlocked = False
        #  every tower placed (or given up on): rounds no longer need to wait between them
        #  for placements, so Auto Start goes on, once a game
        steps = self.strategy.steps
        lastPlace = max((i for i, s in enumerate(steps) if s[0] == "place"), default=-1)
        if not self.planAutoStart and self.planStep > lastPlace and self.placer is None and not self.menuBusy:
            self.planAutoStart = True
            self.autoStartPlay = True
            self.menuBusy = True
            print("PLAN all towers placed, turning Auto Start on")
            threading.Thread(target=self.autostart_worker, args=(True,), daemon=True).start()
            return
        if self.planAbilities:
            self.ability_frame(ref)
        if self.placer is not None or time.time() < self.planNext:
            return
        if self.warning_yes(ref):
            return
        if self.placeResult is not None:
            result, self.placeResult = self.placeResult, None
            step = self.strategy.steps[self.planStep]
            if result == "done" and self.lastPlaced is not None:
                key = self.plan_key(step[1])
                self.planTowers[key] = self.lastPlaced
                self.spots_save(key, self.lastPlaced)
                print("PLAN %s placed at %s" % (step[1], self.lastPlaced))
                self.plan_advance()
            elif "afford" in str(self.placeWhy):
                #  not a failed try: wait for the money
                self.planBlocked = True
                self.planWaitRound = self.hud_round()
            else:
                #  tried again next round, this one played meanwhile; but not before there's
                #  a tower down (Impoppable's first round leaks straight away).  The saved spot it
                #  went for is passed over from now on (the next of a repeated character's)
                self.planTries += 1
                bad = self.planBadSpots.setdefault(step[1], [])
                if getattr(self, "planSpotTried", None) is not None:
                    bad.append(self.planSpotTried)
                #  wherever it was last aimed (a rule's spot too): not again this game
                if getattr(self, "placeLastTarget", None) is not None:
                    bad.append(self.placeLastTarget)
                self.planRetryFrom = getattr(self, "placeLastTarget", None)
                if self.planTowers:
                    self.planWaitRound = self.hud_round()
                else:
                    self.planNext = time.time() + 2
                #  Supermonkey is the strategy's core (Sun God): never given up on
                if self.planTries >= (4 if self.planTowers else 10) and step[1] not in self.NEVER_SKIP:
                    print("PLAN %s couldn't be placed, skipped" % step[1])
                    self.plan_advance()
            return
        if self.planStep >= len(self.strategy.steps):
            self.planBlocked = True
            return
        step = self.strategy.steps[self.planStep]
        money = self.hudLast.get("money")
        if step[0] == "place":
            name, where = step[1], step[2]
            if where == "best coverage":
                where = self.planVariant
            if not self.place_allowed(name, 10 if name in self.ALLY_CARDS else self.plan_slot(name)):
                print("PLAN not placing %s, the quest says %s" % (name, self.conditions_text()))
                return self.plan_advance()
            if self.path is None:
                return
            if not self.play_idle(ref):
                #  placed between rounds: no bloons crossing the map to confuse finding the
                #  pending tower, and the round's money is in
                return
            if panel:
                #  an upgrade panel left open shifts the frame the held tower is found against
                self.panel_close()
                self.planNext = time.time() + 1.2
                return
            if self.planWaitRound == self.hud_round():
                self.planBlocked = True
                return
            #  the card's own price tag says if it's affordable (the Placer checks it red)
            if money is not None and money < 300:
                self.planBlocked = True
                return
            key = self.planCards.get(name)
            if key is None:
                print("PLAN no card for %s, skipped" % name)
                return self.plan_advance()
            taken = list(self.planTowers.values())
            store = place_lib.load_placements(path_lib.map_dir(self.mapName)) if self.mapName else {"blocked": []}
            blocked = [tuple(b) for b in store.get("blocked", [])]
            path = self.path

            #  every saved spot for this character not yet used ("Super Fans", "Super Fans 2", ...),
            #  in order, past any that went red on an earlier try this game
            spots = [v for k, v in self.planSaved.items()
                     if (k == name or re.fullmatch(re.escape(name) + r" \d+", k)) and k not in self.planTowers
                     and v not in self.planTowers.values()]
            bad = self.planBadSpots.setdefault(name, [])
            saved = next((s for s in spots if s not in bad), None)

            #  "near <character>": packed against that tower (in Jake's rings), off the others
            anchor = next((v for k, v in self.planTowers.items() if where.lower() == "near " + k.lower()), None)

            self.planSpotTried = saved

            def planner(r, avoid):
                #  a saved spot (recorded layout, a won game, or where it went before), while free;
                #  gone red, the same spot SAVED_NUDGE to the left before anything else
                for s in spots:
                    if s in bad:
                        continue
                    for c in (s, (s[0] - self.SAVED_NUDGE, s[1])):
                        if c not in avoid:
                            return c
                #  all of them gone red: open ground beside them (Super Fans only need to be on
                #  the map) before the general rule
                near = [tuple(v) for k, v in self.planSaved.items()
                        if k == name or re.fullmatch(re.escape(name) + r" \d+", k)]
                for s in near:
                    for ox, oy in ((0, -45), (45, 0), (-45, 0), (0, 45), (45, -45), (-45, -45), (45, 45), (-45, 45)):
                        c = (s[0] + ox, s[1] + oy)
                        if c not in avoid and 80 < c[0] < place_lib.MAP_RIGHT - 20 and place_lib.MAP_TOP + 20 < c[1] < place_lib.MAP_BOTTOM + 40 \
                                and all(np.hypot(c[0] - t[0], c[1] - t[1]) > place_lib.TAKEN_R for t in taken):
                            return c
                #  a rule's spot that failed last try: aimed again a little off it, a different
                #  way each try (worked out again from scratch it lands in the same place)
                retry = getattr(self, "planRetryFrom", None)
                if self.planTries and retry is not None:
                    for k in range(self.planTries - 1, self.planTries - 1 + len(place_lib.RETRY_DIRS)):
                        c = place_lib.nudged(retry, k)
                        if all(np.hypot(c[0] - a[0], c[1] - a[1]) > place_lib.AVOID_R for a in list(avoid) + blocked) \
                                and all(np.hypot(c[0] - t[0], c[1] - t[1]) > place_lib.TAKEN_R for t in taken):
                            return c
                if anchor is not None:
                    others = [t for t in taken if t != anchor]
                    return place_lib.plan_spot(path, "near towers", r, list(avoid) + blocked + bad + others, [anchor])
                return place_lib.plan_spot(path, where if where in place_lib.PLACE_OPTIONS else "near towers",
                                           r, list(avoid) + blocked + bad, taken)
            print("PLAN place %s %s" % (name, where))
            self.planActed = time.time()
            self.start_place(name, planner, card_key=(key, (22, 52)), ignore=taken)
            #  red spots it meets are kept as the map's blocked ones (placements.json)
            self.placeWhere = where
            self.placeTaken = taken
            return
        if step[0] == "ability":
            self.planAbilities[step[1]] = step[2]
            print("PLAN %s %s" % (step[1], "on round %d" % step[2] if step[2] else "once every round from now"))
            return self.plan_advance()
        #  upgrades: the tower's panel has to be open
        if step[0] == "upgrade cheapest":
            step = ("upgrade all", step[1])
            once = True
        else:
            once = False
        targets = [step[1]] if step[1] != "*" else list(self.planTowers)
        targets = [t for t in targets if t in self.planTowers]
        if not targets:
            return self.plan_advance()
        who = targets[self.planOpens // len(self.PANEL_TAPS) % len(targets)] if step[1] == "*" else targets[0]
        if not panel:
            #  towers stand close together: a few points on this one, in turn
            x, y = self.planTowers[who]
            dx, dy = self.PANEL_TAPS[self.planOpens % len(self.PANEL_TAPS)]
            self.adb_tap(int(x) + dx, int(y) + dy)
            self.planOpens += 1
            self.planNext = time.time() + 1.2
            if step[1] != "*" and self.planOpens > len(self.PANEL_TAPS):
                print("PLAN %s's upgrades didn't open, skipped" % who)
                self.plan_debug_frame(ref, "no_panel_%s" % who)
                self.plan_advance()
            return
        if self.upgradeLib is None:
            return self.plan_advance()
        cards = upgrade_lib.read_cards(upgrade_lib.as_left(ref, self.panelDx), who, self.upgradeLib, self.upgradeKeys)
        known = upgrade_lib.UPGRADES.get(who)
        selected = self.selected_character(ref)
        #  the name over the panel when it's known (skins like Tuxedo Jake aren't), else
        #  whether its cards are this character's
        if selected is not None and who in self.charNames:
            wrong = selected != who
        else:
            wrong = bool(known and cards and not any(c[1] in known for c in cards))
        if wrong and step[0] == "upgrade" and self.planBuying == step[2] and not any(c[1] == step[2] for c in cards):
            #  the last upgrade it could get: only locked cards left, none on its list
            print("PLAN %s: %s bought" % (who, step[2]))
            return self.plan_advance()
        if wrong:
            #  another tower's panel (Finn's, standing next to Jake): close it, try another point
            print("PLAN that's %s's panel, not %s's, trying again" % (selected or "another tower", who))
            self.panel_close()
            self.planOpens += 1
            self.planNext = time.time() + 1.2
            if self.planOpens > len(self.PANEL_TAPS):
                print("PLAN %s's panel not found, skipped" % who)
                self.plan_debug_frame(ref, "wrong_panel_%s" % who)
                if step[1] == "*":
                    #  everyone's upgrades never end: on to the next tower
                    self.planOpens = (self.planOpens // len(self.PANEL_TAPS) + 1) * len(self.PANEL_TAPS)
                else:
                    self.plan_advance()
            return
        if step[0] == "upgrade":
            card = next((c for c in cards if c[1] == step[2]), None)
            if card is None:
                #  bought (its card went), or not offered: either way this step is over.
                #  The cards' prices have to read before "not offered" counts
                if not cards and self.planBuying != step[2]:
                    self.planOpens += 1
                    self.planNext = time.time() + 1
                    if self.planOpens > 8:
                        print("PLAN %s's upgrade cards didn't read, skipped" % who)
                        self.plan_advance()
                    return
                if self.planBuying == step[2] or self.planOpens > 2:
                    if self.planBuying != step[2]:
                        d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "plan_skips")
                        os.makedirs(d, exist_ok=True)
                        cv.imwrite(os.path.join(d, "%s_%s_%s.png" % (datetime.now().strftime("%H%M%S"), who,
                                   re.sub(r"[^A-Za-z]+", "_", step[2]))), ref)
                    print("PLAN %s: %s %s" % (who, step[2], "bought" if self.planBuying == step[2] else
                          "not on the panel (it shows %s), skipped" % ", ".join(str(c[1]) for c in cards)))
                    return self.plan_advance()
                self.planOpens += 1
                self.planNext = time.time() + 1
                return
        else:
            #  a card tapped before that took no money (locked: "needs X nearby") is passed over
            skip = self.planDud.get(who, set())
            ok = [c for c in cards if not c[2][1] and c[0] not in skip and not self.strategy.excluded(who, c[1])]
            if not cards:
                if step[1] != "*":
                    print("PLAN %s fully upgraded" % who)
                    self.plan_debug_frame(ref, "fully_upgraded_%s" % who)
                    return self.plan_advance()
                self.planOpens = (self.planOpens // len(self.PANEL_TAPS) + 1) * len(self.PANEL_TAPS)     # next tower
                return
            #  every card left passed over (locked) or excluded by the strategy (Ice King's
            #  Monsters Of Snow): nothing more to buy here
            if not ok and step[1] != "*" and cards and not any(c[2][1] for c in cards) \
                    and all(c[0] in skip or self.strategy.excluded(who, c[1]) for c in cards):
                print("PLAN %s: only locked or excluded upgrades left, moving on" % who)
                return self.plan_advance()
            if not ok:
                self.planBlocked = True
                if step[1] == "*":
                    self.planOpens = (self.planOpens // len(self.PANEL_TAPS) + 1) * len(self.PANEL_TAPS)
                return
            card = min(ok, key=lambda c: c[2][0])
        slot, cname, (price, red) = card
        if red or (money is not None and money < price):
            self.planBlocked = True
            return
        last = self.planLastBuy
        if last and last[:2] == (who, slot) and money is not None and last[2] is not None and money >= last[2]:
            self.planDudTries += 1
            if self.planDudTries >= 3:
                print("PLAN %s's %s takes no money (locked?), passing it over" % (who, cname or "upgrade %d" % slot))
                self.planDud.setdefault(who, set()).add(slot)
                self.planDudTries = 0
                self.planLastBuy = None
                if step[0] == "upgrade":
                    self.plan_advance()
                return
        else:
            if last and last[0] == who and money is not None and last[2] is not None and money < last[2]:
                self.planDud.pop(who, None)
            self.planDudTries = 0
        self.planLastBuy = (who, slot, money)
        x, y = upgrade_lib.card_box(slot)
        tx, ty, tw, th = upgrade_lib.TAG
        print("PLAN buy %s for %s $%d" % (cname or "upgrade %d" % slot, who, price))
        self.planActed = time.time()
        if once:
            self.plan_advance()
        self.adb_tap(x + tx + tw // 2 - 8 + self.panelDx, y + ty + th // 2)
        self.planBuying = cname if step[0] == "upgrade" else None
        self.planNext = time.time() + 1.2

    #  what the plan placed and how the game went, for the next game on this map
    def plan_save(self, result):
        f = self.plan_file()
        if not f or self.planStep is None or not self.planTowers:
            return
        os.makedirs(os.path.dirname(f), exist_ok=True)
        with open(f, "w") as fh:
            json.dump({"result": result, "strategy": self.strategy.name, "variant": self.planVariant,
                       "towers": self.planTowers,
                       "time": datetime.now().isoformat(timespec="seconds")}, fh, indent=1)

    #  the character whose panel is open, from the name over the card panel (None for an ally)
    def selected_character(self, ref):
        if not self.chars:
            return None
        x, y, w, h = self.chars["name_search"]
        strip = ref[y:y + h, x:x + w]
        best, name = 0.8, None
        for n in self.chars["names"]:
            if n.get("keyImg") is None:
                continue
            v = cv.minMaxLoc(cv.matchTemplate(strip, n["keyImg"], cv.TM_CCOEFF_NORMED))[1]
            if v > best:
                best, name = v, n["name"]
        return name

    def plan_debug_frame(self, ref, what):
        d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "plan_skips")
        os.makedirs(d, exist_ok=True)
        cv.imwrite(os.path.join(d, "%s_%s.png" % (datetime.now().strftime("%H%M%S"), re.sub(r"[^A-Za-z]+", "_", what))), ref)

    def plan_advance(self):
        self.planStep += 1
        self.planTries = 0
        self.planOpens = 0
        self.planBuying = None

    def char_cost(self, name):
        if self.charLast is None or name not in self.charNames:
            return None
        c = self.charLast[1][self.charNames.index(name)]
        return c[0] if c else None

    #  Royal Decree: once a round, tap its icon on the ability column (opened by the ! under it)
    #
    def ability_frame(self, ref):
        rnd = self.hud_round()
        if not rnd:
            return
        due = [a for a, r in self.planAbilities.items()
               if self.abilityUsed.get(a) != rnd and (r is None or r == rnd) and self.abilityKeys.get(a) is not None]
        if not due:
            return
        name = due[0]
        key = self.abilityKeys[name]
        x0, y0, x1, y1 = self.ABILITY_BOX
        _, v, _, loc = cv.minMaxLoc(cv.matchTemplate(ref[y0:y1, x0:x1], key, cv.TM_CCOEFF_NORMED))
        if v < 0.8:
            #  the column is open (its dark blue) but the icon's further down: scroll it up,
            #  a few times a round; closed, the orange ! opens it
            col = cv.cvtColor(ref[100:400, 885:940], cv.COLOR_BGR2HSV).reshape(-1, 3)
            opened = ((col[:, 0] > 95) & (col[:, 0] < 125) & (col[:, 1] > 120) & (col[:, 2] < 170)).mean() > 0.4
            if self.decreeOpened != rnd:
                self.decreeOpened = rnd
                self.decreeScrolls = 0
                if not opened:
                    self.adb_tap(*self.ABILITY_OPEN)
                    return
            if opened and self.decreeScrolls < 3:
                self.decreeScrolls += 1
                self.adb_swipe(912, 420, 912, 160, 600)
            elif opened and self.decreeScrolls == 3:
                self.decreeScrolls += 1
                print("PLAN %s's icon not found (best %.2f)" % (name, v))
                self.plan_debug_frame(ref, "no_%s" % name.lower().replace(" ", "_"))
            return
        self.adb_tap(x0 + loc[0] + key.shape[1] // 2, y0 + loc[1] + key.shape[0] // 2)
        self.abilityUsed[name] = rnd
        print("PLAN %s, round %d" % (name, rnd))

    #  buying Sun God asks to confirm (its warning about Super Fans): Yes
    #
    def warning_yes(self, ref):
        title, yes = self.warningKeys
        if title is None or yes is None:
            return False
        if cv.minMaxLoc(cv.matchTemplate(ref, title, cv.TM_CCOEFF_NORMED))[1] < 0.8:
            return False
        _, v, _, loc = cv.minMaxLoc(cv.matchTemplate(ref, yes, cv.TM_CCOEFF_NORMED))
        if v < 0.8:
            return False
        print("PLAN warning dialog, Yes")
        self.adb_tap(loc[0] + yes.shape[1] // 2, loc[1] + yes.shape[0] // 2)
        self.planNext = time.time() + 1.5
        return True

    #  a placement left waiting for its check mark with no Placer on it (one that failed, or
    #  a drop that took live but not in the recording) blocks every later one: cancel it
    #
    def cancel_pending(self, ref):
        if self.bannerKey is None or self.placer is not None or time.time() < self.cancelNext:
            return False
        at = place_lib.find_banner(ref, self.bannerKey)
        if at is None:
            return False
        print("PLAY a placement was left pending, cancelling it")
        self.cancelNext = time.time() + 2
        self.adb_tap(at[0] + place_lib.CANCEL_OFF[0], at[1] + place_lib.CANCEL_OFF[1])
        return True

    #  Auto Start (pause menu) starts each round by itself; with it off a round starts only
    #  when play is pressed, so the script's steps for a round are all done before the next.
    #  Checked once per run, on a worker
    #
    PAUSE_BTN = (1060, 497)
    AUTOSTART_TOGGLE = (742, 215)
    RESUME_BTN = (740, 370)
    EXIT_BTN = (468, 370)
    QUIT_YES = (551, 375)

    #  Drop & Lock is the toggle under it: the bot drags towers straight to their spot and
    #  expects them placed on release, so it's turned off too
    DROPLOCK_TOGGLE = (742, 280)

    def autostart_on(self, ref, y=200):
        h, s_, _ = cv.cvtColor(ref[y:y + 30, 712:730], cv.COLOR_BGR2HSV).reshape(-1, 3).mean(0)
        return 35 < h < 85 and s_ > 120

    def droplock_on(self, ref):
        return self.autostart_on(ref, 265)

    def paused(self, ref):
        k = self.pausedKey
        return k is not None and cv.minMaxLoc(cv.matchTemplate(self.white_letters(ref[90:190, 450:770]), k,
                                                               cv.TM_CCOEFF_NORMED))[1] > 0.8

    #  want: Auto Start off while towers are being placed (between rounds), on once they
    #  all are (plan_frame); Drop & Lock is set at the start only
    def autostart_worker(self, want=False):
        try:
            self.adb_tap(*self.PAUSE_BTN)
            ok, ref = self.wait_for(self.paused)
            if not ok:
                print("PLAY pause menu didn't open, Auto Start left as it is")
                return
            ref = self.still_frame()
            word = "on" if want else "off"
            if self.autostart_on(ref) != want:
                self.adb_tap(*self.AUTOSTART_TOGGLE)
                ref = self.next_frame(1.0)
                print("PLAY Auto Start turned %s%s" % (word, "" if ref is not None and self.autostart_on(ref) == want else " (unconfirmed)"))
            else:
                print("PLAY Auto Start is already %s" % word)
            ref = self.still_frame()
            if not want and ref is not None and self.droplock_on(ref) != bool(self.dropAndLock):
                self.adb_tap(*self.DROPLOCK_TOGGLE)
                ref = self.next_frame(1.0)
                print("PLAY Drop & Lock turned %s%s" % ("on" if self.dropAndLock else "off",
                      "" if ref is not None and self.droplock_on(ref) == bool(self.dropAndLock) else " (unconfirmed)"))
            elif not want:
                print("PLAY Drop & Lock is already %s" % ("on" if self.dropAndLock else "off"))
            self.adb_tap(*self.RESUME_BTN)
            self.wait_for(lambda r: not self.paused(r))
        finally:
            self.autoStartChecked = True
            self.menuBusy = False

    def hud_round(self):
        r = self.hudLast.get("round")
        return int(r.split("/")[0]) if r and re.fullmatch(r"\d+/\d+", r) else 0

    #  replays the map's recorded game, step by step: a step waits for its round, for the
    #  money the recording had when it was made (dropped once the round has moved on), and
    #  for its gap after the step before has finished.  A place step drops its card with the
    #  recorded drag and hands over to the Placer, which drags the tower to the recorded spot
    #  until its circle isn't red and confirms; the script waits for it.  Only from round 1
    #  of a game autoplay was on for, so a stale round from the last game can't fire it all
    #
    def script_frame(self, ref):
        g = self.game
        if g is None or self.unlocking or self.menuBusy or self.autoStage == "end":
            return
        if self.placer is not None:
            #  a place step is still being worked by place_frame
            self.scriptEnd = time.time()
            return
        if self.cancel_pending(ref):
            self.scriptEnd = time.time() + 1
            return
        if self.placeResult == "fail":
            print("SCRIPT debug: placement failed at step %d (%s), retried %s" % (self.scriptStep,
                  "place" if self.scriptStep and "place" in self.script[self.scriptStep - 1] else "not a place step", self.scriptRetried))
        if self.placeResult == "fail" and self.scriptStep and "place" in self.script[self.scriptStep - 1] \
                and self.scriptRetried != self.scriptStep:
            #  a failed placement gets one more go once its pending tower is cancelled
            self.placeResult = None
            self.scriptRetried = self.scriptStep
            self.scriptStep -= 1
            print("SCRIPT placement failed, trying it once more")
        self.placeResult = None
        if self.scriptGame is not g:
            if g["round"] != 1:
                return
            #  Play turned on with round 1 already up still counts
            g["autoplay"] = True
            self.scriptGame = g
            self.scriptStep = 0
            self.scriptEnd = time.time()
            #  the recording may have started with more cash (it had $300 more than a live
            #  game did); its money gates are lowered by the difference
            money = self.hudLast.get("money")
            self.scriptOffset = max(0, self.scriptStartMoney - money) if self.scriptStartMoney and money else 0
            if self.scriptOffset:
                print("SCRIPT starting cash $%d short of the recording's, money gates lowered by that" % self.scriptOffset)
        if self.scriptStep >= len(self.script):
            return
        s = self.script[self.scriptStep]
        now = time.time()
        rnd = self.hud_round()
        if rnd < s["round"]:
            return
        if rnd == s["round"]:
            money = self.hudLast.get("money")
            if s["money"] is not None and money is not None and money < s["money"] - self.scriptOffset:
                return
            if now < self.scriptEnd + max(0.3, s["after"]):
                return
        elif now < self.scriptEnd + 0.4:
            return
        if "place" in s and not self.place_allowed(s.get("character"), s.get("slot")):
            self.scriptStep += 1
            self.scriptEnd = now
            print("SCRIPT %d/%d round %d: not placing %s, the quest says %s" % (self.scriptStep, len(self.script), rnd,
                  s.get("character") or s["place"], self.conditions_text()))
            return
        if "place" in s:
            self.scriptStep += 1
            print("SCRIPT %d/%d round %d: place %s at %s" % (self.scriptStep, len(self.script), rnd, s["place"], tuple(s["target"])))
            self.start_place(s["place"], tuple(s["target"]), drop=s["drop"], card_key=s.get("cardKey"),
                             drop_and_lock=self.scriptDropAndLock)
            self.scriptEnd = now
            return
        serial = self.actions.serial()
        #  the script's device coordinates are for the phone at 90, like the frames
        dx = self.replay_to_device(0, 0)[0]
        if "x2" in s:
            cmd = ["input", "swipe", str(s["x"] + dx), str(s["y"]), str(s["x2"] + dx), str(s["y2"]), str(s["ms"])]
        else:
            cmd = ["input", "tap", str(s["x"] + dx), str(s["y"])]
        self.lastInput = time.time()
        guest_shell(serial, cmd, popen=True)
        self.scriptStep += 1
        self.scriptEnd = now + s.get("ms", 0) / 1000
        print("SCRIPT %d/%d round %d%s: %s" % (self.scriptStep, len(self.script), rnd,
              "" if rnd == s["round"] else " (recorded in %d)" % s["round"], " ".join(cmd[1:])))

    #  after a win: Level Complete and the reward screens each want a tap anywhere, the
    #  rewards summary its Home button, then every wish orb is sharded until there are
    #  none left.  Returns True while it's handling these screens
    #
    END_SCREENS = [("no_more_orbs", (250, 950, 150, 350)), ("shard_and_get", (0, 330, 380, 540)),
                   ("home", (380, 850, 380, 540)), ("level_complete", (250, 950, 100, 300)),
                   ("defeat", (250, 950, 0, 300))]

    #  the Level Complete and Defeat banners take the zone's colour (pink, green): they're
    #  matched on their white lettering
    END_WHITE = ("level_complete", "defeat")

    @staticmethod
    def white_letters(img):
        hsv = cv.cvtColor(img, cv.COLOR_BGR2HSV)
        return ((hsv[..., 1] < 60) & (hsv[..., 2] > 200)).astype(np.uint8) * 255

    def end_screen(self, ref):
        for k, (x0, x1, y0, y1) in self.END_SCREENS:
            t = self.endKeys.get(k)
            if t is None:
                continue
            area = ref[y0:y1, x0:x1]
            if k in self.END_WHITE:
                area = self.white_letters(area)
            _, score, _, loc = cv.minMaxLoc(cv.matchTemplate(area, t, cv.TM_CCOEFF_NORMED))
            if score > 0.8:
                return k, (x0 + loc[0] + t.shape[1] // 2, y0 + loc[1] + t.shape[0] // 2)
        return None, None

    #  once a second, played by hand or not: say when a game ends on Level Complete or
    #  Defeat, and settle its stats then (the HUD stays up behind Defeat)
    #
    def result_frame(self, ref):
        now = self.clock()
        if now < self.resultNext:
            return
        self.resultNext = now + 1
        screen, _ = self.end_screen(ref)
        if screen not in ("level_complete", "defeat"):
            self.resultSeen = None
            return
        if screen == self.resultSeen:
            return
        self.resultSeen = screen
        print("GAME %s detected on %s" % ("level complete" if screen == "level_complete" else "defeat",
              self.mapTitle or "an unknown map"))
        if self.game is not None:
            self.game["won" if screen == "level_complete" else "lost"] = True
            if screen == "defeat":
                self.end_game()

    #  Navigate (GUI): with a map picked, go to its info screen whenever the game's on a
    #  screen navigation starts from: the opening screen (tapped through first), the main
    #  menu, the adventure list, an area/story page, or another map's info screen.  Not in a
    #  game or while a game's end is being clicked through.  Its own thread
    #
    def nav_worker(self):
        opening = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay",
                                         "opening_tap.png"))
        self.navBusy = False
        while True:
            time.sleep(2)
            target = self.navigateTo
            ref = self.lastRef
            if not target or ref is None or time.time() - self.lastRefTime > 3 or time.time() < self.navNext \
                    or (self.endSeq is not None and not self.endSeq.get("home")) or self.hudVisible or self.menuBusy \
                    or self.unlocking or self.placer:
                continue
            try:
                if self.map_info_screen(ref):
                    if self.mapTitle == target:
                        continue
                    where = "the %s screen" % (self.mapTitle or "map")
                elif opening is not None and cv.minMaxLoc(cv.matchTemplate(ref, opening, cv.TM_CCOEFF_NORMED))[1] > 0.8:
                    print("NAV opening screen, tapping to continue")
                    self.adb_tap(585, 270)
                    self.navNext = time.time() + 6
                    continue
                elif self.key_score(ref, "adventures") > 0.9:
                    where = "the main menu"
                elif self.key_score(ref, "adventure_list") > 0.9:
                    where = "the adventure list"
                elif self.key_score(ref, "home") > 0.9 or self.key_score(ref, "story_play") > 0.9:
                    where = "an area page"
                else:
                    continue
                print("NAV from %s to %s" % (where, target))
                self.navBusy = True
                result = self.navigate_to_map(target)
                print("NAV %s" % result)
                self.navNext = time.time() + (3 if result == "ready" else 30)
            except Exception as e:
                print("NAV failed: %s" % e)
                self.navNext = time.time() + 30
            finally:
                self.navBusy = False

    #  Play stays on from game to game: back on the map's info screen it picks the difficulty
    #  again, and the next game checks Auto Start (off while placing) and Drop & Lock afresh
    def next_game(self):
        if not self.autoplay:
            return
        self.autoStage = "place"
        self.autoNext = 0
        self.autoAway = 0
        self.autoInfoWaits = 0
        self.autoStartChecked = False
        print("PLAY next game on %s" % (self.mapTitle or "this map"))

    #  a game ending holds Play back while end_step (its own thread) clicks through
    def end_frame(self, ref):
        if self.endSeq is not None:
            self.autoStage = "end"
            return True
        screen, at = self.end_screen(ref)
        return screen in ("level_complete", "defeat")

    #  the WISH ORB (k/N) count over the orb being opened: (k, N), or None
    #
    def wish_orbs(self, ref):
        w = cv.copyMakeBorder(self.white_letters(ref[62:98, 420:760]), 12, 12, 12, 12, cv.BORDER_CONSTANT, value=0)
        t = pytesseract.image_to_string(255 - w, config="--psm 7 -c tessedit_char_whitelist=0123456789/()WISHORB ")
        m = re.search(r"(\d+)\s*/\s*(\d+)", t)
        return (int(m[1]), int(m[2])) if m and 0 < int(m[1]) <= int(m[2]) else None

    #  after a game, back to the map's info screen the way it's done by hand (recordings/
    #  game_1016_1648), on its own thread whether Play is on or not, one step a look:
    #     Level Complete, and the rewards after it (coins, wish orb, XP): a tap anywhere
    #     Home on the rewards (where it sits, 50+ px either way), Shard and Get (lower left)
    #     once a look while it shows, Home on "no more wish orbs", Home on Defeat
    #     the map's play button on its chapter screen (replay/chapter_<map>.png)
    #  It's over on the map's info screen, or after END_GIVE_UP s (Navigate can take it from
    #  there)
    #
    CHAPTER_PLAY = (156, 20)        # the play button from the chapter thumbnail's corner
    END_GIVE_UP = 240

    def end_worker(self):
        while True:
            time.sleep(1)
            ref = self.lastRef
            if ref is None or self.unlocking or time.time() - self.lastRefTime > 3:
                continue
            try:
                if self.end_step(ref):
                    time.sleep(0.8)
            except Exception as e:
                print("END step failed: %s" % e)

    def end_step(self, ref):
        now = time.time()
        seq = self.endSeq
        #  "Choose your save!" (at start, when another device saved to the cloud since):
        #  always Use Cloud Save (recordings/cloud_save)
        if self.cloudKey is None:
            self.cloudKey = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure",
                                                   "replay", "cloud_save.png"))
        _, v, _, loc = cv.minMaxLoc(cv.matchTemplate(ref, self.cloudKey, cv.TM_CCOEFF_NORMED))
        if v > 0.8:
            print("SAVE choose your save: Use Cloud Save")
            self.adb_tap(loc[0] + self.cloudKey.shape[1] // 2, loc[1] + self.cloudKey.shape[0] // 2)
            return True
        #  "Rank up!" (the account levelled, on the way back from a game): Continue
        if self.rankKey is None:
            self.rankKey = cv.imread(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure",
                                                  "replay", "rank_up_continue.png"))
        _, v, _, loc = cv.minMaxLoc(cv.matchTemplate(ref, self.rankKey, cv.TM_CCOEFF_NORMED))
        if v > 0.85:
            print("END rank up, Continue")
            self.adb_tap(loc[0] + self.rankKey.shape[1] // 2, loc[1] + self.rankKey.shape[0] // 2)
            return True
        screen, at = self.end_screen(ref)
        if screen == "level_complete":
            if seq is None or seq["home"]:
                print("END level complete")
                self.endSeq = {"start": now, "home": False, "orbs": None}
            self.adb_tap(585, 270)
            return True
        if screen == "defeat":
            if seq is None:
                print("END defeat, Home")
            self.endSeq = {"start": now, "home": True, "orbs": None}
            self.adb_tap(*self.END_HOME["defeat"])
            return True
        if screen == "home":
            print("END rewards, Home")
            self.endSeq = dict(seq or {"start": now, "orbs": None}, home=True)
            self.adb_tap(*at)
            return True
        if screen == "shard_and_get":
            orbs = self.wish_orbs(ref)
            if seq is None:
                self.endSeq = seq = {"start": now, "home": True, "orbs": None}
            if orbs and orbs != seq.get("orbs"):
                print("END wish orb %d/%d: Shard and Get" % orbs)
                seq["orbs"] = orbs
            self.adb_tap(*at)
            return True
        if screen == "no_more_orbs":
            print("END no more wish orbs, Home")
            self.adb_tap(*self.END_HOME["no_more_orbs"])
            if seq is not None:
                seq["home"] = True
            return True
        if seq is None:
            return False
        if self.map_info_screen(ref):
            self.endSeq = None
            print("END back on %s" % (self.mapTitle or "the map screen"))
            self.next_game()
            return False
        cp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay",
                          "chapter_%s.png" % self.mapName) if self.mapName else None
        chapter = cv.imread(cp) if cp and os.path.exists(cp) else None
        if chapter is not None:
            _, v, _, loc = cv.minMaxLoc(cv.matchTemplate(ref, chapter, cv.TM_CCOEFF_NORMED))
            if v > 0.8:
                print("END chapter screen, playing %s" % self.mapTitle)
                self.adb_tap(loc[0] + self.CHAPTER_PLAY[0], loc[1] + self.CHAPTER_PLAY[1])
                return True
        if now - seq["start"] > self.END_GIVE_UP:
            print("END nothing known on screen for a while, leaving it")
            self.endSeq = None
            self.stop_autoplay("finished, end screens not all recognised")
            return False
        if not seq["home"] and not self.hudVisible:
            self.adb_tap(585, 270)
            return True
        return False

    #  HUD boxes move sideways when side panels open; find this one by its icon/label
    #  along the top strip, then take the navy box to the right of it
    #  returns the box crop, or None when the in-game HUD isn't showing (menus score <0.4)
    #
    def locate_hud(self, ref, h):
        key = h.get("keyImg")
        if key is None or not h["box"]:
            return None
        kh, kw = key.shape[:2]
        bh = h["box"][3]
        strip = ref[0:min(ref.shape[0], h["box"][1] + bh + 30)]
        res = cv.matchTemplate(strip, key, cv.TM_CCOEFF_NORMED)
        _minVal, maxVal, _minLoc, (x, y) = cv.minMaxLoc(res)
        if maxVal < 0.8:
            return None
        #  walk right from the icon while the middle row stays navy or white text
        row = min(ref.shape[0] - 1, y + bh // 2)
        line = ref[row:row + 1]
        m = (cv.inRange(line, (60, 10, 0), (150, 70, 40)) | cv.inRange(line, (170, 170, 170), (255, 255, 255)))[0]
        xe = x + kw
        last = xe
        gap = 0
        while xe < ref.shape[1] - 1 and gap < 6:
            xe += 1
            if m[xe]:
                gap = 0
                last = xe
            else:
                gap += 1
        return ref[y:y + bh, x:last + 1]

    #  print lives/money/round when one changes; only re-OCR a box whose pixels changed
    #
    #  the title in the green banner at the top of the area select and map info screens,
    #  e.g. "Apple Thief" (area) or "Tree Trunks' House" (map); None if unreadable.
    #  The font is stylised but tesseract reads it once only the white letters are kept,
    #  except its E, which comes back as a euro sign
    #
    TITLE_BOX = (380, 28, 460, 50)

    MAP_WORDS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "map_words.txt")
    MAP_NAMES = {n.lower(): n for n in open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                         "bloons_adventure", "map_names.txt")).read().split("\n") if n}

    def read_banner_title(self, ref):
        x, y, w, h = self.TITLE_BOX
        crop = ref[y:y + h, x:x + w]
        hsv = cv.cvtColor(crop, cv.COLOR_BGR2HSV)
        letters = ((hsv[..., 1] < 60) & (hsv[..., 2] > 200)).astype(np.uint8) * 255
        #  without the margin tesseract drops the apostrophe in Tree Trunks' House
        img = cv.copyMakeBorder(letters, 20, 20, 20, 20, cv.BORDER_CONSTANT, value=0)
        tconf = "--oem 3 --psm 7 --user-words %s -c tessedit_char_whitelist=\"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-_.\ \"" % self.MAP_WORDS
        raw = pytesseract.image_to_string(img, config=tconf)
        text = re.sub(r"[^a-z' ]", "", raw.lower().replace("€", "e").replace("’", "'")).strip()
        text = re.sub(r"\s+", " ", text)
        title = None
        if len(text.replace(" ", "")) >= 3:
            #  the LSTM engine mostly ignores --user-words, so snap to the nearest real map
            match = difflib.get_close_matches(text, self.MAP_NAMES, 1, 0.6)
            title = self.MAP_NAMES[match[0]] if match else None
        self.dump_title_steps(ref, crop, hsv, letters, img, raw, title)
        return title

    #  every step read_banner_title hands on towards tesseract, as images in
    #  title_ocr/<time>/ (1_frame .. 6_tesseract_input) plus what came back in text.txt;
    #  only when the strip differs from the last one saved
    #
    def dump_title_steps(self, ref, crop, hsv, letters, img, raw, title):
        if self.titleDumpLast is not None and cv.absdiff(crop, self.titleDumpLast).max() < 40:
            return
        self.titleDumpLast = crop.copy()
        d = os.path.join(self.titleDumpDir, datetime.now().strftime("%Y%m%d_%H%M%S_%f")[:-3])
        os.makedirs(d, exist_ok=True)
        x, y, w, h = self.TITLE_BOX
        frame = ref.copy()
        cv.rectangle(frame, (x, y), (x + w, y + h), (0, 0, 255), 1)
        steps = [("1_frame_with_box", frame), ("2_crop", crop),
                 ("3_saturation", hsv[..., 1]), ("4_value", hsv[..., 2]),
                 ("5_white_letters_s_lt_60_v_gt_200", letters),
                 ("6_tesseract_input_bordered", img)]
        for name, im in steps:
            cv.imwrite(os.path.join(d, name + ".png"), im)
        with open(os.path.join(d, "text.txt"), "w") as f:
            f.write("tesseract --psm 7: %r\ntitle: %r\n" % (raw, title))
        print("TITLE ocr %r -> %r, steps in %s" % (raw.strip(), title, d))

    #  the map info screen (difficulty buttons under a map's title), not the area select.
    #  Keyed on "Difficulty:" and its first skull: the buttons get covered by the beacon's
    #  chests, and the label's colon and skulls pop in last, after the title has settled
    #
    def map_info_screen(self, ref):
        if self.mapInfoKey is None:
            return False
        area = ref[240:300, 298:520]
        return cv.minMaxLoc(cv.matchTemplate(area, self.mapInfoKey, cv.TM_CCOEFF_NORMED))[1] > 0.8

    #  the map's name if the map info screen is showing, else None
    #
    def read_map_title(self, ref):
        if not self.map_info_screen(ref):
            return None
        return self.read_banner_title(ref)

    #  "Tree Trunks' House" -> "tree_trunks_house", the name its path is stored under
    #
    @staticmethod
    def map_key(title):
        return re.sub(r"[^a-z]+", "_", title.lower().replace("'", "")).strip("_")

    #  the map about to be played; loads its stored path if it has one
    #
    def set_map(self, title):
        key = self.map_key(title)
        if key == self.mapName:
            return
        self.mapTitle = title
        self.mapName = key
        self.path = path_lib.load_path(key)
        script = os.path.join(path_lib.map_dir(key), "script.json")
        self.script = None
        if os.path.exists(script):
            with open(script) as f:
                sc = json.load(f)
            self.script = sc["steps"]
            self.scriptStartMoney = sc.get("start_money")
            self.scriptDropAndLock = sc.get("drop_and_lock")
            for s in self.script:
                if "card" in s:
                    s["cardKey"] = (cv.imread(os.path.join(path_lib.map_dir(key), s["card"]), cv.IMREAD_GRAYSCALE),
                                    tuple(s["card_off"]))
        self.pathQueue = None
        self.pathRetry = True
        self.placedThisGame = []
        self.map_changed.emit(title)
        print("MAP %s (%s%s)" % (title, "path known" if self.path else "path not learned yet",
              ", %d step game script" % len(self.script) if self.script else ""))

    #  once a second, out of a game: if the map info screen is up, take the map from its title
    #
    def map_title_frame(self, ref):
        now = self.clock()
        if now < self.titleNext:
            return
        self.titleNext = now + 1
        if not self.map_info_screen(ref):
            return
        x, y, w, h = self.TITLE_BOX
        strip = ref[y:y + h, x:x + w]
        if self.titleSeen is not None and cv.absdiff(strip, self.titleSeen).max() < 40:
            return
        #  the banner slides in: a title only counts once two reads a second apart agree
        title = self.read_banner_title(ref)
        if title and title == self.titleCandidate:
            self.titleSeen = strip.copy()
            self.set_map(title)
        self.titleCandidate = title

    #  start learning the current map's path from the arrow intro: frames are handed to
    #  bloons_path.learn_path on a worker until it has seen the arrows run, then the path
    #  is stored under the map's name (only used for this game if the map isn't known).
    #  Call it before pressing play on round 1; False if the path is already known or
    #  it's already learning
    #
    def learn_path(self):
        if self.path is not None or self.pathQueue is not None:
            return False
        print("PATH learning arrow path on %s" % (self.mapTitle or "an unknown map"))
        self.pathQueue = queue.Queue(maxsize=600)
        threading.Thread(target=self.path_worker, args=(self.pathQueue, self.mapName), daemon=True).start()
        return True

    #  feed learn_path; starts it by itself when a game is on round 1 and the path isn't known
    #
    def path_frame(self, ref):
        if not self.hudVisible:
            #  the last round read sticks after a game ends; only learn in a game.  Lost on
            #  round 1, the round still reads 1/ next game: try again then
            self.pathRetry = True
            if self.pathQueue is not None:
                try:
                    self.pathQueue.put_nowait(None)
                except queue.Full:
                    pass
            return
        if self.pathQueue is None:
            if not str(self.hudLast.get("round", "")).startswith("1/"):
                self.pathRetry = True
                return
            if not self.pathRetry or not self.learn_path():
                return
        try:
            self.pathQueue.put_nowait(ref.copy())
        except queue.Full:
            pass

    def path_worker(self, q, name):
        #  None in the queue: the game went away mid-learn
        path = path_lib.learn_path((q.get() for _ in iter(int, 1)), name)
        if name != self.mapName:
            return
        if path is None:
            print("PATH no arrows seen; will try again next game")
            self.pathRetry = False
            self.pathQueue = None
            return
        self.path = path
        self.pathQueue = None
        print("PATH %s learned: %d points, %d spots, %s" % (
            name or "map", len(path["points"]), len(path["spots"]),
            "saved in %s" % path_lib.map_dir(name) if name else "not saved, the map's name isn't known"))

    def hud_frame(self, ref):
        now = self.clock()
        if now < self.hudNext:
            return
        self.hudNext = now + 0.5
        changed = []
        self.hudVisible = False
        for h in self.replay["hud"]:
            roi = self.locate_hud(ref, h)
            if roi is None:
                continue
            self.hudVisible = True
            glyph = cv.threshold(cv.cvtColor(roi, cv.COLOR_BGR2GRAY), 170, 255, cv.THRESH_BINARY)[1]
            prev = self.hudSeen.get(h["name"])
            if prev is not None and prev.shape == glyph.shape and cv.countNonZero(cv.absdiff(prev, glyph)) < 4:
                continue
            self.hudSeen[h["name"]] = glyph
            val = self.read_hud(h["name"], roi)
            if h["name"] == "round" and val is not None and not re.fullmatch(r"\d+/\d+", str(val)):
                #  a misread ("3" in round 38) would look like a new game
                val = None
            if val is not None and val != self.hudLast.get(h["name"]):
                prevRound = self.hudLast.get("round")
                if h["name"] == "money":
                    self.track_money(self.hudLast.get("money"), val)
                self.hudLast[h["name"]] = val
                changed.append(h["name"])
                if h["name"] == "round" and prevRound and int(val.split("/")[0]) < int(prevRound.split("/")[0]):
                    #  round went backwards: a new game, so the drop to its starting cash wasn't spending
                    self.hudSpent = 0
                    self.hudGained = 0
                    self.placedThisGame = []
                    print("HUD new game, spent reset")
        if not self.hudVisible and self.mapName is None and self.pathQueue is None:
            #  a path learned on a map whose name wasn't read was only for that game
            self.path = None
        if "round" in changed:
            #  one line per round: gained is what the round that just ended brought in
            self.print_hud()
            if self.hudShots:
                self.save_hud_frame(ref)
            self.hudGained = 0

    #  with --hud-shots, every HUD console line saves the frame it was read from, values in the
    #  filename, so a misread can be checked against what was on screen
    #
    def save_hud_frame(self, ref):
        if self.hudDir is None:
            self.hudDir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "hud")
            os.makedirs(self.hudDir, exist_ok=True)
            n = 0
            for name in os.listdir(self.hudDir):
                m = re.match(r"hud_(\d+)_", name)
                if m:
                    n = max(n, int(m.group(1)))
            self.hudCount = n + 1
        money = self.hudLast.get("money")
        total = None if money is None else money + self.hudSpent
        name = "hud_%04d_lives%s_money%s_spent%s_total%s_gained%s_round%s.png" % (self.hudCount,
               self.hudLast.get("lives"), money, self.hudSpent, total, self.hudGained,
               str(self.hudLast.get("round")).replace("/", "of"))
        cv.imwrite(os.path.join(self.hudDir, name), ref, [cv.IMWRITE_PNG_COMPRESSION, 1])
        self.hudCount += 1

    #  money going down is spending; total is everything earned so far (cash on hand + spent)
    #
    #  money going down is spending, going up is gained this round
    #
    def track_money(self, prev, val):
        if prev is not None and val < prev:
            self.hudSpent += prev - val
        elif prev is not None and val > prev:
            self.hudGained += val - prev

    #  the header again once half a terminal's worth of lines has gone by since it last showed
    def print_hud(self):
        if not self.hudHeader or LineCounter.lines - self.hudHeaderAt >= LineCounter.every:
            print("HUD %5s %10s %10s %10s %10s %7s" % ("lives", "money", "spent", "total", "gained", "round"))
            self.hudHeader = True
            self.hudHeaderAt = LineCounter.lines
        money = self.hudLast.get("money")
        total = None if money is None else money + self.hudSpent

        def cash(v):
            return "-" if v is None else "${:,}".format(v)
        row = {"lives": str(self.hudLast.get("lives") if self.hudLast.get("lives") is not None else "-"),
               "money": cash(money), "spent": cash(self.hudSpent), "total": cash(total),
               "gained": cash(self.hudGained), "round": str(self.hudLast.get("round") or "-")}
        print("HUD %5s %10s %10s %10s %10s %7s" % (row["lives"], row["money"], row["spent"], row["total"],
              row["gained"], row["round"]))
        self.hud_changed.emit(row)

    #  the account bar's values; a value only counts once it reads with its commas in the
    #  right places (misreads turn a comma into a digit, or add one) and two reads a second
    #  apart agree.  A missed comma in a 4 digit number is let through
    #
    MENU_BOXES = {"level": (170, 206), "exp": (214, 360), "gold": (404, 562), "gems": (640, 792), "shards": (858, 1016)}
    MENU_NUM = r"(\d{1,4}|\d{1,3}(,\d{3})+)"

    def read_menu_hud(self, ref):
        vals = {}
        for name, (x0, x1) in self.MENU_BOXES.items():
            hsv = cv.cvtColor(ref[18:48, x0:x1], cv.COLOR_BGR2HSV)
            letters = ((hsv[..., 1] < 60) & (hsv[..., 2] > 200)).astype(np.uint8) * 255
            #  clouds behind the bar and the shard icon's white tip poke in at the edges
            n, lab, st, _ = cv.connectedComponentsWithStats(letters)
            for i in range(1, n):
                x, y, w, h, _ = st[i]
                if x == 0 or y == 0 or y + h >= letters.shape[0]:
                    letters[lab == i] = 0
            if name in ("level", "gems"):
                #  at 1x the 8 of 86 gems reads 3 and level 61's 1 goes missing; 3x reads both
                #  (the commas of the longer numbers turn into 2s scaled, so only these)
                letters = cv.resize(letters, None, fx=3, fy=3, interpolation=cv.INTER_CUBIC)
            img = cv.copyMakeBorder(letters, 20, 20, 20, 20, cv.BORDER_CONSTANT, value=0)
            text = pytesseract.image_to_string(255 - img, config="--psm 7 -c tessedit_char_whitelist=0123456789,/").strip()
            pattern = self.MENU_NUM + "/" + self.MENU_NUM if name == "exp" else self.MENU_NUM
            if re.fullmatch(pattern, text):
                vals[name] = text
        return vals

    def menu_frame(self, ref):
        now = self.clock()
        if now < self.menuNext or self.menuKey is None:
            return
        self.menuNext = now + 1
        if cv.minMaxLoc(cv.matchTemplate(ref[0:70, 330:460], self.menuKey, cv.TM_CCOEFF_NORMED))[1] < 0.75:
            self.menuCandidate = {}
            return
        vals = self.read_menu_hud(ref)
        #  a digit can flip between reads of the same frame (gems 86 / 36, level 61 / 6):
        #  a value counts once three reads in a row agree
        seen = self.menuCandidate
        agreed = {k: v for k, v in vals.items() if seen.get(k, (None, 0))[0] == v and seen[k][1] >= 2}
        self.menuCandidate = {k: (v, seen[k][1] + 1 if seen.get(k, (None, 0))[0] == v else 1) for k, v in vals.items()}
        changed = False
        for k, v in agreed.items():
            if k == "exp":
                have, need = (int(x.replace(",", "")) for x in v.split("/"))
                v = {"exp": have, "exp_need": need}
            else:
                v = {k: int(v.replace(",", ""))}
            for kk, vv in v.items():
                if kk == "level" and self.menu.get("level") and vv < self.menu["level"]:
                    #  levels only go up: "6" is 61 with its 1 missed
                    continue
                if self.menu.get(kk) != vv:
                    self.menu[kk] = vv
                    changed = True
        if not changed:
            return
        self.stats["menu"].update(self.menu)
        self.settle_menu_gains()
        self.save_stats()
        m = self.menu
        print("MENU level %s, exp %s/%s (%s to next), gold %s, gems %s, shards %s" % (
              m.get("level"), m.get("exp"), m.get("exp_need"),
              m["exp_need"] - m["exp"] if "exp" in m and "exp_need" in m else None,
              m.get("gold"), m.get("gems"), m.get("shards")))
        self.currencies_changed.emit({k: m.get(k) for k in self.MENU_KEYS + ("level", "exp", "exp_need")})
        self.stats_changed.emit(self.stats_parts())

    #  what a game brought in: the account bar read before it against the first full read
    #  after it.  More than a game can give is a misread and isn't counted
    #
    MENU_KEYS = ("gold", "gems", "shards")
    GAME_MAX = {"gold": 5000, "gems": 50, "shards": 3000}

    def settle_menu_gains(self):
        before = self.menuBefore
        if before is None or self.game is not None or not all(k in self.menu for k in self.MENU_KEYS):
            return
        self.menuBefore = None
        gains = {k: self.menu[k] - before[k] for k in self.MENU_KEYS}
        if any(not 0 <= v <= self.GAME_MAX[k] for k, v in gains.items()):
            print("MENU change since the game doesn't look like a game's rewards, not counted: %s" % gains)
            return
        for k, v in gains.items():
            self.stats["gained"][k] += v
        if self.stats["games"]:
            self.stats["games"][-1].update(gains)
        print("MENU the last game brought gold +%d, gems +%d, shards +%d" % (gains["gold"], gains["gems"], gains["shards"]))
        self.stats_changed.emit(self.stats_parts())

    #  a game runs from round 1 showing on the HUD until the HUD has been gone 5 s (the
    #  upgrade panel hiding it doesn't count).  The round's number ticks up when it starts,
    #  so a round's time runs to the next tick, the last one's to when the HUD went away
    #
    def stats_frame(self, ref):
        now = self.clock()
        if now < self.statsNext:
            return
        self.statsNext = now + 1
        t = time.time()
        rnd = self.hudLast.get("round")
        g = self.game
        if self.hudVisible and rnd:
            n = int(rnd.split("/")[0])
            money = self.hudLast.get("money")
            if g is None or n < g["round"]:
                if g is not None:
                    self.end_game()
                if n != 1:
                    return
                if all(k in self.menu for k in self.MENU_KEYS):
                    self.menuBefore = {k: self.menu[k] for k in self.MENU_KEYS}
                g = self.game = {"map": self.mapTitle, "start": t, "seen": t, "round": 1, "roundStart": t,
                                 "roundTimes": [], "base": None, "money": 0, "away": 0,
                                 "autoplay": self.autoplay}
            elif n > g["round"]:
                g["roundTimes"].append(t - g["roundStart"])
                g["round"] = n
                g["roundStart"] = t
            g["seen"] = t
            g["away"] = 0
            g["of"] = int(rnd.split("/")[1]) if "/" in rnd and rnd.split("/")[1].isdigit() else None
            g["lives"] = self.hudLast.get("lives")
            if money is not None:
                if g["base"] is None:
                    g["base"] = money + self.hudSpent
                g["money"] = money + self.hudSpent - g["base"]
            return
        if g is None or (self.sellKey is not None and upgrade_lib.panel_open(ref, self.sellKey)):
            return
        g["away"] += 1
        if g["away"] >= 5:
            self.end_game()

    def end_game(self):
        g = self.game
        self.game = None
        g["roundTimes"].append(g["seen"] - g["roundStart"])
        lives = g.get("lives")
        if g.get("won"):
            result = "win"
        elif g.get("lost") or (lives is not None and int(lives) < 1):
            result = "loss"
        elif g.get("of") and g["round"] >= g["of"]:
            result = "win"
        else:
            #  Impoppable has one life: gone before the last round without a lives read is a leak
            result = "loss" if lives is None else "quit"
        entry = {"map": g["map"], "start": datetime.fromtimestamp(g["start"]).isoformat(timespec="seconds"),
                 "seconds": round(g["seen"] - g["start"], 1), "rounds": g["round"],
                 "round_seconds": [round(x, 1) for x in g["roundTimes"]], "money": g["money"],
                 "result": result, "autoplay": g["autoplay"]}
        self.stats["games"].append(entry)
        self.save_stats()
        if not self.script:
            self.plan_save(result)
        print("STATS %s on %s: round %d in %s, $%s earned" % (result, g["map"] or "an unknown map", g["round"],
              timedelta(seconds=round(entry["seconds"])), format(g["money"], ",")))
        summary = self.stats_summary()
        print("STATS %s" % summary)
        self.stats_changed.emit(self.stats_parts())

    def reset_stats(self):
        if os.path.exists(self.statsPath):
            shutil.copy(self.statsPath, self.statsPath.replace("stats.json", "stats_%s.json" % datetime.now().strftime("%Y%m%d_%H%M%S")))
        self.stats["games"] = []
        self.stats["gained"] = {"gold": 0, "gems": 0, "shards": 0}
        self.save_stats()
        self.stats_changed.emit(self.stats_parts())
        print("STATS reset")

    def save_stats(self):
        with open(self.statsPath + ".tmp", "w") as f:
            json.dump(self.stats, f, indent=1)
        os.replace(self.statsPath + ".tmp", self.statsPath)

    #  the Auto Game frame's lines: Stats, Time, Money, Result
    def stats_parts(self):
        games = self.stats["games"]
        res = [x["result"] for x in games]
        rounds = [r for x in games for r in x["round_seconds"]]
        avg_game = timedelta(seconds=round(sum(x["seconds"] for x in games) / len(games))) if games else "-"
        avg_round = "%.1fs" % (sum(rounds) / len(rounds)) if rounds else "-"
        g = self.stats["gained"]
        last = games[-1] if games else None
        if last:
            got = ", ".join("%s +%s" % (k, format(last[k], ",")) for k in self.MENU_KEYS if k in last)
            result = "%s on %s, round %d%s" % (last["result"], last.get("map") or "?", last.get("rounds", 0),
                                               " (%s)" % got if got else "")
        else:
            result = "-"
        return {"stats": "%d games: %d won, %d lost, %d quit" % (len(games), res.count("win"), res.count("loss"), res.count("quit")),
                "time": "avg game %s, avg round %s" % (avg_game, avg_round),
                "money": "$%s in games; gained gold +%s, gems +%s, shards +%s" % (
                    format(sum(x["money"] for x in games), ","), format(g["gold"], ","), format(g["gems"], ","), format(g["shards"], ",")),
                "result": result}

    def stats_summary(self):
        games = self.stats["games"]
        res = [x["result"] for x in games]
        rounds = [r for x in games for r in x["round_seconds"]]
        gained = self.stats["gained"]
        avg_game = timedelta(seconds=round(sum(x["seconds"] for x in games) / len(games))) if games else "-"
        avg_round = "%.1fs" % (sum(rounds) / len(rounds)) if rounds else "-"
        return ("%d games: %d won, %d lost, %d quit | avg game %s, avg round %s | money $%s | "
                "gold +%s, gems +%s, shards +%s" % (
                len(games), res.count("win"), res.count("loss"), res.count("quit"), avg_game, avg_round,
                format(sum(x["money"] for x in games), ","),
                format(gained["gold"], ","), format(gained["gems"], ","), format(gained["shards"], ",")))

    #  white glyphs of a HUD box left to right, each cut out and resized to the
    #  library's size; the ':' and ',' are too short to count.  Same rules as
    #  bloons_build_glyphs.py, which builds the library from these
    #
    def hud_glyphs(self, roi, name):
        if name in ("lives", "money"):
            #  round icon on the left, about as wide as the box is tall
            roi = roi[:, roi.shape[0]:]
        w = cv.threshold(cv.cvtColor(roi, cv.COLOR_BGR2GRAY), 170, 255, cv.THRESH_BINARY)[1]
        n, lab, st, _ = cv.connectedComponentsWithStats(w, 8)
        hh = w.shape[0]
        #  a light map behind the HUD (Supermonkey Villa's fence) shows past the box's round
        #  right end as a white sliver on the crop's edge: not a glyph
        tall = sorted([i for i in range(1, n) if st[i][3] >= 0.3 * hh and st[i][4] >= 8
                       and st[i][0] + st[i][2] < w.shape[1] - 1], key=lambda i: st[i][0])
        out = []
        for i in tall:
            X, Y, W, Hh, _A = st[i]
            g = (lab[Y:Y + Hh, X:X + W] == i).astype(np.uint8) * 255
            out.append(cv.resize(g, self.glyphSize, interpolation=cv.INTER_AREA).astype(np.float32))
        return out

    #  the HUD font never changes: match each glyph against labelled samples of it
    #  rather than OCR, which kept misreading digits beside commas.  A glyph that
    #  matches nothing well enough fails the read, to be retried on a later frame
    #
    def read_hud(self, name, roi):
        if self.glyphLib is None:
            return None
        text = ""
        for g in self.hud_glyphs(roi, name):
            scores = [float(cv.matchTemplate(g, s, cv.TM_CCOEFF_NORMED)[0][0]) for s in self.glyphLib]
            best = int(np.argmax(scores))
            if scores[best] < 0.7:
                return None
            text += self.glyphChars[best]
        if name == "round":
            #  "ROUND62/75" on adventure maps, "ROUND13" on endless maps
            m = re.fullmatch(r"ROUND(\d+)(?:/(\d+))?", text)
            if not m:
                return None
            if m.group(2):
                if int(m.group(1)) > int(m.group(2)):
                    return None
                return "%d/%d" % (int(m.group(1)), int(m.group(2)))
            return m.group(1)
        if name == "money":
            m = re.fullmatch(r"\$(\d+)", text)
        else:
            m = re.fullmatch(r"(\d+)", text)
        return int(m.group(1)) if m else None

    def angle_cos(self,p0, p1, p2):
        d1, d2 = (p0-p1).astype('float'), (p2-p1).astype('float')
        return abs( np.dot(d1, d2) / np.sqrt( np.dot(d1, d1)*np.dot(d2, d2) ) )

    def tess(self, img,whitelist=""):
        words = []
        chars= "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-_."
        if len(whitelist) > 0:
            chars = whitelist
        tconf = "--oem 3 --psm 8 "+ \
            "-c tessedit_char_whitelist=\"%s\"" % chars
        
        try:
            text = pytesseract.image_to_data(img, config=tconf, output_type='data.frame')
            text = text[text.conf != -1]
            print(text)
#                                    print()
            try:
                #level,page_num,block_num,par_num,line_num,word_num,left,top,width,height,conf,text        
                lines = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['text'].apply(lambda x: x.values.tolist()).tolist()
                confs = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['conf'].mean().tolist()
            
                tl = []
                tc = []
                for i in range(len(lines[0])):
                    if str(lines[0][i]).strip():
                        tl.append(str(lines[0][i]))

                line = " ".join(tl)  #more likely multiple words, but still can be single word
#                        print(line)

                conf = 0
                if (np.any(confs)):
                    conf = round(np.mean(confs),2)
                    print(conf)
                if (conf >= 10):
                    words.append(line)

            except BaseException as err:
                print(f"Unexpected {err=}, {type(err)=}")
                print(text)
        except BaseException as err:
            print(f"Unexpected {err=}, {type(err)=}")

        return words

    #  returns cb []
    #      center coords of bounding box which fast_east algo returns
    #  words []
    #    the words tesseract read inside that box with a 50% confidence or above
    
    def fast_east_tess(self, image):
        cb = []
        words = []
        boxes = self.fast_east(image)

        boxc = 0
        for box in sorted(boxes, key=lambda x: x[0]):
            boxc += 1
           
            (x, y, x2, y2) = box
#                x, y, w, h = unscaled
                #crop
 #               cardimage=orig[y: y + h, x : x + w]
            print("x[%d] y[%d] x2[%d] y2[%d]" % (x,y,x2,y2))
            img = image[y:y2,x:x2]

#            if (img is None):
#                print("Empty!")
#            print(box, boxc,"cards/%d_%d_%d_%d.title.%d.png" % (tile[0], tile[1], tile[2], tile[3], boxc))
#            print(type(img))
            
            # draw the bounding box on the image
#            cv.rectangle(im2, (x, y), (x2, y2), (0, 255, 0, 1))

            tconf = "--oem 3 --psm 7 "+ \
                "-c tessedit_char_whitelist=\"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-_.\ \""
            
            try:
                text = pytesseract.image_to_data(img, config=tconf, output_type='data.frame')
                text = text[text.conf != -1]
#                                    print()
                print(text)
                try:
                    #level,page_num,block_num,par_num,line_num,word_num,left,top,width,height,conf,text        
                    lines = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['text'].apply(lambda x: x.values.tolist()).tolist()
                    confs = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['conf'].mean().tolist()
                
                    tl = []
                    tc = []
                    for i in range(len(lines[0])):
                        if str(lines[0][i]).strip():
                            tl.append(str(lines[0][i]))

                    line = " ".join(tl)  #more likely multiple words, but still can be single word
#                        print(line)

                    conf = 0
                    if (np.any(confs)):
                        conf = round(np.mean(confs),2)
#                        print(conf)
                    if (conf > 50):
                        words.append(line)
                        cb.append((x+(x2-x)/2,y+(y2-y)/2))

                except BaseException as err:
                    print(f"Unexpected {err=}, {type(err)=}")
                    print(text)
            except BaseException as err:
                print(f"Unexpected {err=}, {type(err)=}")
        return (cb, words)
#        return (cb, words)

    def find_mobs(self, img):
        # denoise before edge detection
        #blur = cv.GaussianBlur(img,(5,5),0)

        #  normalize color histogram for greater contrast
        #
        clahe = cv.createCLAHE(clipLimit=2.0, tileGridSize=(8,8))
        contrast = clahe.apply(img)

        median_pix = np.median(img)
#        self.cannyLower = int(max(0 ,0.7*median_pix))
#        self.canny_lower_signal.emit(self.cannyLower)

#        self.cannyUpper = int(min(255,1.3*median_pix))
#        self.canny_upper_signal.emit(self.cannyUpper)

#        print(median_pix, self.cannyLower, self.cannyUpper)

        edge = cv.Canny(contrast, self.cannyLower, self.cannyUpper)#, apertureSize=5)

        contours, hierarchy = cv.findContours(edge, 
            cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

        mobs=[]
        for cnt in contours:
            (x,y,w,h)=cv.boundingRect(cnt)
            if y < 160 and x < 55:
                continue
            if y > 450 and x < 150:
                continue
            if x > 800 and y > 445:
                continue

            area = w * h
            if area > 200 and area < 500:
                mobs.append((x,y,w,h))
            if area > 900 and area < 1600:
                mobs.append((x,y,w,h))

        npcenter = np.array((490,310)) # spell menu x button location with 9 spells
#        dist = int(np.linalg.norm(npa - npb))
        mobs.sort(key = lambda e: int(np.linalg.norm(np.array((e[0],e[1])) - npcenter))) 
        return mobs

    def find_squares(self, img, thresh=None):
        if thresh is None:
            # denoise before edge detection
            blur = cv.GaussianBlur(img,(5,5),0)

            #  normalize color histogram for greater contrast
            #
            clahe = cv.createCLAHE(clipLimit=2.0, tileGridSize=(8,8))
            contrast = clahe.apply(img)

            median_pix = np.median(img)
            if (self.cannyLower is None):
                self.cannyLower = int(max(0 ,0.7*median_pix))
                self.canny_lower_signal.emit(self.cannyLower)

            if (self.cannyUpper is None):
                self.cannyUpper = int(min(255,1.3*median_pix))
                self.canny_upper_signal.emit(self.cannyUpper)

    #        print(median_pix, self.cannyLower, self.cannyUpper)

            edge = cv.Canny(contrast, self.cannyLower, self.cannyUpper)#, apertureSize=5)
        else:
            edge = thresh

        if (self.image_options == "Edge C"):
            im3 = img.copy()
            contours, hierarchy = cv.findContours(edge, 
                cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

            for i in range(len(contours)):
                cv.drawContours(im3, contours, i, (255, 0, 0), \
                                1, cv.LINE_8, hierarchy, 0)
            self.change_pixmap_signal.emit(im3)

        # dilate canny output to remove potential
        # holes between edge segments
        rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (1, 8))
#               edge = cv.erode(edge, rect_kernel, iterations=1)
        edge = cv.dilate(edge, rect_kernel, iterations=1)
        rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (8, 1))
#               edge = cv.erode(edge, rect_kernel, iterations=1)
        edge = cv.dilate(edge, rect_kernel, iterations=1)

        #im2 = np.uint8(im2/2.)
        #im2[edge != 0] = (0,255,0)
        contours, hierarchy = cv.findContours(edge, 
            cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

        if (self.image_options == "Sq Edge"):
            self.change_pixmap_signal.emit(edge)
        elif (self.image_options == "Sq Edge Contours"):
            im3 = img.copy()
            for i in range(len(contours)):
                cv.drawContours(im3, contours, i, (255, 0, 0), \
                                2, cv.LINE_8, hierarchy, 0)
            self.change_pixmap_signal.emit(im3)

        rect=[]
        for cnt in contours:
            approx = cv.approxPolyDP(cnt,0.02*cv.arcLength(cnt,True),True)
            if (len(approx)==4 and abs(cv.contourArea(cnt)) > (self.tileW * self.tileH)):
                #and abs(cv.contourArea(cnt)) <  ):
#                        print(abs(cv.contourArea(cnt)))
                cnt = approx.reshape(-1, 2)
                max_cos = np.max([self.angle_cos( cnt[i], cnt[(i+1) % 4], cnt[(i+2) % 4] ) for i in range(4)])
                if max_cos < 0.1:
                    rect.append(cnt)
        return rect


    def read_percent_bar(self,image, mask):
        width = image.shape[1] - 1
        height = image.shape[0] - 1 

        hsv = cv2.cvtColor(image, cv2.COLOR_BGR2HSV)

        masks = {}
        masks['blue'] = cv2.inRange(hsv, np.array([100, 50, 50]), np.array([120,255,255]))
        red_low = cv2.inRange(hsv, np.array([0, 90, 20]), np.array([10,255,255]))
        red_high = cv2.inRange(hsv, np.array([175, 90, 20]), np.array([185,255,255]))
        masks['red'] = red_low + red_high
        masks['purple'] = cv2.inRange(hsv, np.array([120, 50, 50]), np.array([140,255,255]))

#  test for non exist or 0%
#        masks['black']
        
        masked = cv2.bitwise_and(image,image, mask = masks[mask])

        return round(np.count_nonzero(np.sum(np.sum(masked,0),1) > 0) / masked.shape[1] * 100, 1)


    def run(self):
#if 'size' in params:
#    w, h = map(int, params['size'].split('x'))
#vid.set(cv.CAP_PROP_FRAME_WIDTH, 2400)
#vid.set(cv.CAP_PROP_FRAME_HEIGHT, 1080)

        cap = cv.VideoCapture(self.vdev)
        waited=0
        feedback = ""
        feedback2 = ""
        while self._run_flag:
            _ret, orig = cap.read()
            if (orig is None):
                time.sleep(0.1) 
                waited=waited+0.1
                if (waited > self.timeout):
                    cap = cv.VideoCapture(self.vdev)
                    waited=0
                continue
            else:
                self.frame_count += 1
                rec = self.recorder
                if rec is not None:
                    rec(orig)

        #    if ((frame_count % 2) != 0):
        #        continue

            #  classically OCR uses white as text foreground and black for background
            #  
            #  MTG typically has black text on a lighter color bg
            #
        #    print('Original Dimensions : ',img.shape)
            self.prev_scale = self.scale_percent
#            scale_percent = cv.getTrackbarPos('scale', 'edge')
            self.width = orig.shape[1]
            self.height = orig.shape[0]
            width = int(orig.shape[1] * self.scale_percent / 100)
            height = int(orig.shape[0] * self.scale_percent / 100)
            dim = (width, height)

            t = self.clock()

            #  split frame into tiles so that we can have an area 
            #  for detected cards to occupy for reference
            #
            ih, iw, ic = orig.shape

            img = cv.resize(orig, dim, interpolation = cv.INTER_AREA)
            im2 = img.copy()

            #  with second plus framerates, show something on program start
            #
            if (self.frame_count == 1 or self.image_options == None or self.image_options == "V4L2"):
                self.change_pixmap_signal.emit(img)

            if self.replay:
                ref = self.replay_ref(img)
                self.lastRef = ref
                self.lastRefTime = time.time()
                self.hud_frame(ref)
                self.stats_frame(ref)
                self.result_frame(ref)
                if not self.hudVisible:
                    self.menu_frame(ref)
                if self.path is None:
                    self.path_frame(ref)
                if self.pathQueue is None:
                    self.map_title_frame(ref)
                if self.chars:
                    self.chars_frame(ref)
                if self.placer:
                    self.place_frame(ref)
                self.record_touch_frame(ref)
                if self.autoplay:
                    self.auto_frame(ref)
                if self.autoplay and self.script:
                    self.script_frame(ref)
                if self.image_options == "Bloons":
                    self.replay_frame(ref, im2)

            #try 10 by 10 grid
            rows, cols = 10,10
            tilesize = (int(ih//rows), int(iw//cols))
            self.tilesize = tilesize
            self.tileRows = 10
            self.tileCols = 10
            self.tileW = tilesize[1]
            self.tileH = tilesize[0]

        #    print(ih,iw,tilesize)
        #    print("rows %d, cols %d" % (orig.rows, orig.cols))

            #  first part is card shape detection
            #

        #    fd, hog_image = hog(img, orientations=9, pixels_per_cell=(8, 8),
        #                	cells_per_block=(2, 2), visualize=True, multichannel=True)

        #    cv.imshow('hog', hog_image)

            gray = cv.cvtColor(img, cv.COLOR_BGR2GRAY)

            # denoise before edge detection
            blur = cv.GaussianBlur(gray,(5,5),0)

            # 4. Dilate the image a bit to make differences more seeable; more suitable for contour detection
            kernel = np.ones((5, 5))

            # 5. Only take different areas that are different enough (>20 / 255)
            threshb_frame = cv.threshold(src=blur, thresh=self.threshLower, maxval=self.threshUpper, type=cv.THRESH_BINARY)[1]
            threshw_frame = cv.threshold(src=blur, thresh=self.threshLower, maxval=self.threshUpper, type=cv.THRESH_BINARY)[1]

            
            if (self.image_options in ["World"]) and self.battleEnd != None:
                
                r = self.find_mobs(blur)
                for mob in r:
                    (x,y,w,h) = mob
                    self.actions.tap(x+int(w/2), y + int(h/2))
                    QtTest.QTest.qWait(500)
                    area = w * h
                    if area > 200 and area < 500:
                       cv.rectangle(im2, (x,y), (x + w, y + h), (255,0,0), 2)
                    else:
                       cv.rectangle(im2, (x,y), (x + w, y + h), (0,255,0), 2)

            if (self.image_options == "Thresh"):
                self.change_pixmap_signal.emit(threshb_frame)

        #    cv.drawContours(image=img_rgb, contours=contours, contourIdx=-1, color=(0, 255, 0), thickness=2, lineType=cv2.LINE_AA)

        #    ret, thresh1 = cv.threshold(gray, 175, 255, cv.THRESH_BINARY)
            
            #  locate X button
            #
            w, h = self.xbtn_template.shape[::-1]
            res = cv.matchTemplate(gray, self.xbtn_template, cv.TM_CCOEFF_NORMED)
            threshold = 0.8
            loc = np.where( res >= threshold)

            foundX = False
            for pt in zip(*loc[::-1]):
                cv.rectangle(im2, pt, (pt[0] + w, pt[1] + h), (0,0,255), 2)
                x = int(pt[0] + w / 2)
                y = int(pt[1] + h / 2)
                npa = np.array((x,y))
                npb = np.array((480,548)) # spell menu x button location with 9 spells
                # calculating Euclidean distance
                # using linalg.norm()
                dist = int(np.linalg.norm(npa - npb))
                if dist < 10:
                    cv.circle(im2, (x, y), 2 ,(0,0,255), 2)
                    foundX = True
                    self.spell_menu = True
            if not foundX:
                self.spell_menu = False


            w, h = self.continuebtn_template.shape[::-1]
            res = cv.matchTemplate(gray, self.continuebtn_template, cv.TM_CCOEFF_NORMED)
            _minVal, maxVal, minLoc, maxLoc = cv.minMaxLoc(res, None)
            loc = maxLoc
            if maxVal > 0.8:
                #print(loc, (w,h))
                cv.rectangle(im2, loc, (loc[0] + w, loc[1] + h), (0,0,255), 2)
                if (self.image_options in ["World"] ):
                    dist = int(np.linalg.norm(np.array(loc) - np.array((376,315))))
                    if dist < 25: #battle button
                         self.actions.tap(loc[0] + int(w / 2),loc[1] + int(h / 2))

                dist = int(np.linalg.norm(np.array(loc) - np.array((376,492))))
                if dist < 20: #continue button
                    if self.battleEnd == None:
                        self.battleEnd = datetime.now()
                        self.battle_signal.emit((self.battleStart, self.battleEnd))
                    if (self.image_options in ["World"] ):
                        self.actions.tap(loc[0] + int(w / 2),loc[1] + int(h / 2))
                        QtTest.QTest.qWait(1000)
                        print("tried to autoheal")
                        self.actions.hold(827,569, 2) #auto-heal (d-pad)
#                        self.actions.hold(567,558, 2) #auto-heal (tap to move mode)

            w, h = self.origintown_template.shape[::-1]
            res = cv.matchTemplate(gray, self.origintown_template, cv.TM_CCOEFF_NORMED)
            _minVal, maxVal, minLoc, maxLoc = cv.minMaxLoc(res, None)
            loc = maxLoc
            if maxVal > 0.8:
                cv.rectangle(im2, loc, (loc[0] + w, loc[1] + h), (0,0,255), 2)

            w, h = self.balor_template.shape[::-1]
            res = cv.matchTemplate(gray, self.balor_template, cv.TM_CCOEFF_NORMED)
            _minVal, maxVal, minLoc, maxLoc = cv.minMaxLoc(res, None)
            loc = maxLoc
            if maxVal > 0.8:
                cv.rectangle(im2, loc, (loc[0] + w, loc[1] + h), (0,0,255), 2)
#                self.actions.hold((1140,1110), 2) #auto-heal

            w, h = self.warpgate_template.shape[::-1]
            res = cv.matchTemplate(gray, self.warpgate_template, cv.TM_CCOEFF_NORMED)
            threshold = 0.8
            loc = np.where( res >= threshold)

            for pt in zip(*loc[::-1]):
                cv.rectangle(im2, pt, (pt[0] + w, pt[1] + h), (0,0,255), 2)

            #hp_template = cv.imread('templates/hp_bar_empty_alpha.png', 0)
            #w, h = hp_template.shape[::-1]
            #res = cv.matchTemplate(gray, hp_template, cv.TM_CCOEFF_NORMED)
            #threshold = 0.8
            #loc = np.where( res >= threshold)
            #for pt in zip(*loc[::-1]):
            #    cv.rectangle(im2, pt, (pt[0] + w, pt[1] + h), (0,255,0), 2)
            # locate world bosses


            if self.mode_options == "Canny" or self.mode_options == None:
                rect = self.find_squares(blur)
            if self.mode_options == 'Thresh':
                rect = self.find_squares(blur, threshb_frame)

#            print("width %s height %s" % (self.width, self.height)) 
            #hpbar = nmpy.array([165,317,216,328])

            stats = []
            for stat in self.bars_hpmpward:
                (loc, color) = stat

                barimg = orig[loc[1]:loc[1]+self.barwh[1],loc[0]:loc[0]+self.barwh[0]]
                stats.append( self.read_percent_bar(barimg,color) )

            (self.health_percent, mana, self.ward_percent) = stats
            if mana > 0:
                self.mana_percent = mana

            if not self.spell_menu:

                self.health_summons = []
                for tl in self.bars_hpsummons:

                    # 2,2 rect will be all white at these coords 
                    w = (tl[0]+self.barwh[0]+1, tl[1]+2)
                    if np.count_nonzero(orig[w[1]:w[1]+2,w[0]:w[0]+2] > 200) < 6:
#                        print(orig[w[1]:w[1]+2,w[0]:w[0]+2])
#                        print(np.count_nonzero(orig[w[1]:w[1]+2,w[0]:w[0]+2] > 200))
                        continue

                    barimg = orig[tl[1]:tl[1]+self.barwh[1],tl[0]:tl[0]+self.barwh[0]]
                    shp = self.read_percent_bar(barimg,'red')
                    #cv.rectangle(im2, (tl[0], tl[1]), (tl[0]+self.barwh[0],tl[1]+self.barwh[1]), (0, 255, 0), 1)
                    if shp > 0:
                        self.health_summons.append(shp)
                self.summons = len(self.health_summons)


            if (self.image_options in ["Rects", "Arena"]):
                cardnum=0
                for cnt in rect:
                    cardnum += 1
                    box=cv.boundingRect(cnt)
                    words=[]
                    cb=[]
                    cv.drawContours(im2,[cnt],0,(0,0,255),3)
                    if  (self.image_options in ["Arena", "Rects"] ):
                        unscaled = tuple(int(n / (self.scale_percent / 100)) for n in box)
        #                print(unscaled)
                        x, y, w, h = unscaled
                        cx = x + (w / 2)
                        cy = y + (h / 2)
                        boximage=orig[y: y + h, x : x + w]

                        (cb,words) = self.fast_east_tess(boximage)

                        if len(words):
                            print(" ".join(words))
                        bt = " ".join(words)
                        if (bt in BUTTONS):
                            print(bt)
                            print(BUTTONS[bt])
#                            xt = 0
#                            yt = 0
#                            for i in range(len(cb)):
#                                cx, cy = cb[i]
#                                xt += cx
#                                yt += cy
                            #cx = (xt / len(cb)) / self.scale
                            #cy = (yt / len(cb)) / self.scale
#                            cx = (xt / len(cb))
#                            cy = (yt / len(cb))
 #                           print(cb)
#                            print("scale: %s cx: %s cy: %s" % (self.scale, cx, cy))
                            if (BUTTONS[bt] == "tap"):
                                self.actions.tap(cx,cy)
                            if (BUTTONS[bt] == "hold"):
                                self.actions.hold(cx,cy,2)

                            if (bt == "EXIT"):
                                self.actions.reset()
                            if ((bt == "HOLD SPAR") or (bt == "HOLD TO SPAR") or (bt == "HOLD BATTLE") or (bt == "HOLD TO BATTLE")):
                                print("saw button!!!")
                                self.actions.reset()

            if (self.image_options in ["Raid"]):
                action = self.actions.action()
                if isinstance(action, dict):
                    text = "%s - %s" % (action["name"], action["action"])
                    feedback = text
                cv.putText(im2, feedback, (20, 200), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                self.actions.do()

            if self.image_options == "Stats" or self.image_options == "Battle":

                if self.spell_menu:
                    cv.putText(im2, "spell menu", (20, 300), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)

                if self.ward_turns > 0:
                    cv.putText(im2, "ward turns %s" % (self.ward_turns), (200, 300), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                if self.health_percent > 0:
                    cv.putText(im2, "health %.1f" % (self.health_percent), (220, 340), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                if self.mana_percent > 0:
                    cv.putText(im2, "mana %.1f" % (self.mana_percent), (220, 380), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                if self.ward_percent > 0:
                    cv.putText(im2, "ward %.1f" % (self.ward_percent), (220, 420), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                if self.summons > 0:
                    cv.putText(im2, "summons %s" % (self.summons), (420, 300), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)

                nfo_loc = (420,340)
                for i in range(len(self.health_summons)):
                    hp = self.health_summons[i-1]
                    cv.putText(im2, "hp %s" % (hp), (nfo_loc[0], nfo_loc[1] + i * 35) , cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
            #  decide what to do
            #
            if self.spell_menu and self.image_options in ["Battle", "Arena", "World"]:
                print("spell menu button showed up... dc?")
                self.turns += 1
                action=""

                if self.battleEnd != None:
                    self.battleEnd = None
                    self.battleStart = datetime.now()
                    self.turns = 1

#                if self.mana_percent < 20 and self.mana_percent > 0:
#                    action = "potion"
                if self.health_percent < 80:
                    action = "heal"
                if self.ward_percent < 90:
                    action = "mend"
                if self.summons < 5:
                    if self.turns < 15:
                        action = "summon2"
                    else:
                        action = "summon"
                if self.health_percent < 8:
                    action = "heal"
                if self.turns == 1:
                    if self.ward_percent < 5:
                        action = "ward"
#                if self.turns in [4,5,6]:
#                    if self.lastTurn != "db":
#                        action = "db"
                if self.turns in [9,10]:
                    if self.lastTurn != "ward" and self.summons < 5:
                        action = "ward"
                if self.mana_percent < 16 and self.turns > 1: #10 is too low
                    action = "potion"
                    print("spell menu button showed up... dc?")
                if self.ward_percent < 1:
                    action = "ward"

                if self.mana_percent < 9 and self.turns > 1: #10 is too low
                    action = "potion"


                if self.image_options == 'Arena':
                    if action == "potion":
                        action = "diffuse"
                    if action in ["summon2", "summon3"]:
                        action = "summon"
                    if action == "offhand":
                        action = "freeze"

                if self.turns == 1:
                    action = "ward"

                if not len(action):
                    if len(self.actionStack) <= 0:
                        self.actionStack = ["dc", "rhada", "balor"]
                    print("ActionStack: %s, len %i" % (self.actionStack, len(self.actionStack)))
                    action = self.actionStack.pop(0)

                feedback2 = "%s, turn %s" % (self.lastTurn, self.turns - 1);
                cv.putText(im2, feedback2, (20, 160), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)

                self.lastTurn = action
                self.action = action
                feedback = "%s, turn %s, time %s" % (action, self.turns, str(datetime.now() - self.battleStart).split('.')[0]);
                cv.putText(im2, feedback, (20, 200), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                print("do token %s " % action)
                done = self.actions.doToken(action)
                print("do token %s returned with %s" % (action, done))

            else:
                if self.image_options == "Battle" and self.battleEnd == None:
                    feedback = "%s, turn %s, time %s" % (self.action, self.turns, str(datetime.now() - self.battleStart).split('.')[0]);
                elif self.battleEnd != None:
                    feedback = "turns %s, time %s" % (self.turns, str(self.battleEnd - self.battleStart).split('.')[0]);
                if len(feedback) > 0 and self.image_options in ["Battle", "Stats", "Arena", "Raid"]:
                    cv.putText(im2, feedback, (20, 200), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)
                if len(feedback2) > 0 and self.image_options in ["Battle", "Stats", "Arena", "Raid"]:
                    cv.putText(im2, feedback2, (20, 160), cv.FONT_HERSHEY_SIMPLEX, 1, (0,255,0), 2)

            #  show framerate (time between processed frames)
            #
            dt = self.clock() - t
            cv.putText(im2, 'time: %.1f ms (%.1f)fps' % (dt*1000, 1/dt), (20, 20), cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 2)

            
#            cv.imshow(method, im2)

            #  escape key
#            if cv.waitKey(5) == 27:
#                break
#            if (self.image_options
            if (self.image_options in ["Rects", "Arena", "Raid", "Battle", "Stats", "World", "Bloons"]):
                self.change_pixmap_signal.emit(im2)
#            print("emitting change_table with:")
#            print(self.cardsByTile)

        # shut down capture system
        cap.release()

    def clock(self):
        return cv.getTickCount() / cv.getTickFrequency()

    def get_tile(self,x,y,w,h, tilesize):
        TILE_W = tilesize[1]
        TILE_H = tilesize[0]

        x1 = int(x / TILE_W)
        x2 = (x + w) / TILE_W

        y1 = int(y / TILE_H)
        y2 = (y + h) / TILE_H

        if int(x2) == x2:
            x2 = int(x2 - 1)
        else:
            x2 = int(x2)

        if int(y2) == y2:
            y2 = int(y2 - 1)
        else:
            y2 = int(y2)

        tw = x2 - x1 + 1
        th = y2 - y1 + 1

        return x1+1, y1+1, tw, th

    def stop(self):
        """Sets run flag to False and waits for thread to finish"""
        self._run_flag = False
        self.wait()

    def set_image_options(self, option):
        if (self.debug):
            print("VideoThread: image_options: ", option)
        self.image_options = option
        self.health_summons = []
        self.battleEnd = datetime.now()
        if (self.image_options == 'World'):
            self.actions.tap(80,522) #d-pad center
            QtTest.QTest.qWait(2000)
        if (self.image_options == 'Battle'):
            self.turns = 0
            self.battleStart = datetime.now()
            self.battleEnd = None
            self.action = ""
        else:
            self.battleEnd = datetime.now()
        if (self.image_options == "Bloons"):
            #  checking Bloons (re)starts the replay from the first step
            self.replayStep = 0
            self.replayHits = 0
            self.replayNextOk = 0
        if (self.image_options in ["Arena", "Raid"]):
            self.turns = 0
            self.battleStart = datetime.now()
            self.battleEnd = None
            self.actions = Aethric(mode=self.image_options)
        self.battle_signal.emit((self.battleStart, self.battleEnd))

    def set_mode_options(self, option):
        if (self.debug):
            print("VideoThread: mode_options: ", option)
        self.mode_options = option

class WorkerSignals(QObject):
    '''
    Defines the signals available from a running worker thread.

    Supported signals are:

    finished
        No data

    error
        tuple (exctype, value, traceback.format_exc() )

    result
        object data returned from processing, anything

    progress
        int indicating % progress

    '''
    finished = pyqtSignal()
    error = pyqtSignal(tuple)
    result = pyqtSignal(object)
    progress = pyqtSignal(int)


class Worker(QRunnable):
    '''
    Worker thread

    Inherits from QRunnable to handler worker thread setup, signals and wrap-up.

    :param callback: The function callback to run on this worker thread. Supplied args and
                     kwargs will be passed through to the runner.
    :type callback: function
    :param args: Arguments to pass to the callback function
    :param kwargs: Keywords to pass to the callback function

    '''

    def __init__(self, uri, args, key):
        super(Worker, self).__init__()

        # Store constructor arguments (re-used for processing)
        self.fn = self.request
        self.uri = uri
        self.args = args
        self.key = key
        self.signals = WorkerSignals()

    def request(self):
        print("sending request to %s with %s" % (self.uri, self.args))
        response = requests.get(self.uri+self.args)
        json_response = json.loads(response.text)
        json_response["request"] = {"uri":self.uri, "args":self.args, "key":self.key}
        return json_response

    def print_output(self):
        print(self.response)

    @pyqtSlot()
    def run(self):
        '''
        Initialise the runner function with passed args, kwargs.

        # Retrieve args/kwargs here; and fire processing using them
        '''
        try:
            result = self.request()
        except:
            traceback.print_exc()
            exctype, value = sys.exc_info()[:2]
            self.signals.error.emit((exctype, value, traceback.format_exc()))
        else:
            self.signals.result.emit(result)  # Return the result of the processing
        finally:
            self.signals.finished.emit()  # Done

class RequestPool(QObject):
    on_request_result = pyqtSignal(object)
    def __init__(self):
        super().__init__()
        self.threadpool = QThreadPool()

        self.timer = QTimer()
        self.timer.setInterval(1000)
        self.timer.timeout.connect(self.recurring_timer)
        self.timer.start()
        self.uri = "https://api.scryfall.com/cards/named?fuzzy="
        self.counter = 0


    def recurring_timer(self):
        self.counter +=1

        # Execute
#        self.threadpool.start(worker)

    def result(self, response):
        (key, args, name, image, price, link) = (None, None, None, None, None,None)
        print("request pool result for %s: " % response["request"]["args"])

        args = response["request"]["args"]
        key = response["request"]["key"]

#        {'object': 'error', 'code': 'not_found', 'status': 404, 'details': 'No cards found matching “ein Eldest Redorn”'}
        try:
            print(" name  : %s" % response["name"])
            name = response["name"]
        except:
            print(response)
            return

        try:
            print(" image : %s" % response["image_uris"]["small"])
            image = response["image_uris"]["small"]
        except:
            pass

        try:
            print(" price : %s" % response["prices"]["usd"])
            price = response["prices"]["usd"]
        except:
            pass
  
        try:
            link = response["related_uris"]["gatherer"]
        except:
            pass
  
        card = {"key":key, "args":args, "name": name, "image":image, "price":price, "link": link}
        print("emit on_request_result signal ", card)
        self.on_request_result.emit(card)

        

    def make_request(self,arg,key):
        print(f"RequestPool make_request:{arg}")
        # Pass the function to execute
        uri = self.uri + arg
        worker = Worker(self.uri,arg,key) # Any other args, kwargs are passed to the run function
#        worker.signals.finished.connect(self.thread_complete)
#        worker.signals.progress.connect(self.progress_fn)
        worker.signals.result.connect(self.result)
        # Execute
        self.threadpool.start(worker)


class TransparentOverlay(QWidget):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.setAttribute(QtCore.Qt.WA_NoSystemBackground)
        self._updateParent(self.parentWidget())

    def setParent(self, parent, *args):
        prevParent = self.parentWidget()
        super().setParent(parent, *args)
        self._updateParent(parent, prevParent)

    def unsetParent(self, parent=None):
        if parent is None:
            parent = self.parentWidget()
        if parent is not None and hasattr(parent.resizeEvent, '_original'):
            parent.resizeEvent = parent.resizeEvent._original

    def _updateParent(self, parent, prevParent=None):
        if parent is not prevParent:
            self.unsetParent(prevParent)
            if parent is not None:
                original = parent.resizeEvent
                def resizeEventWrapper(event):
                    original(event)
                    self.resize(event.size())
                resizeEventWrapper._original = original
                parent.resizeEvent = resizeEventWrapper
                self.resize(parent.size())

proc = None
#  touches made on the phone itself, read off its touchscreen with getevent (adb input
#  taps don't go through it, so the bot's own aren't seen).  touch_down when a finger
#  lands, touch_up(action) when it lifts, action named like the GUI's clicks: tap_XxY or
#  swipe_XxY_XxY_Nms, in device coordinates as the screen is turned
#
#  a dropdown of checkboxes: any number ticked, shown comma separated; a click ticks or
#  unticks an item and leaves the list open
class CheckCombo(QComboBox):
    def __init__(self, items, checked=()):
        super().__init__()
        self.setModel(QtGui.QStandardItemModel(self))
        for text in items:
            item = QtGui.QStandardItem(text)
            item.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled)
            item.setCheckState(Qt.Checked if text in checked else Qt.Unchecked)
            self.model().appendRow(item)
        self.setEditable(True)
        self.lineEdit().setReadOnly(True)
        self.view().viewport().installEventFilter(self)
        self.model().dataChanged.connect(self.show_checked)
        self.show_checked()

    def eventFilter(self, obj, ev):
        if obj is self.view().viewport() and ev.type() == QEvent.MouseButtonRelease:
            item = self.model().itemFromIndex(self.view().indexAt(ev.pos()))
            if item is not None:
                item.setCheckState(Qt.Unchecked if item.checkState() == Qt.Checked else Qt.Checked)
            return True
        return super().eventFilter(obj, ev)

    def checked(self):
        return [self.model().item(i).text() for i in range(self.model().rowCount())
                if self.model().item(i).checkState() == Qt.Checked]

    def show_checked(self, *_):
        self.lineEdit().setText(", ".join(self.checked()) or "none")


#  the controls torn off into their own window; closing it puts them back in their tab
class DetachedWindow(QWidget):
    def __init__(self, closing):
        super().__init__()
        self.closing = closing

    def closeEvent(self, event):
        if self.closing:
            self.closing()
        event.accept()


class TouchThread(QThread):
    touch_down = pyqtSignal()
    touch_up = pyqtSignal(str)

    def __init__(self, serial):
        super().__init__()
        self.serial = serial
        self.proc = None
        self.running = True

    def adb_shell(self, *args):
        return guest_shell(self.serial, list(args)).stdout

    #  (device, x max, y max) of the input device whose name says touchscreen
    def find_touchscreen(self):
        dev = name = None
        found = {}
        for line in self.adb_shell("getevent", "-pl").splitlines():
            m = re.match(r"add device \d+: (\S+)", line)
            if m:
                dev = m.group(1)
                continue
            m = re.match(r'\s+name:\s+"(.*)"', line)
            if m:
                name = m.group(1)
                continue
            m = re.search(r"ABS_MT_POSITION_([XY])\s*:.*max (\d+)", line)
            if m and name and "touchscreen" in name:
                found.setdefault(dev, {})[m.group(1)] = int(m.group(2))
        for d, axes in found.items():
            if "X" in axes and "Y" in axes:
                return d, axes["X"], axes["Y"]
        return None, None, None

    def rotation(self):
        #  the built-in panel is display 0; scrcpy's virtual display can come first
        m = re.search(r"mDisplayId=0\b[\s\S]*?mDisplayRotation=ROTATION_(\d+)", self.adb_shell("dumpsys", "window", "displays"))
        return int(m.group(1)) if m else 0

    #  the touchscreen reports in the panel's own (portrait) axes
    def to_screen(self, x, y, rot, xmax, ymax):
        if rot == 90:
            return y, xmax - x
        if rot == 180:
            return xmax - x, ymax - y
        if rot == 270:
            return ymax - y, x
        return x, y

    def run(self):
        if GUEST_OS == GUEST_OS_IOS:
            #  getevent is Android's: an iPhone's own touches can't be read
            print("TOUCH recording touches isn't possible on iOS")
            return
        dev, xmax, ymax = self.find_touchscreen()
        if dev is None:
            print("TOUCH no touchscreen found with getevent")
            return
        rot = self.rotation()
        print("TOUCH reading %s (%dx%d), screen at %d degrees" % (dev, xmax + 1, ymax + 1, rot))
        #  -tt: a pty on the device, else getevent's output is buffered and comes in late
        self.proc = subprocess.Popen(["adb", "-s", self.serial, "shell", "-tt", "getevent", "-lt", dev],
                                     stdout=subprocess.PIPE, stdin=subprocess.DEVNULL,
                                     stderr=subprocess.DEVNULL, text=True)
        x = y = start = t0 = None
        down = up = False
        for line in self.proc.stdout:
            m = re.match(r"\[\s*([\d.]+)\]\s+(\S+)\s+(\S+)\s+(\S+)", line.strip())
            if not m:
                continue
            t, code, val = float(m.group(1)), m.group(3), m.group(4)
            if code == "ABS_MT_POSITION_X":
                x = int(val, 16)
            elif code == "ABS_MT_POSITION_Y":
                y = int(val, 16)
            elif code == "BTN_TOUCH":
                if val == "DOWN":
                    down, up, start, t0 = True, False, None, t
                elif val == "UP":
                    up = True
            elif code == "SYN_REPORT" and down:
                if start is None and x is not None and y is not None:
                    rot = self.rotation() if rot is None else rot
                    start = self.to_screen(x, y, rot, xmax, ymax)
                    self.touch_down.emit()
                if up and start is not None:
                    end = self.to_screen(x, y, rot, xmax, ymax)
                    ms = int((t - t0) * 1000)
                    moved = abs(end[0] - start[0]) + abs(end[1] - start[1])
                    if moved < 10 and ms < 300:
                        action = "tap_%dx%d" % start
                    else:
                        action = "swipe_%dx%d_%dx%d_%dms" % (start[0], start[1], end[0], end[1], max(ms, 100))
                    self.touch_up.emit(action)
                    down = up = False
                    #  the screen may turn between touches
                    rot = None
            if not self.running:
                break

    def stop(self):
        self.running = False
        if self.proc is not None and self.proc.poll() is None:
            self.proc.terminate()

class ImageControl(QWidget):
    check_option_signal = pyqtSignal(str)
    connection_checked = pyqtSignal(str)
    check_mode_option_signal = pyqtSignal(str)
    #  image options that use the threshold sliders
    TUNE_OPTIONS = ("Thresh", "Edge C", "Sq Edge", "Sq Edge Contours")

    #  cb is the box that changed: its stateChanged comes before the group updates
    #  checkedButton(), which still gives the box ticked before
    #
    def imageOptionClicked(self, state, cb=None):
        isChecked = bool(state)
        if (isChecked):
            cb = cb or self.checkBoxes.checkedButton()
            if (cb):
                if (self.debug):
                    print("imageOptionClicked: ",cb.text())
                self.check_option_signal.emit(cb.text())
                #  each option keeps its own window size: save the one being left,
                #  go back to this one's if it was used before
                if self.image_options and cb.text() != self.image_options:
                    self.optionSizes[self.image_options] = self.size()
                self.image_options = cb.text()
                self.tuneGroup.setVisible(cb.text() in self.TUNE_OPTIONS)
                if cb.text() in self.optionSizes:
                    self.resize(self.optionSizes[cb.text()])
            else:
                print("unknown button checked")

    def modeOptionClicked(self, state, cb=None):
        isChecked = bool(state)
        if (isChecked):
            cb = cb or self.modeOptions.checkedButton()
            if (cb):
                if (self.debug):
                    print("modeOptionClicked: ",cb.text())
                self.check_mode_option_signal.emit(cb.text())
            else:
                print("unknown button checked")

    def setThreshLower(self):
        self.thread.threshLower = self.t3Slider.value()
    def setThreshUpper(self):
        self.thread.threshUpper = self.t4Slider.value()
    def updateThreshLower(self, value):
        self.t3Slider.setValue(value)
    def updateThreshUpper(self, value):
        self.t4Slider.setValue(value)
    def setCannyLower(self):
        self.thread.cannyLower = self.t1Slider.value()

    def updateBattle(self,startend):
        self.battleStart = startend[0]
        self.battleEnd = startend[1]

    def updateCannyLower(self, value):
        self.t1Slider.setValue(value)

    def setCannyUpper(self):
        self.thread.cannyUpper = self.t2Slider.value()

    def updateCannyUpper(self,value):
        self.t2Slider.setValue(value)

    def setSliderLabels(self):
        self.t1Label.setText("%d" % self.t1Slider.value())
        self.t2Label.setText("%d" % self.t2Slider.value())
        self.t3Label.setText("%d" % self.t3Slider.value())
        self.t4Label.setText("%d" % self.t4Slider.value())


    def _on_resized(self, event):
        '''
        print(ppretty(event, indent='    ', depth=2, width=30, seq_length=6,
              show_protected=True, show_private=False, show_static=True,
              show_properties=True, show_address=True))
        '''
        ow = event.oldSize().width()
        oh = event.oldSize().height()

        w = event.size().width()
        h = event.size().height()

        wd = w - ow
        hd = h - oh

        print(event.oldSize(), event.size())
        print((ow,oh), (w, h), (wd, hd))

#        self.display_width += wd
#        self.display_height += hd

#        self.image_label.resize(self.display_width, self.display_height)

    #def __init__(self,vdev=0,lower=None, upper=None, debug=False):
    def __init__(self, actions=None):
        super().__init__()
        if (not actions):
            actions = Actions()
            print("not ??")
        else:
            print(type(actions))
        self.actions = actions
#        (self.device_width,self.device_height,self.X11_width,self.X11_height) = self.actions.getResolutions()
        self.scale = 0
#self.actions.scale()

        #  the scrcpy frame's size (-m1170 of a 2340x1080 device): shown 1:1, never smaller
        self.display_width = 1170
        self.display_height = 540
        self.image_options = 'V4L2'
        self.optionSizes = {}

        self.requestPool = RequestPool()

        self.resizeEvent = (lambda old_method: (lambda event: (self._on_resized(event), old_method(event))[-1]))(self.resizeEvent)
        #serial = "FAMVRW9D9HDEHEWS" #BLU Pure

        parser = optparse.OptionParser()
        parser.set_defaults(debug=False)
        parser.add_option('-d', '--debug', action='store_true', dest='debug')
        parser.add_option('--device', type="int", dest='device',
                         help="video device # to read from", default="0")
        parser.add_option('-l', '--lower', type="int", dest='lower', \
                            help="lower canny threshold for rectangle detection processing")
        parser.add_option('-u', '--upper', type="int", dest='upper', \
                            help="upper canny threshold")
        parser.add_option('--map', dest='mapName', default=None,
                            help="map being played, if not read from the map info screen's title; its bloon path is learned from the arrow intro and kept in bloons_adventure/maps/<map>/")
        parser.add_option('--dns', dest='dns', default='dns.adguard.com',
                            help="Private DNS hostname to turn on while running (default dns.adguard.com); off again on exit")
        parser.add_option('--hud-shots', action='store_true', dest='hudShots', default=False,
                            help="save a frame to bloons_adventure/hud/ for every HUD console line")
        parser.add_option('--record-touches', action='store_true', dest='recordTouches', default=False,
                            help="tick Record adb events on start")
        parser.add_option('--play', action='store_true', dest='play', default=False,
                            help="tick Play on start")
        parser.add_option('--quests', action='store_true', dest='quests', default=False,
                            help="tick Quests on start")
        parser.add_option('--place', dest='place', default=None,
                            help="on start, place_character NAME:WHERE (e.g. 'Sai:best coverage')")
        parser.add_option('--drop-and-lock', action='store_true', dest='dropAndLock', default=False,
                            help="the game's Drop & Lock setting is on (placements wait for the check mark)")
        parser.add_option('--campaign', action='store_true', dest='campaign', default=False,
                            help="tick Campaign on start")
        parser.add_option('--goto', dest='goto', default=None,
                            help="on start, navigate_to_map to this map's info screen (then nothing else)")
        (o, args) = parser.parse_args()
        self.startTicks = (o.recordTouches, o.play, o.quests)
        self.startGoto = o.goto
        self.startCampaign = o.campaign
        self.startDropAndLock = o.dropAndLock
        self.startPlace = o.place

        self.debug = False
        if o.debug:
            self.debug = bool(options.debug)

        self.hudShots = o.hudShots
        self.mapName = o.mapName

        global restoreActions
        restoreActions = self.actions
        self.actions.enablePrivateDNS(o.dns)

        self.vdev = 0
        if o.device:
            self.vdev = int(o.device)

        self.cannyLower = None
##        self.cannyLower = 50
        self.cannyLower = 40
        if o.lower:
            self.cannyLower = int(o.lower)

        self.cannyUpper = 237
        if o.upper:
            self.cannyUpper = int(o.upper)

        self.threshLower = 10 
        self.threshLower = 52 #great for high contrast mode balor
        self.threshUpper = 255

        self.replayFramesMax = 25 
        self.replayFrames = []
        self.replayFreq = 0.1
        self.replayLast = None
        self.replaying = False
        self.battleStart = None
        self.battleEnd = None

        self.setWindowTitle("Image Processing Control")
        self.setStyleSheet("QGroupBox { font-weight: bold; } QGroupBox * { font-weight: normal; } "
                           "QGroupBox::title { color: #1864ab; subcontrol-origin: margin; left: 8px; padding: 0 3px; }")
        self.timeout=5
        # create the label that holds the image
        self.image_label = QLabel(self)
        self.image_label.setMinimumSize(self.display_width, self.display_height)
        #  pin pixmap to top-left so label coords == pixmap coords, no centering offset
        self.image_label.setAlignment(Qt.AlignLeft | Qt.AlignTop)
        self.pixmap_width = None
        self.pixmap_height = None
        self.pressPos = None
        self.pressTime = None
        self.pressFrame = None
        self.lastFrame = None
        #  every click on the image saves the frame seen at press time, for offline analysis
        self.clickDir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure")
        os.makedirs(self.clickDir, exist_ok=True)
        #  each run starts a fresh set: clicks.log, touches.log and the click_*.png of the
        #  last run go (only these, not the click folders kept under bloons_adventure/)
        for name in os.listdir(self.clickDir):
            if (name in ("clicks.log", "touches.log") or re.match(r"click_\d+_.*\.png$", name)) and \
                    os.path.isfile(os.path.join(self.clickDir, name)):
                os.remove(os.path.join(self.clickDir, name))
        self.clickCount = self.next_click_number()
        self.touchFrame = None
        self.touchTime = None

#        self.image_label.enterEvent = lambda e:
#        self.image_label.leaveEvent = lambda e: print('goodbye')
        self.image_label.setMouseTracking(True)
        self.image_label.mouseMoveEvent = self.label_mouse_move
        self.image_label.mousePressEvent = self.label_mouse_press
        self.image_label.mouseReleaseEvent = self.label_mouse_release

        # create a text label
        self.lblVdev = QLabel('/dev/video%d' % self.vdev)
        self.lblXY = QLabel('')
        self.snapBtn = QPushButton('Snapshot')
        self.takeSnapshot = False
        self.snapBtn.clicked.connect(self.snapshot)
        #  Start/Stop: save every frame into bloons_adventure/video/
        self.recordBtn = QPushButton('Start')
        self.recordBtn.clicked.connect(self.record_clicked)
        self.recording = False
        self.recordCount = 1
        #  Record/Stop: ffmpeg records the capture device to bloons_adventure/video/
        self.ffmpegBtn = QPushButton('Record')
        self.ffmpegBtn.clicked.connect(self.ffmpeg_clicked)
        self.ffmpegProc = None
        #  Place: put Finn where place_finn_apple1 confirmed him (frame coords);
        #  clicking again while it runs stops it
        self.placeBtn = QPushButton('Place')
        self.placeBtn.clicked.connect(self.place_clicked)
        #  Play: auto play the game on screen, see VideoThread.auto_frame
        self.playBox = QCheckBox('Play')
        self.playBox.stateChanged.connect(self.play_toggled)

        self.t1Slider = QSlider(Qt.Horizontal)
        self.t2Slider = QSlider(Qt.Horizontal)
        self.t3Slider = QSlider(Qt.Horizontal)
        self.t4Slider = QSlider(Qt.Horizontal)
        self.t1Slider.setMinimum(0)
        self.t2Slider.setMinimum(0)
        self.t3Slider.setMinimum(0)
        self.t4Slider.setMinimum(0)
        self.t1Slider.setMaximum(255)
        self.t2Slider.setMaximum(255)
        self.t3Slider.setMaximum(255)
        self.t4Slider.setMaximum(255)
        try:
            self.t1Slider.setValue(self.cannyLower)
        except:
            self.t1Slider.setValue(0)

        try:
            self.t2Slider.setValue(self.cannyUpper)
        except:
            self.t2Slider.setValue(255)

        try:
            self.t3Slider.setValue(self.threshLower)
        except:
            self.t3Slider.setValue(0)

        try:
            self.t4Slider.setValue(self.threshUpper)
        except:
            self.t4Slider.setValue(0)


        self.t1Label = QLabel("%d" % self.t1Slider.value())
        self.t2Label = QLabel("%d" % self.t2Slider.value())
        self.t3Label = QLabel("%d" % self.t3Slider.value())
        self.t4Label = QLabel("%d" % self.t4Slider.value())
        self.t1Slider.setTickPosition(QSlider.TicksBelow)
        self.t2Slider.setTickPosition(QSlider.TicksBelow)
        self.t3Slider.setTickPosition(QSlider.TicksBelow)
        self.t4Slider.setTickPosition(QSlider.TicksBelow)
        self.t1Slider.setTickInterval(5)
        self.t2Slider.setTickInterval(5)
        self.t3Slider.setTickInterval(5)
        self.t4Slider.setTickInterval(5)
        self.t1Slider.valueChanged.connect(self.setSliderLabels)
        self.t2Slider.valueChanged.connect(self.setSliderLabels)
        self.t3Slider.valueChanged.connect(self.setSliderLabels)
        self.t4Slider.valueChanged.connect(self.setSliderLabels)
        self.t1Slider.sliderReleased.connect(self.setCannyLower)
        self.t2Slider.sliderReleased.connect(self.setCannyUpper)
        self.t3Slider.sliderReleased.connect(self.setThreshLower)
        self.t4Slider.sliderReleased.connect(self.setThreshUpper)


        self.checkBoxes = QButtonGroup()
        self.modeOptions = QButtonGroup()
        #'image options')

        replayBtn = QPushButton('Replay')
        replayBtn.clicked.connect(self.replay_clicked)

        #  buttons in a box, at their own width rather than stretched across
        btnGroup = QGroupBox("Actions")
        btnBox = QVBoxLayout(btnGroup)
        for b in (self.snapBtn, self.ffmpegBtn, self.placeBtn, replayBtn, self.recordBtn):
            b.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
            btnBox.addWidget(b)
        btnBox.addStretch()
        btnGroup.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Preferred)

        autoGroup = QGroupBox("Automation")
        autoOuter = QVBoxLayout(autoGroup)
        #  what the automation is doing right now (quest, beacon, campaign map)
        actionGroup = QGroupBox("Current Action")
        actionBox = QVBoxLayout(actionGroup)
        self.questLabel = QLabel("-")
        self.questLabel.setWordWrap(True)
        actionBox.addWidget(self.questLabel)
        autoOuter.addWidget(actionGroup)
        autoGrid = QGridLayout()
        autoOuter.addLayout(autoGrid)
        #  Beacon time: read when Fire Kingdom's beacon activates (beacon_activation)
        self.beaconTimeBox = QCheckBox('Beacon time')
        self.beaconTimeBox.stateChanged.connect(self.beacon_time_toggled)
        autoGrid.addWidget(self.beaconTimeBox, 0, 0)
        autoGrid.addWidget(self.playBox, 1, 0)
        #  Navigate: go to the map picked beside it whenever the game's on a screen navigation
        #  starts from (nav_worker); the list is every known map, alphabetical
        self.navBox = QCheckBox('Navigate')
        self.navBox.stateChanged.connect(self.navigate_changed)
        self.navCombo = QComboBox()
        self.navCombo.addItems(self.known_maps())
        self.navCombo.currentIndexChanged.connect(self.navigate_changed)
        autoGrid.addWidget(self.navBox, 2, 0)
        autoGrid.addWidget(self.navCombo, 2, 1)
        #  Find Beacon: from the home screen, start the beacon map on Impoppable (play_beacon_map)
        self.beaconBox = QCheckBox('Find Beacon')
        self.beaconBox.stateChanged.connect(self.beacon_toggled)
        autoGrid.addWidget(self.beaconBox, 3, 0)
        #  Record adb events: log touches made on the phone itself (TouchThread)
        self.touchBox = QCheckBox('Record adb events')
        self.touchBox.stateChanged.connect(self.touch_toggled)
        self.touchThread = None
        autoGrid.addWidget(self.touchBox, 4, 0, 1, 2)
        #  Quests: play the quest picked in the dropdown (default the best rewarded one)
        self.questBox = QCheckBox('Quests')
        self.questBox.stateChanged.connect(self.quest_toggled)
        self.questCombo = QComboBox()
        self.questCombo.addItem("best rewarded")
        self.questCombo.currentIndexChanged.connect(self.quest_selected)
        autoGrid.addWidget(self.questBox, 5, 0)
        autoGrid.addWidget(self.questCombo, 5, 1)
        #  Campaign: win as many maps as the generic plan can (start_campaign)
        self.campaignBox = QCheckBox('Campaign')
        self.campaignBox.stateChanged.connect(lambda st: self.thread.start_campaign() if st else self.thread.stop_quests())
        autoGrid.addWidget(self.campaignBox, 6, 0)
        #  Keepalive: tap outside the game after 20 s without input so the screen doesn't lock
        self.keepAliveBox = QCheckBox('Keepalive')
        self.keepAliveBox.setChecked(True)
        self.keepAliveBox.stateChanged.connect(lambda st: setattr(self.thread, "keepAlive", bool(st)))
        autoGrid.addWidget(self.keepAliveBox, 7, 0)
        #  scrcpy: the phone's video on /dev/video0, run detached so it outlives the program
        self.scrcpyBox = QCheckBox('scrcpy')
        self.scrcpyBox.setChecked(True)
        self.scrcpyBox.stateChanged.connect(self.scrcpy_toggled)
        autoGrid.addWidget(self.scrcpyBox, 8, 0)
        #  iOS mirror: the iPhone's video on /dev/video0 (ios-mirror-v4l2), detached like scrcpy
        self.iosMirrorBox = QCheckBox('iOS mirror')
        self.iosMirrorBox.setChecked(GUEST_OS == GUEST_OS_IOS)
        self.iosMirrorBox.stateChanged.connect(self.ios_mirror_toggled)
        autoGrid.addWidget(self.iosMirrorBox, 9, 0)
        #  each phone's own: scrcpy and getevent off and greyed out with an iPhone attached, the
        #  iOS mirror with an Android one
        for box, only in ((self.scrcpyBox, GUEST_OS_ANDROID), (self.touchBox, GUEST_OS_ANDROID),
                          (self.iosMirrorBox, GUEST_OS_IOS)):
            if GUEST_OS != only:
                box.blockSignals(True)
                box.setChecked(False)
                box.blockSignals(False)
                box.setEnabled(False)
                box.setToolTip("%s only" % ("Android" if only == GUEST_OS_ANDROID else "iOS"))
        autoGrid.setRowStretch(10, 1)
        autoGroup.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Preferred)

        #  Info: what the bot knows
        infoGroup = QGroupBox("Info")
        infoBox = QVBoxLayout(infoGroup)
        top = QGridLayout()
        self.beaconTimeLabel = QLabel("unknown")
        self.mapLabel = QLabel("None")
        top.addWidget(self.title_label("NEXT BEACON @", "#e8590c"), 0, 0)
        top.addWidget(self.beaconTimeLabel, 0, 1)
        top.addWidget(self.title_label("Map:", "#1971c2"), 1, 0)
        top.addWidget(self.mapLabel, 1, 1)
        top.setColumnStretch(1, 1)
        infoBox.addLayout(top)
        gameGroup = QGroupBox("Auto Game")
        gameGrid = QGridLayout(gameGroup)
        self.statLabels = {}
        for row, (key, title) in enumerate((("stats", "Stats"), ("time", "Time"), ("money", "Money"), ("result", "Result"))):
            self.statLabels[key] = QLabel("-")
            gameGrid.addWidget(self.title_label(title + ":", "#2f9e44"), row, 0)
            gameGrid.addWidget(self.statLabels[key], row, 1)
        gameGrid.setColumnStretch(1, 1)
        #  Reset: start the stats over (the old ones kept as stats_<time>.json)
        resetStats = QPushButton("Reset")
        resetStats.clicked.connect(lambda: self.thread.reset_stats())
        gameGrid.addWidget(resetStats, 4, 0, 1, 2)
        infoBox.addWidget(gameGroup)
        #  Current Game: the HUD as read, the same as the console's HUD lines
        hudGroup = QGroupBox("Current Game")
        hudGrid = QGridLayout(hudGroup)
        self.hudLabels = {}
        for i, (key, title) in enumerate((("round", "Round"), ("lives", "Lives"), ("money", "Money"),
                                          ("spent", "Spent"), ("total", "Total"), ("gained", "Gained"))):
            self.hudLabels[key] = QLabel("-")
            hudGrid.addWidget(self.title_label(title + ":", "#c2255c"), i // 2, (i % 2) * 2)
            hudGrid.addWidget(self.hudLabels[key], i // 2, (i % 2) * 2 + 1)
        hudGrid.setColumnStretch(1, 1)
        hudGrid.setColumnStretch(3, 1)
        infoBox.addWidget(hudGroup)
        curGroup = QGroupBox("Currencies")
        curGrid = QGridLayout(curGroup)
        self.curLabels = {}
        for col, key in enumerate(("gold", "gems", "shards")):
            self.curLabels[key] = QLabel("?")
            curGrid.addWidget(self.title_label(key.capitalize() + ":", {"gold": "#e67700", "gems": "#9c36b5",
                                                                         "shards": "#1098ad"}[key]), 0, col * 2)
            curGrid.addWidget(self.curLabels[key], 0, col * 2 + 1)
        #  the account's level and its exp toward the next (the menu bar's left end)
        self.levelLabel = QLabel("?")
        self.expLabel = QLabel("?")
        curGrid.addWidget(self.title_label("Level:", "#5c940d"), 1, 0)
        curGrid.addWidget(self.levelLabel, 1, 1)
        curGrid.addWidget(self.title_label("Exp:", "#1864ab"), 1, 2)
        curGrid.addWidget(self.expLabel, 1, 3, 1, 3)
        infoBox.addWidget(curGroup)
        questGroup = QGroupBox("Quests")
        questGrid = QGridLayout(questGroup)
        self.questListLabel = QLabel("not read yet")
        questGrid.addWidget(self.questListLabel, 0, 0, 1, 2)
        questGrid.setColumnStretch(1, 1)
        infoBox.addWidget(questGroup)
        infoBox.addStretch()

        optGroup = QGroupBox("Image")
        optGrid = QGridLayout(optGroup)
        options = [QCheckBox(t) for t in ("V4L2", "Stats", "Bloons", "Thresh", "Edge C", "Sq Edge", "Sq Edge Contours")]
        cols = 2
        options[0].setChecked(True)
        for i in range(len(options)):
            optGrid.addWidget(options[i], i // cols, i % cols)
            self.checkBoxes.addButton(options[i], i)
            options[i].stateChanged.connect(lambda state, cb=options[i]: self.imageOptionClicked(state, cb))
        #  Motion: over whichever option's picked (not one of them), the video shows only what
        #  changed since the frame before (motion_only)
        self.motionBox = QCheckBox('Motion')
        self.motionBox.stateChanged.connect(self.motion_toggled)
        optGrid.addWidget(self.motionBox, len(options) // cols, len(options) % cols)
        #  its tuning, under it while it's ticked
        self.motionGroup = QGroupBox("Motion")
        motionGrid = QGridLayout(self.motionGroup)
        self.motionSpins = {}
        for row, (key, label, lo, hi, step, val, tip) in enumerate((
                ("frames", "Frames", 1, 30, 1, 10, "frames back compared: a pixel stays if it differs from any of them"),
                ("blur", "Blur", 1, 31, 2, 1, "Gaussian blur size (odd), before comparing"),
                ("thresh", "Threshold", 0, 255, 1, 20, "how much a pixel has to change (of 255)"),
                ("erode", "Erode", 0, 15, 1, 2, "erosion size: changes smaller than this go (0 keeps every speck)"))):
            spin = QSpinBox()
            spin.setRange(lo, hi)
            spin.setSingleStep(step)
            spin.setValue(val)
            spin.setToolTip(tip)
            spin.valueChanged.connect(self.motion_tuned)
            motionGrid.addWidget(QLabel(label), row, 0)
            motionGrid.addWidget(spin, row, 1)
            self.motionSpins[key] = spin
        self.motionColor = None         # None: the pixels' own colours, else a QColor
        self.motionColorBtn = QPushButton("Original")
        self.motionColorBtn.setToolTip("colour of the pixels that changed: click to pick one, again to go back to their own")
        self.motionColorBtn.clicked.connect(self.motion_pick_color)
        motionGrid.addWidget(QLabel("Color"), 4, 0)
        motionGrid.addWidget(self.motionColorBtn, 4, 1)
        #  shapes found in what moved (motion_shapes), the one picked or all of them
        self.shapeBox = QCheckBox("Shapes")
        self.shapeBox.setChecked(True)
        self.shapeCombo = CheckCombo(("All",) + self.SHAPES, checked=("Triangle",))
        motionGrid.addWidget(self.shapeBox, 5, 0)
        motionGrid.addWidget(self.shapeCombo, 5, 1)
        #  and only shapes one colour inside (within the tolerance, per channel: video's never exact)
        self.sameColorBox = QCheckBox("Same color ±")
        self.sameColorSpin = QSpinBox()
        self.sameColorSpin.setRange(0, 255)
        self.sameColorSpin.setValue(20)
        self.sameColorSpin.setToolTip("most a colour channel may vary inside a shape for it to count as one colour (0: exactly)")
        motionGrid.addWidget(self.sameColorBox, 6, 0)
        motionGrid.addWidget(self.sameColorSpin, 6, 1)
        self.patchSpin = QSpinBox()
        self.patchSpin.setRange(0, 255)
        self.patchSpin.setValue(200)
        self.patchSpin.setToolTip("saturation and brightness a pixel needs to belong to a colour patch (the dark outlines between bloons fall below it)")
        motionGrid.addWidget(QLabel("Color ≥"), 7, 0)
        motionGrid.addWidget(self.patchSpin, 7, 1)
        self.motionGroup.setVisible(False)
        optGrid.addWidget(self.motionGroup, len(options) // cols + 1, 0, 1, cols)
        optGroup.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.Preferred)

        #  thresholds, only shown for the image options that use them
        self.tuneGroup = QGroupBox("Thresholds")
        tuneGrid = QGridLayout(self.tuneGroup)
        opt2 = [QCheckBox('Thresh'), QCheckBox('Canny')]
        opt2[1].setChecked(True)
        for i in range(len(opt2)):
            tuneGrid.addWidget(opt2[i], 0, i)
            self.modeOptions.addButton(opt2[i], i)
            opt2[i].stateChanged.connect(lambda state, cb=opt2[i]: self.modeOptionClicked(state, cb))
        for row, (name, label, slider) in enumerate((
                ("Canny lower", self.t1Label, self.t1Slider), ("Canny upper", self.t2Label, self.t2Slider),
                ("Thresh lower", self.t3Label, self.t3Slider), ("Thresh upper", self.t4Label, self.t4Slider)), 1):
            tuneGrid.addWidget(QLabel(name), row, 0)
            tuneGrid.addWidget(label, row, 1)
            tuneGrid.addWidget(slider, row, 2)
        tuneGrid.setColumnStretch(2, 1)
        self.tuneGroup.setVisible(False)

        grid = QGridLayout()
        grid.addWidget(btnGroup, 0, 0)
        grid.addWidget(optGroup, 0, 1)
        grid.addWidget(autoGroup, 0, 2)
        grid.addWidget(infoGroup, 0, 3)
        grid.setColumnStretch(3, 1)
        grid.addWidget(self.tuneGroup, 1, 0, 1, 4)
        grid.addWidget(self.lblVdev, 2, 0)
        grid.addWidget(self.lblXY, 2, 1, 1, 3)

        videoGroup = QGroupBox("Video")
        videoBox = QVBoxLayout(videoGroup)
        videoBox.addWidget(self.image_label)
        videoGroup.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        #  the controls scroll, so on a 1080 high screen they give way and the video
        #  keeps its full size
        controls = QWidget()
        controls.setLayout(grid)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        scroll.setWidget(controls)
        #  two tabs: the video, and the controls, which can be torn off into their own
        #  window (Detach, or double-click the tab) and come back when it's closed
        self.controlsPage = QWidget()
        controlsBox = QVBoxLayout(self.controlsPage)
        self.detachBtn = QPushButton("Detach")
        self.detachBtn.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.detachBtn.clicked.connect(self.toggle_controls)
        #  Mobile Devices: the phone type found at start (GUEST_OS), beside Detach
        #  in it: OS, Name, ID, Connected (device_startup fills that in), each in its own frame
        deviceGroup = QGroupBox("Mobile Devices")
        deviceRow = QHBoxLayout(deviceGroup)
        try:
            osName, devName, devId = guest_identity(self.actions.serial())
        except Exception:
            osName, devName, devId = ("iOS" if GUEST_OS == GUEST_OS_IOS else "Android"), "?", "none attached"
        for title, value, color in (("OS", osName, "#1c7ed6" if GUEST_OS == GUEST_OS_IOS else "#2f9e44"),
                                    ("Name", devName, "#495057"), ("ID", devId, "#495057")):
            box = QGroupBox(title)
            QHBoxLayout(box).addWidget(self.title_label(value, color))
            deviceRow.addWidget(box)
        box = QGroupBox("Connected")
        self.connectedLabel = self.title_label("...", "#495057")
        QHBoxLayout(box).addWidget(self.connectedLabel)
        deviceRow.addWidget(box)
        self.connection_checked.connect(self.show_connected)
        deviceGroup.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.deviceGroup = deviceGroup
        topRow = QHBoxLayout()
        topRow.addWidget(self.detachBtn)
        topRow.addWidget(deviceGroup)
        topRow.addStretch(1)
        controlsBox.addLayout(topRow)
        controlsBox.addWidget(scroll, 1)
        self.controlsScroll = scroll
        self.controlsWindow = None
        self.tabs = QTabWidget()
        self.tabs.addTab(videoGroup, "Video")
        self.tabs.addTab(self.controlsPage, "Controls")
        self.tabs.tabBarDoubleClicked.connect(lambda i: self.toggle_controls() if self.tabs.widget(i) is self.controlsPage else None)
        vbox = QVBoxLayout()
        vbox.addWidget(self.tabs)

        # set the vbox layout as the widgets layout
        self.setLayout(vbox)
        #  sized to fit, and refitted whenever the controls' layout changes (fit_window)
        controls.installEventFilter(self)
        QTimer.singleShot(0, self.fit_window)

        print("capture /dev/video%d\n" % self.vdev)

    @pyqtSlot(dict)
    def validate_text(self, card):

        #camecase, join with space
        phrase = ""
        for word in card["text"]:
            if (word.istitle()):
                phrase = "+".join([phrase, urllib.parse.quote(word)])
            else:
                phrase = "".join([phrase, urllib.parse.quote(word)])

        #even though this is likely the correct construction of the phrase,
        # there is a chance tesseract had a better OCR on one word over the other

        print("validate_text: make_request phrase %s -> %s" % ("".join(card["text"]), phrase))
        if (float(card["mconf"]) > -1):
            print(card['mconf'])
            self.requestPool.make_request(phrase, card["key"])
        else:
            print(card['mconf'])


    def run(self):
        #  will block for either timeout or time until success string outputs
        #  self.proc is the scrcpy we started, False if video0 was already in use; closeEvent stops it
        self.proc = self.v4l2sink() if self.scrcpyBox.isChecked() or self.iosMirrorBox.isChecked() else False
        if GUEST_OS == GUEST_OS_IOS:
            threading.Thread(target=self.ios_watchdog, name="ios watchdog", daemon=True).start()
        threading.Thread(target=self.device_startup, name="device startup", daemon=True).start()

#        self.isRunningOrStart() #open camera on android device


        # create the video capture thread
        self.thread = VideoThread(vdev=self.vdev,lower=self.cannyLower,upper=self.cannyUpper, lowerT=self.threshLower, upperT=self.threshUpper, debug=self.debug, actions=self.actions, hudShots=self.hudShots, mapName=self.mapName)
        # connect its signal to the update_image slot
        self.thread.change_pixmap_signal.connect(self.update_image)
        self.thread.autoplay_stopped.connect(self.autoplay_stopped)
        self.thread.map_changed.connect(self.mapLabel.setText)
        self.thread.map_changed.connect(self.navigate_select)
        self.thread.beacon_done.connect(self.beacon_finished)
        self.thread.beacon_time_read.connect(self.beacon_time_read)
        self.thread.stats_changed.connect(self.show_stats)
        self.thread.hud_changed.connect(self.show_hud)
        self.thread.currencies_changed.connect(self.show_currencies)
        self.thread.quests_read.connect(self.show_quests)
        self.thread.quest_label.connect(self.questLabel.setText)
        self.thread.quest_play.connect(self.quest_started)
        self.show_stats(self.thread.stats_parts())
        self.show_currencies(self.thread.stats["menu"])
        #  a --map given on the command line was set before this connect
        self.mapLabel.setText(self.thread.mapTitle or "None")
        self.check_option_signal.connect(self.thread.set_image_options)
        self.check_mode_option_signal.connect(self.thread.set_mode_options)
        self.thread.canny_lower_signal.connect(self.updateCannyLower)
        self.thread.canny_upper_signal.connect(self.updateCannyUpper)
        self.thread.thresh_lower_signal.connect(self.updateThreshLower)
        self.thread.thresh_upper_signal.connect(self.updateThreshUpper)
        self.thread.battle_signal.connect(self.updateBattle)

        self.thread.change_text_signal.connect(self.validate_text)

        #  wait for signals to be detected so initial state is set
        #
        self.thread.dropAndLock = self.startDropAndLock
        # start the thread
        self.thread.start()
        if self.startTicks[0] and self.touchBox.isEnabled():
            self.touchBox.setChecked(True)
        if self.startTicks[1]:
            self.playBox.setChecked(True)
        if self.startTicks[2]:
            self.questBox.setChecked(True)
        if self.startPlace:
            name, where = self.startPlace.split(":", 1)
            QTimer.singleShot(4000, lambda: self.thread.place_character(name, where))
        if self.startCampaign:
            self.campaignBox.setChecked(True)
        if self.startGoto:
            threading.Thread(target=lambda: print("NAV %s" % self.thread.navigate_to_map(self.startGoto)), daemon=True).start()


    #  check for existing scrcpy using v42l-sink
    #  if non, start one
    #    TODO: handle errors from scrcpy
    #
    def v4l2sink(self,devN=0):

        #  check for process being run externally
        #
        try:
            fuser = subprocess.run(['fuser', "/dev/video%d" % devN], check=True, capture_output=True, text=True)
            if (len(fuser.stdout) > 0):
                m = re.match(r".*?:?\s*(?P<pid>\d+).*", fuser.stdout)
                ps = subprocess.run(['ps','-q', str(m.group('pid')), '-o', 'user=,pid=,state=,tname=,time=,command='], check=True, capture_output=True, text=True)
                if (len(ps.stdout) > 0):
                    print("v4l2 device video%d in use by the following:\n" % devN, ps.stdout)
                    return False
        except subprocess.CalledProcessError as e:
            if (e.returncode == 1 and len(e.output) == 0):
                print("v4l2 device has no current user")
            else:
                print(e.returncode)
                print(e.output)
        except BaseException as err:
            previous_frame = inspect.currentframe().f_back
            (filename, line_number, function_name, lines, index) = inspect.getframeinfo(previous_frame)
            print(f"Unexpected {err=}, {type(err)=}", line_number, lines)
            pass

        #  begin v4l2_sink with scrcpy as Popen thread with threaded output readers
        #
        if GUEST_OS == GUEST_OS_IOS:
            #  scrcpy is Android's: the iPhone's video comes from ios-mirror-v4l2
            return self.start_ios_mirror(devN)
        print("v4l2 device currently free, starting scrcpy")
    #    cmd = "scrcpy -s %s --lock-video-orientation=3 --v4l2-sink=/dev/video0 --stay-awake --power-off-on-close --no-display --show-touches" % serial
#        cmd = "scrcpy -s %s --lock-video-orientation=3 --v4l2-sink=/dev/video0 --stay-awake --power-off-on-close --no-display --show-touches" % self.serial
        # TODO: get laptop's screensize

        wR = 0
        hR = 0
        s = self.actions.serial()
        m = self.actions.mOption()
        cmd = "scrcpy -s %s -m%s --v4l2-sink=/dev/video0 --no-video-playback --show-touches " % (self.actions.serial(), self.actions.mOption())
        print(cmd)
        #  detached: its own session, output to a log rather than pipes back to us, so it
        #  keeps running when this program exits
        logPath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "scrcpy.log")
        with open(logPath, "w") as log:
            proc = subprocess.Popen(cmd.split(), stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True)
        print("scrcpy pid %d, output in %s" % (proc.pid, logPath))

        waited = 0
        self.timeout = 5
        while waited < self.timeout and proc.poll() is None:
            with open(logPath, errors="replace") as log:
                m = re.search(r"v4l2 sink started to device: (?P<device>[\/\w]+)", log.read())
            if m:
                print("scrcpy v4l2 sink started using device %s" % m.group('device'))
                break
            time.sleep(0.1)
            waited += 0.1
        if proc.poll() is not None:
            print("scrcpy exited with %s, see %s" % (proc.returncode, logPath))
        return proc

    #  the iPhone's screen on /dev/videoN: ios-mirror-v4l2 (on the PATH, else IOS_MIRROR, else
    #  /space/git/iOS/mirror-v4l2), which also brings up WebDriverAgent; started like scrcpy,
    #  detached in its own session with its output in bloons_adventure/ios-mirror.log
    #
    IOS_MIRROR_WAIT = 90        # s for its "streaming" line (mounting and WDA take a while)

    def start_ios_mirror(self, devN=0):
        path = shutil.which("ios-mirror-v4l2") or os.environ.get("IOS_MIRROR") or "/space/git/iOS/mirror-v4l2"
        if not os.path.exists(path):
            print("IOS mirror not found (%s): put ios-mirror-v4l2 on the PATH or set IOS_MIRROR" % path)
            return False
        env = dict(os.environ, V4L2_DEVICE="/dev/video%d" % devN)
        env.setdefault("V4L2_SIZE", "1170x540")     # the frame size the bot works at, landscape
        logPath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "ios-mirror.log")
        try:
            udid = [self.actions.serial()]
        except Exception:
            udid = []
        with open(logPath, "w") as log:
            proc = subprocess.Popen([path] + udid, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True, env=env, cwd=os.path.dirname(os.path.realpath(path)))
        print("IOS mirror %s pid %d (%s), output in %s" % (path, proc.pid, env["V4L2_SIZE"], logPath))
        end = time.time() + self.IOS_MIRROR_WAIT
        while time.time() < end and proc.poll() is None:
            with open(logPath, errors="replace") as log:
                if re.search(r"^\[v4l2\] streaming ", log.read(), re.M):
                    print("IOS mirror streaming to /dev/video%d" % devN)
                    break
            time.sleep(0.5)
        if proc.poll() is not None:
            print("IOS mirror exited with %s, see %s" % (proc.returncode, logPath))
        return proc

    #  Ctrl-C to the script: it stops what it started (ffmpeg, WDA, iproxy)
    def stop_ios_mirror(self):
        proc = getattr(self, "proc", None)
        if isinstance(proc, subprocess.Popen) and proc.poll() is None:
            pids = [proc.pid]
        else:
            #  the script run by bash, not something with it open (an editor)
            pids = [int(p) for p in subprocess.run(["pgrep", "-f", r"^(/usr/bin/|/bin/)?(ba)?sh .*mirror-v4l2"],
                                                   capture_output=True, text=True).stdout.split()]
        for pid in pids:
            print("stopping iOS mirror pid %d" % pid)
            os.kill(pid, signal.SIGINT)

    #  iOS: WebDriverAgent dies now and then (the phone locking, the test runner quitting), and
    #  with it every tap and the screen stream.  Every IOS_CHECK s, while the iOS mirror's
    #  ticked: unreachable for IOS_DEAD s (or the mirror gone), the mirror is stopped, any
    #  WebDriverAgent runner and iproxy left for this phone are killed, and the mirror's started
    #  again (it brings WebDriverAgent up); at most once every IOS_RESTART_GAP s.  Meanwhile the
    #  phone's screen size is asked for until it reads, so taps aren't scaled by 0
    #
    IOS_CHECK = 10
    IOS_DEAD = 60
    IOS_RESTART_GAP = 180

    @staticmethod
    def wda_alive():
        import urllib.request
        try:
            with urllib.request.urlopen(WDA.url + "/status", timeout=5) as r:
                return r.status == 200
        except Exception:
            return False

    def ios_watchdog(self):
        deadSince = None
        lastRestart = 0
        sized = False
        while True:
            time.sleep(self.IOS_CHECK)
            if not self.iosMirrorBox.isChecked():
                deadSince = None
                continue
            alive = self.wda_alive()
            proc = getattr(self, "proc", None)
            gone = isinstance(proc, subprocess.Popen) and proc.poll() is not None
            if alive:
                deadSince = None
                WDA.downUntil = 0
                w, h = self.actions.resolutions()[:2]
                if w and h and not sized:
                    print("IOS screen %sx%s" % (w, h))
                    sized = True
                continue
            sized = False
            deadSince = deadSince or time.time()
            if (time.time() - deadSince < self.IOS_DEAD and not gone) or time.time() - lastRestart < self.IOS_RESTART_GAP:
                continue
            lastRestart = time.time()
            print("IOS WebDriverAgent %s for %d s: restarting the mirror" % (
                  "down (mirror exited)" if gone else "unreachable", time.time() - deadSince))
            self.restart_ios_mirror()
            deadSince = None

    def restart_ios_mirror(self):
        self.stop_ios_mirror()
        proc = getattr(self, "proc", None)
        if isinstance(proc, subprocess.Popen):
            try:
                proc.wait(timeout=15)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
        #  anything still serving this phone from before (a runner whose app died on the phone
        #  keeps port 8100 taken, and the mirror then thinks WebDriverAgent's up)
        udid = self.actions.serial()
        for pattern in ("dvt xcuitest .*%s" % udid, "iproxy -u %s" % udid):
            subprocess.run(["pkill", "-f", pattern])
        time.sleep(2)
        WDA.session = None
        WDA.scale = None
        WDA.downUntil = 0
        self.actions._device_width = self.actions._device_height = None
        self.proc = self.start_ios_mirror(self.vdev)

    def ios_mirror_toggled(self, st):
        if st:
            threading.Thread(target=lambda: setattr(self, "proc", self.v4l2sink()), daemon=True).start()
        else:
            self.stop_ios_mirror()

    def scrcpy_toggled(self, st):
        if st:
            threading.Thread(target=lambda: setattr(self, "proc", self.v4l2sink()), daemon=True).start()
        else:
            self.stop_scrcpy()

    @pyqtSlot(str)
    def show_connected(self, how):
        self.connectedLabel.setText(how)
        self.connectedLabel.setStyleSheet("QLabel { color: %s; font-weight: bold; }"
                                          % ("#c92a2a" if how == "None" else "#2f9e44"))

    #  at start: how the phone is connected (device_connection), then the game brought up if
    #  something else is in front.  Android: scrcpy restarted after, its v4l2 video comes up
    #  with the wrong orientation when the app changes under it
    GAME_START_WAIT = 5         # s for the game's window before scrcpy is restarted
    WDA_START_WAIT = 120        # s for WebDriverAgent (the mirror brings it up)

    def device_startup(self):
        try:
            serial = self.actions.serial()
        except Exception:
            serial = None
        how = device_connection(serial) if serial else None
        print("DEVICE %s connected %s" % (serial, how))
        self.connection_checked.emit(str(how))
        if how is None:
            return
        app = self.foreground_app()
        if app == GAME_PACKAGE:
            return
        print("DEVICE %s in front, starting %s" % (app, GAME_PACKAGE))
        if GUEST_OS == GUEST_OS_IOS:
            try:
                WDA.call("POST", "/session/%s/wda/apps/launch" % WDA.sid(), {"bundleId": GAME_PACKAGE})
            except Exception as e:
                print("DEVICE couldn't start %s: %s" % (GAME_PACKAGE, e))
            return
        guest_shell(serial, "monkey -p %s -c android.intent.category.LAUNCHER 1" % GAME_PACKAGE)
        if self.scrcpyBox.isChecked():
            time.sleep(self.GAME_START_WAIT)
            print("DEVICE restarting scrcpy for its orientation")
            self.stop_scrcpy()
            self.proc = self.v4l2sink()

    #  package (Android) or bundle id (iOS) of the app in front, None if it can't be told
    def foreground_app(self):
        if GUEST_OS == GUEST_OS_IOS:
            end = time.time() + self.WDA_START_WAIT
            while time.time() < end:
                try:
                    return WDA.call("GET", "/wda/activeAppInfo").get("value", {}).get("bundleId")
                except Exception:
                    time.sleep(5)
            return None
        focus = guest_shell(self.actions.serial(), "dumpsys window | grep -E 'mCurrentFocus|mFocusedApp'", timeout=15).stdout
        m = re.search(r"mCurrentFocus=Window\{\S+ \S+ ([\w.]+)/", focus) or re.search(r" ([\w.]+)/[\w.$]+", focus)
        return m.group(1) if m else None

    def checkCurrentFocus(self):
        return guest_shell(self.actions.serial(), "dumpsys window windows | grep -E 'mCurrentFocus|mFocusedApp|mHoldScreenWindow'").stdout

    #  for future reference,
    #   setting up open camera
    #  video mode, hide all gui elements
    #  set resolution to that of phone screen size
    #  enable digital video stabilization
    #  preference_auto_stabilise = true (auto level in gui)
    #    images mat be smaller resolution due to rotating and cropping
    #
    def isRunningOrStart(self,package="net.sourceforge.opencamera"):
        focus=self.checkCurrentFocus()
        m = re.match(r".*?%s.*" % package,focus)
        if (m):
            return
        else:
            guest_shell(self.actions.serial(), "monkey -p %s -c android.intent.category.LAUNCHER 1" % package)



    #  a thin black line round the window's outer edge
    def paintEvent(self, event):
        super().paintEvent(event)
        p = QtGui.QPainter(self)
        p.setPen(QtGui.QColor(0, 0, 0))
        p.drawRect(self.rect().adjusted(0, 0, -1, -1))

    def closeEvent(self, event):
        if self.touchThread is not None:
            self.touchThread.stop()
            self.touchThread.wait(3000)
        self.thread.stop()
        self.stop_ffmpeg()
        event.accept()

    #  the scrcpy box unticked: whichever scrcpy feeds /dev/video0, this program's or not
    #
    def stop_scrcpy(self):
        proc = getattr(self, "proc", None)
        if isinstance(proc, subprocess.Popen) and proc.poll() is None:
            pids = [proc.pid]
        else:
            fuser = subprocess.run(["fuser", "/dev/video0"], capture_output=True, text=True)
            pids = [int(p) for p in fuser.stdout.split()
                    if subprocess.run(["ps", "-q", p, "-o", "comm="], capture_output=True, text=True).stdout.strip() == "scrcpy"]
        for pid in pids:
            print("stopping scrcpy pid %d" % pid)
            os.kill(pid, signal.SIGTERM)
        if isinstance(proc, subprocess.Popen):
            try:
                proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                proc.kill()

    @pyqtSlot(np.ndarray)
    def update_image(self, cv_img):
        """Updates the image_label with a new opencv image"""
        self.lastFrame = cv_img
        if self.recording:
            self.save_video_frame(cv_img)
        drag = getattr(self, "dragAt", None)
        if drag is not None and not getattr(self, "liveDown", False) and self.pixmap_width:
            #  iOS: no live drag on the phone, so where the finger is shows here
            k = cv_img.shape[1] / float(self.pixmap_width)
            cx, cy = int(drag[0] * k), int(drag[1] * k)
            cv_img = cv_img.copy()
            cv.circle(cv_img, (cx, cy), 6, (0, 0, 255), -1)
        if self.motionBox.isChecked():
            cv_img = self.motion_only(cv_img)
        qt_img = self.convert_cv_qt(cv_img)

        if self.replaying == False and self.battleStart != None and self.battleEnd == None:
            if self.replayLast == None or ((datetime.now() - self.replayLast) > timedelta(seconds=self.replayFreq)):
                self.replayFrames.append(qt_img)
                self.replayLast = datetime.now()
                if (len(self.replayFrames) > self.replayFramesMax):
                    self.replayFrames.pop(0)

        if self.replaying == False:
            self.image_label.setPixmap(qt_img)
            self.pixmap_width = qt_img.width()
            self.pixmap_height = qt_img.height()

    SHAPES = ("Triangle", "Square", "Rectangle", "Pentagon", "Circle", "Balloon", "Polygon")
    #  Balloon: a bloon, measured off snapshot.png's red ones (20x24, ~270 px): an ellipse
    #  fitted to the blob covers about its area (0.81-0.99 there), the blob's no deep dents
    #  (its highlight and knot leave 0.75-0.96 of its hull), and it's upright: about as tall as
    #  wide or taller (the lava vents there, ovals too, are at most 0.85 as tall: circles)
    ELLIPSE_FIT = (0.78, 1.1)   # blob area / fitted ellipse's area
    ELLIPSE_SOLID = 0.72        # blob area / its convex hull's area, at least
    TALL = 0.95                 # height / width this or more: upright, like a bloon
    SHAPE_MIN_AREA = 100        # contours smaller than this (px) are noise

    #  each blob in the motion mask: its outline simplified (4% of its perimeter), named by
    #  its corners (3 triangle, 4 square when about as wide as high else rectangle, 5
    #  pentagon, more a circle).
    #  The blobs are img's colour patches (one of PATCH_BINS hues, strong enough: Color ≥) that
    #  touch what moved, not the motion mask's own: a flat-coloured thing moving only changes at
    #  its edges, so the mask shows crescents (a queue of them one long ribbon), never its shape.
    #  Returns the patches that are the shape picked (and with Same color, one colour inside
    #  their outline in img), and their simplified outlines
    PATCH_BINS = 12
    PATCH_NEAR = 9              # px round the motion a patch may be and still count as moving

    def motion_shapes(self, mask, img):
        want = set(self.shapeCombo.checked())
        tol = self.sameColorSpin.value() if self.sameColorBox.isChecked() else None
        keep = np.zeros_like(mask)
        outlines = []
        near = cv.dilate(mask, np.ones((self.PATCH_NEAR, self.PATCH_NEAR), np.uint8))
        hsv = cv.cvtColor(img, cv.COLOR_BGR2HSV)
        #  shifted half a bin so red (hue 0 and 179) is one bin, not split in two
        width = 180 // self.PATCH_BINS
        hue = (hsv[:, :, 0].astype(np.int16) + width // 2) % 180 // width
        strong = (hsv[:, :, 1] >= self.patchSpin.value()) & (hsv[:, :, 2] >= self.patchSpin.value())
        contours = []
        for i in range(self.PATCH_BINS):
            patch = ((hue == i) & strong).astype(np.uint8) * 255
            found, _ = cv.findContours(patch, cv.RETR_EXTERNAL, cv.CHAIN_APPROX_SIMPLE)
            contours += [(c, patch) for c in found]
        for cnt, patch in contours:
            if cv.contourArea(cnt) < self.SHAPE_MIN_AREA:
                continue
            bx, by, bw, bh = cv.boundingRect(cnt)
            if not near[by:by + bh, bx:bx + bw].any():
                continue
            approx = cv.approxPolyDP(cnt, 0.04 * cv.arcLength(cnt, True), True)
            v = len(approx)
            if v == 3 or (v == 4 and self.dented_triangle(approx)):
                shape = "Triangle"
            elif v == 4:
                x, y, w, h = cv.boundingRect(approx)
                shape = "Square" if 0.95 <= w / float(h) <= 1.05 else "Rectangle"
            elif v >= 5 and self.ellipse_like(cnt) is not None:
                x, y, w, h = cv.boundingRect(cnt)
                shape = "Balloon" if h >= self.TALL * w else "Circle"
            elif v == 5:
                shape = "Pentagon"
            elif v > 5:
                shape = "Circle"
            else:
                shape = "Polygon"
            if "All" not in want and shape not in want:
                continue
            if tol is not None:
                inside = np.zeros_like(mask)
                cv.fillPoly(inside, [approx], 255)
                pix = img[inside > 0]
                if not len(pix) or int((pix.max(0).astype(int) - pix.min(0)).max()) > tol:
                    continue
            one = np.zeros_like(mask)
            cv.drawContours(one, [cnt], -1, 255, -1)
            keep |= one & patch
            outlines.append(approx)
        return keep, outlines

    #  short axis / long axis of the ellipse fitted to cnt when cnt's shaped like one, else None
    def ellipse_like(self, cnt):
        if len(cnt) < 5:
            return None
        area = cv.contourArea(cnt)
        hull = cv.contourArea(cv.convexHull(cnt))
        (_, _), (a, b), _ = cv.fitEllipse(cnt)
        ell = np.pi * a * b / 4
        if not ell or not hull or area / hull < self.ELLIPSE_SOLID:
            return None
        if not self.ELLIPSE_FIT[0] <= area / ell <= self.ELLIPSE_FIT[1]:
            return None
        return min(a, b) / max(a, b)

    #  4 corners, one of them inside the triangle the other three make (an arrowhead):
    #  without that one it's a triangle
    @staticmethod
    def dented_triangle(approx):
        pts = approx.reshape(-1, 2).astype(np.float32)
        inside = [cv.pointPolygonTest(np.delete(pts, i, axis=0), (float(pts[i][0]), float(pts[i][1])), False) > 0
                  for i in range(len(pts))]
        return sum(inside) == 1

    def motion_toggled(self, st):
        self.motionPrev = None
        self.motionGroup.setVisible(bool(st))

    #  a new blur size makes the kept frames incomparable: start over
    def motion_tuned(self, _v=None):
        self.motionPrev = None

    def motion_pick_color(self):
        if self.motionColor is not None:
            self.motionColor = None
            self.motionColorBtn.setText("Original")
            self.motionColorBtn.setStyleSheet("")
            return
        c = QColorDialog.getColor(QtGui.QColor(0, 255, 0), self, "Motion pixel colour")
        if c.isValid():
            self.motionColor = c
            self.motionColorBtn.setText(c.name())
            self.motionColorBtn.setStyleSheet("QPushButton { background: %s; color: %s; }"
                                              % (c.name(), "black" if c.lightness() > 127 else "white"))

    #  motion detection as in qtocrcardsmtg.py: grey, blurred, the difference from the frames
    #  before (the most any of the last N), eroded (specks of noise go), thresholded; pixels
    #  outside it are blacked out, the rest keep their colour or take the one picked
    def motion_only(self, img):
        import collections
        sp = self.motionSpins
        n, k, th, er = (sp[x].value() for x in ("frames", "blur", "thresh", "erode"))
        k |= 1
        gray = cv.cvtColor(img, cv.COLOR_BGR2GRAY) if img.ndim == 3 else img
        blur = cv.GaussianBlur(gray, (k, k), 0) if k > 1 else gray
        prev = getattr(self, "motionPrev", None)
        if prev is None or prev.maxlen != n or (prev and prev[0].shape != blur.shape):
            prev = self.motionPrev = collections.deque(maxlen=n)
        if not prev:
            prev.append(blur)
            return np.zeros_like(img)
        diff = np.max([cv.absdiff(p, blur) for p in prev], axis=0)
        prev.append(blur)
        if er > 0:
            diff = cv.erode(diff, np.ones((er, er), np.uint8), iterations=1)
        mask = cv.threshold(diff, th, 255, cv.THRESH_BINARY)[1]
        outlines = []
        if self.shapeBox.isChecked() and img.ndim == 3:
            #  shown: the moving shapes' colour patches, instead of the bare motion
            mask, outlines = self.motion_shapes(mask, img)
        if self.motionColor is None:
            out = cv.bitwise_and(img, img, mask=mask)
        else:
            out = np.zeros_like(img)
            c = self.motionColor
            out[mask > 0] = (c.blue(), c.green(), c.red()) if img.ndim == 3 else c.lightness()
        if outlines and out.ndim == 3:
            cv.drawContours(out, outlines, -1, (0, 255, 255), 2)
        return out

    #  map a point on the displayed pixmap to device input coordinates
    #  returns None when no frame is shown yet or the point is off the image
    #
    def label_to_device(self, x, y):
        if not self.pixmap_width or not self.pixmap_height:
            return None
        if x < 0 or y < 0 or x >= self.pixmap_width or y >= self.pixmap_height:
            return None
        (device_width, device_height, _X11_width, _X11_height) = self.actions.resolutions()
        dx = int(x * int(device_width) / self.pixmap_width)
        dy = int(y * int(device_height) / self.pixmap_height)
        return (dx, dy)

    #  a drag on the video goes to the phone as it happens, like a finger: down on press, moves
    #  as the mouse moves, up on release, so a held tower follows with its range circle.
    #  Android: input motionevent lines into one adb shell kept open (no process per move).
    #  iOS: WebDriverAgent only takes whole gestures, so the drag goes on release; meanwhile
    #  the video shows where the finger is, a red dot (dragAt)
    #
    LIVE_MOVE_S = 0.08          # at most a move this often (each one's an input command)

    def live_shell(self, line):
        if GUEST_OS != GUEST_OS_ANDROID:
            return False
        sh = getattr(self, "liveSh", None)
        if sh is None or sh.poll() is not None:
            sh = self.liveSh = subprocess.Popen(["adb", "-s", self.actions.serial(), "shell"], stdin=subprocess.PIPE,
                                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, text=True)
        try:
            sh.stdin.write(line + "\n")
            sh.stdin.flush()
            return True
        except OSError:
            self.liveSh = None
            return False

    def label_mouse_move(self, e):
        d = self.label_to_device(e.x(), e.y())
        if d:
            self.lblXY.setText('X, Y ( %d, %d ) device ( %d, %d )' % (e.x(), e.y(), d[0], d[1]))
        else:
            self.lblXY.setText('X, Y ( %d, %d )' % (e.x(), e.y()))
        if self.pressPos is None or d is None:
            return
        self.dragAt = (e.x(), e.y())
        now = time.time()
        if getattr(self, "liveDown", False) and now - self.liveSent >= self.LIVE_MOVE_S:
            self.live_shell("input motionevent MOVE %d %d" % d)
            self.liveSent = now

    def label_mouse_press(self, e):
        if e.button() != Qt.LeftButton:
            return
        self.pressPos = (e.x(), e.y())
        self.pressTime = datetime.now()
        #  copy, the video thread may still hand this array around
        self.pressFrame = None if self.lastFrame is None else self.lastFrame.copy()
        d = self.label_to_device(e.x(), e.y())
        self.liveDown = d is not None and self.live_shell("input motionevent DOWN %d %d" % d)
        self.liveSent = time.time()
        self.dragAt = (e.x(), e.y())

    #  continue numbering after whatever click_NNNN_* files already exist
    #
    def next_click_number(self):
        n = 0
        for name in os.listdir(self.clickDir):
            m = re.match(r"click_(\d+)_", name)
            if m:
                n = max(n, int(m.group(1)))
        return n + 1

    def save_click_frame(self, action):
        if self.pressFrame is None:
            return
        self.write_click(action, self.pressFrame, self.pressTime)
        self.pressFrame = None

    def write_click(self, action, frame, when, log="clicks.log"):
        name = "click_%04d_%s.png" % (self.clickCount, action)
        cv.imwrite(os.path.join(self.clickDir, name), frame, [cv.IMWRITE_PNG_COMPRESSION, 1])
        with open(os.path.join(self.clickDir, log), "a") as f:
            f.write("%s %s\n" % (when.isoformat(timespec='milliseconds'), name))
        self.clickCount += 1

    def touch_toggled(self, state):
        if state:
            if self.touchThread is None:
                self.touchThread = TouchThread(self.actions.serial())
                self.touchThread.touch_down.connect(self.touch_down)
                self.touchThread.touch_up.connect(self.touch_up)
                self.touchThread.start()
        elif self.touchThread is not None:
            self.touchThread.stop()
            self.touchThread.wait(3000)
            self.touchThread = None
            print("TOUCH stopped")

    #  a touch on the phone: saved like a click, as click_NNNN_touch_<action>.png, but
    #  logged in touches.log
    #
    def touch_down(self):
        self.touchFrame = None if self.lastFrame is None else self.lastFrame.copy()
        self.touchTime = datetime.now()
        if getattr(self, "thread", None) is not None:
            self.thread.record_touch("down")

    def touch_up(self, action):
        print("TOUCH %s" % action)
        if getattr(self, "thread", None) is not None:
            self.thread.record_touch("up", action)
        if self.touchFrame is not None:
            self.write_click("touch_" + action, self.touchFrame, self.touchTime, log="touches.log")
        self.touchFrame = None

    #  short click -> tap, drag -> swipe (tower placement), long press -> hold
    #
    def label_mouse_release(self, e):
        if e.button() != Qt.LeftButton or self.pressPos == None:
            return
        start = self.label_to_device(self.pressPos[0], self.pressPos[1])
        end = self.label_to_device(e.x(), e.y())
        ms = int((datetime.now() - self.pressTime).total_seconds() * 1000)
        self.pressPos = None
        if start == None:
            return
        if end == None:
            end = start
        moved = abs(end[0] - start[0]) + abs(end[1] - start[1])
        serial = self.actions.serial()
        if moved < 10 and ms < 300:
            cmd = "input tap %d %d" % (start[0], start[1])
            action = "tap_%dx%d" % start
        else:
            cmd = "input swipe %d %d %d %d %d" % (start[0], start[1], end[0], end[1], max(ms, 100))
            action = "swipe_%dx%d_%dx%d_%dms" % (start[0], start[1], end[0], end[1], max(ms, 100))
        self.save_click_frame(action)
        self.dragAt = None
        if getattr(self, "liveDown", False):
            #  the finger's been down since the press: lift it where the mouse let go
            self.liveDown = False
            self.live_shell("input motionevent UP %d %d" % end)
            return
        if self.debug:
            print(cmd)
        #  without waiting, so the GUI thread doesn't stall on the round trip
        guest_shell(serial, cmd, popen=True)

    def snapshot(self):
        self.takeSnapshot = True

    def beacon_toggled(self, state):
        if state:
            self.thread.start_beacon()
        else:
            self.thread.stop_beacon()

    @staticmethod
    def title_label(text, color):
        label = QLabel(text)
        label.setStyleSheet("QLabel { color: %s; font-weight: bold; }" % color)
        return label

    def show_stats(self, parts):
        for k, label in self.statLabels.items():
            label.setText(parts.get(k, "-"))

    def show_currencies(self, cur):
        for k, label in self.curLabels.items():
            if cur.get(k) is not None:
                label.setText(format(cur[k], ","))
        if cur.get("level") is not None:
            self.levelLabel.setText(str(cur["level"]))
        if cur.get("exp") is not None and cur.get("exp_need") is not None:
            self.expLabel.setText("{:,} / {:,} ({:,} to next)".format(cur["exp"], cur["exp_need"], cur["exp_need"] - cur["exp"]))

    #  every quest read, numbered with its reward; the dropdown offers the understood ones,
    #  set to the best rewarded
    def show_quests(self, quests):
        self.questListLabel.setText("\n".join("%d. %s: %s -> %s" % (i + 1, q["tier"], q["text"], q["action"])
                                              for i, q in enumerate(quests)) or "current quests empty")
        self.questCombo.blockSignals(True)
        self.questCombo.clear()
        for i, q in enumerate(quests):
            if q["action"] != "unknown":
                self.questCombo.addItem("%d. %s: %s" % (i + 1, q["tier"], q["text"]), q["text"])
        best = self.thread.pick_quest(quests)
        keep = self.questCombo.findData(best["text"] if best else None)
        self.questCombo.setCurrentIndex(max(keep, 0))
        self.questCombo.blockSignals(False)
        self.quest_selected(self.questCombo.currentIndex())

    def quest_selected(self, i):
        self.thread.questSelected = self.questCombo.itemData(i) if i >= 0 else None

    #  the size the controls page needs to show everything without scrollbars (the scroll
    #  area itself hints small)
    def controls_need(self):
        inner = self.controlsScroll.widget().sizeHint()
        top = max(self.detachBtn.sizeHint().height(), self.deviceGroup.sizeHint().height())
        w = max(inner.width(), self.detachBtn.sizeHint().width() + self.deviceGroup.sizeHint().width()) + 40
        return w, inner.height() + top + 50

    #  the window (or the detached Controls one) grown to fit what's shown, within the screen.
    #  At start and on every relayout of the controls; never shrunk, so it doesn't jump about
    def fit_window(self):
        w, h = self.controls_need()
        avail = QApplication.primaryScreen().availableGeometry()
        if self.controlsWindow is not None:
            win = self.controlsWindow
        else:
            win = self
            video = self.tabs.widget(0).sizeHint()
            bar = self.tabs.tabBar().sizeHint().height()
            w, h = max(w, video.width()) + 30, max(h, video.height()) + bar + 30
        w, h = min(max(w, win.width()), avail.width()), min(max(h, win.height()), avail.height())
        if (w, h) != (win.width(), win.height()):
            win.resize(w, h)

    def eventFilter(self, obj, event):
        if obj is self.controlsScroll.widget() and event.type() == QEvent.LayoutRequest:
            QTimer.singleShot(0, self.fit_window)
        return super().eventFilter(obj, event)

    def toggle_controls(self):
        if self.controlsWindow is None:
            self.tabs.removeTab(self.tabs.indexOf(self.controlsPage))
            self.controlsWindow = DetachedWindow(self.toggle_controls)
            self.controlsWindow.setWindowTitle("Controls")
            QVBoxLayout(self.controlsWindow).addWidget(self.controlsPage)
            self.controlsPage.show()
            self.detachBtn.setText("Attach")
            #  big enough that nothing's clipped
            w, h = self.controls_need()
            self.controlsWindow.resize(w, h)
            self.controlsWindow.show()
        else:
            w, self.controlsWindow = self.controlsWindow, None
            self.tabs.addTab(self.controlsPage, "Controls")
            self.detachBtn.setText("Detach")
            w.closing = None
            w.close()

    def quest_toggled(self, state):
        if state:
            self.thread.start_quests()
        else:
            self.thread.stop_quests()

    def beacon_time_toggled(self, state):
        if state:
            self.thread.start_beacon_time()
        else:
            self.thread.stop_beacon()

    def beacon_time_read(self, text):
        if text == "busy":
            #  Find Beacon is driving the device; unticking must not stop it
            self.beaconTimeBox.blockSignals(True)
            self.beaconTimeBox.setChecked(False)
            self.beaconTimeBox.blockSignals(False)
            return
        self.beaconTimeLabel.setText(text)
        self.beaconTimeBox.setChecked(False)

    #  every map the bot knows of (the adventure list's index and the map names list), A to Z
    @staticmethod
    def known_maps():
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "maps_index.json")
        names = []
        if os.path.exists(path):
            with open(path) as f:
                maps = json.load(f)["maps"]
            names = sorted(maps, key=lambda m: (maps[m]["area_index"], maps[m]["slot"]))
        return sorted(set(names) | set(VideoThread.MAP_NAMES.values()), key=str.lower)

    #  slots on this window (not lambdas) so Qt runs them on the GUI thread: the signals come
    #  from the video thread
    #
    #  the map last seen on a title screen is the one picked in Navigate's list (not moved)
    @pyqtSlot(str)
    def navigate_select(self, title):
        i = self.navCombo.findText(title, Qt.MatchFixedString)
        if i >= 0:
            self.navCombo.setCurrentIndex(i)

    @pyqtSlot(str)
    def beacon_finished(self, result):
        self.beaconBox.setChecked(False)

    @pyqtSlot()
    def quest_started(self):
        self.playBox.setChecked(True)

    @pyqtSlot(dict)
    def show_hud(self, row):
        for k, v in row.items():
            self.hudLabels[k].setText(v)

    def navigate_changed(self, *_):
        self.thread.navigateTo = self.navCombo.currentText() if self.navBox.isChecked() else None
        self.thread.navNext = 0

    #  unticked by hand: everything the bot is driving stops, the placement in progress and
    #  Campaign/Quests (which would start Play again) included
    def play_toggled(self, state):
        if state:
            self.thread.start_autoplay()
            return
        self.thread.stop_autoplay("stopped by hand")
        self.thread.placer = None
        self.thread.stop_quests()
        for box in (self.questBox, self.campaignBox):
            box.blockSignals(True)
            box.setChecked(False)
            box.blockSignals(False)

    #  the bot stopping Play itself (a defeat, between campaign games) only unticks the box
    def autoplay_stopped(self):
        self.playBox.blockSignals(True)
        self.playBox.setChecked(False)
        self.playBox.blockSignals(False)

    def place_clicked(self):
        if self.thread.placer is not None:
            print("place: stopped")
            self.thread.placer = None
            return
        if not self.thread.place_character("Finn", "near beginning"):
            self.thread.start_place("Finn", (611, 540))

    #  only one process can stream from /dev/video0 and the frame loop already
    #  does, so ffmpeg -f v4l2 gets "Device or resource busy".  Instead the loop
    #  pipes each raw frame it reads into ffmpeg, timestamped as it arrives
    #  (-use_wallclock_as_timestamps) so the video keeps real time even when
    #  frames come unevenly; .mkv stays playable if ffmpeg dies before finishing
    #
    def ffmpeg_clicked(self):
        if self.ffmpegProc is not None:
            self.stop_ffmpeg()
            return
        videoDir = os.path.join(self.clickDir, "video")
        os.makedirs(videoDir, exist_ok=True)
        self.ffmpegOut = os.path.join(videoDir, "record_%s.mkv" % datetime.now().strftime("%Y%m%d_%H%M%S"))
        self.ffmpegSize = None
        self.ffmpegBtn.setText('Stop')
        self.thread.recorder = self.record_frame

    #  called from the video thread with each captured frame; ffmpeg starts on the
    #  first one, since the raw pipe needs the frame size up front
    #
    def record_frame(self, img):
        h, w = img.shape[:2]
        if self.ffmpegProc is None:
            cmd = ["ffmpeg", "-hide_banner", "-loglevel", "error", "-use_wallclock_as_timestamps", "1",
                   "-f", "rawvideo", "-pix_fmt", "bgr24", "-s", "%dx%d" % (w, h), "-i", "-",
                   "-c:v", "libx264", "-preset", "veryfast", "-pix_fmt", "yuv420p", "-fps_mode", "passthrough",
                   self.ffmpegOut]
            print(" ".join(cmd))
            self.ffmpegProc = subprocess.Popen(cmd, stdin=subprocess.PIPE)
            self.ffmpegSize = (w, h)
        if (w, h) != self.ffmpegSize:
            return
        try:
            self.ffmpegProc.stdin.write(img.tobytes())
        except (BrokenPipeError, ValueError):
            #  ffmpeg died; drop the recorder, the button resets on Stop
            self.thread.recorder = None

    #  closing stdin is end of input, so ffmpeg finishes the file and exits
    #
    def stop_ffmpeg(self):
        self.thread.recorder = None
        #  let a write already in progress on the video thread finish
        time.sleep(0.1)
        proc = self.ffmpegProc
        self.ffmpegProc = None
        self.ffmpegBtn.setText('Record')
        if proc is None:
            return
        try:
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
        print("recording stopped, ffmpeg exit %s: %s" % (proc.returncode, self.ffmpegOut))

    #  numbering continues after whatever frame_NNNNNN.png files already exist
    #
    def record_clicked(self):
        if self.recording:
            self.recording = False
            self.recordBtn.setText('Start')
            return
        self.videoDir = os.path.join(self.clickDir, "video")
        os.makedirs(self.videoDir, exist_ok=True)
        n = 0
        for name in os.listdir(self.videoDir):
            m = re.match(r"frame_(\d+)", name)
            if m:
                n = max(n, int(m.group(1)))
        self.recordCount = n + 1
        self.recording = True
        self.recordBtn.setText('Stop')

    def save_video_frame(self, img):
        name = "frame_%06d.png" % self.recordCount
        cv.imwrite(os.path.join(self.videoDir, name), img, [cv.IMWRITE_PNG_COMPRESSION, 1])
        self.recordCount += 1

    def replay_clicked(self):
        self.replaying = True
        #self.replayFrame = 0
        #self.replay = True
        count = 0
        for frame in self.replayFrames:
            count += 1
            self.image_label.setPixmap(frame)
            QtTest.QTest.qWait(int(1000 * self.replayFreq * 3))
        self.replaying = False


    def convert_cv_qt(self, cv_img):
        if (self.takeSnapshot == True):
            self.takeSnapshot = False
            cv.imwrite("snapshot.png", cv_img)
        """Convert from an opencv image to QPixmap"""
        rgb_image = cv.cvtColor(cv_img, cv2.COLOR_BGR2RGB)
        h, w, ch = rgb_image.shape
        bytes_per_line = ch * w
        convert_to_Qt_format = QtGui.QImage(rgb_image.data, w, h, bytes_per_line, QtGui.QImage.Format_RGB888)
        p = convert_to_Qt_format.scaled(self.display_width, self.display_height, Qt.KeepAspectRatio)
        return QPixmap.fromImage(p)
    
if __name__=="__main__":
    signal.signal(signal.SIGINT, handler)
    signal.signal(signal.SIGTERM, handler)
    signal.signal(signal.SIGHUP, handler)
    sys.excepthook = excepthook
    app = QApplication(sys.argv)
    #  the window icon (every window: the main one and Controls when detached).  GNOME's task
    #  list takes it from the .desktop file named by the app id instead:
    #  ~/.local/share/applications/bloons-adventure.desktop (Icon= bloonstd.png)
    app.setWindowIcon(QtGui.QIcon(os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloonstd.png")))
    app.setApplicationName("bloons-adventure")
    app.setDesktopFileName("bloons-adventure")
    main = ImageControl(actions=Aethric())
    main.run()
    cb = main.checkBoxes.checkedButton()
    if (cb):
        print("imageOptionClicked: ",cb.text())
        main.check_option_signal.emit(cb.text())
    main.show()
    #  Qt's C++ loop blocks Python signal handlers; a no-op timer gives Ctrl-C a chance to run
    sigTimer = QTimer()
    sigTimer.timeout.connect(lambda: None)
    sigTimer.start(250)
    rc = app.exec_()
    sys.exit(rc)

