#!/usr/bin/env python3
#  Keep the bot running unattended: start bloons_adventure.py (Campaign, Record adb
#  events) and restart it when it stops getting anywhere:
#     no progress line (SCRIPT, PLAN, HUD, NAV, CAMPAIGN, BEACON, GAME, PLAY, QUEST)
#     for STALL seconds; the last LOOP progress lines being the same few over and over;
#     or every MAX_RUN seconds regardless.
#  Each run's output goes to bloons_adventure/runs/<time>.log, restarts to watchdog.log.
#
#  usage: bloons_watchdog.py [extra bot options]
#
import os
import queue
import re
import threading
import signal
import subprocess
import sys
import time
from collections import deque
from datetime import datetime

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.join(HERE, "bloons_adventure", "runs")
WLOG = os.path.join(HERE, "bloons_adventure", "watchdog.log")
STALL = 8 * 60
LOOP = 30
MAX_RUN = 2 * 3600
PROGRESS = re.compile(r"^(SCRIPT|PLAN|HUD|NAV|CAMPAIGN|BEACON|GAME|PLAY|QUEST|place )")
DECISION = re.compile(r"^(SCRIPT|PLAN|NAV|CAMPAIGN|BEACON|PLAY|QUEST)")
BOT = [os.path.join(HERE, ".venv", "bin", "python"), "-u", os.path.join(HERE, "bloons_adventure.py"),
       "--campaign", "--record-touches"] + sys.argv[1:]

def note(msg):
    line = "%s %s" % (datetime.now().isoformat(timespec="seconds"), msg)
    print(line, flush=True)
    with open(WLOG, "a") as f:
        f.write(line + "\n")

def run_once():
    os.makedirs(RUNS, exist_ok=True)
    log = os.path.join(RUNS, datetime.now().strftime("%Y%m%d_%H%M%S") + ".log")
    out = open(log, "w")
    proc = subprocess.Popen(BOT, cwd=HERE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
    note("started pid %d, log %s" % (proc.pid, log))
    lines = queue.Queue()
    threading.Thread(target=lambda: [lines.put(l) for l in proc.stdout], daemon=True).start()
    start = last = time.time()
    recent = deque(maxlen=LOOP)
    why = None
    while proc.poll() is None:
        try:
            line = lines.get(timeout=1)
        except queue.Empty:
            line = None
        if line:
            out.write(line)
            out.flush()
            if PROGRESS.match(line):
                last = time.time()
                #  decisions only (a round's HUD line, a drag, a decree repeat by design);
                #  numbers change while the same thing is retried, so compare without them
                if DECISION.match(line) and "Royal Decree" not in line:
                    recent.append(re.sub(r"\d+", "#", line.strip()))
                    if len(recent) == LOOP and len(set(recent)) <= 3:
                        why = "the same %d lines over and over: %s" % (len(set(recent)), recent[-1])
                        break
            continue
        if time.time() - last > STALL:
            why = "no progress for %d minutes" % (STALL // 60)
        elif time.time() - start > MAX_RUN:
            why = "running %d hours, routine restart" % (MAX_RUN // 3600)
        if why:
            break
    if proc.poll() is None:
        note("restarting: %s" % why)
        proc.send_signal(signal.SIGTERM)
        try:
            proc.wait(timeout=20)
        except subprocess.TimeoutExpired:
            proc.kill()
    else:
        note("bot exited with %s" % proc.returncode)
    out.close()

def main():
    while True:
        run_once()
        time.sleep(5)

main()
