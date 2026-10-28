#!/usr/bin/env python3
#  Build a whole-game autoplay script from touches recorded with "Record adb events".
#
#  Every touch made during the game (from the first frame showing the HUD up to the
#  Level Complete banner) becomes a step that the bot replays when the HUD reaches the
#  same round and shows at least the money the frame had when the touch was made.
#  The gap to the touch before is kept, so panels have time to open.
#
#  A placement (a card dragged off the panel onto the map, the pending tower dragged
#  about, the check mark tapped) becomes one "place" step instead: the drag that dropped
#  the card, and where the pending tower's range circle was when the check was tapped.
#  The bot drops the card the same way, then bloons_place.Placer moves the tower to
#  that spot until the circle isn't red and taps the check.
#
#  usage: bloons_build_script.py <recording dir> <map title>
#  writes bloons_adventure/maps/<map>/script.json
#
import cv2 as cv
import json
import numpy as np
import os
import re
import sys
from datetime import datetime

sys.argv, args = sys.argv[:1], sys.argv[1:]
import bloons_adventure as ba
import bloons_path as path_lib
import bloons_place as place_lib

src, title = args
key = ba.VideoThread.map_key(title)
reader = ba.VideoThread.__new__(ba.VideoThread)
reader.replay = None
reader.layoutDx = 0
reader.load_replay()
rd = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "replay")
banner = cv.imread(os.path.join(rd, place_lib.BANNER_KEY))
chars = json.load(open(os.path.join(rd, "chars.json")))
for n in chars["names"]:
    n["img"] = cv.imread(os.path.join(rd, n["key"]))
lock = cv.imread(os.path.join(rd, "lock_icon.png"))
done = ba.VideoThread.white_letters(cv.imread(os.path.join(rd, "end_level_complete.png")))

steps = []
prev_start = None
rnd = None
for line in open(os.path.join(src, "touches.log")):
    stamp, name = line.split()
    m = re.match(r"click_\d+_touch_(tap|swipe)_(\d+)x(\d+)(?:_(\d+)x(\d+)_(\d+)ms)?\.png$", name)
    if not m:
        continue
    #  frames and touches both made as if the phone were at 90 (see replay_ref)
    ref = reader.replay_ref(cv.imread(os.path.join(src, name)))
    dx = 2 * reader.layoutDx
    #  the phone dimmed or locked: these touches woke and unlocked it, which the bot's
    #  lock_watcher does itself (a dialog darkens the frame too, but only to about 60)
    if ref.mean() < 35 or cv.minMaxLoc(cv.matchTemplate(ref[235:355, 525:645], lock, cv.TM_CCOEFF_NORMED))[1] > 0.8:
        print("%s: screen dimmed or locked, skipped" % name)
        continue
    if cv.minMaxLoc(cv.matchTemplate(ba.VideoThread.white_letters(ref[100:300, 250:950]), done, cv.TM_CCOEFF_NORMED))[1] > 0.8:
        break
    hud = {}
    for h in reader.replay["hud"]:
        roi = reader.locate_hud(ref, h)
        if roi is not None:
            hud[h["name"]] = reader.read_hud(h["name"], roi)
    r = hud.get("round")
    r = int(r.split("/")[0]) if r and re.fullmatch(r"\d+/\d+", r) else None
    ms = int(m.group(6)) if m.group(6) else 0
    start = datetime.fromisoformat(stamp).timestamp() - ms / 1000
    if rnd is None and r is None:
        #  still on the map screen: the first step's gap runs from the last tap here
        prev_start = start
        continue
    #  a panel over the HUD, or a misread: the round can't go backwards
    if r is None or (rnd is not None and r < rnd):
        r = rnd
    rnd = r
    step = {"touch": name, "round": r, "money": hud.get("money"),
            "after": round(start - prev_start, 2) if prev_start else 0,
            "x": int(m.group(2)) - dx, "y": int(m.group(3))}
    if m.group(1) == "swipe":
        step.update({"x2": int(m.group(4)) - dx, "y2": int(m.group(5)), "ms": ms})
    step["frame"] = ref
    steps.append(step)
    prev_start = start

#  device x of the panel's left edge
PANEL_X = place_lib.MAP_RIGHT * 2 + 10

def panel_drop(s):
    return "x2" in s and s["x"] >= PANEL_X and s["x2"] < PANEL_X

#  the card's art above its price tag (the finger, and scrcpy's touch circle, sit on the
#  tag); returns the grey crop and where the drag starts relative to its corner
CARD_ART = (-22, -52, 22, -18)

def card_art(ref, x, y):
    #  a card grabbed by its face rather than its tag: the art is taken from above the
    #  card's own price tag (green, or red when unaffordable), found below the touch
    hsv = cv.cvtColor(ref, cv.COLOR_BGR2HSV)
    h, s = hsv[..., 0], hsv[..., 1]
    tag = (s > 120) & (hsv[..., 2] > 90) & (((h > 45) & (h < 80)) | (h < 8) | (h > 170))
    ax, ay = max(0, x - 40), max(0, y - 30)
    n, _, stats, _ = cv.connectedComponentsWithStats(tag[ay:y + 50, ax:x + 40].astype(np.uint8))
    best = None
    for bx, by, bw, bh, _ in stats[1:]:
        bx, by = bx + ax, by + ay
        if not (30 <= bw <= 62 and 8 <= bh <= 24) or not (bx - 6 <= x <= bx + bw + 6) or not (by - 40 <= y <= by + bh + 6):
            continue
        if best is None or by < best[1]:
            best = (bx + bw // 2, by)
    if best is not None:
        cx, t = int(best[0]), int(best[1])
        x0, y0 = cx - 22, t - 34
        return cv.cvtColor(ref[y0:t - 2, x0:cx + 22], cv.COLOR_BGR2GRAY), (x - x0, y - y0)
    x0, y0, x1, y1 = CARD_ART
    return cv.cvtColor(ref[y + y0:y + y1, x + x0:x + x1], cv.COLOR_BGR2GRAY), (-x0, -y0)

def char_name(ref):
    x, y, w, h = chars["name_search"]
    score, name = max((cv.minMaxLoc(cv.matchTemplate(ref[y:y + h, x:x + w], n["img"], cv.TM_CCOEFF_NORMED))[1], n["name"])
                      for n in chars["names"] if n["img"] is not None)
    return name if score > 0.8 else "ally"

#  the panel as the game starts, before any scrolling: a card found on it has its slot
#  (0-11, chars.json order) and so its character; one that isn't is an ally further down
first_panel = steps[0]["frame"]

#  An ally's art can pass for a character's (Gumbald's pink head scored 0.86 on PB's card,
#  greyed or reskinned real ones 0.81-0.99): below 0.95 the name strip has to agree
def card_slot(art, off, name):
    x0, y0, x1, y1 = place_lib.PANEL_BOX
    area = cv.cvtColor(first_panel[y0:y1, x0:x1], cv.COLOR_BGR2GRAY)
    _, score, _, loc = cv.minMaxLoc(cv.matchTemplate(area, art, cv.TM_CCOEFF_NORMED))
    if score < 0.8:
        return None
    fx, fy = x0 + loc[0] + off[0], y0 + loc[1] + off[1]
    d = [np.hypot(fx - (tx + 30), fy - (ty + 12)) for tx, ty in chars["tags"]]
    i = int(np.argmin(d))
    if d[i] > 30 or (score < 0.95 and chars["chars"][i] != name):
        return None
    return i

start_money = next((s["money"] for s in steps if s["money"] is not None), None)
os.makedirs(os.path.join(path_lib.map_dir(key), "cards"), exist_ok=True)
#  scrolls of the panel: the place steps find their cards themselves
steps = [s for s in steps if not ("x2" in s and s["x"] >= PANEL_X and s["x2"] >= PANEL_X)]
pending = [place_lib.find_banner(s["frame"], banner) is not None for s in steps]
out_steps = []
i = 0
while i < len(steps):
    j = i
    #  drops that didn't start a placement are followed by another drop
    while panel_drop(steps[j]) and j + 1 < len(steps) and panel_drop(steps[j + 1]) and not pending[j + 1]:
        j += 1
    if panel_drop(steps[j]) and j + 1 < len(steps) and pending[j + 1]:
        k = j + 1
        while k + 1 < len(steps) and pending[k + 1]:
            k += 1
        d, c = steps[j], steps[k]
        spot = place_lib.find_pending(c["frame"], d["frame"])
        if spot is not None:
            art, off = card_art(d["frame"], d["x"] // 2, d["y"] // 2)
            slot = card_slot(art, off, char_name(c["frame"]))
            card = os.path.join("cards", d["touch"])
            cv.imwrite(os.path.join(path_lib.map_dir(key), card), art)
            out_steps.append({"card": card, "card_off": list(off), "slot": slot,
                              "character": chars["chars"][slot] if slot is not None and slot < 10 else "ally","touch": d["touch"], "round": steps[i]["round"], "money": d["money"],
                              "after": steps[i]["after"], "place": char_name(c["frame"]),
                              "drop": [d["x"] // 2, d["y"] // 2, d["x2"] // 2, d["y2"] // 2, d["ms"]],
                              "target": [int(round(spot[0])), int(round(spot[1]))], "confirm": c["touch"]})
            i = k + 1
            continue
        print("%s: placement but no pending tower found, kept as recorded" % d["touch"])
    elif panel_drop(steps[i]):
        #  a card drop that started no placement (the card greyed out for lack of money);
        #  replayed live it can take, and leave a tower waiting on its check mark
        print("%s: card drop with no placement after it, left out" % steps[i]["touch"])
        i += 1
        continue
    out_steps.append(steps[i])
    i += 1
steps = out_steps
for s in steps:
    s.pop("frame", None)

os.makedirs(path_lib.map_dir(key), exist_ok=True)
out = os.path.join(path_lib.map_dir(key), "script.json")
with open(out, "w") as f:
    json.dump({"map": title, "from": os.path.abspath(src), "start_money": start_money, "steps": steps}, f, indent=1)
print("%d steps (%d placements) over rounds %s..%s written to %s" % (len(steps), sum("place" in s for s in steps),
      steps[0]["round"], steps[-1]["round"], out))
