#!/usr/bin/env python3
#  Build the HUD digit library bloons_adventure.py reads lives, money and round with.
#
#  The HUD font never changes, so instead of tesseract each white glyph in a HUD
#  box is matched against labelled samples of the same font.  The samples come
#  from snapshots whose HUD values are known (LABELS below); each entry names a
#  frame, the box, and the text drawn in it after the icon:
#     lives  "158"        money  "$2790"  (commas are too short to count as glyphs)
#     round  "ROUND13"    or "ROUND62/75" on adventure maps (the ':' is too short too)
#
#  Writes replay/glyphs.npz next to replay.json.  Add a labelled frame whenever
#  a reading comes out wrong, then rerun.
#
#  usage: bloons_build_glyphs.py [dir]
#
import cv2 as cv
import numpy as np
import json
import os
import sys

GLYPH_SIZE = (10, 14)

LABELS = [
    ("../char_select_left.png", "money", "$419"),
    ("../activated_abilities.png", "money", "$177"),
    ("../char_select_right_abilities.png", "money", "$9057"),
    ("../char_select_right.png", "money", "$10167"),
    ("click_0016_tap_1162x63.png", "money", "$1225"),
    ("click_0016_tap_1162x63.png", "lives", "1"),
    ("click_0022_tap_1984x1001.png", "money", "$525"),
    ("click_0023_tap_538x46.png", "money", "$556"),
    ("click_0024_swipe_238x39_238x39_307ms.png", "money", "$568"),
    ("click_0025_tap_1796x56.png", "money", "$743"),
    ("click_0026_tap_999x860.png", "round", "ROUND62/75"),
    ("click_0028_tap_282x243.png", "money", "$12740"),
    ("click_0029_tap_2074x68.png", "round", "ROUND64/75"),
    ("click_0031_tap_2037x80.png", "money", "$2942"),
    ("click_0034_tap_1818x977.png", "lives", "158"),
    ("click_0034_tap_1818x977.png", "round", "ROUND13"),
    ("click_0038_tap_1725x589.png", "round", "ROUND14"),
    ("click_0041_tap_1737x387.png", "money", "$3349"),
    ("click_0042_tap_1750x553.png", "money", "$3064"),
    ("click_0043_tap_1850x41.png", "money", "$2515"),
    ("click_0045_tap_1847x41.png", "lives", "158"),
    ("click_0045_tap_1847x41.png", "money", "$2790"),
]

#  find a HUD box by its icon/label key along the top strip; same walk as
#  VideoThread.locate_hud in bloons_adventure.py
#
def locate(img, h, key):
    kh, kw = key.shape[:2]
    bh = h["box"][3]
    strip = img[0:min(img.shape[0], h["box"][1] + bh + 30)]
    _minVal, maxVal, _minLoc, (x, y) = cv.minMaxLoc(cv.matchTemplate(strip, key, cv.TM_CCOEFF_NORMED))
    if maxVal < 0.8:
        return None
    row = min(img.shape[0] - 1, y + bh // 2)
    line = img[row:row + 1]
    m = (cv.inRange(line, (60, 10, 0), (150, 70, 40)) | cv.inRange(line, (170, 170, 170), (255, 255, 255)))[0]
    xe = x + kw
    last = xe
    gap = 0
    while xe < img.shape[1] - 1 and gap < 6:
        xe += 1
        if m[xe]:
            gap = 0
            last = xe
        else:
            gap += 1
    return img[y:y + bh, x:last + 1]

#  white glyphs left to right, each cut out and resized to GLYPH_SIZE;
#  same rules as VideoThread.hud_glyphs
#
def glyphs(roi, name):
    if name in ("lives", "money"):
        roi = roi[:, roi.shape[0]:]
    w = cv.threshold(cv.cvtColor(roi, cv.COLOR_BGR2GRAY), 170, 255, cv.THRESH_BINARY)[1]
    n, lab, st, _ = cv.connectedComponentsWithStats(w, 8)
    hh = w.shape[0]
    tall = sorted([i for i in range(1, n) if st[i][3] >= 0.3 * hh and st[i][4] >= 8
                   and st[i][0] + st[i][2] < w.shape[1] - 1], key=lambda i: st[i][0])
    out = []
    for i in tall:
        X, Y, W, Hh, _A = st[i]
        g = (lab[Y:Y + Hh, X:X + W] == i).astype(np.uint8) * 255
        out.append(cv.resize(g, GLYPH_SIZE, interpolation=cv.INTER_AREA))
    return out

if __name__ == "__main__":
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure")
    rd = os.path.join(d, "replay")
    with open(os.path.join(rd, "replay.json")) as f:
        hud = {h["name"]: h for h in json.load(f)["hud"]}
    keys = {n: cv.imread(os.path.join(rd, h["key"])) for n, h in hud.items()}

    chars = []
    imgs = []
    for (fname, name, text) in LABELS:
        img = cv.imread(os.path.join(d, fname))
        if img is None:
            print("missing %s, skipped" % fname)
            continue
        roi = locate(img, hud[name], keys[name])
        gl = [] if roi is None else glyphs(roi, name)
        if len(gl) != len(text):
            print("skip %s %s: want %d glyphs for %r, found %d" % (fname, name, len(text), text, len(gl)))
            continue
        chars += list(text)
        imgs += gl
    np.savez_compressed(os.path.join(rd, "glyphs.npz"), chars=np.array(chars), glyphs=np.array(imgs))
    print("wrote %s: %d samples of %s" % (os.path.join(rd, "glyphs.npz"), len(chars), "".join(sorted(set(chars)))))
