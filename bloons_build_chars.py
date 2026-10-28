#!/usr/bin/env python3
#  Build what bloons_adventure.py reads the character panel with.
#
#  The panel on the right is a fixed 2x6 grid of character cards, each with a
#  cost tag under it: white text on green when affordable, red on grey when
#  not.  The selected character's name shows in the box at the top right.
#
#     name keys   one crop of that name box per character (the font is too
#                 stylised for OCR, but each name box is a fixed image)
#     tags.npz    labelled glyph samples of the tag font, white and red kept
#                 apart since red is read from a different channel
#
#  The same tag_glyphs()/read_tag() are used by the program, so the library
#  and the reader can't drift apart.
#
#  usage: bloons_build_chars.py [dir]
#
import cv2 as cv
import numpy as np
import json
import os
import re
import sys

GLYPH_SIZE = (10, 14)

#  cards in panel order, left to right then down; costs never change
CHARS = ["Finn", "C4 Charlie", "PB", "Hunter Marceline", "Supermonkey", "Tuxedo Jake",
         "Ice King", "Sai", "Flame Princess", "Commander Cassie", "BMO", "Tiny Manticore"]
COSTS = [300, 600, 650, 1200, 3000, 400, 700, 800, 900, 2800, 700, 840]

#  top left of each cost tag; the selected card is drawn bigger, which shifts
#  its tag a few px, so tag_roi() pads the cell
TAGS = [(961 + 65 * c, 112 + 64 * r) for r in range(6) for c in range(2)]
NAME_BOX = (960, 10, 80, 20)        # x, y, w, h of the name text, no portrait
NAME_SEARCH = (945, 0, 155, 45)     # where to look for it

#  frames with the panel open, whose tags are the COSTS above
TAG_FRAMES = ["click_0002_tap_1976x197.png", "click_0006_tap_1984x41.png", "click_0014_tap_1989x453.png"]
#  frame showing each character selected, in CHARS order
NAME_FRAMES = ["click_%04d" % n for n in range(3, 37, 3)]

def tag_roi(img, i):
    x, y = TAGS[i]
    return img[y - 2:y + 28, x - 3:x + 66]

#  glyphs of one tag left to right, and whether it's red (can't afford)
#
def tag_glyphs(roi):
    hsv = cv.cvtColor(roi, cv.COLOR_BGR2HSV)
    red = cv.inRange(hsv, (0, 120, 150), (10, 255, 255)) | cv.inRange(hsv, (170, 120, 150), (180, 255, 255))
    isred = cv.countNonZero(red) > 60
    if isred:
        #  how much redder than anything else; a hard mask merges the 2 and 3
        b, g, r = cv.split(roi.astype(np.int16))
        soft = np.clip(r - np.maximum(g, b), 0, 255).astype(np.uint8)
        w = cv.threshold(soft, 0, 255, cv.THRESH_BINARY + cv.THRESH_OTSU)[1]
    else:
        soft = None
        w = cv.threshold(cv.cvtColor(roi, cv.COLOR_BGR2GRAY), 170, 255, cv.THRESH_BINARY)[1]
    n, lab, st, _ = cv.connectedComponentsWithStats(w, 4)
    ks = [i for i in range(1, n) if 9 <= st[i][3] <= 17 and st[i][2] <= 14 and st[i][4] >= 8]
    if ks:
        #  one line of text: drop whatever doesn't share its baseline
        base = np.median([st[i][1] + st[i][3] for i in ks])
        ks = [i for i in ks if abs(st[i][1] + st[i][3] - base) <= 3]
    out = []
    for i in sorted(ks, key=lambda i: st[i][0]):
        X, Y, W, H, _A = st[i]
        src = soft[Y:Y + H, X:X + W] if isred else (lab[Y:Y + H, X:X + W] == i).astype(np.uint8) * 255
        out.append(cv.resize(src, GLYPH_SIZE, interpolation=cv.INTER_AREA).astype(np.float32))
    return out, isred

#  zero mean, unit length: a dot product of two of these is TM_CCOEFF_NORMED
#
def unit(g):
    v = g.ravel() - g.mean()
    n = np.linalg.norm(v)
    return v / n if n else v

#  (cost, red) or None; lib is {False: (chars, vectors), True: (chars, vectors)}
#
def read_tag(roi, lib, min_score=0.6):
    gl, isred = tag_glyphs(roi)
    chars, vecs = lib[isred]
    if not gl or not len(chars):
        return None
    scores = np.array([unit(g) for g in gl]) @ vecs.T
    best = scores.argmax(axis=1)
    if scores[np.arange(len(gl)), best].min() < min_score:
        return None
    m = re.fullmatch(r"\$(\d+)", "".join(chars[best]))
    return (int(m.group(1)), isred) if m else None

if __name__ == "__main__":
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure")
    rd = os.path.join(d, "replay")
    os.makedirs(rd, exist_ok=True)

    chars, imgs, reds = [], [], []
    for fname in TAG_FRAMES:
        img = cv.imread(os.path.join(d, fname))
        if img is None:
            print("missing %s, skipped" % fname)
            continue
        for i, cost in enumerate(COSTS):
            text = "$%d" % cost
            gl, isred = tag_glyphs(tag_roi(img, i))
            if len(gl) != len(text):
                print("skip %s %s: want %d glyphs for %r, found %d" % (fname, CHARS[i], len(text), text, len(gl)))
                continue
            chars += list(text)
            imgs += gl
            reds += [isred] * len(gl)
    np.savez_compressed(os.path.join(rd, "tags.npz"), chars=np.array(chars), glyphs=np.array(imgs), red=np.array(reds))
    print("wrote tags.npz: %d samples (%d red)" % (len(chars), sum(reds)))

    x, y, w, h = NAME_BOX
    names = []
    for name, prefix in zip(CHARS, NAME_FRAMES):
        files = [f for f in os.listdir(d) if f.startswith(prefix + "_")]
        if not files:
            print("missing %s* for %s, skipped" % (prefix, name))
            continue
        img = cv.imread(os.path.join(d, files[0]))
        kname = "char_%s.png" % name.lower().replace(" ", "_")
        cv.imwrite(os.path.join(rd, kname), img[y:y + h, x:x + w])
        names.append({"name": name, "key": kname})

    with open(os.path.join(rd, "chars.json"), "w") as f:
        json.dump({"chars": CHARS, "costs": COSTS, "tags": TAGS, "name_search": NAME_SEARCH,
                   "names": names}, f, indent=2)
    print("wrote chars.json: %d name keys" % len(names))
