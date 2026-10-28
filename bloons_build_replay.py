#!/usr/bin/env python3
#  Build a replay script from the click snapshots bloons_adventure.py saves.
#
#  For each click_NNNN_*.png, find a shape with a discernable edge around the
#  clicked point, crop it as a template, and record where the click falls
#  inside it.  At runtime the replay template matches each step against the
#  live frame and clicks only once the step's template is found.
#
#  The last --hud clicks are not replayed: they mark dark HUD boxes with white
#  text (lives, money, round, left to right) that get read by OCR instead.
#
#  usage: bloons_build_replay.py [dir] [--hud 3] [--first N] [--last N]
#
import cv2 as cv
import numpy as np
import glob
import json
import optparse
import os
import re

#  frames are scrcpy -m1170 of a 2340 wide device; filenames carry device coords
FRAME_SCALE = 0.5

def parse_click(path):
    name = os.path.basename(path)
    m = re.match(r"click_(\d+)_(tap|swipe)_(\d+)x(\d+)(?:_(\d+)x(\d+)_(\d+)ms)?\.png$", name)
    if not m:
        return None
    c = {"n": int(m.group(1)), "kind": m.group(2), "file": name,
         "x": int(int(m.group(3)) * FRAME_SCALE), "y": int(int(m.group(4)) * FRAME_SCALE)}
    if m.group(5):
        c["ex"] = int(int(m.group(5)) * FRAME_SCALE)
        c["ey"] = int(int(m.group(6)) * FRAME_SCALE)
        c["ms"] = int(m.group(7))
    return c

#  candidate boxes around pt, smallest first: enclosing contours from a few edge
#  maps, flood filled regions of the clicked colour, then plain growing squares
#
def candidate_boxes(img, pt):
    H, W = img.shape[:2]
    gray = cv.cvtColor(img, cv.COLOR_BGR2GRAY)
    blur = cv.GaussianBlur(gray, (3, 3), 0)
    boxes = set()
    for lo, hi in ((30, 90), (50, 150), (80, 200)):
        edges = cv.Canny(blur, lo, hi)
        for dil in (False, True):
            e = cv.dilate(edges, np.ones((3, 3), np.uint8)) if dil else edges
            contours, _ = cv.findContours(e, cv.RETR_TREE, cv.CHAIN_APPROX_SIMPLE)
            for c in contours:
                x, y, w, h = cv.boundingRect(c)
                if cv.pointPolygonTest(c, pt, False) >= 0:
                    boxes.add((x, y, w, h, "contour"))
    for tol in (6, 12, 20, 32):
        mask = np.zeros((H + 2, W + 2), np.uint8)
        flags = 8 | cv.FLOODFILL_MASK_ONLY | cv.FLOODFILL_FIXED_RANGE | (255 << 8)
        cv.floodFill(img.copy(), mask, pt, 0, (tol,) * 3, (tol,) * 3, flags)
        ys, xs = np.nonzero(mask[1:-1, 1:-1])
        if len(xs):
            boxes.add((int(xs.min()), int(ys.min()), int(xs.max() - xs.min() + 1),
                       int(ys.max() - ys.min() + 1), "fill"))
    for s in (24, 32, 48, 64, 96, 128):
        x = max(0, pt[0] - s // 2)
        y = max(0, pt[1] - s // 2)
        boxes.add((x, y, min(s, W - x), min(s, H - y), "square"))

    keep = []
    for (x, y, w, h, src) in boxes:
        if w < 16 or h < 12:
            continue
        if w * h > 0.25 * W * H:
            continue
        #  a click on the very edge of a box can't be located inside it
        if not (x <= pt[0] < x + w and y <= pt[1] < y + h):
            continue
        #  real shapes first, smallest first; plain squares only as a fallback
        keep.append((src == "square", w * h, x, y, w, h, src))
    return [k[1:] for k in sorted(keep)]

#  mean gradient magnitude along the box border: how discernable its edge is
#
def edge_strength(gray, x, y, w, h):
    gx = cv.Sobel(gray, cv.CV_32F, 1, 0)
    gy = cv.Sobel(gray, cv.CV_32F, 0, 1)
    mag = cv.magnitude(gx, gy)
    border = np.concatenate([mag[y, x:x + w], mag[y + h - 1, x:x + w],
                             mag[y:y + h, x], mag[y:y + h, x + w - 1]])
    return float(border.mean())

#  best score and runner up (outside the best match's footprint) for tmpl in img
#
def match_scores(img, tmpl):
    res = cv.matchTemplate(img, tmpl, cv.TM_CCOEFF_NORMED)
    _, best, _, loc = cv.minMaxLoc(res)
    h, w = tmpl.shape[:2]
    res[max(0, loc[1] - h // 2):loc[1] + h // 2 + 1, max(0, loc[0] - w // 2):loc[0] + w // 2 + 1] = -1
    _, second, _, _ = cv.minMaxLoc(res)
    return best, loc, second

#  smallest candidate that is unique on its own frame and has a real edge
#
def pick_template(img, pt, max_second=0.8, min_edge=40.0):
    gray = cv.cvtColor(img, cv.COLOR_BGR2GRAY)
    for (_, x, y, w, h, src) in candidate_boxes(img, pt):
        tmpl = img[y:y + h, x:x + w]
        if float(tmpl.std()) < 8:
            continue
        _, _, second = match_scores(img, tmpl)
        edge = edge_strength(gray, x, y, w, h)
        if second <= max_second and (src != "square" and edge >= min_edge or src == "square"):
            return {"box": [x, y, w, h], "source": src, "second": round(second, 3),
                    "edge": round(edge, 1)}
    return None

#  HUD boxes are dark navy (BGR ~100,34,0) behind white text
#
def navy_mask(img):
    mask = cv.inRange(img, (60, 10, 0), (150, 70, 40))
    #  close across the white glyphs so each box is one region; the money icon's
    #  ring separates lives from money by only a few px, so keep the kernel narrow
    return cv.morphologyEx(mask, cv.MORPH_CLOSE, np.ones((15, 3), np.uint8))

#  the navy box holding pt (or nearest to it), as [x, y, w, h]
#
def hud_box(img, pt):
    n, labels, stats, _ = cv.connectedComponentsWithStats(navy_mask(img), 8)
    for r in range(0, 16):
        y0, y1 = max(0, pt[1] - r), min(img.shape[0], pt[1] + r + 1)
        x0, x1 = max(0, pt[0] - r), min(img.shape[1], pt[0] + r + 1)
        labs = set(labels[y0:y1, x0:x1].ravel().tolist()) - {0}
        best = None
        for lab in labs:
            x, y, w, h, area = stats[lab]
            if 30 <= w <= 400 and 10 <= h <= 60:
                if best is None or w * h < best[2] * best[3]:
                    best = (int(x), int(y), int(w), int(h))
        if best:
            return list(best)
    return None

if __name__ == "__main__":
    parser = optparse.OptionParser(usage="%prog [dir]")
    parser.add_option("--hud", type="int", default=3, help="last N clicks mark HUD values")
    parser.add_option("--first", type="int", default=None, help="first click number to use")
    parser.add_option("--last", type="int", default=None, help="last click number to use")
    (o, args) = parser.parse_args()
    d = args[0] if args else os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure")

    clicks = [c for c in (parse_click(p) for p in glob.glob(os.path.join(d, "click_*.png"))) if c]
    clicks.sort(key=lambda c: c["n"])
    if o.first is not None:
        clicks = [c for c in clicks if c["n"] >= o.first]
    if o.last is not None:
        clicks = [c for c in clicks if c["n"] <= o.last]
    hud = clicks[len(clicks) - o.hud:] if o.hud else []
    steps = clicks[:len(clicks) - o.hud] if o.hud else clicks

    out = os.path.join(d, "replay")
    os.makedirs(out, exist_ok=True)

    first = cv.imread(os.path.join(d, clicks[0]["file"]))
    script = {"frame_scale": FRAME_SCALE, "frame_size": [first.shape[1], first.shape[0]],
              "steps": [], "hud": []}
    for c in steps:
        img = cv.imread(os.path.join(d, c["file"]))
        pt = (c["x"], c["y"])
        step = {"n": c["n"], "kind": c["kind"], "source_frame": c["file"]}
        pick = pick_template(img, pt)
        if pick:
            x, y, w, h = pick["box"]
            tname = "step_%04d.png" % c["n"]
            cv.imwrite(os.path.join(out, tname), img[y:y + h, x:x + w])
            step.update({"template": tname, "box": pick["box"], "offset": [pt[0] - x, pt[1] - y],
                         "shape": pick["source"], "second": pick["second"], "edge": pick["edge"]})
        else:
            step["template"] = None
        step["point"] = [pt[0], pt[1]]
        if c["kind"] == "swipe":
            #  drops are tower placements on the map: an absolute spot, not a shape
            step.update({"end": [c["ex"], c["ey"]], "ms": c["ms"]})
        script["steps"].append(step)
        print("%04d %-5s pt=%-11s %s" % (c["n"], c["kind"], pt,
              "box=%s %s second=%.2f edge=%.0f" % (pick["box"], pick["source"], pick["second"], pick["edge"]) if pick else "NO TEMPLATE"))

    names = ["lives", "money", "round"]
    for name, c in zip(names, sorted(hud, key=lambda c: c["x"])):
        img = cv.imread(os.path.join(d, c["file"]))
        box = hud_box(img, (c["x"], c["y"]))
        h = {"name": name, "box": box, "source_frame": c["file"], "key": None}
        if box:
            #  the part that never changes (heart / money bag icon, "ROUND:" label)
            #  tells the in-game HUD apart from menus with navy boxes in the same spot
            x, y, w, bh = box
            kw = bh if name in ("lives", "money") else w // 2
            kname = "hud_%s.png" % name
            cv.imwrite(os.path.join(out, kname), img[y:y + bh, x:x + kw])
            h["key"] = kname
        script["hud"].append(h)
        print("hud %-6s pt=(%d, %d) box=%s" % (name, c["x"], c["y"], box))

    with open(os.path.join(out, "replay.json"), "w") as f:
        json.dump(script, f, indent=2)
    print("wrote %s" % os.path.join(out, "replay.json"))
