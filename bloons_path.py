#!/usr/bin/env python3
#  Learn a map's bloon path from the arrows shown before round 1.
#
#  Every game opens with arrows running along the path the bloons will take:
#  green at the start, fading through orange to red at the end.  Diffing each
#  frame against the one before shows only what just changed, and of that only
#  the newest arrow is a large, saturated, bright blob (swaying trees are small,
#  the chimney smoke is white).  So each frame gives at most one new point on
#  the path, and their order in time is the order along the path, laps and all
#  (apple_arrows: in at the bottom, two laps of the ring, out at the bottom).
#
#  From the ordered points:
#     track      the path drawn as wide as the road; nothing can be placed on it
#     coverage   for every map pixel, how much path (counted once per pass, so a
#                ring the bloons go round twice counts twice) lies within RANGE
#     spots      the best coverage peaks, spaced apart: where to try placing
#
#  The arrows can't show trees, rocks or the house, so a spot may still turn out
#  red when placing; the Placer probes around it.
#
#  Stored per map in bloons_adventure/maps/<map>/: path.json, track.png,
#  coverage.npy, path.png (a picture to check by eye).
#
#     usage: bloons_path.py <frames dir> <map name>
#
import cv2 as cv
import numpy as np
import glob
import json
import os
import sys

MAP_RIGHT = 940         # map ends here, the character panel starts
MAP_TOP = 75            # HUD above
ARROW_TOP = 45          # arrows run up to here between the HUD boxes
DIFF = 40               # a pixel changed this much since the last frame
MIN_AREA = 120          # newest arrow is 190-370 px; partial ones show at 120-150
MERGE = 12              # a detection this close to the last point is the same arrow
TRACK_W = 40            # road width
RANGE = 100             # coverage radius; roughly a short-range character
SPOT_GAP = 45           # spots at least this far apart
SPOTS = 12
GIVE_UP = 400           # no arrow at all within this many frames: not the arrow intro
MAX_FRAMES = 3000       # never learn for longer than this (~2 min)
LEAD = 10               # first arrow after this many arrowless frames: caught the intro from its start
CONFIRM = 20            # a far detection is the arrows restarting if another follows it within this many frames
GREEN = 50              # arrow hues: green at the entry ...
RED = 15                # ... red towards the exit
REDS = 3                # this many red arrows, then a green one: the arrows started again
NEAR = 20               # an arrow this close to a learned point is that point again
REPEAT = 4              # the first this many points seen again in order: the run is repeating
SCENE = 0.05            # more than this share of the map changed at once: a screen change, not arrows
JUMP = 130              # arrows step 40-50 px (108 across the smoke); a farther detection is noise

def maps_dir():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "bloons_adventure", "maps")

def map_dir(name):
    return os.path.join(maps_dir(), name)

#  the newest arrow in img, from what changed since prev: (x, y, hue) or None
#
def find_arrow(img, prev):
    d = cv.absdiff(img, prev).max(2)
    if np.count_nonzero(d[MAP_TOP:, :MAP_RIGHT] > DIFF) > SCENE * (img.shape[0] - MAP_TOP) * MAP_RIGHT:
        return None
    hsv = cv.cvtColor(img, cv.COLOR_BGR2HSV)
    h = hsv[..., 0]
    #  green through orange is hue 60 down to 0; red wraps round to 165-180
    m = ((d > DIFF) & (hsv[..., 1] > 120) & (hsv[..., 2] > 150) & ((h < 72) | (h > 165))).astype(np.uint8)
    m[:ARROW_TOP] = 0
    m[:, MAP_RIGHT:] = 0
    m = cv.morphologyEx(m, cv.MORPH_OPEN, np.ones((3, 3), np.uint8))
    n, lab, st, c = cv.connectedComponentsWithStats(m)
    best = max(range(1, n), key=lambda j: st[j][4], default=None)
    if best is None or st[best][4] < MIN_AREA:
        return None
    hue = int(np.median(h[lab == best]))
    return (float(c[best][0]), float(c[best][1]), hue if hue < 90 else hue - 180)

#  feed frames one at a time; done is set when one whole run of the arrows has been
#  seen, which is known when the arrows start it again: green after red, a jump back to
#  a far entry, or the run's first points coming round again in order.  Pauses don't
#  count for anything (arrows leave the screen between lanes on some maps).  The intro
#  repeats until play is pressed, so learning may begin partway through a run: that
#  partial run is dropped at the restart and the next whole one learned
#
class PathLearner:
    def __init__(self):
        self.prev = None
        self.points = []        # (x, y, hue, frame)
        self.frames = 0
        self.lastHit = 0
        self.reds = 0
        self.match = 0          # how many of the run's first points have just been seen again
        self.matchAt = 0        # len(points) when that repeat began
        self.whole = False      # points start at the entry, not partway through a run
        self.far = None         # a detection too far from the last point: noise or a restart
        self.done = False

    def start(self, a, whole):
        self.points = [(a[0], a[1], a[2], self.frames)]
        self.reds = 0
        self.match = 0
        self.whole = whole
        self.lastHit = self.frames

    def add(self, a):
        x, y = self.points[-1][:2]
        dist = lambda p, q: np.hypot(p[0] - q[0], p[1] - q[1])
        step = dist(a, (x, y))
        if step <= JUMP:
            self.far = None
            self.lastHit = self.frames
            if self.whole and self.repeating(a):
                del self.points[self.matchAt:]
                self.done = True
            elif self.reds >= REDS and a[2] > GREEN:
                #  the arrows started again, at an entry next to the exit
                if self.whole:
                    self.done = True
                else:
                    self.start(a, True)
            elif step > MERGE:
                self.points.append((a[0], a[1], a[2], self.frames))
                self.reds += a[2] < RED
        elif self.far is not None and self.frames - self.far[3] <= CONFIRM and 0 < dist(a, self.far) <= JUMP:
            #  the arrows started again at the entry
            if self.whole and len(self.points) >= 5:
                self.done = True
            else:
                self.start(self.far, True)
                self.far = None
                self.add(a)
        else:
            self.far = (a[0], a[1], a[2], self.frames)

    #  is a the next of the run's first points coming round again?
    def repeating(self, a):
        if len(self.points) <= 2 * REPEAT:
            return False
        near = lambda i: np.hypot(a[0] - self.points[i][0], a[1] - self.points[i][1]) <= NEAR
        if self.match and near(self.match - 1):
            pass                                # the same arrow again
        elif near(self.match):
            if self.match == 0:
                self.matchAt = len(self.points)
            self.match += 1
        else:
            self.match = 0
            if near(0):
                self.matchAt = len(self.points)
                self.match = 1
        return self.match >= REPEAT

    def feed(self, img):
        if self.done:
            return
        self.frames += 1
        if self.prev is not None:
            a = find_arrow(img, self.prev)
            if a is not None:
                if self.points:
                    self.add(a)
                else:
                    self.start(a, self.frames > LEAD and a[2] > GREEN)
        self.prev = img.copy()
        if not self.points and self.frames > GIVE_UP:
            self.done = True
        elif self.frames > MAX_FRAMES:
            self.done = True

#  the path along the points, every `step` px; returns an (n, 2) array
#
def resample(points, step=3.0):
    p = np.array([(x, y) for x, y, *_ in points], np.float64)
    seg = np.hypot(*np.diff(p, axis=0).T)
    s = np.concatenate([[0], np.cumsum(seg)])
    t = np.arange(0, s[-1], step)
    return np.column_stack([np.interp(t, s, p[:, 0]), np.interp(t, s, p[:, 1])]), s

#  what the points say about placing: track mask, coverage map, best spots
#
def analyse(points, shape, rng=RANGE):
    h, w = shape[:2]
    samples, s = resample(points)
    track = np.zeros((h, w), np.uint8)
    cv.polylines(track, [np.round([(x, y) for x, y, *_ in points]).astype(np.int32)], False, 255, TRACK_W)

    hits = np.zeros((h, w), np.float32)
    for x, y in samples:
        xi, yi = int(round(x)), int(round(y))
        if 0 <= xi < w and 0 <= yi < h:
            hits[yi, xi] += 1
    disc = np.zeros((2 * rng + 1, 2 * rng + 1), np.float32)
    cv.circle(disc, (rng, rng), rng, 1, -1)
    coverage = cv.filter2D(hits, -1, disc, borderType=cv.BORDER_CONSTANT) * 3.0     # px of path in range
    coverage[track > 0] = 0
    coverage[:MAP_TOP] = 0
    coverage[:, MAP_RIGHT:] = 0

    spots = []
    left = coverage.copy()
    while len(spots) < SPOTS:
        _, v, _, (x, y) = cv.minMaxLoc(left)
        if v <= 0:
            break
        spots.append({"x": int(x), "y": int(y), "coverage": int(v)})
        cv.circle(left, (int(x), int(y)), SPOT_GAP, 0, -1)
    return track, coverage, spots, float(s[-1])

#  learn a map's path from the arrow intro and store it under the map's name.
#  frames is any iterable of frames (1170x540 BGR); it's read until the arrows
#  finish, so a live source can keep running after; a None frame aborts.  Returns
#  the path dict with its track and coverage, as load_path gives it, or None if no
#  arrows were seen or it was aborted.  Not stored when map_name is None.
#
def learn_path(frames, map_name, store=True):
    learner = PathLearner()
    shape = None
    for img in frames:
        if img is None:
            #  the source gave up (left the game): don't store a partial path
            return None
        shape = img.shape
        learner.feed(img)
        if learner.done:
            break
    if len(learner.points) < 5:
        return None
    pts = learner.points
    track, coverage, spots, length = analyse(pts, shape)
    _, s = resample(pts)
    path = {
        "map": map_name,
        "frame": [shape[1], shape[0]],
        "range": RANGE,
        "length": round(length, 1),
        "entry": [round(pts[0][0]), round(pts[0][1])],
        "exit": [round(pts[-1][0]), round(pts[-1][1])],
        #  progress 0 at the entry to 1 at the exit; hue goes 60 (green) to 0 (red)
        "points": [{"x": round(x), "y": round(y), "hue": hue, "progress": round(si / s[-1], 3)}
                   for (x, y, hue, _), si in zip(pts, s)],
        "spots": spots,
    }
    if store and map_name:
        save_path(path, track, coverage, last=learner.prev)
    path["track"] = track
    path["coverage"] = coverage
    return path

def save_path(path, track, coverage, last=None):
    d = map_dir(path["map"])
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "path.json"), "w") as f:
        json.dump(path, f, indent=1)
    cv.imwrite(os.path.join(d, "track.png"), track)
    np.save(os.path.join(d, "coverage.npy"), coverage.astype(np.float32))
    if last is not None:
        cv.imwrite(os.path.join(d, "path.png"), draw_path(last, path, track, coverage))

#  stored path for a map, with track and coverage loaded, or None
#
def load_path(map_name):
    d = map_dir(map_name)
    p = os.path.join(d, "path.json")
    if not os.path.exists(p):
        return None
    with open(p) as f:
        path = json.load(f)
    path["track"] = cv.imread(os.path.join(d, "track.png"), cv.IMREAD_GRAYSCALE)
    path["coverage"] = np.load(os.path.join(d, "coverage.npy"))
    return path

def draw_path(img, path, track, coverage):
    vis = img.copy()
    heat = cv.applyColorMap((coverage / max(coverage.max(), 1) * 255).astype(np.uint8), cv.COLORMAP_JET)
    on = coverage > 0
    vis[on] = (vis[on] * 0.5 + heat[on] * 0.5).astype(np.uint8)
    vis[track > 0] = (vis[track > 0] * 0.6).astype(np.uint8)
    pts = path["points"]
    for a, b in zip(pts, pts[1:]):
        g = int(255 * (1 - a["progress"]))
        cv.line(vis, (a["x"], a["y"]), (b["x"], b["y"]), (0, g, 255 - g), 2)
    for i, sp in enumerate(path["spots"]):
        cv.circle(vis, (sp["x"], sp["y"]), 6, (255, 255, 255), -1)
        cv.putText(vis, str(i + 1), (sp["x"] + 8, sp["y"] + 5), cv.FONT_HERSHEY_SIMPLEX, 0.5, (255, 255, 255), 1)
    return vis

if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit("usage: bloons_path.py <frames dir> <map name>")
    files = sorted(glob.glob(os.path.join(sys.argv[1], "*.png")))
    path = learn_path((cv.imread(f) for f in files), sys.argv[2])
    if path is None:
        sys.exit("no arrows found")
    print("%s: %d points, %.0f px long, entry %s exit %s" % (
        path["map"], len(path["points"]), path["length"], path["entry"], path["exit"]))
    for i, sp in enumerate(path["spots"]):
        print("  spot %d (%d,%d) %d px of path in range" % (i + 1, sp["x"], sp["y"], sp["coverage"]))
    print("wrote %s" % map_dir(path["map"]))
