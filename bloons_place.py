#!/usr/bin/env python3
#  Place a character at a spot on the map, closed loop.
#
#  Placing goes: drag the character's card onto the map -> a pending tower shows
#  with its range circle (red where it can't go, darkened grey where it can) and
#  a "Confirm character placement?" banner -> drag the pending tower to adjust
#  -> tap the check mark.
#
#  Drags don't move the pending tower 1:1 (in place_finn_apple1 some moved it a
#  third of the swipe), so each drag is followed by finding where the tower
#  actually is and dragging again by what's left, until it's within tolerance
#  and the circle isn't red.
#
#  Everything here is in frame coordinates (the 1170x540 scrcpy frame); the
#  caller scales actions to the device.  Placer.step() is fed frames and returns
#  the next action, so it can be tested offline against saved snapshots:
#
#     usage: bloons_place.py [click dir]     replays the decisions on a click dir
#
import cv2 as cv
import numpy as np
import glob
import json
import os
import re
import sys
import time

#  confirm banner: template from place_finn_apple1, buttons relative to its corner
BANNER_KEY = "place_banner.png"
BANNER_BOX = (395, 8, 215, 67)
CHECK_OFF = (180, 35)
CANCEL_OFF = (20, 30)
MAP_RIGHT = 940         # map ends here, the panel starts
MAP_TOP = 75            # HUD and banner above
MAP_BOTTOM = 455        # the powers bar and the ability button below: drops there don't take
SLOP = 15               # frame px a drag loses before the pending tower follows
#  a picked spot at least this far left of the panel: a drop that close to the cards
#  reads as a tap on the card (its info opens) and nothing is placed
PANEL_GAP = 60
#  a drop that didn't take is aimed again this far off, a different way each time
RETRY_NUDGE = 20
RETRY_DIRS = [(-1, 0), (0, -1), (1, 0), (0, 1), (-1, -1), (1, -1), (-1, 1), (1, 1)]


#  spot moved RETRY_NUDGE the k-th way round, kept on the map and off the panel (a way that
#  the map's edge stops is passed over for the next)
def nudged(spot, k):
    for j in range(k, k + len(RETRY_DIRS)):
        dx, dy = RETRY_DIRS[j % len(RETRY_DIRS)]
        c = (int(min(max(spot[0] + dx * RETRY_NUDGE, 90), MAP_RIGHT - PANEL_GAP)),
             int(min(max(spot[1] + dy * RETRY_NUDGE, MAP_TOP + 10), MAP_BOTTOM)))
        if c != (int(spot[0]), int(spot[1])):
            return c
    return c

#  where to put a character, in terms of the map's learned path (bloons_path):
#     near X               as close to that point of the path as it will go
#     range just outside X the range circle's edge just past that point, the tower
#                          set back so the circle covers the path right after it
#                          (beginning) or right before it (end)
#     best coverage        the most path in range, laps counted per pass
#  progress 0 is where bloons come in, 1 where they leave
PLACE_OPTIONS = {
    "near beginning": ("near", 0.0),
    "near middle": ("near", 0.5),
    "near end": ("near", 1.0),
    "range just outside beginning": ("edge", 0.0),
    "range just outside middle": ("edge", 0.5),
    "range just outside end": ("edge", 1.0),
    "best coverage": ("best", None),
    #  support towers (Jake's music, PB's presence) buff what's in their range
    "near towers": ("towers", None),
    #  eco towers (Monkey Farmer): beside the road where it covers least of it
    "far from path": ("far", None),
}
CLEAR = 8               # tower centre at least this far off the road's edge
#  the road (the arrows' path) is the one ground known not to take a tower, and the ground
#  beside it the ground known to: spots are looked for within this of it, anywhere only if
#  nothing there is free (further out is trees, water, rocks, the map's void)
NEAR_BAND = 35
GRID = 4                # candidate spacing
EDGE_GAP = 8            # 'just outside': the point this far beyond the circle
WINDOW = 0.25           # 'just outside': cover this much progress next to the point
AVOID_R = 14            # a spot seen red rules out this much round it
#  'far from path': in the band by the road, the least road in range (the good spots left
#  for combat towers), with room from the map's edges, the buttons on it and spots seen red
#  counted up to EDGE_ENOUGH
EDGE_ENOUGH = 60
#  buttons and readouts drawn over the map, (x0, y0, x1, y1): lives and money, the round,
#  the ! (ability) button, the powers bar
MAP_UI = [(46, 0, 300, 50), (790, 0, 940, 50), (875, 465, 945, 540), (46, 465, 630, 540)]
TAKEN_R = 45            # and a placed tower this much (35 let Jake land on Finn)

#  where a click dir placed its character: the last swipe before the confirm tap
#  is the final adjustment; returns (frame x, y) of its end
#
def parse_click(name):
    m = re.search(r"click_(\d+)_(tap|swipe)_(\d+)x(\d+)(?:_(\d+)x(\d+)_(\d+)ms)?", name)
    if not m:
        return None
    c = {"n": int(m.group(1)), "kind": m.group(2), "x": int(m.group(3)) // 2, "y": int(m.group(4)) // 2}
    if m.group(5):
        c.update({"ex": int(m.group(5)) // 2, "ey": int(m.group(6)) // 2, "ms": int(m.group(7))})
    return c

#  the pending tower: what changed against the map before the drop, as one blob,
#  fitted with a circle on the part of its edge that isn't cut by the frame.
#  returns (cx, cy, r, red) or None
#
#  a just placed tower's sprite: what's new since before the drop within NEAR_R of where it
#  was thought to be (the path's arrows are new too, further off), (x, y) or None
NEAR_R = 90

def find_sprite_near(img, base, at, ignore=()):
    if at is None:
        return None
    d = np.abs(img.astype(np.int16) - base.astype(np.int16)).sum(2)[:, :MAP_RIGHT]
    m = (d > 40).astype(np.uint8) * 255
    near = np.zeros_like(m)
    cv.circle(near, (int(at[0]), int(at[1])), NEAR_R, 255, -1)
    m &= near
    m[:MAP_TOP, :] = 0
    for x, y in ignore:
        cv.circle(m, (int(x), int(y)), IGNORE_R, 0, -1)
    m = cv.morphologyEx(m, cv.MORPH_OPEN, np.ones((3, 3), np.uint8))
    n, lab, st, cen = cv.connectedComponentsWithStats(m)
    best = [j for j in range(1, n) if 150 <= st[j][4] <= 6000]
    if not best:
        return None
    j = max(best, key=lambda j: st[j][4])
    #  the sprite stands above its spot: its middle, a little low
    return (float(cen[j][0]), float(cen[j][1]) + 10)

IGNORE_R = 45           # towers already down animate (Jake's music rings): not the pending one

def find_pending(img, base, ignore=()):
    d = np.abs(img.astype(np.int16) - base.astype(np.int16)).sum(2)[:, :MAP_RIGHT]
    m = (d > 25).astype(np.uint8) * 255
    for x, y in ignore:
        cv.circle(m, (int(x), int(y)), IGNORE_R, 0, -1)
    m[:MAP_TOP, :] = 0
    m = cv.morphologyEx(m, cv.MORPH_OPEN, np.ones((5, 5), np.uint8))
    m = cv.morphologyEx(m, cv.MORPH_CLOSE, np.ones((9, 9), np.uint8))
    n, lab, st, _ = cv.connectedComponentsWithStats(m)
    if n < 2:
        return None
    j = max(range(1, n), key=lambda j: st[j][4])
    if st[j][4] < 400:
        return None
    disc = (lab == j).astype(np.uint8)
    if st[j][4] < 3000:
        #  a range circle barely bigger than the sprite (Monkey Farmer): taken by its middle
        #  red there means its base disc tinted pure red; the farmer's own orange and
        #  brown don't count
        x, y, w, h, _ = st[j]
        hsv = cv.cvtColor(img[:, :MAP_RIGHT], cv.COLOR_BGR2HSV)[disc > 0]
        pure = ((hsv[:, 0] < 6) | (hsv[:, 0] > 170)) & (hsv[:, 1] > 90) & (hsv[:, 2] > 100)
        return (float(x + w / 2), float(y + h / 2), float(max(w, h) / 2), bool(pure.mean() > 0.15))
    cs, _ = cv.findContours(disc, cv.RETR_EXTERNAL, cv.CHAIN_APPROX_NONE)
    p = max(cs, key=len)[:, 0, :].astype(np.float64)
    p = p[(p[:, 0] > 2) & (p[:, 0] < MAP_RIGHT - 3) & (p[:, 1] > MAP_TOP + 2) & (p[:, 1] < img.shape[0] - 3)]
    if len(p) < 20:
        return None
    A = np.column_stack([2 * p[:, 0], 2 * p[:, 1], np.ones(len(p))])
    cx, cy, c = np.linalg.lstsq(A, (p ** 2).sum(1), rcond=None)[0]
    r = float(np.sqrt(max(c + cx * cx + cy * cy, 0)))
    #  invalid spots tint the disc red, valid ones only darken it
    #  on white snow red can't rise (it's already 255): the tint shows as green and blue
    #  dropping, so it's measured as redness, red over the other two
    def redness(im):
        i = im[:, :MAP_RIGHT].astype(np.int16)
        return (i[..., 2] - (i[..., 1] + i[..., 0]) // 2)[disc > 0].mean()
    red = float(redness(img)) - float(redness(base)) > 20
    return (float(cx), float(cy), r, red)

def find_banner(img, key, min_score=0.6):
    _, score, _, loc = cv.minMaxLoc(cv.matchTemplate(img[0:110], key, cv.TM_CCOEFF_NORMED))
    return loc if score >= min_score else None

#  the panel's card list, where find_card looks; PANEL_X is the middle of it, for scrolling
PANEL_BOX = (MAP_RIGHT + 5, 40, 1110, 525)
PANEL_X = 1028
SCROLLS = 12

#  top left of a card's art on the panel, or None.  Grey so a card greyed out for lack
#  of money still matches
#
def find_card(img, key, min_score=0.8):
    x0, y0, x1, y1 = PANEL_BOX
    area = cv.cvtColor(img[y0:y1, x0:x1], cv.COLOR_BGR2GRAY)
    _, score, _, loc = cv.minMaxLoc(cv.matchTemplate(area, key, cv.TM_CCOEFF_NORMED))
    return (x0 + loc[0], y0 + loc[1]) if score >= min_score else None

#  one placement.  step() returns ("swipe", x1, y1, x2, y2, ms), ("tap", x, y),
#  ("wait",), ("done",) or ("fail", why); call it again on frames after each
#  action has had time to show
#
class Placer:
    def __init__(self, name, card, target, banner_key, tolerance=12, max_drags=14, drop=None, card_key=None,
                 ignore=(), drop_and_lock=True, r_guess=60):
        self.name = name
        #  the game's Drop & Lock setting.  Off: a drag ends in place if the spot is valid (no
        #  confirm banner); on an invalid one the tower stays held, red ringed, its card blank
        self.dropAndLock = drop_and_lock
        self.rGuess = r_guess       # range to plan the first spot with, before the circle shows
        self.slot = None            # (x, y) of the card's drag point, to watch it blank and return
        self.slotBefore = None
        self.card = card            # card centre on the panel
        #  or the drag that drops the card on the map, (x1, y1, x2, y2, ms): a recorded one
        #  reaches cards chars.json doesn't know (skins, allies further down the panel).
        #  With card_key, (grey card art, (x, y) of the drag's start in it), the card is
        #  looked for on the panel, scrolling it, and dragged from wherever it is
        self.drop = drop
        self.cardKey = card_key
        self.panelPrev = None
        self.ends = 0
        self.ignore = list(ignore)
        self.final = None
        self.dragEnd = None
        self.scrolls = 0
        #  where the tower's circle centre should end up: a point, or planner(r, avoid)
        #  giving one once the range circle shows, asked again when a spot turns out red
        self.planner = target if callable(target) else None
        self.target = None if self.planner else target
        self.avoid = []
        self.replans = 0
        self.seen = []              # (x, y, r, red) every time the pending tower was found
        self.key = banner_key
        self.tol = tolerance
        self.maxDrags = max_drags
        self.base = None
        self.state = "drop"
        self.drags = 0
        self.drops = 0
        self.last = None
        #  spots tried around the target once close but red; valid ground can be a
        #  patch only a few px wide (live: red at (600,539), (607,534); ok at (614,540))
        self.probes = [(0, 0)] + [(int(round(r * np.cos(a))), int(round(r * np.sin(a))))
                                  for r in (6, 11) for a in np.arange(0, 2 * np.pi, np.pi / 4)]
        self.probe = 0
        #  how far the tower moved per px of the last drags: live it went 1.4-1.9x as far,
        #  overshooting back and forth (Apple Forest, Finn) until the drags ran out
        self.gain = []
        self.lastDrag = None
        self.misses = 0

    def step(self, img):
        if not self.dropAndLock:
            a = self.step_free(img)
            #  whatever went wrong on the way (the held tower lost from sight, a drop not
            #  seen to take), a tower that's down is placed: its own card now shows the check
            #  mark it didn't before the drop
            if a[0] == "fail" and "afford" not in str(a[1:]) and self.placed_anyway(img):
                self.state = "done"
                return ("done",)
            return a
        banner = find_banner(img, self.key)
        if self.state == "drop":
            if banner is not None:
                return ("fail", "a placement is already pending")
            if self.drops >= 3:
                return ("fail", "card drop didn't start a placement")
            drop = self.drop
            if self.cardKey is not None:
                at = find_card(img, self.cardKey[0])
                if at is None:
                    return self.scroll_for_card(img)
                sx, sy = at[0] + self.cardKey[1][0], at[1] + self.cardKey[1][1]
                #  no recorded drop: a short drag just past the panel's edge starts it
                #  dropped at mid height: a card near the panel's top would put the pending
                #  tower under the HUD, where it can't be found (Cobra, Black Heart)
                drop = (sx, sy) + (tuple(self.drop[2:]) if self.drop else (MAP_RIGHT - 47, min(max(sy + 40, 180), 420), 900))
            #  the map without the tower, to find the tower against
            self.base = img.copy()
            self.drops += 1
            self.state = "dropped"
            #  a long drag off the card doesn't start a placement (place_finn_apple1
            #  clicks 2-3, and live); a short one just past the panel edge does
            #  (click 4), then the adjust drags bring it to the target
            if drop:
                return ("swipe",) + tuple(drop)
            return ("swipe", self.card[0], self.card[1], MAP_RIGHT - 47, self.card[1] + 40, 900)
        if banner is None:
            if self.state == "confirmed":
                self.state = "done"
                return ("done",)
            if self.state == "dropped":
                #  the drop didn't take; try again from the same map
                self.state = "drop"
                return ("wait",)
            return ("fail", "confirm banner went away")
        pend = find_pending(img, self.base, self.ignore)
        if pend is not None and not (0 <= pend[0] < MAP_RIGHT and -60 <= pend[1] < img.shape[0]):
            #  a circle fitted to a sliver can land anywhere (-810, 307): not a sighting
            pend = None
        if pend is None:
            #  something passing over the map (the round's intro, a popup) can hide it for a bit
            self.misses += 1
            if self.misses <= 6:
                return ("wait",)
            return ("fail", "can't find the pending tower")
        self.misses = 0
        cx, cy, r, red = pend
        if self.lastDrag is not None and self.last is not None:
            (rx, ry), (px, py) = self.lastDrag, self.last[:2]
            asked = float(np.hypot(rx, ry))
            if asked > 8:
                moved = ((cx - px) * rx + (cy - py) * ry) / asked
                self.gain.append(min(max(moved / asked, 0.3), 3.0))
        self.lastDrag = None
        self.last = pend
        self.seen.append(pend)
        if self.planner and self.target is None:
            self.target = self.planner(r, self.avoid)
            if self.target is None:
                return ("fail", "no spot left for %s" % self.name)
        dx, dy = self.target[0] - cx, self.target[1] - cy
        if np.hypot(dx, dy) <= self.tol and not red:
            self.state = "confirmed"
            return ("tap", banner[0] + CHECK_OFF[0], banner[1] + CHECK_OFF[1])
        if self.drags >= self.maxDrags:
            self.state = "drop"
            return ("fail", "tower at (%d,%d)%s after %d drags" % (cx, cy, " red" if red else "", self.drags))
        self.drags += 1
        self.state = "dragging"
        if np.hypot(dx, dy) <= 15 and red and self.planner and self.replans < 8:
            #  can't go here: rule it out and take the next best spot
            self.avoid.append(self.target)
            self.replans += 1
            self.target = self.planner(r, self.avoid)
            if self.target is None:
                return ("fail", "no spot left for %s" % self.name)
            dx, dy = self.target[0] - cx, self.target[1] - cy
        elif np.hypot(dx, dy) <= 15 and red and self.probe < len(self.probes):
            #  close enough but not allowed here: aim for the next spot around the target
            ox, oy = self.probes[self.probe]
            self.probe += 1
            dx, dy = self.target[0] + ox - cx, self.target[1] + oy - cy
            if np.hypot(dx, dy) < 2:
                ox, oy = self.probes[self.probe % len(self.probes)]
                self.probe += 1
                dx, dy = self.target[0] + ox - cx, self.target[1] + oy - cy
        #  grab the tower by its body, a little above the circle centre (where its
        #  feet are), and drag it by what's left.  Every drag loses about SLOP px
        #  before the tower starts following (live: a 461px drag moved it 446, a
        #  17px one moved it 3), so lengthen the drag by that much
        #  a drag that starts on a tower already down doesn't move the pending one, and it
        #  follows a drag started anywhere: start clear of them (support towers go in
        #  among the others)
        gx, gy = int(cx), int(cy) - 30
        for ox, oy in ((0, -30), (0, 45), (-55, 0), (55, 0), (0, 90), (-60, 60), (60, 60)):
            px, py = int(cx) + ox, int(cy) + oy
            if MAP_TOP + 20 < py < 520 and 20 < px < MAP_RIGHT - 20 and \
                    all(np.hypot(px - tx, py - ty) > 50 for tx, ty in self.ignore):
                gx, gy = px, py
                break
        dist = max(float(np.hypot(dx, dy)), 1.0)
        if self.gain:
            k = 1.0 / float(np.median(self.gain[-3:]))
        else:
            k = (dist + SLOP) / dist
        ex, ey = int(round(gx + dx * k)), int(round(gy + dy * k))
        self.lastDrag = (ex - gx, ey - gy)
        #  the tower follows a drag started anywhere on the map (the recorded Lumpy House
        #  game drags roof towers from well below them), so keep the drag off the HUD and
        #  the banner, which cover towers near the top
        shift = MAP_TOP + 15 - min(gy, ey)
        if shift > 0:
            gy, ey = gy + shift, ey + shift
        return ("swipe", gx, gy, ex, ey, 1000)

    #  the card isn't showing: flicks carry on scrolling, so short slow drags, down the list
    #  until it stops moving, then up until it stops again; after both ends, it isn't there
    def scroll_for_card(self, img):
        x0, y0, x1, y1 = PANEL_BOX
        panel = cv.cvtColor(img[y0:y1, x0:x1], cv.COLOR_BGR2GRAY)
        #  at an end the swipe moves nothing (the panel's animations still change a little);
        #  the whole list is a few swipes long, so turn round after 6 either way
        self.dirSwipes = getattr(self, "dirSwipes", 0) + 1
        if (self.panelPrev is not None and cv.absdiff(panel, self.panelPrev).mean() < 6) or self.dirSwipes > 6:
            self.ends += 1
            self.dirSwipes = 1
            if self.ends >= 2:
                return ("fail", "card not found on the panel")
        self.panelPrev = panel
        self.scrolls += 1
        if self.scrolls > 40:
            return ("fail", "card not found on the panel")
        up = self.ends % 2 == 1
        return ("swipe", PANEL_X, 250 if up else 420, PANEL_X, 420 if up else 250, 700)

    #  Drop & Lock off.  The card is dragged straight to the spot: valid, it's placed on
    #  release; not, it stays held and gets dragged to the next spot, until one takes.
    #  Its card on the panel says which: blank blue while held, back once it's placed
    def step_free(self, img):
        if self.state == "drop":
            if self.drops >= 3:
                return ("fail", "card drop didn't start a placement")
            if self.cardKey is not None:
                at = find_card(img, self.cardKey[0])
                if at is None:
                    return self.scroll_for_card(img)
                self.slot = (at[0] + self.cardKey[1][0], at[1] + self.cardKey[1][1])
                if slot_red(img, self.slot):
                    return ("fail", "can't afford %s yet" % self.name)
            elif self.drop:
                self.slot = tuple(self.drop[:2])
            else:
                self.slot = tuple(self.card)
            self.base = img.copy()
            self.slotBefore = slot_crop(img, self.slot)
            if self.target is None:
                self.target = self.planner(self.rGuess, self.avoid) if self.planner else None
                if self.target is None:
                    return ("fail", "no spot left for %s" % self.name)
            elif self.drops:
                #  the last drop didn't start a placement: the same aim would fail the same way
                self.target = nudged(self.target, self.drops - 1)
            self.drops += 1
            self.state = "held?"
            #  the tower settles ~10 above where the finger lets go (measured: Monkey Farmer and
            #  Super Fans landed 20-24 low with 30): let go just under the spot
            #  (but not onto the powers bar under the map: a drop there doesn't take)
            return ("drag", self.slot[0], self.slot[1], int(self.target[0]), min(int(self.target[1]) + 10, MAP_BOTTOM + 60))
        if self.state == "cancel":
            return ("fail", self.why)
        #  the drag can scroll the panel instead (a card dragged up off a low slot): then
        #  another card sits in the slot, maybe one already placed with its check mark
        #  (a placed card's check mark covers part of its art, so a slot showing one is left to
        #  the checks below)
        #  the card list can still be gliding from a scroll when the card's dragged off: its
        #  blank slot a little above or below where the card was
        if self.cardKey is not None and not slot_blank(img, self.slot):
            for dy in (-8, 8, -16, 16, -24, 24, -32, 32):
                if slot_blank(img, (self.slot[0], self.slot[1] + dy)):
                    self.slot = (self.slot[0], self.slot[1] + dy)
                    break
        if self.cardKey is not None and not slot_blank(img, self.slot) and not slot_placed(img, self.slot):
            at = find_card(img, self.cardKey[0])
            here = at is not None and np.hypot(at[0] + self.cardKey[1][0] - self.slot[0],
                                               at[1] + self.cardKey[1][1] - self.slot[1]) <= 12
            if not here and self.state != "held":
                self.state = "drop"
                return ("wait",)
        if slot_blank(img, self.slot):
            self.state = "held"
        elif self.state == "held" and slot_placed(img, self.slot):
            self.final = find_sprite_near(img, self.base, self.last[:2] if self.last is not None else self.target,
                                          self.ignore)
            self.state = "done"
            return ("done",)
        elif slot_placed(img, self.slot):
            #  never seen blank, but its price tag's gone for a check mark: placed straight off,
            #  as long as a new tower stands near where it was aimed
            #  It stands where it was aimed (the drop allows for where it settles): the sprite
            #  search only proves a tower appeared, as it picks up animation nearby (Tuxedo
            #  Jake's music notes) as readily as the new tower
            if find_sprite_near(img, self.base, self.target, self.ignore) is None:
                self.state = "drop"
                return ("wait",)
            self.final = (float(self.target[0]), float(self.target[1]))
            self.state = "done"
            return ("done",)
        else:
            self.misses += 1
            if self.misses <= 2:
                return ("wait",)
            self.misses = 0
            self.state = "drop"
            return ("wait",)
        pend = find_pending(img, self.base, self.ignore)
        if pend is not None and not (0 <= pend[0] < MAP_RIGHT and -60 <= pend[1] < img.shape[0]):
            pend = None
        #  the held tower is where it was last dragged to, give or take: something else that
        #  changed (the "Round N" sign sliding in at the lower left) isn't it
        expect = self.dragEnd or self.target
        if pend is not None and expect is not None and np.hypot(pend[0] - expect[0], pend[1] - expect[1]) > 160:
            pend = None
        if pend is None:
            self.misses += 1
            if self.misses <= 6:
                return ("wait",)
            return self.cancel(None, "can't find the held tower")
        self.misses = 0
        cx, cy, r, _ = pend
        if self.lastDrag is not None and self.last is not None:
            (rx, ry), (px, py) = self.lastDrag, self.last[:2]
            asked = float(np.hypot(rx, ry))
            if asked > 8:
                moved = ((cx - px) * rx + (cy - py) * ry) / asked
                self.gain.append(min(max(moved / asked, 0.15), 3.0))
        self.lastDrag = None
        self.last = pend
        self.seen.append((cx, cy, r, True))
        if self.drags >= self.maxDrags:
            return self.cancel((cx, cy), "tower held at (%d,%d) after %d drags" % (cx, cy, self.drags))
        #  still held where it was aimed: that spot's no good, take the next
        if np.hypot(self.target[0] - cx, self.target[1] - cy) <= 15:
            self.avoid.append(self.target)
            self.target = self.planner(r, self.avoid) if self.planner and self.replans < 10 else None
            self.replans += 1
            if self.target is None:
                ox, oy = self.probes[self.probe % len(self.probes)]
                self.probe += 1
                self.target = (cx + ox * 3, cy + oy * 3)
        dx, dy = self.target[0] - cx, self.target[1] - cy
        self.drags += 1
        gx, gy = int(cx), int(cy) - 30
        for ox, oy in ((0, -30), (0, 45), (-55, 0), (55, 0), (0, 90), (-60, 60), (60, 60)):
            px, py = int(cx) + ox, int(cy) + oy
            if MAP_TOP + 20 < py < 520 and 20 < px < MAP_RIGHT - 20 and \
                    all(np.hypot(px - tx, py - ty) > 50 for tx, ty in self.ignore):
                gx, gy = px, py
                break
        #  the held tower trails the finger; with the finger held at the end it gets there
        k = 1.0 / float(np.median(self.gain[-3:])) if self.gain else 1.0
        ex, ey = int(round(gx + dx * k)), int(round(gy + dy * k))
        ex, ey = min(max(ex, 5), MAP_RIGHT - 5), min(max(ey, MAP_TOP), MAP_BOTTOM + 30)
        self.lastDrag = (ex - gx, ey - gy)
        self.dragEnd = (ex, ey + 30)
        return ("drag", gx, gy, ex, ey)

    #  give up on a held tower: dragged back onto the panel it goes back to being a card
    def placed_anyway(self, img):
        if self.slot is None or self.base is None or self.drops == 0:
            return False
        if slot_placed(self.base, self.slot) or not slot_placed(img, self.slot):
            return False
        if self.cardKey is not None:
            #  its own card in the slot (not another, placed one scrolled in); the check mark
            #  covers part of the art, so the match is looser
            at = find_card(img, self.cardKey[0], min_score=0.6)
            if at is None or np.hypot(at[0] + self.cardKey[1][0] - self.slot[0], at[1] + self.cardKey[1][1] - self.slot[1]) > 12:
                return False
        #  where it stands: last seen held, else where the last drag took it, else the aim
        at = self.last[:2] if self.last is not None else (self.dragEnd or self.target)
        self.final = (float(at[0]), float(at[1])) if at is not None else None
        return True

    def cancel(self, at, why):
        self.why = why
        if at is None or not slot_blank_seen(self):
            return ("fail", why)
        self.state = "cancel"
        return ("drag", int(at[0]), int(at[1]) - 30, PANEL_X, 300)

def slot_blank_seen(p):
    return p.state in ("held", "cancel")

#  a card's slot on the panel while its character is held: blank, the panel's blue
def slot_crop(img, at):
    x, y = int(at[0]), int(at[1])
    return img[max(y - 25, 0):y + 15, max(x - 22, 0):x + 22]

#  a placed character's card has a check mark where its price tag was: no green tag (it
#  could afford it) and no red price (it couldn't), but the check's white
def slot_placed(img, at):
    if at is None:
        return False
    x, y = int(at[0]), int(at[1])
    h = cv.cvtColor(img[max(y - 8, 0):y + 8, max(x - 22, 0):x + 22], cv.COLOR_BGR2HSV).reshape(-1, 3)
    green = ((h[:, 0] > 40) & (h[:, 0] < 85) & (h[:, 1] > 120) & (h[:, 2] > 100)).mean()
    red = (((h[:, 0] < 8) | (h[:, 0] > 170)) & (h[:, 1] > 120) & (h[:, 2] > 120)).mean()
    white = ((h[:, 1] < 60) & (h[:, 2] > 200)).mean()
    return bool(green < 0.3 and red < 0.1 and white > 0.1)

#  its price in red: it costs more than the money
def slot_red(img, at):
    x, y = int(at[0]), int(at[1])
    h = cv.cvtColor(img[max(y - 8, 0):y + 8, max(x - 22, 0):x + 22], cv.COLOR_BGR2HSV).reshape(-1, 3)
    return bool((((h[:, 0] < 8) | (h[:, 0] > 170)) & (h[:, 1] > 120) & (h[:, 2] > 120)).mean() > 0.2)

def slot_blank(img, at):
    if at is None:
        return False
    hsv = cv.cvtColor(slot_crop(img, at), cv.COLOR_BGR2HSV).reshape(-1, 3)
    return float(((hsv[:, 0] > 95) & (hsv[:, 0] < 125) & (hsv[:, 1] > 150) & (hsv[:, 2] > 120)).mean()) > 0.8

#  the path as (n, 2) samples every 3 px with their progress
#
def path_samples(path):
    p = np.array([(q["x"], q["y"]) for q in path["points"]], np.float64)
    seg = np.hypot(*np.diff(p, axis=0).T)
    s = np.concatenate([[0], np.cumsum(seg)])
    t = np.arange(0, s[-1], 3.0)
    return np.column_stack([np.interp(t, s, p[:, 0]), np.interp(t, s, p[:, 1])]), t / s[-1]

#  the spot for a placement option given the measured range r, away from spots
#  seen red (avoid) and towers already down (taken); (x, y) or None
#
def plan_spot(path, where, r, avoid=(), taken=()):
    mode, prog = PLACE_OPTIONS[where]
    if mode == "towers" and not taken:
        mode = "best"
    track = path["track"]
    h, w = track.shape
    clear = cv.distanceTransform((track == 0).astype(np.uint8), cv.DIST_L2, 5)
    #  not the map's very edges (trees; upside down the frame's left 46 px are padding)
    ys, xs = np.mgrid[MAP_TOP + 10:min(h - 15, MAP_BOTTOM):GRID, 90:MAP_RIGHT - PANEL_GAP:GRID]
    c = np.column_stack([xs.ravel(), ys.ravel()]).astype(np.float64)
    ok = clear[c[:, 1].astype(int), c[:, 0].astype(int)] >= CLEAR
    for pts, rad in ((avoid, AVOID_R), (taken, TAKEN_R)):
        for x, y in pts:
            ok &= np.hypot(c[:, 0] - x, c[:, 1] - y) > rad
    near = ok & (clear[c[:, 1].astype(int), c[:, 0].astype(int)] <= NEAR_BAND)
    c = c[near] if near.any() else c[ok]
    if not len(c):
        return None
    smp, sp = path_samples(path)
    d = np.hypot(c[:, None, 0] - smp[None, :, 0], c[:, None, 1] - smp[None, :, 1])      # candidates x samples
    inr = d <= r
    if mode == "best":
        score = inr.sum(1).astype(np.float64)
    elif mode == "far":
        x, y = c[:, 0], c[:, 1]
        room = np.minimum.reduce([x - 46, MAP_RIGHT - x, y - MAP_TOP, MAP_BOTTOM + 40 - y])
        for x0, y0, x1, y1 in MAP_UI:
            room = np.minimum(room, np.hypot(np.maximum.reduce([x0 - x, x - x1, np.zeros_like(x)]),
                                             np.maximum.reduce([y0 - y, y - y1, np.zeros_like(y)])))
        #  and from spots seen red: those come in patches (rocks, water, the map's void)
        for ax, ay in avoid:
            room = np.minimum(room, np.hypot(x - ax, y - ay) - AVOID_R)
        cover = inr.sum(1)
        score = np.minimum(room, EDGE_ENOUGH) - EDGE_ENOUGH * cover / max(cover.max(), 1)
    elif mode == "towers":
        cx, cy = np.mean(np.array(taken, np.float64), axis=0)
        score = -np.hypot(c[:, 0] - cx, c[:, 1] - cy) + 0.01 * inr.sum(1)
    else:
        a = smp[np.argmin(np.abs(sp - prog))]
        da = np.hypot(c[:, 0] - a[0], c[:, 1] - a[1])
        if mode == "near":
            score = -da + 0.01 * inr.sum(1)
        else:
            lo, hi = (prog, prog + WINDOW) if prog < 0.5 else (prog - WINDOW, prog) if prog > 0.5 else (prog - WINDOW / 2, prog + WINDOW / 2)
            near = inr[:, (sp >= lo) & (sp <= hi)].sum(1)
            score = near - 5.0 * np.abs(da - (r + EDGE_GAP))
    i = int(np.argmax(score))
    return (int(c[i, 0]), int(c[i, 1]))

#  what's been learned about placing on a map: maps/<map>/placements.json
#     ranges   range circle radius measured per character
#     placed   every confirmed placement: character, option, spot
#     blocked  spots the circle went red at with no tower of ours near (trees, rocks, house)
#
def load_placements(d):
    p = os.path.join(d, "placements.json")
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return {"ranges": {}, "placed": [], "blocked": []}

def record_placement(d, placer, where, taken=()):
    store = load_placements(d)
    for x, y, r, red in placer.seen:
        if red and all(np.hypot(x - tx, y - ty) > 2 * TAKEN_R for tx, ty in taken) \
                and all(np.hypot(x - bx, y - by) > AVOID_R / 2 for bx, by in store["blocked"]):
            store["blocked"].append([int(x), int(y)])
    if placer.state == "done" and placer.last is not None:
        x, y, r, _ = placer.last
        rs = [q[2] for q in placer.seen]
        store["ranges"][placer.name] = round(float(np.median(rs)), 1)
        store["placed"].append({"character": placer.name, "where": where, "x": int(round(x)), "y": int(round(y)),
                                "r": round(r, 1), "drags": placer.drags, "time": time.strftime("%Y-%m-%d %H:%M:%S")})
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "placements.json"), "w") as f:
        json.dump(store, f, indent=1)
    return store

#  card centre for a character from chars.json (tags sit under the cards)
#
def card_centre(chars, name):
    i = chars["chars"].index(name)
    tx, ty = chars["tags"][i]
    return (tx + 30, ty - 20)

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "bloons_adventure", "place_finn_apple1")
    rd = os.path.join(here, "bloons_adventure", "replay")
    files = sorted(glob.glob(os.path.join(d, "click_*.png")))
    clicks = [(f, parse_click(os.path.basename(f))) for f in files]

    #  the confirm banner key, cut from the last frame (it's showing there)
    kpath = os.path.join(rd, BANNER_KEY)
    if not os.path.exists(kpath):
        x, y, w, h = BANNER_BOX
        cv.imwrite(kpath, cv.imread(files[-1])[y:y + h, x:x + w])
        print("wrote %s" % kpath)
    key = cv.imread(kpath)

    #  the frame before the first card drop is the bare map; the last frame shows
    #  the tower where it was confirmed, which is the target
    first_drop = next(i for i, (f, c) in enumerate(clicks) if c["kind"] == "swipe" and c["x"] >= MAP_RIGHT
                      and find_banner(cv.imread(clicks[i + 1][0]), key) is not None)
    base = cv.imread(clicks[first_drop][0])
    final = find_pending(cv.imread(files[-1]), base)
    print("recorded: card drag at click %d from (%d,%d), confirmed at (%d,%d) r=%d" % (
        clicks[first_drop][1]["n"], clicks[first_drop][1]["x"], clicks[first_drop][1]["y"], final[0], final[1], final[2]))

    with open(os.path.join(rd, "chars.json")) as f:
        chars = json.load(f)
    card = card_centre(chars, "Finn")
    target = (int(round(final[0])), int(round(final[1])))
    p = Placer("Finn", card, target, key)
    p.step(base)
    print("click %04d frame -> drop Finn card (%d,%d) onto (%d,%d)" % (clicks[first_drop][1]["n"], card[0], card[1], *target))

    #  the recorded frames after the drop weren't produced by these actions, so this
    #  checks what the placer sees and would do on each, not a full run
    for f, c in clicks[first_drop + 1:]:
        a = p.step(cv.imread(f))
        seen = "tower (%d,%d) r=%d %s" % (p.last[0], p.last[1], p.last[2], "red" if p.last[3] else "ok") if p.last else ""
        rec = "recorded %s (%d,%d)%s" % (c["kind"], c["x"], c["y"], " -> (%d,%d)" % (c["ex"], c["ey"]) if "ex" in c else "")
        print("click %04d frame: %-34s -> %-28s | %s" % (c["n"], seen, " ".join(str(v) for v in a), rec))
