#!/usr/bin/env python3
#  Index where every map is on the adventure list, for navigate_to_map.
#
#  From the main menu: Adventures, then for each area (the < > arrows at the list's top
#  left) the list is scrolled from the top with the same slow swipe navigate_to_map uses,
#  and every map row seen is stored with
#     area        the area it's listed under (the green area banner above it)
#     arrow_area  the area the arrows were left on to reach it (the label between them)
#     area_index  right-arrow presses from the area the list opened on
#     chapter     the heading the map sits under (Apple Thief, Cyclops, ...)
#     slot        its place in the area's list, from 1
#     scrolls     swipes (LIST_SWIPE) from where the area's arrow jumps to, until its GO showed
#  in bloons_adventure/maps_index.json.  Drives the phone over adb with screencaps, so run
#  it with the bot not driving.
#
#  usage: bloons_index_maps.py [serial]
#
import cv2 as cv
import difflib
import json
import os
import pytesseract
import subprocess
import sys
import time

sys.argv, args = sys.argv[:1], sys.argv[1:]
import bloons_adventure as ba

SERIAL = args[0] if args else "RFCY61ANQSR"
HERE = os.path.dirname(os.path.abspath(__file__))
RD = os.path.join(HERE, "bloons_adventure", "replay")
V = ba.VideoThread
AREA_PREV, AREA_NEXT = (259, 105), V.ZONE_NEXT
AREA_LABEL = (270, 395, 92, 120)        # x0, x1, y0, y1 of the area's name between the arrows

def adb(*a):
    subprocess.run(["adb", "-s", SERIAL, "shell"] + [str(x) for x in a], capture_output=True)

def shot():
    png = subprocess.run(["adb", "-s", SERIAL, "exec-out", "screencap", "-p"], capture_output=True).stdout
    img = cv.imdecode(__import__("numpy").frombuffer(png, "uint8"), cv.IMREAD_COLOR)
    return cv.resize(img, (1170, 540), interpolation=cv.INTER_AREA)

def tap(x, y, wait=1.5):
    adb("input", "tap", x * 2, y * 2)
    time.sleep(wait)

def swipe(x1, y1, x2, y2, ms, wait=1.2):
    adb("input", "swipe", x1 * 2, y1 * 2, x2 * 2, y2 * 2, ms)
    time.sleep(wait + ms / 1000)

def ocr_white(img, psm=7):
    m = cv.copyMakeBorder(V.white_letters(img), 15, 15, 15, 15, cv.BORDER_CONSTANT, value=0)
    return pytesseract.image_to_string(255 - m, config="--psm %d" % psm).strip()

reader = V.__new__(V)
reader.beaconKeys = {n: cv.imread(os.path.join(RD, "beacon_%s.png" % n)) for n in ("go", "adventures", "adventure_list")}

LIST_SWIPE = ((620, 400), (620, 250))   # short and slow, so no row is skipped past

AREAS = ["Grasslands", "Candy Kingdom", "Ice Kingdom", "Badlands", "Fire Kingdom", "Lemongrab",
         "Underwater City", "Haunted Swamp", "Lumpy Space"]

#  the game's font reads Candy Kingdom as "Canpy Kincpom": snapped to the area names
def snap_area(t):
    m = difflib.get_close_matches(t.lower(), [a.lower() for a in AREAS], 1, 0.6)
    return AREAS[[a.lower() for a in AREAS].index(m[0])] if m else None

def area_name(ref):
    x0, x1, y0, y1 = AREA_LABEL
    t = ocr_white(ref[y0 - 6:y1 + 6, x0:x1], psm=6)
    t = " ".join(w for w in t.split() if sum(c.isalpha() for c in w) >= 2)
    return snap_area(t) or t.title()

def same(a, b):
    return bool(a and b) and difflib.SequenceMatcher(None, a.lower(), b.lower()).ratio() > 0.8

#  chapter headings between the map rows: [(y, text)].  Rows are boxed from 82 above their
#  GO to 22 below, headings sit in the gaps, white on the list's blue
def headings(ref, gos):
    #  headings start at the list's left edge; a row's name and "Difficulty:" start
    #  inside it at x 445, so a row cut off at the bottom (GO off screen) doesn't count
    w = V.white_letters(ref[:, 272:440])
    for gx, gy in reader.find_buttons(ref, "go"):
        w[max(0, gy - 84):gy + 24] = 0
    w[:135] = 0
    w[505:] = 0
    rows = (w > 0).sum(1) > 3
    out, y = [], 0
    while y < len(rows):
        if rows[y]:
            y0 = y
            while y < len(rows) and rows[y]:
                y += 1
            if 10 <= y - y0 <= 34:
                t = ocr_white(ref[y0 - 4:y + 4, 272:700])
                t = " ".join(x for x in t.split() if sum(c.isalpha() for c in x) >= 2).title()
                if len(t.replace(" ", "")) >= 4 and not difflib.get_close_matches(t.lower(), V.MAP_NAMES, 1, 0.75):
                    out.append((y0, t))
        y += 1
    return out

def main():
    ref = shot()
    if reader.key_score(ref, "adventure_list") < 0.9:
        if reader.key_score(ref, "adventures") < 0.9:
            sys.exit("start on the main menu or the adventure list")
        tap(608, 446, 2.5)
    #  the nine areas in arrow order (AREAS); each is reached by pressing right until the
    #  label names it
    areas = list(AREAS)
    index = {}
    (x1, y1), (x2, y2) = LIST_SWIPE
    for ai, name in enumerate(areas):
        #  the arrows step from the area the label shows, which follows the scrolling:
        #  press until it names this one
        for _ in range(len(areas) + 2):
            label = area_name(shot())
            if label == name:
                break
            tap(*AREA_NEXT, 2.0)
        else:
            print("area %s not reached (label reads %r), skipped" % (name, label))
            continue
        #  and once more round, so the list sits at the area's start the way an arrow leaves it
        if ai:
            tap(*AREA_PREV, 2.0)
            tap(*AREA_NEXT, 2.0)
        #  the label lags the list by a row or two, so the area a map is in comes from the
        #  area banner above it; the arrow's area and the scrolls are how it was reached
        slot, chapter, prev, section = 0, None, None, name
        for scrolls in range(40):
            ref = shot()
            if scrolls and area_name(ref) != name:
                break
            gos = reader.list_maps(ref)
            items = sorted([(y, "h", t) for y, t in headings(ref, gos)] + [(gy - 82, "m", (m, (gx, gy))) for m, (gx, gy) in gos])
            for _, kind, what in items:
                if kind == "h":
                    if snap_area(what) and difflib.SequenceMatcher(None, what.lower(), snap_area(what).lower()).ratio() > 0.7:
                        section = snap_area(what)
                    else:
                        chapter = what
                    continue
                mname = what[0]
                if mname in index:
                    continue
                slot += 1
                index[mname] = {"area": section, "arrow_area": name, "area_index": ai, "chapter": chapter,
                                "slot": slot, "scrolls": scrolls}
                print("%-28s area %-16s arrow %-16s chapter %-22s slot %2d  scrolls %d" % (mname, section, name, chapter, slot, scrolls))
            if prev is not None and cv.absdiff(ref, prev).max(2).mean() < 1:
                break
            prev = ref
            swipe(x1, y1, x2, y2, 1000)
    out = os.path.join(HERE, "bloons_adventure", "maps_index.json")
    with open(out, "w") as f:
        json.dump({"areas": areas, "swipe": LIST_SWIPE, "maps": index}, f, indent=1)
    missing = sorted(set(V.MAP_NAMES.values()) - set(index))
    print("%d maps in %d areas written to %s" % (len(index), len(areas), out))
    if missing:
        print("not found: %s" % ", ".join(missing))

main()
