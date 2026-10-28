#!/usr/bin/env python3
#  Buy a character upgrade by name, closed loop.
#
#  With a placed character selected, its upgrade panel shows on the left: a
#  column of cards 82px apart, each a title over an icon with a price tag.
#  Buying one removes its card and the ones below move up, so cards are found
#  by name every time, never by slot.
#
#     title   matched against a saved crop of each upgrade's title (scores 1.0
#             vs <0.6 for the others, in any slot).  Upgrades without a crop yet
#             fall back to tesseract fuzzy matched to UPGRADES, which is shaky:
#             it reads "SWORDPLAYER" as "eo" when the card art bleeds in
#     price   glyph matched like the character tags, but these tags are smaller,
#             so they get their own samples (upgrade_tags.npz)
#
#  Upgrader.step() is fed frames and returns the next action, like Placer.
#  A buy is confirmed when the card is gone, or retried once if it's still there.
#
#     usage: bloons_upgrade.py      builds upgrade_tags.npz from upgrade_run_live
#
import cv2 as cv
import numpy as np
import difflib
import os
import re
import sys
import pytesseract

import bloons_build_chars as chars_lib

#  every upgrade name per character, from its info screen
UPGRADES = {
    "Finn": ["Radder, Faster!", "Raddest, Fastest!", "Limber Limbs", "Swordplayer", "Swordmaster",
             "Slicer", "Flying Kick", "Right in the Glubs", "Moab Ripper", "Finn of Fury"],
    #  from the recorded Apple Forest game's panels (recordings/apple_forest_2008)
    "Tuxedo Jake": ["Turn It Up!", "Busker", "Rock Out!", "Musician", "Royalties", "Superstar", "Allegro Tempo",
             "Full Orchestra", "Inspiring Melody", "Pleasant Melody", "Encore"],
    "PB": ["Unwavering Loyalty", "Regal Presence", "Bloon Science", "Super Intelligence", "Gun Familiarity",
           "Royal Decree"],
    "Supermonkey": ["Supersonic Speed", "Hypersonic Speed", "Laser Eyes", "Plasma Eyes", "Super Range",
                    "Hyper Range", "Heroic Aura", "Disarming Charisma", "Sun Avatar", "Sun God", "Call In Friends"],
    #  from the recorded Supermonkey Villa win (recordings/supermonkey_villa_1016_1605)
    "Dr Monkey": ["Slowing Solution", "Damage Decoction", "Alchemy"],
    "Hunter Marceline": ["Garlic Bomb", "Blood Rush", "Soul Sucking", "Hunter Training", "Stronger Garlic",
                  "Circular Flight Path", "Straight Flight Path", "Mass Soul Sucking", "Advanced Hunter Training",
                  "Smart Stakes"],
    "Ice King": ["Ice Bolts", "Wizard Eyes", "Chilled To The Bone", "Colder Ice", "Faster Freezing",
                 "Lightning Strike", "Hailstorm", "Arrows Of Frozen Rain", "Monsters Of Snow", "Crown Influence",
                 "Winter Weather", "Freeze Lightning"],
}

CARD_X = 72             # left of the card column
CARD_Y0 = 81            # top of the first card
CARD_DY = 82            # card pitch
CARDS = 5               # at most this many show
TITLE = (20, 4, 105, 40)    # x, y, w, h inside a card; tall enough for two-line titles
TAG = (50, 44, 86, 30)      # price tag inside a card
TITLE_KEY = (30, 6, 92, 16) # title crop saved as the key; searched for in the card's top 30 px

#  where each upgrade's title key comes from: (frame, slot)
TITLE_FRAMES = {"Radder, Faster!": ("00_start.png", 0), "Limber Limbs": ("00_start.png", 1),
                "Swordplayer": ("00_start.png", 2), "Right in the Glubs": ("00_start.png", 3),
                "Raddest, Fastest!": ("../auto_run/bought_04.png", 0), "Moab Ripper": ("../auto_run/bought_04.png", 1),
                "Slicer": ("../auto_run/bought_04.png", 3), "Swordmaster": ("../auto_run/bought_03.png", 1), "Flying Kick": ("../auto_run/flying_kick_red.png", 0)}

#  frames whose upgrade prices are known, for the tag samples
TAG_FRAMES = {"00_start.png": [200, 150, 150, 450], "01_after_tap_limber.png": [200, 150, 450],
              "../auto_run/bought_04.png": [250, 500, 450, 400], "../auto_run/flying_kick_red.png": [1000]}

def card_box(i):
    return (CARD_X, CARD_Y0 + CARD_DY * i)

def tag_roi(img, i):
    x, y = card_box(i)
    tx, ty, tw, th = TAG
    return img[y + ty:y + ty + th, x + tx:x + tx + tw]

def title_key(img, i):
    x, y = card_box(i)
    kx, ky, kw, kh = TITLE_KEY
    return img[y + ky:y + ky + kh, x + kx:x + kx + kw]

#  upgrade name on card i: best saved title over 0.8, else OCR
#
def match_title(img, i, names, keys):
    x, y = card_box(i)
    strip = img[y:y + 30, x:x + 130]
    best, name = 0.8, None
    for n in names:
        k = keys.get(n)
        if k is None:
            continue
        score = cv.minMaxLoc(cv.matchTemplate(strip, k, cv.TM_CCOEFF_NORMED))[1]
        if score > best:
            best, name = score, n
    if name:
        return name
    return read_title(img, i, [n for n in names if n not in keys])[0]

#  upgrade name on card i, matched to that character's list, or None
#
def read_title(img, i, names):
    x, y = card_box(i)
    tx, ty, tw, th = TITLE
    g = cv.cvtColor(img[y + ty:y + ty + th, x + tx:x + tx + tw], cv.COLOR_BGR2GRAY)
    text = pytesseract.image_to_string(cv.resize(g, None, fx=3, fy=3, interpolation=cv.INTER_CUBIC),
                                       config="--psm 6")
    flat = re.sub(r"[^a-z]", "", text.lower())
    if len(flat) < 3:
        return None, text
    keys = {re.sub(r"[^a-z]", "", n.lower()): n for n in names}
    m = difflib.get_close_matches(flat, list(keys), 1, 0.6)
    return (keys[m[0]] if m else None), text

#  the upgrade panel is open: its SELL button sits at the bottom left whatever
#  the cards say (all red when broke, which reads no prices with older samples)
SELL_BOX = (78, 502, 50, 28)

#  a tower on the map's left half gets its panel on the right instead, beside the character
#  cards: the same panel this much further right (SELL measured at x 78 and 799)
RIGHT_DX = 721
PANEL_X = (46, 232)     # the left panel's columns in the frame


#  0 when the panel's open on the left, RIGHT_DX when on the right, None when it's shut
def panel_side(img, sell_key):
    x, y, w, h = SELL_BOX
    for dx in (0, RIGHT_DX):
        area = img[y - 10:y + h + 10, x + dx - 10:x + dx + w + 10]
        if cv.minMaxLoc(cv.matchTemplate(area, sell_key, cv.TM_CCOEFF_NORMED))[1] > 0.85:
            return dx
    return None


def panel_open(img, sell_key):
    return panel_side(img, sell_key) is not None


#  the frame with a right-hand panel copied over to where the left one goes, so the card
#  reading (all in left-panel coordinates) works on either
def as_left(img, dx):
    if not dx:
        return img
    out = img.copy()
    a, b = PANEL_X
    out[:, a:b] = img[:, a + dx:b + dx]
    return out

#  what the panel shows: [(slot, name, (price, red) or None)]
#
def read_cards(img, character, lib, keys):
    out = []
    for i in range(CARDS):
        price = chars_lib.read_tag(tag_roi(img, i), lib)
        if price is None:
            #  the tag samples are Finn's prices: a card whose saved title matches still
            #  counts, priced from its tag's colour (red when it can't be afforded)
            name = match_title(img, i, [n for n in UPGRADES.get(character, []) if n in keys], keys)
            if name is None and not card_present(img, i):
                continue
            #  priced from its tag's colour: red when it can't be afforded
            out.append((i, name, (0, tag_red(img, i))))
            continue
        out.append((i, match_title(img, i, UPGRADES.get(character, []), keys), price))
    return out

#  a card is there when its price tag's green is (whatever the price reads as)
def card_present(img, i):
    hsv = cv.cvtColor(tag_roi(img, i), cv.COLOR_BGR2HSV).reshape(-1, 3)
    green = (hsv[:, 0] > 40) & (hsv[:, 0] < 85) & (hsv[:, 1] > 120) & (hsv[:, 2] > 100)
    if green.mean() < 0.3:
        return False
    #  the tag's own green (hue ~52, fully saturated) with a price on it; the hills behind
    #  an empty slot are duller (hue ~41, saturation ~209) with nothing written
    text = ((hsv[:, 1] < 50) & (hsv[:, 2] > 200)) | ((hsv[:, 0] < 8) | (hsv[:, 0] > 170)) & (hsv[:, 1] > 120)
    return bool(47 <= np.median(hsv[green, 0]) <= 58 and np.median(hsv[green, 1]) > 235 and text.mean() > 0.04)

#  the price tag's text is red when the upgrade costs more than the money
def tag_red(img, i):
    hsv = cv.cvtColor(tag_roi(img, i), cv.COLOR_BGR2HSV)
    red = ((hsv[..., 0] < 8) | (hsv[..., 0] > 170)) & (hsv[..., 1] > 120) & (hsv[..., 2] > 120)
    white = (hsv[..., 1] < 50) & (hsv[..., 2] > 200)
    #  red letters are outlined in white, so only the red counts
    return bool(red.mean() > 0.05)

#  saved title crops, {name: image}
#
def load_keys(rd):
    keys = {}
    for names in UPGRADES.values():
        for n in names:
            path = os.path.join(rd, key_name(n))
            if os.path.exists(path):
                keys[n] = cv.imread(path)
    return keys

def key_name(upgrade):
    return "upgrade_%s.png" % re.sub(r"[^a-z]+", "_", upgrade.lower()).strip("_")

def load_lib(path):
    t = np.load(path)
    vecs = np.array([chars_lib.unit(g.astype(np.float32)) for g in t["glyphs"]])
    red = t["red"]
    return {r: (t["chars"][red == r], vecs[red == r] if (red == r).any() else np.zeros((0, vecs.shape[1])))
            for r in (False, True)}

#  one purchase; step() returns ("tap", x, y), ("wait",), ("done", price) or ("fail", why)
#
class Upgrader:
    def __init__(self, character, upgrade, lib, keys, tries=2):
        self.character = character
        self.upgrade = upgrade
        self.lib = lib
        self.keys = keys
        self.tries = tries
        self.taps = 0
        self.price = None
        self.cards = []

    def step(self, img):
        self.cards = read_cards(img, self.character, self.lib, self.keys)
        if not self.cards:
            return ("fail", "no upgrade panel; select the character first")
        mine = [c for c in self.cards if c[1] == self.upgrade]
        if not mine:
            if self.taps:
                #  its card went away after the tap: bought
                return ("done", self.price)
            return ("fail", "%s not offered (%s)" % (self.upgrade, ", ".join(str(c[1]) for c in self.cards)))
        slot, _, (price, red) = mine[0]
        self.price = price
        if red:
            return ("fail", "%s costs $%d, can't afford" % (self.upgrade, price))
        if self.taps >= self.tries:
            return ("fail", "%s still offered after %d taps" % (self.upgrade, self.taps))
        self.taps += 1
        x, y = card_box(slot)
        tx, ty, tw, th = TAG
        return ("tap", x + tx + tw // 2 - 8, y + ty + th // 2)

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "bloons_adventure", "upgrade_run_live")
    rd = os.path.join(here, "bloons_adventure", "replay")
    chars, imgs, reds = [], [], []
    for fname, prices in TAG_FRAMES.items():
        img = cv.imread(os.path.join(d, fname))
        if img is None:
            print("missing %s, skipped" % fname)
            continue
        for i, p in enumerate(prices):
            text = "$%d" % p
            gl, isred = chars_lib.tag_glyphs(tag_roi(img, i))
            if len(gl) != len(text):
                print("skip %s card %d: want %d glyphs for %r, found %d" % (fname, i, len(text), text, len(gl)))
                continue
            chars += list(text)
            imgs += gl
            reds += [isred] * len(gl)
    path = os.path.join(rd, "upgrade_tags.npz")
    np.savez_compressed(path, chars=np.array(chars), glyphs=np.array(imgs), red=np.array(reds))
    print("wrote %s: %d samples (%d red)" % (path, len(chars), sum(reds)))

    for name, (fname, slot) in TITLE_FRAMES.items():
        img = cv.imread(os.path.join(d, fname))
        if img is None:
            continue
        cv.imwrite(os.path.join(rd, key_name(name)), title_key(img, slot))
    print("wrote %d title keys" % len(TITLE_FRAMES))
    x, y, w, h = SELL_BOX
    cv.imwrite(os.path.join(rd, "upgrade_sell.png"), cv.imread(os.path.join(d, "00_start.png"))[y:y + h, x:x + w])

    lib = load_lib(path)
    keys = load_keys(rd)
    for fname in TAG_FRAMES:
        img = cv.imread(os.path.join(d, fname))
        print(fname, [(s, n, p) for s, n, p in read_cards(img, "Finn", lib, keys)])
