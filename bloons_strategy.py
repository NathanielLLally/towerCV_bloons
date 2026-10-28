#!/usr/bin/env python3
#  Strategies for maps without a recorded game: a name and an order of operations.
#
#     place <character>             where it goes comes from its role (CHARACTERS), unless
#                                   the step says: place <character> at <option>
#     upgrade <character> <upgrade> a named upgrade
#     upgrade <character>           the next one in the character's order for this
#                                   strategy (ORDERS), else its cheapest
#     upgrade all <character>       every upgrade it has left, cheapest first ("*": everyone)
#     activate <skill>              an activated skill, used once every round from then on
#
#  exclude: upgrades never bought by this strategy, per character, because they'd break it
#  (Supermonkey's Call In Friends).  "upgrade all" passes over them
#
#  Monkey Farmer, Cobra, Dr Monkey and Super Fans are allies.  Characters go by their
#  full names (Tuxedo Jake and Hunter Marceline aren't Jake and Marceline).
#
#     usage: bloons_strategy.py     prints every strategy's steps
#

#  role: combat towers go where bloons are, support ones among the other towers, eco
#  ones (they make money, not damage) out of the way where nothing comes near
ROLE_PLACE = {"combat": "best coverage", "support": "near towers", "eco": "far from path",
              #  Super Fans only have to be on the map for Sun God (its warning says in
              #  Supermonkey's range, which isn't so): any free spot will do
              "fan": "far from path"}

CHARACTERS = {
    "Finn": {"role": "combat"},
    "Tuxedo Jake": {"role": "support"},
    "Monkey Farmer": {"role": "eco", "ally": True},
    "Cobra": {"role": "combat", "ally": True},
    "Sai": {"role": "combat"},
    "PB": {"role": "support"},
    "Supermonkey": {"role": "combat"},
    "Ice King": {"role": "combat"},
    "Hunter Marceline": {"role": "combat"},
    "Dr Monkey": {"role": "support", "ally": True},
    "Super Fans": {"role": "fan", "ally": True},
    "C4 Charlie": {"role": "combat"},
    "Flame Princess": {"role": "combat"},
    "Commander Cassie": {"role": "combat"},
    "BMO": {"role": "support"},
    "Tiny Manticore": {"role": "combat"},
}

#  each character's upgrade order, per plan kind (eco favours money, dps damage)
ORDERS = {
    "eco": {"Tuxedo Jake": ["Busker", "Royalties", "Musician"],
            "PB": ["Regal Presence", "Royal Decree"]},
    "dps": {"Tuxedo Jake": ["Turn It Up!", "Rock Out!", "Superstar"],
            "PB": ["Regal Presence", "Royal Decree"]},
}


def character(name):
    low = name.lower()
    for c in CHARACTERS:
        if low == c.lower():
            return c
    raise ValueError("unknown character %r" % name)


def is_ally(name):
    return CHARACTERS.get(name, {}).get("ally", False)


#  what always comes straight after placing a character, unless the step says
#  "place <character> alone": Supermonkey's damage and range before anything else is placed
FOLLOW_UP = {"Supermonkey": ["Heroic Aura", "Laser Eyes", "Plasma Eyes", "Super Range", "Hyper Range",
                             "Disarming Charisma"]}

#  upgrades no strategy should buy unless it says otherwise
EXCLUDE = {"Supermonkey": ["Call In Friends"], "Ice King": ["Monsters Of Snow"]}


class Strategy:
    #  steps come out as tuples: ("place", character, where), ("upgrade", character,
    #  upgrade), ("upgrade all", character or "*"), ("ability", skill)
    def __init__(self, name, kind, ops, exclude=None):
        self.name = name
        self.kind = kind
        self.exclude = {character(c): list(u) for c, u in (EXCLUDE if exclude is None else exclude).items()}
        self.steps = []
        used = {}
        for op in ops:
            words = op.strip()
            low = words.lower()
            if low.startswith("place "):
                rest = words[6:]
                where = None
                alone = rest.lower().endswith(" alone")
                if alone:
                    rest = rest[:-6]
                if " at " in rest:
                    rest, where = rest.split(" at ", 1)
                c = character(rest)
                self.steps.append(("place", c, where or ROLE_PLACE[CHARACTERS[c]["role"]]))
                if not alone:
                    self.steps += [("upgrade", c, u) for u in FOLLOW_UP.get(c, [])]
            elif low.startswith("upgrade all "):
                rest = words[12:].strip()
                self.steps.append(("upgrade all", "*" if rest in ("*", "everyone") else character(rest)))
            elif low.startswith("upgrade "):
                rest = words[8:]
                c, upg = self.split_upgrade(rest)
                if upg is None:
                    order = ORDERS.get(kind, {}).get(c, [])
                    i = used.get(c, 0)
                    if i < len(order):
                        upg = order[i]
                        used[c] = i + 1
                if upg is None:
                    self.steps.append(("upgrade cheapest", c))
                else:
                    self.steps.append(("upgrade", c, upg))
            elif low.startswith("activate "):
                #  "activate <skill> on round N": only that round, else every round
                skill, _, rnd = words[9:].partition(" on round ")
                self.steps.append(("ability", skill.strip().title(), int(rnd) if rnd else None))
            else:
                raise ValueError("can't read step %r" % op)

    #  "tuxedo jake busker" -> ("Tuxedo Jake", "Busker"); "tuxedo jake" -> ("Tuxedo Jake", None)
    @staticmethod
    def split_upgrade(rest):
        words = rest.split()
        for n in range(len(words), 0, -1):
            try:
                c = character(" ".join(words[:n]))
            except ValueError:
                continue
            upg = " ".join(words[n:]).strip(" ,")
            return c, (upg.title() if upg else None)
        raise ValueError("no character in %r" % rest)

    def excluded(self, char, upgrade):
        return upgrade is not None and upgrade in self.exclude.get(char, [])

    def characters(self):
        return [s[1] for s in self.steps if s[0] == "place"]

    def __repr__(self):
        return "Strategy(%s, %d steps)" % (self.name, len(self.steps))


STRATEGIES = [
    #  the recorded Supermonkey Villa win (recordings/game_1016_1648): one tight cluster
    #  around Finn and Tuxedo Jake (Jake's rings buff Ice King and Hunter Marceline packed
    #  against them), Monkey Farmer out of the way.  Jake's money first, Supermonkey to Sun
    #  Avatar, Ice King, the rest of Jake, Hunter Marceline, four Super Fans so Sun God can
    #  be bought; Sun God is set off on round 74
    Strategy("sun_god", "eco", [
        "place finn", "place tuxedo jake at near finn", "place monkey farmer",
        "upgrade tuxedo jake busker", "upgrade tuxedo jake royalties", "upgrade tuxedo jake musician",
        "upgrade tuxedo jake superstar", "place supermonkey alone", "upgrade supermonkey laser eyes",
        "upgrade supermonkey plasma eyes", "upgrade supermonkey super range", "upgrade supermonkey hyper range",
        "upgrade supermonkey heroic aura", "upgrade supermonkey disarming charisma",
        "upgrade supermonkey supersonic speed", "upgrade supermonkey hypersonic speed",
        "upgrade supermonkey sun avatar", "place ice king at near tuxedo jake",
        "upgrade ice king crown influence", "upgrade ice king ice bolts", "upgrade ice king wizard eyes",
        "upgrade ice king chilled to the bone", "upgrade ice king winter weather", "upgrade ice king colder ice",
        "upgrade ice king faster freezing", "upgrade ice king lightning strike", "upgrade ice king freeze lightning",
        "upgrade ice king hailstorm", "upgrade ice king arrows of frozen rain",
        "upgrade tuxedo jake turn it up!", "upgrade tuxedo jake allegro tempo", "upgrade tuxedo jake rock out!",
        "upgrade tuxedo jake full orchestra", "upgrade tuxedo jake inspiring melody",
        "place hunter marceline at near tuxedo jake",
        "upgrade hunter marceline garlic bomb", "upgrade hunter marceline blood rush",
        "upgrade hunter marceline soul sucking", "upgrade hunter marceline hunter training",
        "upgrade hunter marceline advanced hunter training", "upgrade hunter marceline smart stakes",
        "upgrade hunter marceline stronger garlic", "upgrade hunter marceline straight flight path",
        "upgrade hunter marceline mass soul sucking",
        "place super fans", "place super fans", "place super fans", "place super fans",
        "upgrade supermonkey sun god", "activate sun god on round 74"]),
    #  the order of the recorded Apple Forest win (recordings/apple_forest_2008): PB early so
    #  Royal Decree pays from round 11, Jake and Finn maxed before the late towers
    Strategy("eco_recorded", "eco", [
        "place finn", "place tuxedo jake", "place pb", "place monkey farmer", "place cobra",
        "upgrade tuxedo jake busker", "upgrade tuxedo jake royalties", "upgrade tuxedo jake musician",
        "upgrade pb regal presence", "upgrade pb royal decree", "activate royal decree",
        "upgrade all tuxedo jake", "upgrade all finn", "place supermonkey",
        "place ice king", "upgrade all ice king", "place sai", "upgrade all *"]),
    Strategy("eco_farmer", "eco", [
        "place finn", "place tuxedo jake", "place monkey farmer", "place cobra",
        "upgrade tuxedo jake busker", "upgrade tuxedo jake royalties", "place sai",
        "place pb", "upgrade tuxedo jake musician", "upgrade pb regal presence",
        "upgrade pb royal decree", "activate royal decree",
        "place supermonkey", "place ice king", "upgrade all ice king", "upgrade all *"]),
    Strategy("dps", "dps", [
        "place finn", "place sai", "place cobra", "place tuxedo jake", "upgrade finn",
        "upgrade sai", "place pb", "upgrade pb", "upgrade pb", "activate royal decree",
        "place supermonkey", "place ice king", "upgrade all ice king", "upgrade all *"]),
]

BY_NAME = {s.name: s for s in STRATEGIES}

if __name__ == "__main__":
    for s in STRATEGIES:
        print(s)
        for st in s.steps:
            print("   ", st)
