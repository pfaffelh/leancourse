#!/usr/bin/env python3
"""How the recursor of `MyNat` is built from its declaration.

Chapter 1.3, deck slide before "The recursor in general". Top: the
declaration. Bottom: the type of `MyNat.rec`, with the cases named.
Each part of the declaration is boxed in a colour, and an arrow leads
to the part of the recursor it produces:

* the type `MyNat`            -> the motive `MyNat → Sort u`
* the constructor `zero`      -> the case `zero`
* the constructor `succ`      -> the case `succ`
* the recursive argument `n`  -> `(n : MyNat) → motive n`

Text is monospace; positions are counted in characters, so a box is
given by the substring it surrounds. Lines carry a white background,
arrows run underneath them.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from matplotlib.path import Path as MPath

INK, MUTED = "#0b0b0b", "#52514e"
BLUE, ORANGE, GREEN, RED, GREY = "#2a78d6", "#d9822b", "#2e9b5f", "#c8423b", "#898781"

FS = 13                       # font size in pt
CW = 0.602 * FS / 72          # width of one character of DejaVu Sans Mono, inches
PITCH = 1.75 * FS / 72        # one unit of y, inches

X, B = 16, 6                  # left edge of the declaration and of the recursor
# (x of first character, y of the line, text); y counts downwards
LINES = {
    "t0": (X, 0.0, "inductive MyNat where"),
    "t1": (X, 1.4, "  | zero : MyNat"),
    "t2": (X, 2.8, "  | succ (n : MyNat) : MyNat"),
    "b0": (B, 7.4, "MyNat.rec : {motive : MyNat → Sort u} →"),
    "b1": (B, 8.8, "  (zero : motive MyNat.zero) →"),
    "b2": (B, 10.2, "  (succ : (n : MyNat) → motive n → motive (MyNat.succ n)) →"),
    "b3": (B, 11.6, "  (t : MyNat) → motive t"),
}
W, Y0, Y1 = 70, -1.7, 12.5    # canvas: width in characters, y range

fig = plt.figure(figsize=(W * CW, (Y1 - Y0) * PITCH))
ax = fig.add_axes((0, 0, 1, 1))
ax.set_xlim(0, W); ax.set_ylim(Y1, Y0); ax.axis("off")

for x, y, s in LINES.values():   # leading blanks get no white background
    ax.text(x + len(s) - len(s.lstrip()), y, s.lstrip(), family="DejaVu Sans Mono", fontsize=FS, color=INK,
            va="center", ha="left", zorder=3,
            bbox=dict(facecolor="white", edgecolor="none", pad=1.5))


def box(line, sub, color, pad=0.22, lw=1.6):
    """Draw a box around `sub` in `line`; return (left, right, top, bottom)."""
    x, y, s = LINES[line]
    i = s.index(sub)
    l, r = x + i, x + i + len(sub)
    for fc, ec, a in ((color, "none", 0.10), ("none", color, 1.0)):
        ax.add_patch(FancyBboxPatch((l, y - 0.36), r - l, 0.72,
                                    boxstyle=f"round,pad={pad},rounding_size=0.25",
                                    facecolor=fc, edgecolor=ec, alpha=a, lw=lw,
                                    zorder=2 if ec == "none" else 4))
    return l - pad, r + pad, y - 0.36 - pad, y + 0.36 + pad


def route(points, color, r=0.8):
    """Arrow along a polyline through `points`, corners rounded with radius r."""
    verts, codes = [points[0]], [MPath.MOVETO]
    for p, q, n in zip(points, points[1:], points[2:]):
        def towards(a, b, d):
            dx, dy = b[0] - a[0], b[1] - a[1]
            L = (dx * dx + dy * dy) ** 0.5
            d = min(d, L / 2)
            return (a[0] + dx * d / L, a[1] + dy * d / L)
        verts += [towards(q, p, r), q, towards(q, n, r)]
        codes += [MPath.LINETO, MPath.CURVE3, MPath.CURVE3]
    verts.append(points[-1]); codes.append(MPath.LINETO)
    ax.add_patch(FancyArrowPatch(path=MPath(verts, codes), color=color, lw=1.8,
                                 arrowstyle="-|>,head_width=0.3,head_length=0.6",
                                 mutation_scale=18, zorder=1))


def label(x, y, s, color, ha="left"):
    ax.text(x, y, s, fontsize=10.5, color=color, ha=ha, va="center", zorder=5,
            linespacing=1.25, bbox=dict(facecolor="white", edgecolor="none", pad=1.0))


# the type -> the motive: over the top, down the left, across the gap
tl, tr, tt, tb = box("t0", "MyNat", BLUE)
bl, br, bt, bb = box("b0", "{motive : MyNat → Sort u}", BLUE)
route([((tl + tr) / 2, tt), ((tl + tr) / 2, -1.3), (1.0, -1.3), (1.0, 5.3),
       (bl + 4, 5.3), (bl + 4, bt)], BLUE)
label(5.0, 4.65, "the type: the motive says what to define on it", BLUE)

# constructor zero -> case zero: down the left
tl, tr, tt, tb = box("t1", "zero : MyNat", ORANGE)
bl, br, bt, bb = box("b1", "(zero : motive MyNat.zero)", ORANGE)
route([(tl, 1.4), (2.6, 1.4), (2.6, 8.8), (bl, 8.8)], ORANGE)
label(4.0, 2.25, "constructor zero:\ncase zero", ORANGE)

# constructor succ -> case succ: down the right
tl, tr, tt, tb = box("t2", "succ (n : MyNat) : MyNat", GREEN)
gl, gr, gt, gb = box("b2", "(succ : (n : MyNat) → motive n → motive (MyNat.succ n))",
                     GREEN, pad=0.34)
route([(tr, 2.8), (gr - 5, 2.8), (gr - 5, gt)], GREEN)
label(gr - 5.8, 6.0, "constructor succ:\ncase succ", GREEN, ha="right")

# recursive argument -> also the value at n
rl, rr, rt, rb = box("t2", "(n : MyNat)", RED, pad=0.12, lw=1.4)
ql, qr, qt, qb = box("b2", "(n : MyNat) → motive n", RED, pad=0.14, lw=1.4)
route([(rr - 1.5, rb), (qr - 1.0, qt)], RED)
label(rr + 1.0, 4.3, "recursive argument n:\nalso the value motive n", RED)

# the result
box("b3", "(t : MyNat) → motive t", GREY, lw=1.3)
label(B + 27.5, 11.6, "the result: a function on all of MyNat", GREY)

out = Path(__file__).resolve().parents[2] / "static" / "figures" / "mynat_rec"
fig.savefig(f"{out}.png", dpi=200, facecolor="white")
fig.savefig(f"{out}.pdf", facecolor="white"); print("wrote", out)
