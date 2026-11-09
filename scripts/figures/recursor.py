#!/usr/bin/env python3
"""How a recursor is built from the declaration (chapter 1.3, deck).

Three figures, each with the declaration on top and a generated
constant below. Parts of the declaration are boxed in a colour; an
arrow leads to the part they produce.

* mynat_rec      -- `MyNat` and the type of `MyNat.rec`
* rec_general    -- an arbitrary `T` and the type of `T.rec`
* mynat_casesOn  -- `MyNat` and the type of `MyNat.casesOn`

Colours: blue the type -> motive, orange/grey the other constructors,
green a constructor with arguments -> its case, purple non-recursive
arguments, red recursive arguments.

Text is monospace; positions are counted in characters, so a box is
given by the substring it surrounds. Lines carry a white background,
arrows run underneath them.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from matplotlib.path import Path as MPath

INK = "#0b0b0b"
BLUE, ORANGE, GREEN, RED, GREY, PURPLE = (
    "#2a78d6", "#d9822b", "#2e9b5f", "#c8423b", "#898781", "#8a4fbf")
FS = 13                       # font size in pt
CW = 0.602 * FS / 72          # width of one character of DejaVu Sans Mono, inches
PITCH = 1.75 * FS / 72        # one unit of y, inches
OUT = Path(__file__).resolve().parents[2] / "static" / "figures"


class Fig:
    def __init__(self, lines, width, y0, y1):
        """lines: name -> (x of first character, y, text); y counts downwards."""
        self.lines = lines
        self.lfs = 10.5           # font size of the labels
        self.fig = plt.figure(figsize=(width * CW, (y1 - y0) * PITCH))
        self.ax = ax = self.fig.add_axes((0, 0, 1, 1))
        ax.set_xlim(0, width); ax.set_ylim(y1, y0); ax.axis("off")
        for x, y, s in lines.values():   # leading blanks get no white background
            ax.text(x + len(s) - len(s.lstrip()), y, s.lstrip(),
                    family="DejaVu Sans Mono", fontsize=FS, color=INK,
                    va="center", ha="left", zorder=3,
                    bbox=dict(facecolor="white", edgecolor="none", pad=1.5))

    def span(self, line, sub):
        x, y, s = self.lines[line]
        i = s.index(sub)
        return x + i, x + i + len(sub), y

    def box(self, first, sub, color, last=None, pad=0.22, lw=1.6):
        """Box around `sub` in line `first`; with `last`, around the lines
        first..last, from the start of `sub` to the end of the longest
        line. Returns (left, right, top, bottom)."""
        l, r, y = self.span(first, sub)
        yb = y
        if last:
            names = list(self.lines)
            for n in names[names.index(first):names.index(last) + 1]:
                x, yy, s = self.lines[n]
                r = max(r, x + len(s.rstrip(" →")))
                yb = yy
        top, h = y - 0.36, yb - y + 0.72
        for fc, ec, a, z in ((color, "none", 0.10, 2), ("none", color, 1.0, 4)):
            self.ax.add_patch(FancyBboxPatch(
                (l, top), r - l, h, boxstyle=f"round,pad={pad},rounding_size=0.25",
                facecolor=fc, edgecolor=ec, alpha=a, lw=lw, zorder=z))
        return l - pad, r + pad, top - pad, top + h + pad

    def route(self, points, color, r=0.8):
        """Arrow along a polyline through `points`, corners rounded."""
        def towards(a, b, d):
            dx, dy = b[0] - a[0], b[1] - a[1]
            L = (dx * dx + dy * dy) ** 0.5
            d = min(d, L / 2)
            return (a[0] + dx * d / L, a[1] + dy * d / L)
        verts, codes = [points[0]], [MPath.MOVETO]
        for p, q, n in zip(points, points[1:], points[2:]):
            verts += [towards(q, p, r), q, towards(q, n, r)]
            codes += [MPath.LINETO, MPath.CURVE3, MPath.CURVE3]
        verts.append(points[-1]); codes.append(MPath.LINETO)
        self.ax.add_patch(FancyArrowPatch(
            path=MPath(verts, codes), color=color, lw=1.8, mutation_scale=18,
            arrowstyle="-|>,head_width=0.3,head_length=0.6", zorder=1))

    def label(self, x, y, s, color, ha="left"):
        self.ax.text(x, y, s, fontsize=self.lfs, color=color, ha=ha, va="center",
                     zorder=5, linespacing=1.25,
                     bbox=dict(facecolor="white", edgecolor="none", pad=1.0))

    def save(self, name):
        out = OUT / name
        self.fig.savefig(f"{out}.png", dpi=200, facecolor="white")
        self.fig.savefig(f"{out}.pdf", facecolor="white"); print("wrote", out)
        plt.close(self.fig)


DECL = ["inductive MyNat where", "  | zero : MyNat", "  | succ (n : MyNat) : MyNat"]


def mynat(bottom, red_label, rec=True):
    """`MyNat` on top, `bottom` (four lines) below."""
    X, B = 16, 6
    ys = [7.4, 8.8, 10.2, 11.6] if rec else [7.4, 8.8, 10.2, 12.3]
    lines = {f"t{i}": (X, 1.4 * i, s) for i, s in enumerate(DECL)}
    lines |= {f"b{i}": (B, y, s) for i, (y, s) in enumerate(zip(ys, bottom))}
    f = Fig(lines, 70, -1.7, ys[-1] + 0.9)

    tl, tr, tt, tb = f.box("t0", "MyNat", BLUE)
    bl, br, bt, bb = f.box("b0", "{motive : MyNat → Sort u}", BLUE)
    f.route([((tl + tr) / 2, tt), ((tl + tr) / 2, -1.3), (1.0, -1.3), (1.0, 5.3),
             (bl + 4, 5.3), (bl + 4, bt)], BLUE)
    f.label(5.0, 4.65, "the type: the motive says what to define on it", BLUE)

    tl, tr, tt, tb = f.box("t1", "zero : MyNat", ORANGE)
    bl, br, bt, bb = f.box("b1", "(zero : motive MyNat.zero)", ORANGE)
    f.route([(tl, 1.4), (2.6, 1.4), (2.6, 8.8), (bl, 8.8)], ORANGE)
    f.label(4.0, 2.25, "constructor zero:\ncase zero", ORANGE)

    succ = bottom[2].strip().rstrip(" →")
    y2 = lines["b2"][1]
    tl, tr, tt, tb = f.box("t2", "succ (n : MyNat) : MyNat", GREEN)
    gl, gr, gt, gb = f.box("b2", succ, GREEN, pad=0.34)
    rl, rr, rt, rb = f.box("t2", "(n : MyNat)", RED, pad=0.12, lw=1.4)
    if rec:
        gx = gr - 5
        f.route([(tr, 2.8), (gx, 2.8), (gx, gt)], GREEN)
        f.label(gx - 0.8, 6.0, "constructor succ:\ncase succ", GREEN, ha="right")
        ql, qr, qt, qb = f.box("b2", "(n : MyNat) → motive n", RED, pad=0.14, lw=1.4)
        f.route([(rr - 1.5, rb), (qr - 1.0, qt)], RED)
        f.label(rr + 1.0, 4.3, red_label, RED)
    else:
        # the motive line is long: green comes down right of it, red goes
        # round the right end of the case and enters its box from below
        gx = 65
        f.route([(tr, 2.8), (gx, 2.8), (gx, y2 + 0.55), (gr, y2 + 0.55)], GREEN)
        f.label(gx - 0.8, lines["b1"][1], "constructor succ:\ncase succ", GREEN, ha="right")
        ql, qr, qt, qb = f.box("b2", "(n : MyNat)", RED, pad=0.14, lw=1.4)
        yb = (gb + lines["b3"][1] - 0.58) / 2
        f.route([(rr - 1.5, rb), (rr - 1.5, 3.9), (68, 3.9), (68, yb),
                 (qr - 2.5, yb), (qr - 2.5, qb)], RED, r=0.6)
        f.label(rr + 1.0, 5.0, red_label, RED)
    return f


# MyNat.rec
f = mynat(["MyNat.rec : {motive : MyNat → Sort u} →",
           "  (zero : motive MyNat.zero) →",
           "  (succ : (n : MyNat) → motive n → motive (MyNat.succ n)) →",
           "  (t : MyNat) → motive t"],
          "recursive argument n:\nalso the value motive n")
f.box("b3", "(t : MyNat) → motive t", GREY, lw=1.3)
f.label(6 + 27.5, 7.4 + 4.2, "the result: a function on all of MyNat", GREY)
f.save("mynat_rec")

# MyNat.casesOn
f = mynat(["MyNat.casesOn : {motive : MyNat → Sort u} → (t : MyNat) →",
           "  (zero : motive MyNat.zero) →",
           "  (succ : (n : MyNat) → motive (MyNat.succ n)) →",
           "  motive t"],
          "recursive argument n: no value\nmotive n, so no recursion",
          rec=False)
f.box("b0", "(t : MyNat)", GREY, lw=1.3)
f.box("b3", "motive t", GREY, lw=1.3)
f.label(6 + 13, 12.3, "t comes first; the result is one value motive t", GREY)
f.save("mynat_casesOn")

# T.rec in general
X, B = 12, 3
TOP = ["inductive T where",
       "  | c₁ (b₁ : B₁) … (bₗ : Bₗ) (r₁ … rₖ : T) : T",
       "  | …"]
BOT = ["T.rec : {motive : T → Sort u} →",
       "  (f₁ : (b₁ : B₁) → … → (bₗ : Bₗ) →",
       "        (r₁ … rₖ : T) → motive r₁ → … → motive rₖ →",
       "        motive (c₁ b₁ … bₗ r₁ … rₖ)) →",
       "  … → (t : T) → motive t"]
P = 1.7                       # line pitch of the recursor
lines = {f"t{i}": (X, 1.4 * i, s) for i, s in enumerate(TOP)}
lines |= {f"b{i}": (B, 7.4 + P * i, s) for i, s in enumerate(BOT)}
yb = lambda i: 7.4 + P * i
f = Fig(lines, 70, -1.7, yb(4) + 0.9)
f.lfs = 12.5                  # this figure is shown smaller on the slide

tl, tr, tt, tb = f.box("t0", "T", BLUE)
bl, br, bt, bb = f.box("b0", "{motive : T → Sort u}", BLUE)
f.route([((tl + tr) / 2, tt), ((tl + tr) / 2, -1.3), (0.8, -1.3), (0.8, 5.3),
         (bl + 4, 5.3), (bl + 4, bt)], BLUE)
f.label(3.0, 4.7, "the type: motive", BLUE)

tl, tr, tt, tb = f.box("t2", "…", GREY, pad=0.15)
ql, qr, qt, qb = f.box("b4", "…", GREY, pad=0.15)
f.route([(tl, 2.8), (2.0, 2.8), (2.0, yb(4)), (ql, yb(4))], GREY)
f.label(3.3, 3.65, "c₂ … cₘ:\ncases f₂ … fₘ", GREY)

c1 = "c₁ (b₁ : B₁) … (bₗ : Bₗ) (r₁ … rₖ : T) : T"
tl, tr, tt, tb = f.box("t1", c1, GREEN)
gl, gr, gt, gb = f.box("b1", "(f₁ :", GREEN, last="b3", pad=0.34)
f.route([(gr - 1.5, tb), (gr - 1.5, gt)], GREEN)
f.label(gr - 0.7, 4.4, "constructor c₁:\ncase f₁", GREEN)

pl, pr, pt, pb = f.box("t1", "(b₁ : B₁) … (bₗ : Bₗ)", PURPLE, pad=0.12, lw=1.4)
ql, qr, qt, qb = f.box("b1", "(b₁ : B₁) → … → (bₗ : Bₗ)", PURPLE, pad=0.14, lw=1.4)
f.route([((pl + pr) / 2, pb), ((ql + qr) / 2 + 3, qt)], PURPLE)
f.label((pl + pr) / 2 + 1.0, 3.3, "non-recursive\narguments:\npassed on", PURPLE)

rl, rr, rt, rb = f.box("t1", "(r₁ … rₖ : T)", RED, pad=0.12, lw=1.4)
ql, qr, qt, qb = f.box("b2", "(r₁ … rₖ : T) → motive r₁ → … → motive rₖ", RED,
                       pad=0.14, lw=1.4)
f.route([((rl + rr) / 2, rb), ((rl + rr) / 2, qt)], RED)
f.label((rl + rr) / 2 - 0.8, 5.5, "recursive arguments:\nalso the values\nmotive r₁ … motive rₖ",
        RED, ha="right")

f.box("b4", "(t : T) → motive t", GREY, lw=1.3)
f.label(B + 27, yb(4), "the result: a function on all of T", GREY)
f.save("rec_general")
