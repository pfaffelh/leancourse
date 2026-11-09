#!/usr/bin/env python3
"""Three elements of `BinTree` (chapter 1.3, Recursion and termination).

    inductive BinTree where
      | leaf : BinTree
      | node (l : BinTree) (a : ℕ) (r : BinTree) : BinTree

Both constructors build a whole tree. Nodes (circles) carry their
number; leaves (empty squares) carry nothing and mark where a branch
ends. Every end of every tree is drawn as a leaf, so `.leaf` on its
own is a picture too. Under each tree: its Lean term and its height.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE, SAND, INK, MUTED, CODE = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e", "#898781"

# a tree is None (leaf) or (left, a, right)
TREES = [
    (None, ".leaf", 0),
    ((None, 4, None), ".node .leaf 4 .leaf", 1),
    ((None, 3, (None, 4, None)), ".node .leaf 3\n  (.node .leaf 4 .leaf)", 2),
]

fig, ax = plt.subplots(figsize=(8.0, 3.0))
XS = [0.0, 2.8, 6.0]  # roots, one axis so that all three share a scale


def draw(ax, t, x, y, dx):
    """Draw t with its root at (x, y); children dx to the side, 1 lower."""
    if t is None:
        ax.add_patch(plt.Rectangle((x - 0.17, y - 0.17), 0.34, 0.34,
                                   facecolor="white", edgecolor=INK, lw=1.1, zorder=3))
        return
    l, a, r = t
    for side, sub in ((-1, l), (1, r)):
        ax.plot([x, x + side * dx], [y, y - 1], color=SAND, lw=1.4, zorder=1)
        draw(ax, sub, x + side * dx, y - 1, dx / 2)
    ax.add_patch(plt.Circle((x, y), 0.24, facecolor=BLUE, edgecolor=INK, lw=1.0, zorder=3))
    ax.text(x, y, str(a), ha="center", va="center", fontsize=12,
            color="white", fontweight="bold", zorder=4)


for x, (t, term, h) in zip(XS, TREES):
    draw(ax, t, x, 0.0, 0.9)
    ax.text(x, -2.55, term, ha="center", va="top", fontsize=9.5,
            color=CODE, family="monospace", linespacing=1.4)
    ax.text(x, 0.6, f"height {h}", ha="center", va="center", fontsize=10, color=MUTED)
ax.set_xlim(-1.0, 7.6); ax.set_ylim(-3.4, 0.85)
ax.set_aspect("equal"); ax.axis("off")

out = Path(__file__).resolve().parents[2] / "static" / "figures" / "bintree"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
