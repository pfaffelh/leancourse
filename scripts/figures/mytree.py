#!/usr/bin/env python3
"""The infinitely branching tree `MyTree` of chapter 1.3 (Strict positivity).

Draws the term
    .node (fun n => if n = 0 then .node .leaf else .leaf n)
A node (filled circle) has one subtree for every natural number; the
edge to the subtree `f n` is labelled `n`. Leaves (squares) carry their
number and are labelled `leaf n`. Only the first subtrees are drawn, the dots stand for the rest.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
BLUE, SAND, INK, MUTED = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e"
K = 4  # subtrees drawn per node

fig, ax = plt.subplots(figsize=(6.2, 3.1))

def edge(x0, y0, x1, y1, label):
    ax.plot([x0, x1], [y0, y1], color=SAND, lw=1.4, zorder=1)
    ax.text(x0 + 0.62 * (x1 - x0), y0 + 0.62 * (y1 - y0), label,
            ha="center", va="center", fontsize=10, color=BLUE,
            bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none"), zorder=2)

def node(x, y):
    ax.add_patch(plt.Circle((x, y), 0.16, facecolor=BLUE, edgecolor=INK, lw=1.0, zorder=3))

def leaf(x, y, a):
    ax.add_patch(plt.Rectangle((x - 0.2, y - 0.2), 0.4, 0.4, facecolor="white",
                               edgecolor=INK, lw=1.1, zorder=3))
    ax.text(x, y, str(a), ha="center", va="center", fontsize=12, color=INK, zorder=4)
    ax.text(x, y - 0.33, f"leaf {a}", ha="center", va="center", fontsize=8, color=MUTED)

def dots(x, y):
    ax.text(x, y, "…", ha="center", va="center", fontsize=16, color=MUTED)

root = (4.0, 2.0)
node(*root)
xs = [1.6, 3.6, 5.1, 6.6]
for n, x in enumerate(xs):
    edge(*root, x, 1.0, str(n))
    if n == 0:
        node(x, 1.0)
        ax.text(x - 0.3, 1.05, "node", ha="right", va="center", fontsize=11, color=MUTED)
        for k in range(K):
            xk = x - 1.5 + k * 0.8
            edge(x, 1.0, xk, 0.0, str(k))
            leaf(xk, 0.0, k)
        dots(x - 1.5 + K * 0.8 + 0.1, 0.0)
    else:
        leaf(x, 1.0, n)
dots(xs[-1] + 1.0, 1.0)

ax.text(root[0] + 0.3, root[1] + 0.05, "node", fontsize=11, color=MUTED, va="center")
ax.text(4.0, -0.85, ".node (fun n => if n = 0 then .node .leaf else .leaf n)",
        ha="center", va="center", fontsize=10, color="#898781", family="monospace")
ax.set_xlim(-0.3, 8.2); ax.set_ylim(-1.05, 2.35); ax.set_aspect("equal"); ax.axis("off")
out = Path(__file__).resolve().parents[2] / "static" / "figures" / "mytree"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
