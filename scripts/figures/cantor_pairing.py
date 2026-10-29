#!/usr/bin/env python3
"""Cantor's enumeration of N x N, diagonal by diagonal.

Illustrates `pairIndex` in chapter 1.2 (Recursion and termination):
each point (m, n) carries its position in the list; arrows run along
a diagonal. The jump from the end of one diagonal to the start of the
next is left out, it would cross the picture.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
BLUE, SAND, INK, MUTED = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e"
D = 4  # last diagonal drawn: m + n = D

order = [(m, d - m) for d in range(D + 1) for m in range(d + 1)]
fig, ax = plt.subplots(figsize=(4.6, 4.6))
for (m0, n0), (m1, n1) in zip(order, order[1:]):
    if m0 + n0 != m1 + n1:
        continue
    ax.annotate("", xy=(m1, n1), xytext=(m0, n0),
                arrowprops=dict(arrowstyle="-|>", color=BLUE, lw=1.6,
                                shrinkA=13, shrinkB=13))
for i, (m, n) in enumerate(order):
    ax.add_patch(plt.Circle((m, n), 0.27, facecolor="white", edgecolor=INK,
                            lw=1.2, zorder=3))
    ax.text(m, n, str(i), ha="center", va="center", fontsize=12, color=INK, zorder=4)
ax.set_xticks(range(D + 1)); ax.set_yticks(range(D + 1))
ax.set_xlabel("$m$", fontsize=13, color=INK); ax.set_ylabel("$n$", fontsize=13, color=INK,
                                                             rotation=0, labelpad=12)
ax.tick_params(colors=MUTED, length=0)
for s in ("top", "right"): ax.spines[s].set_visible(False)
for s in ("left", "bottom"): ax.spines[s].set_color(SAND)
ax.set_xlim(-0.5, D + 0.5); ax.set_ylim(-0.5, D + 0.5); ax.set_aspect("equal")
fig.text(0.5, 0.0, "pairIndex m n is the number at (m, n).",
         ha="center", fontsize=8.5, color="#898781")
fig.tight_layout()
out = Path(__file__).resolve().parents[2] / "static" / "figures" / "cantor_pairing"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
