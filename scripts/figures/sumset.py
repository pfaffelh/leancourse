#!/usr/bin/env python3
"""A set of small doubling and its sumset.

The polynomial Freiman-Ruzsa conjecture, proved by Gowers, Green, Manners
and Tao in 2023 and formalized in three weeks, says that a set with
|A+A| <= K|A| is covered by polynomially many in K translates of a
subgroup.  Everything here is computed from the drawn set A.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

BLUE, SAND, INK, MUTED = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e"
A = [(x, y) for x in range(4) for y in range(3)]
A.remove((3, 0)); A.remove((0, 2))
S = sorted({(a + c, b + d) for (a, b) in A for (c, d) in A})
K = len(S) / len(A)
print(f"|A| = {len(A)}, |A+A| = {len(S)}, doubling K = {K:.2f}")

fig, axes = plt.subplots(1, 2, figsize=(9.2, 3.6))
for ax, (pts, title, col) in zip(axes, [(A, f"$A$,  $|A| = {len(A)}$", BLUE),
                                        (S, f"$A+A$,  $|A+A| = {len(S)}$", SAND)]):
    if pts is S:
        for (x, y) in A:
            ax.add_patch(Rectangle((2 * x - .42, 2 * y - .42), .84, .84,
                                   facecolor="none", edgecolor=BLUE, lw=1.6, zorder=3))
    for (x, y) in pts:
        ax.add_patch(Rectangle((x - .42, y - .42), .84, .84, facecolor=col,
                               edgecolor="white", lw=1.2, zorder=2))
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_xlim(-1, 7); ax.set_ylim(-1, 5)
    ax.set_title(title, fontsize=12, color=INK, pad=4)
axes[1].text(6.6, -0.75, f"$K = {K:.2f}$", ha="right", fontsize=11, color=MUTED)
fig.text(0.5, 0.005,
         "Small doubling forces structure: that is what the polynomial "
         "Freiman-Ruzsa conjecture makes precise.",
         ha="center", fontsize=8.5, color="#898781")
fig.tight_layout()
out = Path(__file__).resolve().parents[2] / "static" / "figures" / "sumset"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
