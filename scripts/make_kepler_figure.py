#!/usr/bin/env python3
"""Cannonball stack: the packing Kepler conjectured to be optimal.

House style of the arxiv_fulltext_* / github_language_* figures:
blue is the subject, sand is recessive, ink for labels, no frame.
"""
import math
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

BLUE, SAND, INK, MUTED = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e"

R = 1.0
dx, dy = 2 * R, R * math.sqrt(3)
LAYERS = 5                                   # front rows, bottom to top

fig, ax = plt.subplots(figsize=(7.6, 4.6))

# two receding layers behind, drawn first and washed out
for depth, (col, alpha, off) in enumerate(
        [(SAND, 0.55, (0.62 * dx, 0.40 * dy)), (SAND, 0.85, (0.31 * dx, 0.20 * dy))]):
    for row in range(LAYERS - 1):
        n = LAYERS - 1 - row
        y = row * dy + off[1]
        x0 = -(n - 1) * dx / 2 + off[0]
        for i in range(n):
            ax.add_patch(Circle((x0 + i * dx, y), R, facecolor=col, alpha=alpha,
                                edgecolor="white", linewidth=1.2, zorder=1 + depth))

# the front layer, in blue
for row in range(LAYERS):
    n = LAYERS - row
    y = row * dy
    x0 = -(n - 1) * dx / 2
    for i in range(n):
        ax.add_patch(Circle((x0 + i * dx, y), R, facecolor=BLUE,
                            edgecolor="white", linewidth=1.4, zorder=5))

ax.set_aspect("equal")
ax.axis("off")
xl = -LAYERS * R - 0.35
xr = LAYERS * R + 0.62 * dx + 0.35
ax.set_xlim(xl, xr)
ax.set_ylim(-R - 0.35, (LAYERS - 1) * dy + 0.40 * dy + R + 0.35)

ax.text(xr, (LAYERS - 1) * dy + 0.4 * dy + R,
        r"density $\dfrac{\pi}{\sqrt{18}} \approx 0.7405$",
        ha="right", va="top", fontsize=13, color=INK)
fig.text(0.99, 0.015,
         "Kepler 1611: no packing of equal spheres is denser.  "
         "Hales 1998, formally verified 2014 (Flyspeck).",
         ha="right", fontsize=7.5, color="#898781")

out = Path("/home/pfaffelh/Code/lean/leancourse/static/figures/kepler_packing")
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white")
print("wrote", out)
