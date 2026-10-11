#!/usr/bin/env python3
"""The Cantor set: the prototype of a profinite set.

Condensed mathematics, the setting of the Liquid Tensor Experiment,
replaces topological spaces by sheaves on profinite sets.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
BLUE, SAND = "#2a78d6", "#c3c2b7"
LEVELS = 7
fig, ax = plt.subplots(figsize=(8.0, 3.0))
segs = [(0.0, 1.0)]
for k in range(LEVELS):
    y = -k
    for (a, b) in segs:
        ax.plot([a, b], [y, y], color=BLUE if k == LEVELS - 1 else SAND,
                linewidth=5.0 if k == LEVELS - 1 else 4.4, solid_capstyle="butt")
    segs = [s for (a, b) in segs for s in ((a, a + (b - a) / 3), (b - (b - a) / 3, b))]
print(f"{LEVELS} levels, {2**LEVELS} intervals at the bottom")
ax.set_xlim(-0.02, 1.02); ax.set_ylim(-LEVELS + 0.4, 0.6); ax.axis("off")
fig.text(0.5, 0.02, "Condensed mathematics is built on profinite sets; "
         "the Cantor set is the prototype.", ha="center", fontsize=8.5, color="#898781")
fig.tight_layout()
out = Path(__file__).resolve().parents[2] / "static" / "figures" / "cantor_profinite"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
