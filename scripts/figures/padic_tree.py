#!/usr/bin/env python3
"""Z_3 as the inverse limit of Z/3^n, drawn as a rooted ternary tree.

Perfectoid spaces live over p-adic fields; this is what "p-adic" means
before any of the rest.  Depth n shows Z/3^n, and the tree is the limit.
"""
from pathlib import Path
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
BLUE, SAND, MUTED = "#2a78d6", "#c3c2b7", "#52514e"
P, DEPTH = 3, 4
fig, ax = plt.subplots(figsize=(8.6, 3.8))
nodes = {(): 0.5}
for d in range(DEPTH):
    new = {}
    for path, x in nodes.items():
        w = 1.0 / P ** (d + 1)
        for i in range(P):
            cx = x - w * (P - 1) / 2 + i * w
            new[path + (i,)] = cx
            ax.plot([x, cx], [-d, -d - 1], color=SAND, linewidth=1.1, zorder=1)
    for path, x in nodes.items():
        ax.scatter([x], [-d], s=34, color=BLUE, zorder=3, edgecolor="white", linewidth=0.6)
    ax.text(-0.035, -d, f"$\\mathbf{{Z}}/3^{d}$", ha="right", va="center",
            fontsize=9, color=MUTED)
    nodes = new
for path, x in nodes.items():
    ax.scatter([x], [-DEPTH], s=34, color=BLUE, zorder=3, edgecolor="white", linewidth=0.6)
ax.text(-0.035, -DEPTH, f"$\\mathbf{{Z}}/3^{DEPTH}$", ha="right", va="center",
        fontsize=9, color=MUTED)
print(f"tree with {P**DEPTH} leaves at depth {DEPTH}")
ax.set_xlim(-0.16, 1.03); ax.set_ylim(-DEPTH - 0.5, 0.5); ax.axis("off")
fig.text(0.5, 0.02, r"$\mathbf{Z}_3$ is the inverse limit of the $\mathbf{Z}/3^n$: every branch is a 3-adic integer.",
         ha="center", fontsize=8.5, color="#898781")
fig.tight_layout()
out = Path(__file__).resolve().parents[2] / "static" / "figures" / "padic_tree"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
