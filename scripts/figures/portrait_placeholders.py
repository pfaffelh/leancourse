#!/usr/bin/env python3
"""Placeholder portraits for people with no freely licensed photograph.

Deliberately a silhouette, not an invented face: the point is that the
picture is missing, and for whom.  The dashed ring marks the slot as
open.  Replace a file with the real photograph once permission arrives
and nothing else has to change.
"""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Wedge

SAND, MUTED, PAPER = "#c3c2b7", "#8a8980", "#f3f2ee"
# Commelin, Massot and Nash gave permission on 2026-10-15; their real
# photographs are in place, so they are no longer generated here.
PEOPLE = {"gonthier": "GG", "vandoorn": "FvD", "manners": "FM",
          "church": "AC"}
OUT = Path(__file__).resolve().parents[2] / "static" / "figures" / "portraits"


def make(slug, initials):
    fig, ax = plt.subplots(figsize=(3.0, 3.0))
    ax.add_patch(Circle((0, 0), 1.0, facecolor=PAPER, edgecolor="none", zorder=0))
    # head and shoulders, centred so the circular CSS crop keeps everything
    ax.add_patch(Circle((0, 0.26), 0.30, facecolor=SAND, edgecolor="none", zorder=2))
    ax.add_patch(Wedge((0, -0.56), 0.56, 0, 180, facecolor=SAND,
                       edgecolor="none", zorder=2))
    ax.add_patch(Circle((0, 0), 0.97, facecolor="none", edgecolor=SAND,
                        linewidth=2.0, linestyle=(0, (5, 5)), zorder=3))
    ax.text(0, -0.80, initials, ha="center", va="center",
            fontsize=15, color=MUTED, zorder=4)
    ax.set_xlim(-1.02, 1.02); ax.set_ylim(-1.02, 1.02)
    ax.set_aspect("equal"); ax.axis("off")
    fig.subplots_adjust(left=0, right=1, top=1, bottom=0)
    p = OUT / f"placeholder_{slug}.png"
    fig.savefig(p, dpi=130, facecolor="white")
    plt.close(fig)
    print("  wrote", p.name)


OUT.mkdir(parents=True, exist_ok=True)
for slug, ini in PEOPLE.items():
    make(slug, ini)
