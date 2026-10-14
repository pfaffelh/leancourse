#!/usr/bin/env python3
"""The proof assistants: when each began, which tradition it belongs to,
and what it added that its predecessors could not do.

The point of the picture is that the field accumulates rather than
replaces.  Of the seven systems only Automath and LCF stopped, and both
left their architecture to their successors.

Colour is the tradition, not the system:
  blue   -- the de Bruijn line: the proof is a term, rechecked afterwards
  green  -- the LCF line: no proof object, soundness from an abstract type
  orange -- Mizar: declarative proofs over set theory

  python3 scripts/figures/itp_lineage.py [--out PATH]
"""
import argparse
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

HERE = Path(__file__).resolve().parent
BLUE, SAND, INK, MUTED, GRID = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e", "#e1e0d9"
ORANGE, GREEN = "#eb6834", "#1baf7a"
NOW = 2026.8

DEBRUIJN, LCF, DECL = "de Bruijn line", "LCF line", "declarative"
COLOR = {DEBRUIJN: BLUE, LCF: GREEN, DECL: ORANGE}

# name, start, end (None = still running), tradition, what it added
ROWS = [
    ("Automath",   1967, 1980, DEBRUIJN, "the proof as a term"),
    ("LCF",        1972, 1987, LCF,      "automation at no cost in trust"),
    ("Mizar",      1973, None, DECL,     "readable proofs, and a library"),
    ("Isabelle",   1986, None, LCF,      "the logic as a parameter"),
    ("HOL",        1988, None, LCF,      "a small logic that automates well"),
    ("Coq / Rocq", 1989, None, DEBRUIJN, "dependent types and proof terms back"),
    ("Lean",       2013, None, DEBRUIJN, "tactics in the language, one library"),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(
        HERE.parent.parent / "static" / "figures" / "itp_lineage"))
    ap.add_argument("--size", nargs=2, type=float, default=[10, 5.6])
    a = ap.parse_args()

    fig, ax = plt.subplots(figsize=tuple(a.size))
    pitch = 1.5
    ax.set_xlim(1963, NOW + 1.2)
    ax.set_ylim((len(ROWS) - 1) * pitch + 0.75, -0.75)
    ax.set_yticks([])
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(SAND)
    ax.tick_params(colors=MUTED, labelsize=9, length=0)
    ax.set_xticks(range(1970, 2031, 10))
    ax.xaxis.grid(True, color=GRID, linewidth=0.8, zorder=0)

    for i, (name, start, end, line, added) in enumerate(ROWS):
        y = i * pitch
        alive = end is None
        stop = NOW if alive else end
        ax.add_patch(FancyBboxPatch(
            (start, y - 0.16), stop - start, 0.32,
            boxstyle="round,pad=0,rounding_size=0.16",
            linewidth=0, facecolor=COLOR[line], alpha=1.0 if alive else 0.38,
            zorder=3))
        ax.text(start, y - 0.33, name, ha="left", va="bottom", color=INK,
                fontsize=10.5, fontweight="bold" if name == "Lean" else "normal",
                zorder=4)
        ax.text(start, y + 0.36, added, ha="left", va="top", color=MUTED,
                fontsize=8.8, zorder=4)
        if not alive:
            ax.text(stop + 0.7, y, "stopped", ha="left", va="center",
                    color=MUTED, fontsize=8.2, style="italic", zorder=4)

    # legend in the empty top right
    for i, line in enumerate((DEBRUIJN, LCF, DECL)):
        y = -0.35 + i * 0.52
        ax.add_patch(FancyBboxPatch(
            (1999, y - 0.11), 1.5, 0.22,
            boxstyle="round,pad=0,rounding_size=0.11",
            linewidth=0, facecolor=COLOR[line], zorder=3))
        ax.text(2001.3, y, line, ha="left", va="center", color=INK, fontsize=9)

    fig.tight_layout()
    out = Path(a.out)
    fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
    fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
