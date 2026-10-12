#!/usr/bin/env python3
"""Share of arXiv math papers whose results are checked in Lean.

Plotted per 100 papers rather than as a weekly count, because the
denominator moved: arXiv math went from about a thousand submissions a
week in January 2026 to about twenty-four hundred at the end of
September.  A rising count would partly be that growth; the share shows
the level, which is still under two in a hundred.

Data: scripts/data/arxiv_math_weekly.csv -- a full-text scan of every
arXiv math submission of the period for uses of Lean and Mathlib,
harvested with arxiv_fulltext_harvest.py / _scan.py (see
ANLEITUNG_arxiv_fulltext.md).  `complete` marks the weeks that were
fully covered; the partial weeks at either end are dropped.

  python3 scripts/make_arxiv_figure.py [--out PATH]
"""
import argparse
import csv
from datetime import date, datetime
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.dates as mdates

HERE = Path(__file__).resolve().parent
BLUE, SAND, INK, MUTED, GRID = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e", "#e1e0d9"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(
        HERE.parent / "static" / "figures" / "arxiv_lean_formalized_share"))
    ap.add_argument("--size", nargs=2, type=float, default=[10, 4.2])
    a = ap.parse_args()

    weeks, share = [], []
    for r in csv.DictReader((HERE / "data" / "arxiv_math_weekly.csv").open()):
        if r["complete"] != "1":
            continue
        weeks.append(datetime.strptime(r["week_start"], "%Y-%m-%d").date())
        share.append(int(r["lean_formalized"]) / int(r["papers"]) * 100)

    fig, ax = plt.subplots(figsize=tuple(a.size))
    ax.yaxis.grid(True, color=GRID, linewidth=0.8, zorder=0)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(SAND)
    ax.tick_params(colors=MUTED, labelsize=9, length=0)

    ax.bar(weeks, share, width=5.4, color=BLUE, zorder=3)
    ax.set_ylim(0, max(share) * 1.25)
    ax.set_ylabel("papers per 100 with a Lean proof", color=MUTED, fontsize=9)
    ax.xaxis.set_major_locator(mdates.MonthLocator())
    ax.xaxis.set_major_formatter(mdates.DateFormatter("%b"))

    fig.text(0.99, 0.005,
             "full-text scan of all arXiv math submissions, by submission week "
             f"· retrieved {date.today()}",
             ha="right", fontsize=7.5, color="#898781")
    fig.tight_layout()
    out = Path(a.out)
    fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
    fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white")
    print("wrote", out, "/ weeks:", weeks[0], "..", weeks[-1],
          "/ share:", f"{share[0]:.2f}", "..", f"{share[-1]:.2f}")


if __name__ == "__main__":
    main()
