#!/usr/bin/env python3
"""New GitHub repositories for the three interactive theorem provers,
per million new repositories overall.

The raw counts are misleading at the right-hand edge.  In September 2026
the number of all new GitHub repositories jumped by 37 % in one month,
and on top of that the Justin Sun Prize (announced 16 September 2026,
up to one million dollars per problem, paid only for a machine-verified
proof) produced a burst of Lean repositories: 666 of that month's 3 224
carry a prize identifier, and a single account created 284 of them.
Normalizing by the overall repository count removes the first effect;
the second is left in and stated in the caption, because it is a real
part of what happened.

Data: github_language_monthly.csv, harvested with the scripts in
~/bwSyncShare/Vortraege/20260720_CRC (GitHub search `language:X`,
primary language, forks excluded).

  python3 scripts/make_itp_figure.py [--from 2018] [--out PATH]
"""
import argparse
import csv
from collections import defaultdict
from datetime import date
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
BLUE, SAND, INK, MUTED, GRID = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e", "#e1e0d9"
LANGS = ["Lean", "Coq", "Isabelle"]
COLOR = {"Lean": BLUE, "Coq": "#eb6834", "Isabelle": "#1baf7a"}
LABEL = {"Coq": "Coq / Rocq"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--from", dest="y0", type=int, default=2018)
    ap.add_argument("--out", default=str(
        HERE.parent / "static" / "figures" / "itp_github_repos_per_million"))
    ap.add_argument("--size", nargs=2, type=float, default=[10, 4.2])
    a = ap.parse_args()

    # monthly -> quarterly sums, so that one noisy month cannot carry a point
    num = defaultdict(lambda: defaultdict(int))
    den = defaultdict(int)
    for r in csv.DictReader((HERE / "data" / "github_language_monthly.csv").open()):
        y, m = int(r["month"][:4]), int(r["month"][5:7])
        if y < a.y0:
            continue
        q = (y, (m - 1) // 3 + 1)
        for l in LANGS:
            num[l][q] += int(r[l])
        den[q] += int(r["ALL"])

    quarters = sorted(den)
    # a quarter with fewer than three months of data would sit too low
    counts = defaultdict(int)
    for r in csv.DictReader((HERE / "data" / "github_language_monthly.csv").open()):
        y, m = int(r["month"][:4]), int(r["month"][5:7])
        if y >= a.y0:
            counts[(y, (m - 1) // 3 + 1)] += 1
    quarters = [q for q in quarters if counts[q] == 3]

    x = [q[0] + (q[1] - 1) / 4 for q in quarters]
    series = {l: [num[l][q] / den[q] * 1e6 for q in quarters] for l in LANGS}

    fig, ax = plt.subplots(figsize=tuple(a.size))
    ax.yaxis.grid(True, color=GRID, linewidth=0.8, zorder=0)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color(SAND)
    ax.tick_params(colors=MUTED, labelsize=9, length=0)
    for l in reversed(LANGS):
        ax.plot(x, series[l], color=COLOR[l], linewidth=2.6 if l == "Lean" else 2.0,
                label=LABEL.get(l, l), zorder=4 if l == "Lean" else 3)

    ymax = max(max(v) for v in series.values())
    ax.set_ylim(0, ymax * 1.22)
    ax.set_xlim(min(x) - 0.1, max(x) + 1.25)
    for l in LANGS:
        ax.text(max(x) + 0.12, series[l][-1], f"  {LABEL.get(l, l)}  {series[l][-1]:.0f}",
                va="center", fontsize=10.5, color=INK,
                fontweight="bold" if l == "Lean" else "normal")
    handles, labels = ax.get_legend_handles_labels()
    ax.legend(handles[::-1], labels[::-1], frameon=False, loc="upper left",
              fontsize=11, labelcolor=INK)
    ax.set_ylabel("new repositories per million", color=MUTED, fontsize=9)

    fig.text(0.99, 0.005,
             "GitHub search language:X (primary language, forks excluded), by creation "
             f"quarter, per million new repositories overall · retrieved {date.today()}",
             ha="right", fontsize=7.5, color="#898781")
    fig.tight_layout()
    out = Path(a.out)
    fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
    fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white")
    print("wrote", out, "/ quarters:", quarters[0], "..", quarters[-1])


if __name__ == "__main__":
    main()
