#!/usr/bin/env python3
"""Turning numbers of closed plane curves.

The turning number is invariant under regular homotopy (Whitney-Graustein),
so a circle cannot be turned inside out in the plane: that would send +1
to -1.  In three dimensions the corresponding obstruction vanishes, and a
sphere *can* be everted -- Smale's paradox, a consequence of the h-principle
and the subject of the sphere eversion formalization.

Each label is the number this script computed from the drawn curve, not a
number typed in by hand.
"""
from pathlib import Path
import numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE, SAND, INK, MUTED = "#2a78d6", "#c3c2b7", "#0b0b0b", "#52514e"
T = np.linspace(0, 2 * np.pi, 4001)

def polar(r):      return lambda t: (r(t) * np.cos(t), r(t) * np.sin(t))
CURVES = {
    "circle":        lambda t: (np.cos(t), np.sin(t)),
    "figure eight":  lambda t: (np.sin(t), np.sin(t) * np.cos(t)),
    "limacon":       polar(lambda t: 1 + 2 * np.cos(t)),
    "three loops":   polar(lambda t: 1 + 2 * np.cos(2 * t)),
}

def turning(f):
    x, y = f(T)
    dx, dy = np.gradient(x, T), np.gradient(y, T)
    assert np.min(dx**2 + dy**2) > 1e-6, "curve is not an immersion"
    ang = np.unwrap(np.arctan2(dy, dx))
    return (ang[-1] - ang[0]) / (2 * np.pi)

vals = {k: turning(f) for k, f in CURVES.items()}
for k, v in vals.items():
    n = round(v)
    assert abs(v - n) < 1e-3, (k, v)
    print(f"  {k:14} turning number {n:+d}")

fig, axes = plt.subplots(1, 4, figsize=(10.4, 3.0))
for ax, (name, f) in zip(axes, CURVES.items()):
    x, y = f(T)
    ax.plot(x, y, color=BLUE, linewidth=2.2, solid_capstyle="round")
    k = len(T) // 7
    ax.annotate("", xy=(x[k + 60], y[k + 60]), xytext=(x[k], y[k]),
                arrowprops=dict(arrowstyle="-|>", color=BLUE, lw=2.2))
    ax.set_aspect("equal"); ax.axis("off")
    m = 1.18 * max(np.abs(x).max(), np.abs(y).max())
    ax.set_xlim(-m, m); ax.set_ylim(-m * 0.92, m * 1.14)
    ax.set_title(f"turning number {round(vals[name]):d}", fontsize=11, color=INK, pad=2)
fig.text(0.5, 0.005,
         "Invariant under regular homotopy, so a circle cannot be everted in the plane. "
         "In three dimensions the obstruction disappears.",
         ha="center", fontsize=8.5, color="#898781")
fig.tight_layout()
out = Path(__file__).resolve().parents[2] / "static" / "figures" / "turning_number"
fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white"); print("wrote", out)
