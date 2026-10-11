#!/usr/bin/env python3
"""A planar map, properly coloured with four colours.

The map is a Voronoi diagram of random seed points, clipped to a box;
adjacency comes from the Voronoi ridges, so it is a genuine planar
graph.  The colouring is computed by backtracking and *verified*: the
script asserts that no two adjacent regions share a colour.
"""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from scipy.spatial import Voronoi

BLUE, SAND, INK = "#2a78d6", "#c3c2b7", "#0b0b0b"
PALETTE = [BLUE, "#eb6834", "#1baf7a", "#f2c744"]
BOX = (0.0, 10.0, 0.0, 6.0)


def clip(poly, box):
    """Sutherland-Hodgman against an axis-aligned box."""
    x0, x1, y0, y1 = box
    edges = [(lambda p: p[0] >= x0, lambda a, b: inter(a, b, 0, x0)),
             (lambda p: p[0] <= x1, lambda a, b: inter(a, b, 0, x1)),
             (lambda p: p[1] >= y0, lambda a, b: inter(a, b, 1, y0)),
             (lambda p: p[1] <= y1, lambda a, b: inter(a, b, 1, y1))]
    for inside, cut in edges:
        out, n = [], len(poly)
        if n == 0:
            return []
        for i in range(n):
            a, b = poly[i - 1], poly[i]
            if inside(b):
                if not inside(a):
                    out.append(cut(a, b))
                out.append(b)
            elif inside(a):
                out.append(cut(a, b))
        poly = out
    return poly


def inter(a, b, axis, val):
    t = (val - a[axis]) / (b[axis] - a[axis])
    return (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))


def colour(adj, n):
    col = [-1] * n
    order = sorted(range(n), key=lambda i: -len(adj[i]))

    def go(k):
        if k == n:
            return True
        v = order[k]
        for c in range(4):
            if all(col[u] != c for u in adj[v]):
                col[v] = c
                if go(k + 1):
                    return True
                col[v] = -1
        return False
    assert go(0), "no 4-colouring found"
    return col


def main():
    rng = np.random.default_rng(20261011)
    pts = rng.uniform([BOX[0], BOX[2]], [BOX[1], BOX[3]], size=(34, 2))
    # Lloyd relaxation: rounder, more map-like regions
    for _ in range(3):
        v = Voronoi(np.vstack([pts, mirror(pts)]))
        new = []
        for i in range(len(pts)):
            r = v.regions[v.point_region[i]]
            if not r or -1 in r:
                new.append(pts[i]); continue
            p = clip([tuple(v.vertices[j]) for j in r], BOX)
            new.append(np.mean(p, axis=0) if p else pts[i])
        pts = np.array(new)

    vor = Voronoi(np.vstack([pts, mirror(pts)]))
    n = len(pts)
    adj = [set() for _ in range(n)]
    for (a, b) in vor.ridge_points:
        if a < n and b < n:
            adj[a].add(b); adj[b].add(a)

    col = colour(adj, n)
    for v in range(n):
        for u in adj[v]:
            assert col[u] != col[v], "colouring is not proper"
    print(f"{n} regions, {sum(len(a) for a in adj)//2} borders, 4-colouring verified")

    fig, ax = plt.subplots(figsize=(8.4, 5.2))
    for i in range(n):
        r = vor.regions[vor.point_region[i]]
        p = clip([tuple(vor.vertices[j]) for j in r], BOX)
        if p:
            ax.add_patch(Polygon(p, facecolor=PALETTE[col[i]], edgecolor="white",
                                 linewidth=2.0, zorder=2))
    ax.set_xlim(BOX[0], BOX[1]); ax.set_ylim(BOX[2], BOX[3])
    ax.set_aspect("equal"); ax.axis("off")
    fig.text(0.99, 0.01,
             "Appel and Haken 1976; formally verified by Gonthier in 2005.",
             ha="right", fontsize=7.5, color="#898781")
    fig.tight_layout()
    out = Path(__file__).resolve().parents[2] / "static" / "figures" / "four_colour"
    fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
    fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white")
    print("wrote", out)


def mirror(p):
    """Reflect the seeds across all four sides, so every real cell is bounded."""
    x0, x1, y0, y1 = BOX
    out = []
    for (mx, bx) in ((-1, 2 * x0), (-1, 2 * x1)):
        out.append(np.column_stack([mx * p[:, 0] + bx, p[:, 1]]))
    for (my, by) in ((-1, 2 * y0), (-1, 2 * y1)):
        out.append(np.column_stack([p[:, 0], my * p[:, 1] + by]))
    return np.vstack(out)


if __name__ == "__main__":
    main()
