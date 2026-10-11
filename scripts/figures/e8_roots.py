#!/usr/bin/env python3
"""The 240 roots of E8, projected onto the Coxeter plane.

E8 is the lattice that solves the sphere packing problem in dimension
eight (Viazovska 2016).  Everything here is computed, not drawn: the
240 roots are generated from their definition, the Coxeter element is
built as a product of the eight simple reflections, and the projection
uses its eigenvector for exp(2*pi*i/30).  The script checks the root
count, the Coxeter number and the resulting ring structure.
"""
from pathlib import Path
import itertools
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BLUE, SAND, INK = "#2a78d6", "#c3c2b7", "#0b0b0b"


def roots():
    R = []
    for i, j in itertools.combinations(range(8), 2):
        for si in (1, -1):
            for sj in (1, -1):
                v = np.zeros(8); v[i] = si; v[j] = sj
                R.append(v)
    for signs in itertools.product((1, -1), repeat=8):
        if np.prod(signs) == 1:                      # even number of minus signs
            R.append(np.array(signs, float) / 2)
    return np.array(R)


def simple_roots():
    e = np.eye(8)
    a1 = (e[0] - e[1] - e[2] - e[3] - e[4] - e[5] - e[6] + e[7]) / 2
    return np.array([a1, e[0] + e[1], e[1] - e[0], e[2] - e[1],
                     e[3] - e[2], e[4] - e[3], e[5] - e[4], e[6] - e[5]])


def main():
    R = roots()
    assert len(R) == 240, len(R)
    assert np.allclose(np.einsum("ij,ij->i", R, R), 2.0)

    S = simple_roots()
    C = np.array([[2 * S[i] @ S[j] / (S[j] @ S[j]) for j in range(8)] for i in range(8)])
    assert np.allclose(np.diag(C), 2) and set(np.unique(C)) <= {-1.0, 0.0, 2.0}, C

    cox = np.eye(8)
    for a in S:                                      # w = s_1 s_2 ... s_8
        cox = cox @ (np.eye(8) - 2 * np.outer(a, a) / (a @ a))
    ev, evec = np.linalg.eig(cox)
    h = 30                                           # Coxeter number of E8
    assert np.allclose(np.sort(np.angle(ev) % (2 * np.pi)),
                       np.sort(np.array([1, 7, 11, 13, 17, 19, 23, 29]) * 2 * np.pi / h)), \
        "exponents are not those of E8"

    k = int(np.argmin(np.abs(ev - np.exp(2j * np.pi / h))))
    v = evec[:, k]
    u1, u2 = np.real(v), np.imag(v)
    u1 /= np.linalg.norm(u1); u2 /= np.linalg.norm(u2)
    assert abs(u1 @ u2) < 1e-9, "projection plane is not orthogonal"

    xy = np.column_stack([R @ u1, R @ u2])
    rad = np.round(np.linalg.norm(xy, axis=1), 6)
    rings = sorted(set(rad))
    counts = [int((rad == r).sum()) for r in rings]
    print(f"240 roots, {len(rings)} rings, sizes {counts}")
    assert counts == [30] * 8, counts

    fig, ax = plt.subplots(figsize=(6.4, 6.4))
    # the edges of the Gosset polytope: roots at the minimal mutual distance
    G = R @ R.T
    for i in range(240):
        for j in range(i + 1, 240):
            if abs(G[i, j] - 1.0) < 1e-9:            # angle 60 degrees
                ax.plot(*zip(xy[i], xy[j]), color=SAND, linewidth=0.35,
                        alpha=0.55, zorder=1, solid_capstyle="round")
    ax.scatter(xy[:, 0], xy[:, 1], s=26, color=BLUE, zorder=3,
               edgecolor="white", linewidth=0.7)
    ax.set_aspect("equal"); ax.axis("off")
    m = rad.max() * 1.06
    ax.set_xlim(-m, m); ax.set_ylim(-m, m)
    fig.text(0.5, 0.012,
             "The 240 roots of $E_8$ in the Coxeter plane: eight rings of thirty.",
             ha="center", fontsize=8.5, color="#898781")
    fig.tight_layout()
    out = Path(__file__).resolve().parents[2] / "static" / "figures" / "e8_roots"
    fig.savefig(f"{out}.png", dpi=200, bbox_inches="tight", facecolor="white")
    fig.savefig(f"{out}.pdf", bbox_inches="tight", facecolor="white")
    print("wrote", out)


if __name__ == "__main__":
    main()
