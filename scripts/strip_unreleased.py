#!/usr/bin/env python3
"""Keep the headings of a chapter, drop the text underneath.

The course notes are written in full on the `preparation` branch.  On
`main` only the chapters that have been taught carry their text; the
rest are reduced to their heading tree, so that readers see where the
course is going without reading drafts.

Every `{ref}` target in the notes is a heading tag, and the headings
stay, so stripping a chapter cannot produce a dangling reference.
The fifteen figure tags, the only tags defined in running text, all
live in the Introduction, which is never stripped.

Usage:
    scripts/strip_unreleased.py                 # strip WITHHELD below
    scripts/strip_unreleased.py FILE...         # strip these files
    scripts/strip_unreleased.py --check         # list what would change

Regenerating main from preparation:
    git checkout main
    git checkout preparation -- Leancourse Slides scripts static
    scripts/strip_unreleased.py
    git commit -am "Release through chapter N"
"""
import re
import subprocess
import sys
from pathlib import Path

PLACEHOLDER = "This section is published right before the chapter is taught."

# Chapters whose text is withheld on `main`, in reading order.
WITHHELD = [
    "Leancourse/Coursenotes/1-Lean/2-Types.lean",             # 1.2
    "Leancourse/Coursenotes/1-Lean/3-TypeFormers.lean",       # 1.3
    "Leancourse/Coursenotes/1-Lean/4-Rules.lean",             # 1.4
    "Leancourse/Coursenotes/1-Lean/5-Typeclasses.lean",       # 1.5
    "Leancourse/Coursenotes/1-Lean/6-CurryHoward.lean",       # 1.6
    "Leancourse/Coursenotes/1-Lean/7-Notation.lean",          # 1.7
    "Leancourse/Coursenotes/2-Mathematics/1-SetsAndTypes.lean",       # 2.1
    "Leancourse/Coursenotes/2-Mathematics/2-UniversesAndAxioms.lean", # 2.2
    "Leancourse/Coursenotes/2-Mathematics/3-Logic.lean",              # 2.3
    "Leancourse/Coursenotes/2-Mathematics/4-OrdersAndLattices.lean",  # 2.4
    "Leancourse/Coursenotes/2-Mathematics/5-AlgebraicHierarchy.lean", # 2.5
    "Leancourse/Coursenotes/2-Mathematics/6-Filters.lean",            # 2.6
    "Leancourse/Coursenotes/2-Mathematics/7-Topology.lean",           # 2.7
    "Leancourse/Coursenotes/2-Mathematics/8-MeasureTheory.lean",      # 2.8
    "Leancourse/Coursenotes/2-Mathematics/9-Probability.lean",        # 2.9
    "Leancourse/Coursenotes/3-Projects/1-Girard.lean",                # 3
    "Leancourse/Coursenotes/3-Projects/2-CantorSchroederBernstein.lean",
    "Leancourse/Coursenotes/3-Projects/3-Limits.lean",
    "Leancourse/Coursenotes/3-Projects/4-Integers.lean",
    "Leancourse/Coursenotes/3-Projects/5-MontyHall.lean",
]

HEADING = re.compile(r"^#{1,6} ")


def strip(text: str) -> str:
    lines = text.splitlines()
    out: list[str] = []
    i, n = 0, len(lines)

    # Imports, `open`s and `set_option`s stay untouched.
    while i < n and not lines[i].startswith("#doc (Manual)"):
        out.append(lines[i])
        i += 1
    if i == n:
        raise SystemExit("no #doc command found")
    out.append(lines[i])
    i += 1

    def copy_meta() -> None:
        """Copy the %%% block that carries tag, number and htmlSplit."""
        nonlocal i
        while i < n and not lines[i].strip():
            i += 1
        if i < n and lines[i].rstrip() == "%%%":
            out.append(lines[i])
            i += 1
            while i < n and lines[i].rstrip() != "%%%":
                out.append(lines[i])
                i += 1
            if i < n:
                out.append(lines[i])
                i += 1

    copy_meta()
    out += ["", PLACEHOLDER]
    while i < n:
        if HEADING.match(lines[i]):
            out += ["", lines[i]]
            i += 1
            copy_meta()
            out += ["", PLACEHOLDER]
        else:
            i += 1
    return "\n".join(out) + "\n"


def tags(text: str) -> list[str]:
    return re.findall(r'tag := "([^"]+)"', text)


def main() -> None:
    args = [a for a in sys.argv[1:] if a != "--check"]
    check = "--check" in sys.argv[1:]
    root = Path(subprocess.run(["git", "rev-parse", "--show-toplevel"],
                               capture_output=True, text=True,
                               check=True).stdout.strip())
    targets = [Path(a) for a in args] or [root / p for p in WITHHELD]

    for path in targets:
        before = path.read_text()
        after = strip(before)
        # A lost tag would mean a dangling {ref}; refuse to write.
        lost = set(tags(before)) - set(tags(after))
        figures = {t for t in lost if t in before.split("#doc")[0]}
        if lost - figures:
            raise SystemExit(f"{path}: would lose tags {sorted(lost)}")
        verb = "would strip" if check else "stripped"
        print(f"{verb} {path.relative_to(root)}: "
              f"{len(before.splitlines())} -> {len(after.splitlines())} lines, "
              f"{len(tags(after))} tags kept")
        if not check:
            path.write_text(after)


if __name__ == "__main__":
    main()
