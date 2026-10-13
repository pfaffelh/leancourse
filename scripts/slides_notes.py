#!/usr/bin/env python3
"""Dump the speaker notes of a built deck as markdown, for reading through.

    lake exe slides _out/html-multi/slides
    python3 scripts/slides_notes.py introduction > notes.md

Reads the generated HTML rather than the Lean source, so what comes out is
what reveal shows under `S`.
"""

import html
import pathlib
import re
import sys

DECKS = pathlib.Path("_out/html-multi/slides")


def to_markdown(frag: str) -> str:
    frag = re.sub(r"(?is)<(script|style).*?</\1>", "", frag)
    frag = re.sub(r"(?is)<(em|i)>(.*?)</\1>", r"*\2*", frag)
    frag = re.sub(r"(?is)<(strong|b)>(.*?)</\1>", r"**\2**", frag)
    frag = re.sub(r"(?is)<code[^>]*>(.*?)</code>", r"`\1`", frag)
    frag = re.sub(r"(?i)</p>", "\n\n", frag)
    frag = re.sub(r"(?i)<br\s*/?>", "\n", frag)
    frag = re.sub(r"(?i)<li[^>]*>", "\n  - ", frag)
    frag = re.sub(r"<[^>]+>", "", frag)
    frag = html.unescape(frag)
    frag = re.sub(r"[ \t]+", " ", frag)
    lines = [l if l.startswith("  - ") else l.strip() for l in frag.split("\n")]
    return re.sub(r"\n{3,}", "\n\n", "\n".join(lines)).strip()


def dump(deck: str) -> str:
    page = (DECKS / deck / "index.html").read_text(encoding="utf-8")
    body = page[page.index('<div class="slides">'):]
    out = [f"# Speaker notes -- {deck}", ""]
    n = 0
    for m in re.finditer(
        r"(?is)<section\b(?![^>]*\bdata-)[^>]*>(.*?)</section>\s*(?=<section|</div>)", body
    ):
        section = m.group(1)
        heading = re.search(r"(?is)<h[12][^>]*>(.*?)</h[12]>", section)
        if not heading:
            continue
        n += 1
        notes = re.search(r'(?is)<aside class="notes">(.*?)</aside>', section)
        out += [
            f"## {n}. {to_markdown(heading.group(1))}",
            "",
            to_markdown(notes.group(1)) if notes else "*(no notes)*",
            "",
        ]
    return "\n".join(out)


if __name__ == "__main__":
    decks = sys.argv[1:] or sorted(p.name for p in DECKS.iterdir() if p.is_dir())
    print("\n".join(dump(d) for d in decks))
