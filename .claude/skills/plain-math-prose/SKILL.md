---
name: plain-math-prose
description: Write or edit mathematical teaching texts (lecture notes, tutorials, textbook chapters, Lean/Mathlib documentation, transitions between sections) in a short, plain, precise style without sales language, filler or needless jargon. Use this skill whenever the user asks to write, shorten, polish, tighten or review explanatory math or formalization text, in English or German, including requests like "make this shorter", "kürzer", "auf den Punkt", "less wordy", or when drafting introductions, overviews and transitions in teaching material.
---

# Plain Math Prose

Goal: The reader gets the point in as few words as possible. Every sentence must carry information.

## Rules

1. **Cut announcements and recaps.** No "In this section we will…", "As we have seen…", "It is worth noting that…". State the thing.
2. **No sales or economic language.** Avoid metaphors of trade and advertising: price, cost, pay, buy, gain, payoff, in return for, powerful, elegant, remarkable, beautiful, crucial, key, seamless, magic, for free. German too: Preis, kostet, mächtig, elegant, bemerkenswert, spannend, entscheidend. Say what happens instead ("there are no stable releases" rather than "the price is…").
3. **No staged contrasts.** Avoid "The price is… The gain is…", "Not only… but…", "This is where X shines". Plain statements, in logical order.
4. **One example at most, and only if it shows something the sentence alone does not.** Drop examples that merely illustrate a claim the reader already accepts. Never end a paragraph on a decorative example.
5. **Jargon only when used later.** A technical term earns its place if the text relies on it afterwards. Otherwise use the ordinary word.
6. **Transitions in one sentence:** what we have, what is missing, what comes next. E.g. "It remains to show that f is continuous." No bridging paragraphs.
7. **Pointers to other chapters as a short parenthesis or one clause**, not a separate sentence describing what those chapters are about.
8. **Prefer short sentences.** Split chains with "and", "because", "so that" when each part is a separate fact.
9. **Keep all mathematical content.** Shortening must not drop hypotheses, definitions or claims. If something is cut, it must be redundant.

## When editing

- Aim for roughly half the original length.
- Return only the revised text unless asked for comments. If something was removed that might matter, add one line saying what.
- Keep the author's notation and terminology.

## Example

Before:
> Mathlib is a single repository holding essentially all of the mathematics, compiled as one unit, with every change reviewed by maintainers and continuous integration keeping the whole library building against the current Lean. The price is that there is no stable release to depend on: Mathlib tracks Lean, and your own development must track Mathlib. The gain is that everything composes. A theorem about topological groups can be applied to the reals without anyone having arranged for it, because there is only one hierarchy of structures and the reals sit inside it. That hierarchy, built out of `class` and `instance`, is what the chapters on typeclasses and the algebraic hierarchy are about.

After:
> Mathlib is one repository, compiled as a unit. Maintainers review every change, and CI keeps it building against the current Lean. There are no stable releases: Mathlib follows Lean, and your project follows Mathlib. Results combine without extra work, because all structures live in one hierarchy, built from `class` and `instance` (see the chapters on typeclasses and the algebraic hierarchy).

What changed: "price"/"gain" framing removed; decorative example dropped; chapter pointer reduced to a parenthesis; long first sentence split.
