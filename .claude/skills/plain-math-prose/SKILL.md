---
name: "plain-math-prose"
description: Write or edit mathematical teaching texts (lecture notes, tutorials, textbook chapters, Lean/Mathlib documentation, transitions between sections) in a short, plain, precise style without sales language, filler or needless jargon. Use this skill whenever the user asks to write, shorten, polish, tighten or review explanatory math or formalization text, in English or German, including requests like "make this shorter", "kürzer", "auf den Punkt", "less wordy", or when drafting introductions, overviews and transitions in teaching material.
---

# Plain Math Prose

Goal: The reader gets the point in as few words as possible. Every sentence carries information. Structure does the work that long prose would otherwise do.

## Structure

1. **Section openers: goal plus the result that reaches it.** Two to five sentences. Name the aim in plain words ("The aim is to assign a probability to as many sets as possible") and point to the numbered result where it is achieved ("The answer is Theorem 2.16"). An announcement is fine if it names a concrete result; vague announcements ("In this section we will discuss…") are not.
2. **Roadmaps as ordered steps with numbers.** "First, in Chapter 1, … Second, in Chapter 2, …", one clause per step.
3. **Show relations compactly.** Use a displayed implication chain (A ⇒ B ⇒ C), an equivalence scheme for numbered statements (1. ⇔ 2. ⇒ 3.), or a small table of hypotheses vs. conclusions, instead of a paragraph.
4. **Every definition, lemma, theorem and example gets a short title in parentheses** saying what it is about, e.g. "Lemma 2.5 (Set functions on semi-rings)".
5. **Numbered lists inside statements** when a definition or result has several parts.
6. **Cross-references inline:** "see Definition 1.7", "recall from (2.3)". No sentence describing what another chapter contains.
7. **Notation and side facts go into footnotes or a one-line remark**, not into the main text.
8. **Say what you will not use.** One sentence suffices ("Such functions are also called contents. We will not use this term.").

## Language

9. **No sales or economic language.** Avoid: price, cost, pay, buy, gain, payoff, in return, powerful, elegant, remarkable, beautiful, crucial, key, seamless, magic, for free. German: Preis, kostet, mächtig, elegant, bemerkenswert, spannend, entscheidend. Say what happens instead.
10. **No staged contrasts or rhetorical questions.** Avoid "The price is… The gain is…", "Not only… but…", "You may ask whether…". State facts in logical order.
11. **No recaps** of what was just said.
12. **Jargon only when used later.** Otherwise the ordinary word.
13. **Short sentences, plain "we".** Split chains joined by "and", "because", "so that" when they carry separate facts.
14. **Transitions in one sentence:** what we have, what is missing, what comes next. Typical forms: "We now show…", "It remains to show…", "The next result shows how…", "The following theorem explains why…".

## Examples and proofs

15. **Examples must do a job:** check a definition on a standard case ("Indeed: …"), connect to a known course result, or show that a hypothesis cannot be dropped (counterexample). Drop decorative examples. Never end a paragraph on one.
16. **Terse proofs where the step is routine:** "Clear.", "'⇒': clear.", "We only show X; Y follows analogously." Longer proofs get "Step 1: … Step 2: …" with a short label each.
17. **Keep all mathematical content.** Shortening must not drop hypotheses, definitions or claims.

## When editing

- Aim for roughly half the original length; move content into structure (lists, tables, titles, footnotes) where possible.
- Return only the revised text unless asked for comments. If something that might matter was removed, add one line saying what.
- Keep the author's notation and terminology.

## Example

Before:
> Mathlib is a single repository holding essentially all of the mathematics, compiled as one unit, with every change reviewed by maintainers and continuous integration keeping the whole library building against the current Lean. The price is that there is no stable release to depend on: Mathlib tracks Lean, and your own development must track Mathlib. The gain is that everything composes. A theorem about topological groups can be applied to the reals without anyone having arranged for it, because there is only one hierarchy of structures and the reals sit inside it. That hierarchy, built out of `class` and `instance`, is what the chapters on typeclasses and the algebraic hierarchy are about.

After:
> Mathlib is one repository, compiled as a unit. Maintainers review every change, and CI keeps it building against the current Lean. There are no stable releases: Mathlib follows Lean, and your project follows Mathlib. Results combine without extra work, because all structures live in one hierarchy, built from `class` and `instance` (see Chapters X and Y).

What changed: "price"/"gain" framing removed; decorative example dropped; chapter pointer reduced to a parenthesis; long first sentence split.
