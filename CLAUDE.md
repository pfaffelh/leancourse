# CLAUDE.md

Project notes for future Claude Code sessions working on the
`leancourse` Verso manual.

## Repository overview

- Source for the rendered course notes lives under
  [Leancourse/Coursenotes/](Leancourse/Coursenotes/). Each chapter is a
  Lean file that uses Verso's `#doc (Manual) "..."` macro; fenced
  ```` ```lean ```` blocks are type-checked by Lean at build time.
- Student exercise files (problem sets with `sorry`s) live under
  [Leancourse/Exercises/](Leancourse/Exercises/); they are plain Lean
  files, not part of the Verso manual. Exercise files for the
  mathematics chapter are in
  [Leancourse/Exercises/06-Mathematics/](Leancourse/Exercises/06-Mathematics/).
- Build individual chapter: `lake env lean <path-to-.lean>`.

## Verso conventions (gotchas)

- Verso markup uses **single `*`** for bold (`*Theorem*`), not `**`.
  Double `**` triggers a linter warning.
- Square brackets `[...]` inside ordinary text can be parsed as Verso
  link syntax and may cause parse errors (`expected '(' or '['`).
  Workarounds: avoid the brackets (`0 to ∞` instead of `[0, ∞]`), or
  escape.
- Any ```` ```lean ```` code block is *executed*: do not redeclare
  names already defined in Mathlib (e.g. `structure Filter`, `def
  Tendsto`). Use a plain ```` ``` ```` fence when showing code that
  should not run.
- Line-length linter: code inside lean blocks should be ≤ 60 columns.

## Session history (2026-04-13)

### Mathematics chapter rewrites

- Rewrote [03-Filters.lean](Leancourse/Coursenotes/06-Mathematics/03-Filters.lean)
  following the Buzzard/Mehta pedagogy from
  [b-mehta/formalising-mathematics-notes](https://github.com/b-mehta/formalising-mathematics-notes)
  (Section12Filters): "a filter is a generalized subset".
- Expanded the Knaster-Tarski fixed-point section in
  [01-OrdersAndLattices.lean](Leancourse/Coursenotes/06-Mathematics/01-OrdersAndLattices.lean)
  with full statement, short lfp proof, and `OrderHom.lfp`/`gfp` API.
- Added a "Notation and naming conventions" table at the top of each
  chapter
  ([01](Leancourse/Coursenotes/06-Mathematics/01-OrdersAndLattices.lean),
  [02](Leancourse/Coursenotes/06-Mathematics/02-AlgebraicHierarchy.lean),
  [03](Leancourse/Coursenotes/06-Mathematics/03-Filters.lean),
  [04](Leancourse/Coursenotes/06-Mathematics/04-Topology.lean),
  [05](Leancourse/Coursenotes/06-Mathematics/05-MeasureTheory.lean))
  listing symbol / Lean name / reading / input sequence.
- Moved the `#check` / `#print` / `inferInstance` / `exact?` / `apply?`
  exposition out of chapter 02 and into a dedicated section in
  [01-Notes-Lean.lean](Leancourse/Coursenotes/01-Lean/01-Notes-Lean.lean).
  Chapter 02 now just *refers back* to those commands.

### Exercise file reorganization

One exercise file per math chapter (before: three files bundled
chapters 1, 3, and 4+5):

- [06-a.lean](Leancourse/Exercises/06-Mathematics/06-a.lean) -- Orders
  and lattices; extended with Knaster-Tarski exercises (Part 7).
- [06-b.lean](Leancourse/Exercises/06-Mathematics/06-b.lean) -- Filters;
  extended with "build filters from scratch" exercises (principal,
  cofinite, atTop', nhds', map') and order-on-filters exercises.
- [06-c.lean](Leancourse/Exercises/06-Mathematics/06-c.lean) -- Trimmed
  down to Topology only (measure theory split off).
- [06-d.lean](Leancourse/Exercises/06-Mathematics/06-d.lean) -- *New*.
  Algebraic hierarchy (monoids, groups, rings, fields, morphisms,
  substructures, quotients).
- [06-e.lean](Leancourse/Exercises/06-Mathematics/06-e.lean) -- *New*.
  Measure theory (measurable sets/functions, measures, Lebesgue,
  probability, almost-everywhere).
- [06-f.lean](Leancourse/Exercises/06-Mathematics/06-f.lean) -- *New*.
  Probability mass functions: properties of `PMF`, the Dirac (`pure`),
  monad laws for `bind`, functor laws for `map`, `join` (defined as
  `bind id`), and a small concrete coin example. Note: `pure` is
  ambiguous between `PMF.pure` and `Pure.pure`; exercises qualify it
  explicitly as `PMF.pure`.

### New chapter: Probability

- [06-Probability.lean](Leancourse/Coursenotes/06-Mathematics/06-Probability.lean)
  -- *New*. Verso chapter on the `PMF` monad: definition, `pure`
  (Dirac), `bind` with monad laws, `map` with functor laws, `join`
  derived as `bind id`, the `Monad PMF` instance, and where
  measurability still creeps in. Registered in
  [06-Mathematics.lean](Leancourse/Coursenotes/06-Mathematics.lean).
