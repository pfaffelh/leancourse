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
- Tag names passed to `{ref "..."}` must not contain `?` or other
  punctuation that looks like regex/URL syntax — Verso's cross-
  reference resolver fails silently at build time with
  `No destination found for tag '...' in none`. Sanitize tags
  (e.g. `apply?` → `apply-qm`) and adjust every matching `{ref}`.
- The course notes and exercises use different numbering schemes.
  Exercise directories ([Leancourse/Exercises/](Leancourse/Exercises/))
  still use the old `04-FunctionalProgramming`, `06-Mathematics`,
  `07-ProofEngineering` names — they were *not* renumbered when the
  course notes were restructured. Keep that in mind when updating
  cross-links.

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

### Later additions

- Pattern matching subsection in
  [01-Notes-Lean.lean](Leancourse/Coursenotes/01-Lean/01-Notes-Lean.lean)
  with `factorial` and examples on `Bool`, `Option`, `List`.
- Fixed the Sigma-type exercises in
  [05-b-DependentTypes.lean](Leancourse/Exercises/05-TypeTheory/05-b-DependentTypes.lean):
  `Σ` requires a `Type`-valued second component. Prop-valued cases
  now use `Subtype` / `{x // P x}`, with a pointer to `PSigma` for
  the Sigma variant that accepts `Prop`.
- Expanded the "Defining new notation" section with
  `prefix`/`postfix`, multi-argument `notation`, scoped notation,
  plus a new notation-exercise file
  [05-c-Notation.lean](Leancourse/Exercises/05-TypeTheory/05-c-Notation.lean).
  Note: `notation` is a *command*, so exercise templates are
  commented-out rather than stubbed with `sorry`.
- Added tactic entries for `omega`, `field_simp`, `ring_nf`,
  `push_cast`, `nlinarith`, `gcongr`, `fun_prop`, `ext`, `funext`,
  `filter_upwards`; wired them into the tactics index and appended
  cheatsheet rows.
- Extended thin exercise files: 01-b, 01-e, 02-b, 02-c, 03-a, 03-c.

### Audit sweep (follow-up)

- Deleted dead files: `Leancourse/Coursenotes/03-Projects copy.lean`
  and `Leancourse/Coursenotes/projects.lean` (neither was imported).
- Fixed chapter numbering in
  [00-Introduction.lean](Leancourse/Coursenotes/00-Introduction.lean)
  (0–7 to match directory layout) and softened "we formalize" to
  "we survey how Mathlib organizes".
- Added intro paragraphs to the part-index files
  [04-FunctionalProgramming.lean](Leancourse/Coursenotes/04-FunctionalProgramming.lean),
  [05-TypeTheory.lean](Leancourse/Coursenotes/05-TypeTheory.lean),
  [06-Mathematics.lean](Leancourse/Coursenotes/06-Mathematics.lean),
  [07-ProofEngineering.lean](Leancourse/Coursenotes/07-ProofEngineering.lean).
- Added a "Pattern matching" subsection + an "Inductive types"
  section to [01-Notes-Lean.lean](Leancourse/Coursenotes/01-Lean/01-Notes-Lean.lean).
- Added a "structure vs class" clarification to
  [03-Typeclasses.lean](Leancourse/Coursenotes/04-FunctionalProgramming/03-Typeclasses.lean).
- Added a "Nonempty and propositional truncation" section to
  [01-CurryHoward.lean](Leancourse/Coursenotes/05-TypeTheory/01-CurryHoward.lean).
- Added a worked `1/(n+1) → 0` proof to
  [03-Filters.lean](Leancourse/Coursenotes/06-Mathematics/03-Filters.lean).
- Added a "Closure, interior, and frontier" section to
  [04-Topology.lean](Leancourse/Coursenotes/06-Mathematics/04-Topology.lean).
- Added a worked Lebesgue-measure computation and a longer
  `condExp` note to
  [05-MeasureTheory.lean](Leancourse/Coursenotes/06-Mathematics/05-MeasureTheory.lean).
- Added "Concrete distributions" and "Beyond PMFs" sections to
  [06-Probability.lean](Leancourse/Coursenotes/06-Mathematics/06-Probability.lean).
- Added 10 new tactic entries — `contradiction`, `contrapose`,
  `decide`, `norm_cast`, `positivity`, `set`, `show`, `simp_rw`,
  `symm`, `trivial` — wired into the tactics index and cheatsheet.

### Exercise file naming convention

All exercise files have been renamed from `NN-x.lean` to
`NN-x-Topic.lean` so the subject is visible from the filename, e.g.
[06-b-Filters.lean](Leancourse/Exercises/06-Mathematics/06-b-Filters.lean),
[06-e-MeasureTheory.lean](Leancourse/Exercises/06-Mathematics/06-e-MeasureTheory.lean).
The `Solutions/` and `MyExercises/` trees were renamed in lockstep.
Tracked files used `git mv` (history preserved); untracked files
(e.g. `MyExercises/`) used plain `mv`.

### New chapter: Probability

- [06-Probability.lean](Leancourse/Coursenotes/06-Mathematics/06-Probability.lean)
  -- *New*. Verso chapter on the `PMF` monad: definition, `pure`
  (Dirac), `bind` with monad laws, `map` with functor laws, `join`
  derived as `bind id`, the `Monad PMF` instance, and where
  measurability still creeps in. Registered in
  [06-Mathematics.lean](Leancourse/Coursenotes/06-Mathematics.lean).

## Session history (2026-04-15)

### Chapter restructure

The coursenotes tree was flattened and renumbered. The old layout
had eight parts (`00`–`07`); the new layout has five (`00`–`04`).
Mapping:

| Old                             | New                                           |
|---------------------------------|-----------------------------------------------|
| `00-Introduction`               | `00-Introduction`                             |
| `01-Lean`                       | `01-Lean` (now also holds tactics + FP basics)|
| `02-Tactics/`                   | `01-Lean/Tactics/` (folded in)                |
| `03-Projects`                   | *deleted*                                     |
| `04-FunctionalProgramming/`     | *abandoned*; content redistributed            |
| &nbsp;&nbsp;`01-Basics`         | → `01-Lean/03-FunctionalBasics`               |
| &nbsp;&nbsp;`02-Structures`     | → `02-TypeTheory/04-Structures`               |
| &nbsp;&nbsp;`03-Typeclasses`    | → `02-TypeTheory/05-Typeclasses`              |
| &nbsp;&nbsp;`04-Monads`         | → prepended into `03-Mathematics/06-Probability` |
| `05-TypeTheory`                 | `02-TypeTheory`                               |
| `06-Mathematics`                | `03-Mathematics`                              |
| `07-ProofEngineering`           | `04-AdvancedTopics` (retitled)                |

All moves used `git mv` so history is preserved. The
[Leancourse.lean](Leancourse.lean) root and every part-index file
(`01-Lean.lean`, `02-TypeTheory.lean`, `03-Mathematics.lean`,
`04-AdvancedTopics.lean`) were updated to match, as was the chapter
listing in [00-Introduction.lean](Leancourse/Coursenotes/00-Introduction.lean).

Monads are now the opening section of the probability chapter
(`Monads and Probability Mass Functions`): the general
`Option`/`List`/`IO`/`StateM`/`Except`/`Set`/`Filter`/`Finset`
discussion comes first, then the PMF-specific material.

### Help / search services

Added a "Getting help" section to
[01-Notes-Lean.lean](Leancourse/Coursenotes/01-Lean/01-Notes-Lean.lean)
covering **Loogle**, **LeanSearch**, **Moogle**, the generated
Mathlib docs, and Zulip, with the `#loogle` / `#leansearch` /
`#moogle` inline commands and a rule-of-thumb on which to try first.

### Build fixes

Fixed the four pre-existing build errors that had been masked by
`verso.docstring.allowMissing`:

- [Tactics/Ext.lean](Leancourse/Coursenotes/01-Lean/Tactics/Ext.lean):
  removed a stray `{docstring Lean.Nat.induction}` (unknown constant).
- [03-Mathematics/03-Filters.lean](Leancourse/Coursenotes/03-Mathematics/03-Filters.lean):
  replaced the brittle `rw [div_lt_iff₀, lt_div_iff₀]` chain in the
  `1/(n+1) → 0` proof with a `linarith`-closed step.
- [03-Mathematics/05-MeasureTheory.lean](Leancourse/Coursenotes/03-Mathematics/05-MeasureTheory.lean):
  added `open MeasureTheory in` before the `volume (Set.Icc 0 1) = 1`
  example.
- [03-Mathematics/06-Probability.lean](Leancourse/Coursenotes/03-Mathematics/06-Probability.lean):
  fixed the `PMF.pure_apply_of_ne` call (it takes the centre and the
  query point explicitly before the hypothesis).

Also renamed the `apply?` tag to `apply-qm` (in
[Applyqm.lean](Leancourse/Coursenotes/01-Lean/Tactics/Applyqm.lean)
and the `{ref}` in
[Exact.lean](Leancourse/Coursenotes/01-Lean/Tactics/Exact.lean)) so
that `lake exe leancourse --output _out/` produces clean HTML with
no "No destination found for tag" warnings.
