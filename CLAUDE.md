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

## Session history (2026-04-15, follow-up)

### GitHub Pages deployment

- Merged `course_2026WS` into `main` (fast-forward) and pushed.
- **Superseded (see 2026-07-04 below).** At the time, GitHub Pages
  served from `main` branch, `/docs` folder, and every refresh needed
  a manual rebuild + copy `_out/html-multi` → `docs/`. This is no
  longer true: deployment is now automated via GitHub Actions and
  `docs/` is git-ignored.

### Tables: pipe → `:::table`

Verso does **not** parse markdown pipe tables -- they rendered as
literal `|` characters inside a `<p>`.  All tables in the coursenotes
were converted to Verso's directive syntax:
```
:::table (align := left) +header
* + Header 1
  + Header 2
* + Row 1 cell 1
  + Row 1 cell 2
:::
```
The converter lives at `/tmp/convert_tables.py` (re-creatable; not
committed).  Ten files were touched across 02-TypeTheory,
03-Mathematics, and 04-AdvancedTopics.

### Search-bar width

`static/search/search-box.css` drops the desktop `--search-bar-width`
from `24rem` to `14rem` (mobile from `12rem` to `8rem`) to shrink the
top-of-page search/jump-to widget.

### Concept-ordering audit + intro polish

Audit found several tactics used in
[02-Notes-Proofs.lean](Leancourse/Coursenotes/01-Lean/02-Notes-Proofs.lean)
before their glossary entry (`ring`, `simp`, `apply?`,
`filter_upwards`).  Mitigation: added a **preview cheatsheet table**
at the top of the *First steps* section listing
`intro`/`exact`/`apply`/`rw`/`simp`/`apply?`/`have`/`refine`/`obtain`
with when-to-use and effect, mirroring the style of
[Cheatsheet.lean](Leancourse/Coursenotes/01-Lean/Tactics/Cheatsheet.lean).

[00-Introduction.lean](Leancourse/Coursenotes/00-Introduction.lean)
edits:

- Softened the hardware requirement (mentions Gitpod / Lean web editor
  as fallback).
- Re-framed the tactics chapter as an *alphabetical reference /
  glossary*, not a pedagogical sequence.
- Added a **How the course is organized** section explaining that
  tactics and theory are interleaved, and that the tactics chapter is
  meant to be consulted on demand.
- Concretized the "immediate feedback" promise as "error messages from
  the elaborator + live proof-state panel".

### AI assistants

Added a bullet to the "Getting help" section of
[01-Notes-Lean.lean](Leancourse/Coursenotes/01-Lean/01-Notes-Lean.lean)
encouraging students to use ChatGPT/Claude/Gemini/Copilot alongside
`#loogle` / `#leansearch`, with the caveat that AI output must be
verified in Lean (invented lemmas, Mathlib 3 syntax) and a suggested
"paste goal → candidates → verify" workflow.

## Session history (2026-07-04)

### Deployment is now via GitHub Actions (no committed `docs/`)

The manual-deployment scheme documented above (rebuild + copy
`_out/html-multi` → `docs/`, commit, push) is **obsolete**. Since
commit `bf7e4ac` ("Deploy manual via GitHub Actions; drop committed
docs/ + deploy script"):

- `.github/workflows/deploy.yml` builds and deploys on every push to
  `main` (and via manual `workflow_dispatch`). It installs the Lean
  toolchain + Mathlib cache, runs `lake exe leancourse --output _out/`,
  uploads `_out/html-multi` as the Pages artifact, and deploys with
  `actions/deploy-pages@v4`.
- `docs/` is **git-ignored** (`.gitignore` has `/_out` and `/docs`).
  Any local `docs/` directory is a stale leftover from the old scheme;
  do **not** commit it or treat it as the source of truth for what is
  live.
- **To publish a change: just push to `main`.** No `docs/` copy step.
- The workflow uses `concurrency: { group: pages,
  cancel-in-progress: true }`. Rapid successive pushes therefore
  **cancel** the earlier run's deploy — only the newest push's build
  goes live. After a burst of commits, check
  `gh run list --workflow=deploy.yml` and, if the latest run was
  cancelled, wait for (or re-trigger) a clean run so the newest content
  actually deploys.
- Live site: <https://pfaffelh.github.io/leancourse/>. Verify a change
  landed by fetching the page and grepping the rendered HTML (e.g.
  `curl -sL <page-url> | grep ...`), not by inspecting local `docs/`.

### `:::example` is the project's collapsible box

For content the reader may skip but that should stay available behind
a clickable summary, use Verso Manual's built-in `:::example "title"`
directive (from `Manual.Meta`, already imported wherever
`import Manual.Meta` is present). It renders as
`<details class="example">` with a bordered box, an italic summary
prefixed by "Example: ", and JS that auto-opens the box when an anchor
targets inside it. This is what the tactic descriptions use
(`:::example " "`, 57 occurrences). Do **not** hand-roll a `<details>`
block extension — a bare `<details>` misses the `.example` CSS (no
box, no click affordance). The title argument is `.inlinesString`, so
inline code like `` "The connection of `Type` to `Sort`" `` works.

## Session history (2026-07-11)

### New chapter `01-Nat`; Lean part renumbered

The `Nat` / definitional-equality / reduction-rules material that used
to open the *Types* chapter is now a chapter of its own,
[01-Nat.lean](Leancourse/Coursenotes/01-Lean/01-Nat.lean), titled
*"The natural numbers and reduction rules"* and placed **before**
*Types*. It holds the `Nat` constructors + `Nat.rec` walkthrough
(`myDouble`), the `# Definitional equality and `rfl`` section, and the
`## The reduction rules` table. The chapters of the Lean part were
renumbered with `git mv` (history preserved):

| Old                    | New                     |
|------------------------|-------------------------|
| —                      | `01-Nat` *(new)*        |
| `01-Types`             | `02-Types`              |
| `02-Terms`             | `03-Terms`              |
| `03-Typeclasses`       | `04-Typeclasses`        |
| `04-CurryHoward`       | `05-CurryHoward`        |
| `05-DependentTypes`    | `06-DependentTypes`     |
| `06-Notation`          | `07-Notation`           |

Knock-on edits:

- [01-Lean.lean](Leancourse/Coursenotes/01-Lean.lean): imports,
  `{include}`s, and the part intro paragraph.
- [03-Terms.lean](Leancourse/Coursenotes/01-Lean/03-Terms.lean) still
  imports the Types chapter (for `Point`, `MyNat`, `MyComplex`) — the
  import path was updated to `«02-Types»`.
- Tag `types-intro` was renamed to `nat-intro`; the `{ref}`s in
  [02-Types.lean](Leancourse/Coursenotes/01-Lean/02-Types.lean)
  (*Inductive types* section) and inside the new chapter follow.
  Tags `defeq` / `reduction-rules` kept their names, so the external
  refs from
  [04-Equality.lean](Leancourse/Coursenotes/04-Appendix/04-Equality.lean)
  and
  [00b-UniversesAndAxioms.lean](Leancourse/Coursenotes/03-Mathematics/00b-UniversesAndAxioms.lean)
  still resolve (the Appendix wording "of the Types chapter" was
  updated).

### `myDouble` reduction trace fixed

The commented trace under `def myDouble` mislabelled the first step
(`myDouble 2 ⟶ Nat.rec 0 step 2`) as ι; it is δ (unfolding the
definition). The second step is ι *plus* δβ (unfolding and applying
`step`). Also noted in the prose that numerals such as `2` are put
into constructor form before ι can fire.

## Session history (2026-07-26)

### New chapter: Projects

- [05-Projects.lean](Leancourse/Coursenotes/05-Projects.lean) -- *new*
  top-level chapter (included between Appendix and Bibliography) with
  five suggested student projects, each with description,
  implementation sketch, and references: (1) Girard's paradox,
  (2) Cantor-Schröder-Bernstein via Knaster-Tarski, (3) limits with
  and without filters, (4) ℤ as a quotient of ℕ × ℕ,
  (5) Monty Hall with `PMF`. Tags: `projects`, `project-girard`,
  `project-csb`, `project-limits`, `project-integers`,
  `project-monty-hall`. Code in this chapter uses plain ``` fences
  (nothing executes), so the file needs no Mathlib import.
- The long "Girard's paradox" section (τ/σ construction, smuggled
  Cantor paradox, Coquand's paradoxical universe -- the work of the
  2026-07 "Girard:" commit series) was **removed** from
  [00b-UniversesAndAxioms.lean](Leancourse/Coursenotes/03-Mathematics/00b-UniversesAndAxioms.lean)
  and distilled into Project 1. The tag `girard` no longer exists;
  cross-refs in `00c-Logic.lean` and `01-Lean/02-Types.lean` now
  point to `project-girard`. If the full text is ever wanted again,
  it is in git history (commit `fdd5b69` and ancestors).
- New bibliography entries in
  [References.lean](Leancourse/Coursenotes/References.lean):
  `coquand1986`, `hurkens1995`, `mathematicsInLean`; listed in
  [99-Bibliography.lean](Leancourse/Coursenotes/99-Bibliography.lean).

### Exercises export script

- [scripts/export_exercises.sh](scripts/export_exercises.sh) exports
  `Leancourse/Exercises/` into a standalone student repository
  (default target `../leancourse_exercises`). **Superseded in part
  (see 2026-10-10 below): the `--with-solutions` flag is gone and
  `Solutions/` no longer exists.** It writes a Mathlib-only `lakefile.lean`
  (rev extracted from this repo's lakefile), copies `lean-toolchain`,
  and filters `lake-manifest.json` down to Mathlib + its 8 deps so
  `lake exe cache get` matches the pinned revisions. `README.md` and
  `.gitignore` (ignores `/MyExercises`) are written only on first
  export. Exercise files import only Mathlib, so nothing else needs
  to be copied. Workflow: edit exercises here → run script → commit +
  push inside the exercises repo.
- Built-in safety net: before exporting, the script type-checks every
  `.lean` file that would change (`rsync -cin` dry run → `lake env
  lean` with this repo's prebuilt Mathlib, 2 files in parallel).
  Errors abort the export before anything is copied; warnings such as
  `declaration uses sorry` pass. Skip with `--no-check`. There is
  deliberately **no CI** in the exercises repo — this pre-export
  check is the substitute, and it is cheaper (no cache download).
- The student repo is **live**:
  <https://github.com/pfaffelh/leancourse_exercises> (public, created
  2026-07-26, sibling checkout at `../leancourse_exercises`). The
  setup instructions in [Leancourse.lean](Leancourse.lean) now tell
  students to clone *that* repo (paths `Exercises/...`, copy to
  `MyExercises`); the course repo itself no longer needs to be cloned
  by students. When exercises change here, re-run the export script
  and push in the sibling checkout — the script never touches the
  sibling's `README.md`/`.gitignore` after the first export, but
  everything under `Exercises/` is mirrored with `--delete`.

## Session history (2026-10-10)

### `Exercises/Solutions/` → `Leancourse/Checks/`

Model solutions for students are no longer maintained. The tree moved
with `git mv` out of the exercises directory entirely:

| Old                            | New                   |
|--------------------------------|-----------------------|
| `Leancourse/Exercises/Solutions/` | `Leancourse/Checks/` |

Moving it *out* of `Exercises/` rather than renaming it in place is
deliberate: `export_exercises.sh` rsyncs `Leancourse/Exercises/` with
`--delete`, so anything inside that tree is one missing `--exclude`
away from being published. Outside it, the witnesses cannot leak
structurally.

Knock-on edits:

- `--with-solutions` removed from
  [scripts/export_exercises.sh](scripts/export_exercises.sh) (flag
  parsing, the conditional `--exclude 'Solutions'`, the usage line and
  the closing message).
- New [scripts/check_solvable.sh](scripts/check_solvable.sh): checks
  every file under `Leancourse/Checks/` with `lake env lean`, 4 in
  parallel. **Unlike the pre-export check, a `sorry` is a failure
  here** — the whole point of a witness is that the exercise can be
  finished. Takes optional file/directory arguments.
- [Leancourse/Checks/README.md](Leancourse/Checks/README.md) states
  the purpose, the non-goals (not pedagogical, not complete, not
  published) and the coverage table.
- [README.md](README.md) layout section updated.

Rationale, for whoever wonders why the solutions vanished: they were
only 13 of 28 sheets, they were never exported anyway
(`--with-solutions` was opt-in and the live student repo has no
`Solutions/`), and any student now gets a better-commented solution
from a chat model in seconds. What *was* worth keeping is the one
thing a type-check cannot do: confirm an exercise is actually
solvable.

### Haiku one-shot run over `01-Logic`

Eight Haiku instances, one per sheet, single pass, no Lean feedback,
forbidden from running any build. Result: **68 of 72 solvable `sorry`s
(94%)**; six of eight sheets compiled fully clean and `sorry`-free.
Statement integrity was verified afterwards (md5 over all
`example`/`lemma`/`theorem`/`variable` lines per file) — no instance
weakened a statement.

Failures, all four worth knowing about:

- `01-e` Ex 2: `exact absurd hq` (missing argument), and `·` bullets
  nested inside a `cases h with | inr h => ...` arm, which does not
  parse.
- `01-h` Ex 4: one `intro` too many. Ex 6: `choose f hf` without
  `using h`.
- `01-h` Ex 2: **a defect in the sheet, not the model.** The exercise
  hands the student `rw [l1]` as the first line, but
  `l1 : (P → Q) ↔ (Q ∨ ¬P)` matches the *outer* implication of
  `((P → Q) → P) → P` first, turning the goal into
  `P ∨ ¬((P → Q) → P)` (verified with `trace_state`). `intro` then
  fails with "no binders to introduce".

Two consequences recorded here so they are not rediscovered:

1. **`Exercises/01-h` and its witness had silently diverged.** The
   witness proves Ex 2 with three `rw [imp_iff_or_not]` and Ex 3 with
   `rw [not_imp_not]` — neither uses `l1`, although both exercise
   texts tell the student to. The witness also already says
   "you can use `apply?`" where the sheet still says
   `library_search` (the Lean 3 name). Unfixed as of this entry.
2. **Sheet 01 is no barrier to LLM use.** The cheapest model, one
   shot, no feedback, gets 94%. It also correctly flagged *both*
   deliberately unprovable statements in `01-a` (the uncommented
   `example : False` and `P → P → Q` from Exercise 4), so the
   "decide which of these are valid" exercise does not survive
   contact either. Relevant to `exam.md` and to any plan that rests
   on homework being done unaided.

Style note: Haiku writes `cases h with | inl .. | inr ..` throughout
and never `cases'`, and reaches for `choose`, `absurd` and `simp` —
none of which sheet 01 introduces. Solutions students obtain will not
resemble what the sheets teach.

### Undocumented earlier work (2026-10-02, commits `de54897`, `aca12e1`)

Recorded late: the toolchain was upgraded to
`leanprover/lean4:v4.34.0` (lakefile Mathlib rev `v4.34.0`, student
repo exported and pushed in lockstep), and
[Slides/Filters.lean](Slides/Filters.lean) +
[SlidesMain.lean](SlidesMain.lean) added a VersoSlides deck for the
Filters chapter — currently the only deck.

### `01-Logic` rebuilt (same day)

Sheet 01 was rewritten from scratch under two constraints from the
course author: **propositional logic only** (no type variables, no
predicates, no `ℕ`), and **every tactic explained and demonstrated
before the first exercise that needs it**. House style: short
sentences, no chat.

| Old                   | New                  | Tactics introduced                                   |
|-----------------------|----------------------|------------------------------------------------------|
| `01-a-Propositions`   | `01-a-Propositions`  | `trivial` `intro` `exact` `assumption` `apply` `revert` |
| `01-b-Apply`          | `01-b-AndIff`        | `constructor` `⟨_,_⟩` `.1/.2` `.mp/.mpr` `obtain`     |
| `01-c-Negation`       | `01-c-Or`            | `left` `right` `Or.inl/inr` `obtain (_\|_)`           |
| `01-d-AndOr`          | `01-d-Negation`      | `show` `exfalso` `False.elim` `contradiction` `absurd` |
| `01-e-ByCasesHave`    | `01-e-Classical`     | `by_cases` `Classical.em` `by_contra` `push_neg`      |
| `01-f-PatternTactics` | `01-f-Structure`     | `have` `suffices` `refine ?_` `rintro` `rcases`       |
| —                     | `01-g-Automation`    | `exact?` `apply?` `tauto` `itauto` `simp`             |

81 exercises in total. The old `01-b` … `01-f` were deleted, not
edited; `git log` has them.

**The organising principle is the constructive/classical cut between
`01-d` and `01-e`.** Everything up to and including `01-d` is provable
without the excluded middle; `01-e` is exactly the sheet where it is
needed. This is not a claim, it is checked: `itauto` proves all 14
relevant statements on `01-c`/`01-d` and fails on all 12 of `01-e`.
Re-run that probe if you move an exercise across the boundary. It also
kills the old bug where `01-d` asked for `¬(P ∧ Q) → ¬P ∨ ¬Q` one
sheet before `by_cases` existed — that statement now cannot land
before `01-e` by construction.

`01-g` turns the same mechanism into an exercise: students run
`itauto` and `tauto` on the same goal and see which statements need
classical logic. That replaces a paragraph of assertion with an
experiment.

New tactics that sheet 01 never had: `revert`, `contradiction`,
`absurd`, `show`, `suffices`, `push_neg`, `tauto`, `itauto`, and
`exact?`/`apply?` as executable code rather than prose mentions.
`cases'` is gone; `obtain`/`rcases` is taught from `01-b` on.

### Quantifiers and predicates left `01-Logic`

They need a type, and any type puts you in `Set` territory at once, so
they move to the head of the sets chapter (author's call):

| Old                           | New                                      |
|-------------------------------|------------------------------------------|
| `01-Logic/01-g-Quantifiers`   | `03-Functions_and_Sets/03-00-Quantifiers` |
| `01-Logic/01-h-Predicates`    | `03-Functions_and_Sets/03-01-Predicates`  |

`git mv`, witnesses moved in lockstep. **Both files are still in the
old style and still carry the known defects** (the misleading
`rw [l1]` scaffold, `library_search` instead of `exact?`, the `xxx`
author note, and the sheet/witness divergence on exercises 2 and 3).
They were relocated, not rewritten.

### Coursenotes not yet updated

The Verso chapters still reference the old sheet names and the old
`Solutions/` tree in places. Not touched in this session.

### `grind` solves sheet 01 outright

Measured on all seven `01-Logic` sheets: every `example` statement
(128 of them, demonstrations included) proved by a bare `grind`, no
arguments. **127 succeeded.** The single failure is
`example : P → P → Q` in `01-a` — the statement that is deliberately
not provable.

So `grind` closes 100% of what is provable on sheet 01. That is a
stronger result than the Haiku run above, and it needs no AI at all:
the tactic ships with Lean and is documented in this repo's own
appendix (`04-Appendix/Tactics/Grind.lean`).

Two consequences:

1. **Homework cannot be graded on correctness**, and that conclusion
   does not depend on language models. It is recorded in `plan.md`.
2. **`01-g` now teaches `grind` explicitly** rather than leaving it to
   be discovered. Hiding it would be futile — it is one `grind` away
   in a file students already have. The sheet puts the honest case
   instead: `grind` is a finishing tactic, it is silent on which lemma
   to state and how to structure a theory, and unlike `itauto` it
   proves constructive and classical statements without distinguishing
   them. Exercise 8 asks which `01-a` statement it fails on and why.

The three-way comparison `itauto` ⊂ `tauto` ⊂ `grind` is the spine of
`01-g`: constructive propositional, classical propositional, and
general automation with arithmetic and congruence closure.

### `plan.md`

The semester plan now lives in [plan.md](plan.md): computed dates
(19.10.2026–13.02.2027, 15 lectures but only 14 labs because the
Christmas break eats three Wednesdays and two Mondays), the week-by-
week content plan, the five paper tests (11.11., 02.12., 16.12.,
27.01., 10.02.; pass 3 of 5), the AI policy, and the project
arrangement. Weighting: nine weeks of craft before the break, five
weeks of mathematics after it.

### 2026-10-11 -- Kapitel 0 ausgebaut, erster Foliensatz, drei Grafiken

`Leancourse.lean` (das Wurzeldokument, faktisch Kapitel 0) hat drei
neue Abschnitte vor *Other theorem provers*:

- *Why formalize?* -- Vierfarbensatz 1976/2005, Kepler/Hales 1998 mit
  Flyspeck 2014, Liquid Tensor Experiment 2020--22.
- *A short prehistory.* -- Frege, Russell, Principia, Automath,
  Landau 1977; Lean ab 2013.
- *What changed in 2026.* -- vier datierte Punkte: FLT (Anthropic,
  04.09.), Navier-Stokes mit Kraftterm (OpenAI, 08.09.), der Katalog
  vom 06.10. (719 Manuskripte, 372 Familien, ~42 % mit Lean-Beweis)
  und die drei Rücknahmen vom 07.10. Daran der Abschnitt darüber, was
  ein Lean-Beweis zertifiziert und was nicht.
- *Where the field stands.* -- die beiden Grafiken.

*Other theorem provers* ist von zwei Aufzählungspunkten auf einen
Abschnitt mit Tabelle gewachsen: formale Grundlage (CIC-Variante /
pCuIC / HOL), abhängige Typen, und wie die Bibliotheken organisiert
sind (Mathlib als Monorepo, Rocq als Paketlandschaft, Isabelle mit
dem AFP).

**Zahlen im Text sind gemessen, nicht geschätzt.** Mathlib-Kennzahlen
aus dem gepinnten Checkout (Stand 15.09.2026); die OpenAI-Zahlen aus
`github.com/openai/math` (README und `history.md`, Stand 11.10.2026).
Die ~42 % und die Manuskriptzahl ändern sich -- im Text steht deshalb
"at the time of writing".

**Grafiken** in `static/figures/`, erzeugt mit den Skripten aus
`~/bwSyncShare/Vorträge/20260720_CRC/`:

- `itp_github_repos_quarterly` -- `github_language_quarterly_plot.py
  --langs Lean Coq Isabelle --no-title`
- `arxiv_lean_formalized_weekly` -- `arxiv_fulltext_counts.py`, Kopie
  im Scratchpad mit angepasstem Untertitel (das Original verweist auf
  `KRITERIUM_formalisiert.md`, für Studierende undurchsichtig)
- `kepler_packing` -- neu gezeichnet (`kepler.py`, Hausfarben), weil
  kein lizenzfreies Bild vorlag

**Foliensatz** `Slides/Introduction.lean`, 15 Folien, folgt dem
Kapitel Abschnitt für Abschnitt, damit beides nebeneinander benutzbar
ist. Die Sprechernotizen tragen die Einordnung, die im Skript als
Fließtext steht.

`SlidesMain.lean` nimmt jetzt ein **Basisverzeichnis** und schreibt
jedes Deck in einen Unterordner mit seinem Namen; `deploy.yml` ruft
entsprechend `lake exe slides _out/html-multi/slides` auf. Ein
weiteres Deck braucht damit keine Workflow-Änderung mehr.

**Bildpfade in Folien** werden relativ zur *Quelldatei* aufgelöst, also
`../static/figures/...` aus `Slides/`. Syntax ist `{image "..."}[alt]`,
nicht `![alt](...)` -- letzteres baut durch, erzeugt aber kein Bild.
VersoSlides kopiert die Dateien nach `<deck>/images/`, die Decks sind
also in sich geschlossen.

Hinfällig: der frühere Hardware-Punkt unter *Some notes on Lean and
Mathlib* (8 GB, Gitpod, Web-Editor) ist entfernt -- er widersprach dem
Hardware-Abschnitt vom 10.10.

### 2026-10-11 (2) -- Foliensatz zu Kapitel 0, Verlinkung

`Slides/Introduction.lean` hat jetzt 20 Folien, darunter eine je
Meilenstein-Projekt mit der zugehörigen Grafik und den Portraits.

**VersoSlides-Eigenheiten, die Zeit gekostet haben:**

- Bildsyntax ist `{image "pfad" (height := "26vh") (class := "x")}[alt]`,
  nicht `![alt](pfad)`. Letzteres baut durch, erzeugt aber kein Bild.
- Pfade werden relativ zur **Quelldatei** aufgelöst, aus `Slides/` also
  `../static/figures/...`. VersoSlides kopiert die Dateien dann nach
  `<deck>/images/`, die Decks sind damit in sich geschlossen.
- Eigenes CSS geht über einen ````css`-Codeblock im Dokument; er landet
  als `<style>` im Header. Für eine Klasse um Blöcke: `:::class "names"`.
- `:::names` o.ä. gibt es nicht -- die Direktiven sind attr, class,
  fitText, fragment, frame, hstack, idDirective, notes, stack, stretch,
  table, vstack.

**Layout muss man ansehen, nicht ausrechnen.** Die Browser-Erweiterung
war nicht verbunden; `google-chrome --headless --screenshot` auf
`file://.../index.html#/10` tut es genauso. Dabei fiel auf, dass die
PFR-Folie unten überlief (zweizeilige Überschrift + Bild + vier
Portraits) -- Überschrift gekürzt, Bild auf 22vh, Portraits auf 92px.

Ein verstecktes `:::fragment` belegt seinen Platz schon vor dem Klick.
Die Lücke in der Folienmitte ist also kein Fehler.

Beide Decks sind in `Leancourse.lean` unter *How to use this course*
verlinkt; die Filter-Folien zusätzlich aus dem Filter-Kapitel.

## 2026-10-11 (3) -- Kapitel 0 umgebaut

**Reihenfolge.** Das Kapitel beginnt jetzt mit einer Definition
(*What formalizing means*), grenzt gegen Beweissuche und
Autoformalisierung ab, zeigt dann den Stand (Herbst 2026) und geht erst
danach *vorwaerts* durch die Geschichte. Voll rueckwaerts-chronologisch
wurde erwogen und verworfen: die vier Episoden sind eine Begruendungs-
kette, die gegen die Leserichtung nicht traegt. Der Orga-Teil (Goals,
Ablauf, Folien, Hardware, Installation) steht am Kapitelende.

**Voevodsky** ist als dritte Episode dazugekommen -- der Fall, in dem der
Autor selbst der Zweifelnde ist. Quelle ist sein IAS-Essay von 2014
(ias.edu/ideas/2014/voevodsky-origins, ueber web.archive.org, die Seite
liefert sonst 403). Belegt daraus: Kapranov/Voevodsky 1989, Simpsons
Einwand Oktober 1998, Einsicht erst Herbst 2013; der zweite Fehler im
eigenen Lemma von 1992, gefunden 1999. Lean 2 hatte einen HoTT-Modus
(van Doorn, von Raumer, Buchholtz), Lean 3 nicht mehr -- das
Definitionspaket braucht Axiom K.

**Bilder.** Voevodsky-Foto: MFO Oberwolfach 2011, CC BY-SA 2.0 de, vom
Mini-Workshop zur Homotopie-Interpretation der Typentheorie. Buzzard
wurde vom 2007er Schnappschuss (642x930, Blick nach unten) auf den
Bergman-Headshot von 1996 umgestellt -- gleiche Quelle wie das
Scholze-Bild. Firmen-Wortmarken von Anthropic und OpenAI liegen unter
`static/figures/logos/`, beide gemeinfrei (unterhalb der Schoepfungs-
hoehe), aber eingetragene Marken; im Kapitel nur zur Zuordnung, wer was
angekuendigt hat. Holskript: `scripts/figures/fetch_logos.py`.

**Figuren-Layout** (`static/figures.css`). Grafik und Portraits stehen
jetzt als Flex-Reihe nebeneinander, gleiche Hoehe, alle Portraits
ueberall gleich gross (12.5rem -- der groesste Wert, bei dem drei noch in
eine Reihe passen). Zwei Fallen dabei:
- Die Regel fuer die Mathe-Grafik (`figure:has(...) > p > img`) hat eine
  hoehere Spezifitaet als `figure img[src*="/portraits/"]` und
  ueberschreibt deren `width`/`height`. Ohne `:not([src*="/portraits/"])`
  werden aus den Kreisen Ellipsen -- und zwar unauffaellig, weil die
  quadratischen Platzhalter korrekt aussehen.
- Ein Portrait darf nicht schrumpfen (`flex: 0 0 auto`); laeuft die Reihe
  um zwei Pixel ueber, staucht Flexbox sonst das erste Bild zur Ellipse.

**Verso-Fallen, neu.**
- Inline-Mathe (`$`...``) funktioniert in VersoSlides *nicht in
  Ueberschriften*: "Failed to convert ... inline_math".
- In einem Manual-`lean`-Block ist `and` ein Token, kein Bezeichner --
  `⟨and⟩` scheitert, `⟨(· && ·)⟩` geht. Ausserhalb von Verso compiliert
  dasselbe Snippet.
- Fuer gepruefte Lean-Bloecke im Wurzeldokument braucht es
  `import Manual.Meta` und `open Verso.Genre.Manual.InlineLean`.
- `.reveal section img` schlaegt `img.logo`; Folien-Bildklassen muessen
  als `.reveal section img.logo` geschrieben werden.

**Equational Theories** hat statt einer Grafik ein gepruefts Lean-
Beispiel: Gleichung 4 (`x = x ◇ y`) impliziert Gleichung 3
(`x = x ◇ x`) durch Substitution, die Umkehrung scheitert an `Bool`
mit `&&`. Nummerierung aus dem Projekt-Repo
(`equational_theories/Equations/Basic.lean`), nicht geraten.

## 2026-10-11 (4) -- KI-Abschnitt nach vorn, Folien entschlackt

Die beiden Kurven (GitHub, arXiv) stehen jetzt direkt hinter dem
2026-Abschnitt statt hinter den Meilensteinen. Weil Rocq und Isabelle
dort erstmals auftauchen, aber erst am Kapitelende erklaert werden,
nennt ein Halbsatz sie mit Links und verweist nach hinten.

Kugelpackung Dimension 8 hat zusaetzlich einen datierten Punkt im
2026-Abschnitt (Februar, vor FLT). Sie ist der sauberste Fall: die
Mathematik war fertig, nur das Formalisieren fehlte. Der Meilenstein-
Eintrag bleibt stehen und verweist darauf.

Logos sind jetzt Claude und ChatGPT (die Produkte) statt Anthropic und
OpenAI (die Firmen) -- beide quadratisch, dadurch faellt die
Kapitalhoehen-Korrektur weg.

**Folien.** Bild und Portraits stehen in einem `:::hstack` direkt unter
der Ueberschrift, nicht mehr untereinander am Folienende; das war der
Grund, warum Bilder zu viel vertikalen Platz brauchten. Portraits von
92px auf 17vh (skaliert mit der Foliengroesse). Milestone-Bilder
einheitlich 21vh, die quadratischen Ausnahmen (e8_roots 30vh,
four_colour 26vh, kepler_packing 27vh) groesser -- eine Hoehengrenze,
die fuer breite Bilder passt, laesst quadratische verschwinden.

Die Voevodsky-Folie hiess "1989" und stand hinter "1998", lief also
rueckwaerts. Sie heisst jetzt "2013: the author concedes" -- datiert
nach dem Ende der Episode, wie in der Uebersicht -- und nennt 1989 im
Text.

Neu am Ende: eine Mathlib-Folie (Repository und interaktive
Import-Karte) und eine Folie "Where to start" (NNG, Mehta, Mathematics
in Lean). Die Schlussfolie verlinkt die Installationsanleitung und das
Skript.

**Bildrechte, Stand.** Buzzard: auf Commons gibt es nur 1995, 1996 und
2007; wir nehmen den Bergman-Headshot 1996. Massolit (massolit.io) und
Zulip-Avatare gehen nicht -- kommerzielle Plattform bzw. von den Leuten
selbst hochgeladen, in beiden Faellen keine Lizenz fuer Dritte. Das
bleibt bei den drei angefragten Personen.

## 2026-10-11 (5) -- Kapitel 0 sprachlich durchgegangen

Mit dem Skill `plain-math-prose`. Prosa von 5 260 auf 4 031 Woerter
(-23 %); alle Zahlen, Namen und Jahreszahlen stehen noch drin,
maschinell gegengeprueft -- weggefallen sind ausschliesslich
Satzanfaenge wie "Finally", "However", "Furthermore", "Concretely".

Was systematisch raus ist:
- Ankuendigungen und Rueckblicke ("This first part is about...",
  "Begin with where things stand", "Concretely:").
- Handels- und Werbesprache. Der Mathlib-Absatz hatte woertlich das
  "The price is... The gain is..."-Muster, das der Skill als Beispiel
  fuehrt; ebenso "the best argument we could have asked for", "what
  that check buys", "This is where Lean's reputation begins".
- Ein Beispiel, das zweimal spaeter nochmal kommt: die Kugelpackung
  stand in der Autoformalisierungs-Definition *und* im 2026-Abschnitt
  *und* bei den Meilensteinen. In der Definition jetzt gestrichen.

Die Zielmarke des Skills (Haelfte) ist hier nicht erreichbar: ein
grosser Teil des Kapitels sind datierte Stichpunkte, die Tabelle, die
Linklisten und der Lean-Block. Gekuerzt wurde, was Prosa war.

Die Orga-Abschnitte (Goals, Installation) waren am staerksten
aufgeblaeht und sind am deutlichsten geschrumpft.

## 2026-10-11 (6) -- Skill im Repo, Folien durchgegangen

`plain-math-prose` liegt jetzt unter
`.claude/skills/plain-math-prose/SKILL.md` und ist damit im Git, statt
nur ueber Remote Control aktiv zu sein. Wichtig fuers naechste Mal:
ein so aktivierter Skill taucht nicht in der Skill-Liste der laufenden
Session auf -- erst nach Neustart oder wenn der Name genannt wird.

Folien-Durchgang: Sprechernotizen 1 119 -> 1 023 Woerter, Folientext
praktisch unveraendert (1 069 -> 1 065). Das ist richtig so, der
Folientext war schon telegrafisch; die Prosa stand in den Notizen.

Gefunden und behoben:
- Die Eroeffnungsnotiz und die Notiz zu "What formalizing means"
  sagten beide "Everything that follows is ...".
- Ankuendigungen darueber, was die naechste Folie tut.
- "This is where Lean's reputation begins" (dieselbe Wendung wie im
  Kapitel), "the best automation", "an impossible amount of
  bookkeeping".
- Im Filters-Deck hiess eine Folie "The payoff" -- jetzt "One
  definition instead of three", und der doppelte Satz darunter ist weg.

Folien und Kapitel verwenden jetzt dieselben Formulierungen an den
Stellen, wo beide dasselbe sagen.

## 2026-10-11 (7) -- Skill-Update, Folien nach den neuen Regeln

Das Update per Remote Control lag rund 30 Minuten nach der Aenderung
noch nicht auf der Platte; eine vollstaendige Sync-Runde lief dazwischen
und brachte es nicht. Ein Hintergrund-Watcher auf die Datei hat es dann
nach 20 Sekunden gesehen (manifest `updatedAt` 21:48:07Z). Fuers
naechste Mal: nicht raten, ob ein RC-Update da ist -- `manifest.json`
im Sync-Ordner nennt `updatedAt` je Skill.

Der Skill hat jetzt einen Abschnitt *Structure*. Der groesste Teil
davon zielt auf Skripte mit nummerierten Saetzen (Lemma-Titel in
Klammern, nummerierte Teilaussagen, "see Definition 1.7", Fussnoten)
und greift auf Folien nicht. Angewandt wurden:
- Regel 3 (Relationen kompakt zeigen): die Folie "Three systems" war
  eine Liste aus drei Fragmenten und ist jetzt eine Tabelle
  System / Logic / Library, wie im Kapitel.
- Regel 10 (keine rhetorischen Fragen): "Which sets may contain F?"
  im Filters-Deck -> "The sets that may contain F:".
- Regel 11 (keine Rueckblicke): drei Notizen gekuerzt.

Folien-Tabellen brauchen `.reveal section table { font-size: 0.62em }`,
sonst fuellt eine vierzeilige Tabelle die Folie und schiebt alles
darunter aus dem Bild.

Offen: Kapitel 0 ist noch nicht gegen die neuen Structure-Regeln
geprueft. Dort gibt es keine nummerierten Saetze, aber die Roadmap in
"How to use this course" und die Querverweise waeren Kandidaten.

## 2026-10-12 -- Manuskript mit plain-math-prose durchgegangen

Skill-Fassung vom 11.10., 21:58 UTC (neue Regel 11). Sie liegt in
`.claude/skills/plain-math-prose/`.

**Ergebnis: 46 629 -> 45 433 Woerter Prosa, 2,6 %.** Das ist weit von
der Zielmarke des Skills (Haelfte) entfernt. Die Zusammensetzung
erklaert einen Teil davon: von den rund 46 000 Woertern sind 13 300
Listen (API-Namen, Lemma-Aufzaehlungen) und 9 400 Tabellen. Echter
Fliesstext sind etwa 33 000. Die Haelfte davon zu streichen hiesse,
mathematischen Inhalt zu streichen, was Regel 18 verbietet.

**Systematisch durchsucht und behoben:**
- Regel 11 (Behauptungen ueber den Eindruck des Lesers): 5 Fundstellen,
  darunter "A formal check is narrower than it looks" in Kapitel 0 --
  genau der Satz, den der Skill als Negativbeispiel fuehrt.
- Regel 9/10 (Werbesprache, inszenierte Gegensaetze): 14 Fundstellen,
  u.a. "payoff", "the price of this expressiveness", "not only
  elegant", "a beautiful example", "powerful" (3x), "magic".
- Regel 1 (vage Ankuendigungen): die Einstiege von OrdersAndLattices,
  AlgebraicHierarchy, Topology, MeasureTheory, Filters, 01-Nat,
  SetsAndTypes, Projects.
- Regel 12 (Doppelungen): zwei echte Funde. In 06-Probability stand
  die Monaden-Definition zweimal fast wortgleich, in 00-SetsAndTypes
  die Definition von `Set α` als `α → Prop`.

**Nicht gemacht:** ein Absatz-fuer-Absatz-Umbau des gesamten
Fliesstexts. Dafuer waeren die grossen Kapitel einzeln durchzugehen;
02-Types, 01-Nat, 00b-Universes, 04-Typeclasses und 06-Probability
sind angefangen, der Rest nicht. Wer das fortsetzt: die Methode war,
Absaetze ab 45 Woertern auszugeben und einzeln zu pruefen -- die
Kuerzungen liegen dort, nicht in den Listen.

## 2026-10-12 -- Favicon, Kapitel "6. Slides", Zurueck-Button auf den Folien

- **Favicon.** Die Seite hatte keins. `static/favicon.svg` ist das `L`
  der Lean-Wortmarke, neu gezeichnet: ein Strich (`stroke-width 7` auf
  `viewBox 0 0 64 64`) auf einem Quadrat im Freiburger Identity-Blau
  `#34499a` (aus `--wp--preset--color--identity-blue-100` der
  Uni-Website; das Lean-Blau `#0073a3` war die erste Fassung).  Das
  Original `static/lean_logo.svg` ist als Favicon unbrauchbar: die
  Striche der Wortmarke sind bei 16 px unsichtbar.  Daneben
  `favicon-32.png` (Fallback) und `favicon-180.png`
  (`apple-touch-icon`), beide mit `inkscape --export-width` erzeugt.
  Eingehaengt ueber `staticIcons` in `Main.lean`, das in `extraHead`
  kommt; Verso schreibt `/static/...` pro Seite auf den `<base>` um.
- **"6. Slides".** Die Decks standen vorher als Absatz in *Practical
  matters*.  Jetzt eigener Top-Level-Teil
  `Leancourse/Coursenotes/06-Slides.lean`, eingebunden nach der
  Bibliographie, also Nummer 6.  Wichtig: `file := "Lecture-slides"` im
  `%%%`-Block, sonst hiesse das Verzeichnis `Slides` und kollidierte
  auf case-insensitiven Dateisystemen mit dem Deck-Verzeichnis
  `slides/`.  In *Practical matters* steht jetzt "six parts" und ein
  Stichpunkt *Slides*.
- **Zurueck-Button.** `VersoSlides.Config` hat `extraHead : Array Html`.
  `SlidesMain.lean` haengt dort ein `<style>` und ein `<script>` ein;
  das Script setzt beim `DOMContentLoaded` ein `<a class="course-back">`
  an `body` -- also ausserhalb von `.reveal`, damit reveal.js es weder
  mitskaliert noch pro Folie bewegt.  Ziel ist relativ:
  `../../Lecture-slides/` (Deck liegt unter `<site>/slides/<deck>/`).
  Opacity 0.45, bei Hover 1, `@media print { display: none }`.
- **Lean-Falle.** In `SlidesMain.lean` braucht es `open
  Verso.Output.Html in` fuer die `{{ ... }}`-Syntax, aber der Typ muss
  dann voll qualifiziert geschrieben werden (`Array
  Verso.Output.Html`): mit geoeffnetem Namespace loest ein blosses
  `Html` auf etwas anderes auf, und der Fehler lautet dann "has type
  Verso.Output.Html but is expected to have type Html".  Umgekehrt
  bringt `open Verso Output in` zwar den Typ, aber nicht die
  `{{ }}`-Syntax.

## 2026-10-12 (2) -- Kapitel 0 bekommt Struktur, Bilder ausgeduennt

- **Kapitel 0 ist jetzt ein eigener Teil**,
  `Leancourse/Coursenotes/00-Introduction.lean`, mit zehn
  `#`-Abschnitten und darunter `##`-Unterabschnitten.  Der Grund ist
  eine Verso-Eigenheit: ob Unterteile eigene HTML-Seiten werden,
  entscheidet der **Elternteil** (`VersoManual.lean:943`,
  `if depth > 0 ∧ part.htmlSplit != .never`).  `#`-Ueberschriften direkt
  im Wurzeldokument werden deshalb zwangslaeufig eigene Seiten -- ein
  `htmlSplit := .never` an der Ueberschrift selbst hilft nicht.  Als
  eigener Teil mit `htmlSplit := .never` bleibt alles auf einer Seite.
- **`number := false`** am Teil haelt ihn aus der Nummerierung heraus:
  Introduction ohne Nummer, danach weiter mit 1. bis 6., also bleibt
  "6. Slides" wie gewuenscht.  Die Wurzelseite ist jetzt eine
  Titelseite mit Inhaltsverzeichnis.
- **Verso-Falle:** `*x*` ist in Verso **fett**, nicht kursiv, und
  erzeugt `<strong>`.  `**x**` erzeugt dasselbe und bringt nur die
  Warnung "Unnecessary '*'".  Fette Absatz-Header waeren von der
  normalen Hervorhebung also nicht zu unterscheiden gewesen -- daher
  echte `##`-Ueberschriften.
- **Bildzeilen.** `static/figures.css` ist umgebaut: die `figure` ist
  jetzt eine Spalte, und jeder `<p>` darin eine zentrierte Zeile.  Weil
  Verso Bilder in aufeinanderfolgenden Quellzeilen in **einen** Absatz
  setzt und bei Leerzeile dazwischen in getrennte, steuert die Quelle
  die Zeilenaufteilung: Portraits beginnen eine neue Zeile, ausser wo
  alles in eine passt (four colour, Kepler, die beiden Logos).
- **Weg sind** die Bilder zu LTE, Perfectoid Spaces, Sphere Eversion
  und Freiman-Ruzsa, und der doppelte Sphere-Packing-Eintrag unten (er
  steht oben im 2026-Abschnitt).  Die PNGs bleiben im Repo, die Folien
  benutzen sie weiter.
- **arXiv-Grafik als Anteil.** `scripts/make_arxiv_figure.py` mit
  `scripts/data/arxiv_math_weekly.csv` (Auszug aus dem Volltext-Scan in
  `~/bwSyncShare/Vortraege/20260720_CRC`).  Anteil statt Zahl, weil der
  Nenner mitgewachsen ist: arXiv-math ging von ~1 000 Einreichungen pro
  Woche im Januar auf ~2 450 Ende September.  Der Anteil steigt von
  ~0,3 auf ~1,5 bis 2 pro 100.

## 2026-10-12 (3) -- Foliensatz Introduction ueberarbeitet

26 -> 24 Folien. Weg: "Two things it is not" (die Autoformalize-Zeile
steht jetzt auf "What formalizing means"), "One day apart" (die Pointe
steht im letzten Punkt der 2026-Folie) und "In between". Neu: "What the
course is for" (Ziele) und "What your machine needs" (Hardware-Tabelle).

- **Vertikaler Ueberlauf** war auf mehreren Folien die letzte Zeile.
  Zwei Ursachen und zwei Hebel: `.reveal section p { font-size: 0.8em }`
  als einziger globaler Knopf, und kuerzere Zeilen, damit keine Zeile
  zweizeilig umbricht. `%%%state := "dense"%%%` funktioniert dafuer
  **nicht** -- reveal haengt `data-state` an das Deck, nicht an die
  `<section>`, ein `section.dense`-Selektor greift also nie.
- **Screenshot-Kontrolle:** `#/N` zeigt nur den ersten Fragment-Zustand.
  Um den echten Platzbedarf zu sehen, braucht die Kopie der Seite
  `.reveal .fragment { opacity:1; visibility:visible; transform:none }`
  -- ohne `transform:none` ueberlappen `fadeUp`-Fragmente und man sieht
  einen Fehler, den es nicht gibt. Skript dafuer im Scratchpad.
- **Bildunterschrift direkt unter dem Portrait:** Direktiven lassen sich
  schachteln, wenn die aeussere mehr Doppelpunkte hat. Also
  `::::::hstack` > `::::vstack` > `:::class "names"`. Dazu
  `.reveal .r-hstack .r-vstack { gap: 0 }`.
- **Listen in Fragmenten vermeiden.** Mehrere `:::fragment`-Bloecke mit
  je einem `- item` verschachteln sich beim Rendern unterschiedlich
  tief. Stattdessen normale Absaetze mit `*1879* -- ...`.
- **Inhaltlich beantwortet:** Automath ist von N. G. de Bruijn (1967)
  und steht auf getyptem Lambda-Kalkuel, nicht auf Mengenlehre; das
  Vierfarben-Programm von 1976 war ein gewoehnliches Programm, kein
  Beweisassistent, Gonthier hat es 2005 in Coq neu gemacht; Flyspeck
  lief in HOL Light und Isabelle; Sphere Packing lief in Lean auf
  Mathlib.
- **Portraits von Frege und Russell** ergaenzt (`fetch_portraits.py`,
  beide public domain). Die Lizenzpruefung im Skript laesst jetzt
  ausser CC auch "public domain" zu -- nur fuer diese beiden.

## 2026-10-12 (4) -- Portraits zurueck, Folien nachgezogen

- **Missverstaendnis korrigiert:** "die Bilder weg" bei LTE, Perfectoid,
  Sphere Eversion und Freiman-Ruzsa meinte die *Mathe-Grafiken*, nicht
  die Personen. Die vier Portrait-Gruppen stehen wieder im Skript, ohne
  die Grafik davor, als eigene `:::figure` mit allen Portraits in einem
  Absatz (= eine Bildzeile, bei vieren bricht sie um).
- Folien: 24 -> 23. "7 Oct" von der 2026-Folie runter (steht in den
  Sprechernotizen), Kepler-Folie heisst "The Kepler conjecture",
  Voevodsky-Folien zusammengezogen, Ziele-Folie woertlich aus dem
  Skript (sechs Punkte, `.goals li { font-size: 0.56em }`, sonst passt
  es nicht), arXiv-Folie nennt jetzt die Verdopplung der Einreichungen
  statt den Anteil zu wiederholen.
- **CSS-Spezifitaet, zum zweiten Mal:** `.reveal section p` (0,1,2)
  schlaegt `.names` und `.caption` (0,1,0), die Bildunterschrift kam
  dadurch in Fliesstextgroesse. Beide Regeln sind jetzt als
  `.reveal section p.names` / `.reveal section .names p` geschrieben.
  Die Diagramme brauchen ausserdem ein explizites `(height := "40vh")`,
  sonst bleibt unter der Unterschrift kein Platz.
- **Ueberlauf-Test** statt Augenmass: `scratchpad/overflow.sh` setzt in
  einer Kopie der Seite jede `<section>` kurz auf `display:block`,
  misst die Hoehe und vergleicht sie mit den 700 px des Decks. Reveal
  blendet nicht benachbarte Folien aus, deshalb der Umweg -- ohne ihn
  meldet `scrollHeight` fuer fast alle Folien 0.


## 2026-10-12 (5) -- Hilbert, Church, Turing, Lambda-Kalkuel

- **Luecke im Kapitel 0 geschlossen.** Zwischen Russell (1902) und
  Automath (1967) stand nichts. Jetzt drei Abschnitte unter "How it got
  here": `prehistory` (Frege, Russell, Hilbertprogramm, Goedel 1931),
  `entscheidungsproblem` (Hilbert/Ackermann 1928, Church und Turing
  1936, Lambda-Kalkuel, Curry-Howard) und `first-assistants` (Automath,
  Mizar, LCF, HOL, Isabelle, Coq; LCF-Architektur gegen de-Bruijn-
  Kriterium).
- **Der didaktische Kern** ist die Dreiteilung: einen Beweis *pruefen*
  ist entscheidbar (Kernel), einen *finden* semi-entscheidbar
  (`exact?`, `grind`, daher das Zeitlimit), *Beweisbarkeit entscheiden*
  unentscheidbar (1936). Das ist die Antwort auf "warum macht es der
  Rechner nicht einfach selbst" und die Begruendung dafuer, dass Blatt
  `01-g` `grind` eine finishing tactic nennt.
- **Folien 23 -> 28**: "The idea is old" aufgeteilt in The idea is old /
  Hilbert's programme / 1936: Church and Turing / The lambda calculus /
  Checking is not finding / 1967: the first checker.
- **Mathe im Folien-Header geht nicht**: `# The $`\lambda`-calculus`
  bricht mit "Failed to convert ... inline_math". Ein literales `λ` im
  Header wird von reveals `text-transform: uppercase` zu `Λ` -- deshalb
  heisst die Folie ausgeschrieben "The lambda calculus".
- **KaTeX wurde doppelt geladen.** `Main.lean` brachte ueber `staticCss`
  /`staticJs` eine eigene Kopie von `katex.min.js` und `math.js` mit,
  Verso laedt unter `-verso-data/katex/` dieselben Dateien. Beide
  Listener rufen `katex.render(m.textContent, m, ...)` auf derselben
  Stelle auf, der zweite liest den schon gerenderten Text -- jede Formel
  stand zwei- bis dreimal da. Im Manuskript war vorher nirgends Mathe
  gesetzt, deshalb ist es nie aufgefallen. Die drei Tags in `Main.lean`
  sind raus; `static/katex/` (3 MB) und `static/math.js` sind damit
  unbenutzt und koennen weg.
- **Neue Portraits** (`fetch_portraits.py`): Hilbert, Goedel, Turing
  (alle public domain), de Bruijn (MFO, CC BY-SA 2.0 de, auf Kopf und
  Schultern beschnitten -- `CROP` im Skript, in CREDITS.md vermerkt).
  Von Alonzo Church gibt es kein freies Foto, er bekommt eine
  Silhouette wie Gonthier und die anderen.
- **URLs mit Klammern** zerlegen Versos Markdown-Links: der Commons-
  Pfad `File:Alan_Turing_(1951)_(crop).jpg` muss `%28`/`%29` schreiben,
  sonst `error: '_'`.

## 2026-10-13 -- Hintergrund ans Ende

- **Kapitel 0 umgestellt.** `# How it got here` enthaelt jetzt nur noch
  die Geschichte der Beweisassistenten: Automath 1967, die vier Linien
  (Mizar, LCF, HOL, Coq), die vier Episoden 1976/1998/2013/2020, Lean.
  Frege, Russell, Hilbert, Goedel, das Entscheidungsproblem, der
  Lambda-Kalkuel und Curry-Howard stehen in einem neuen Abschnitt
  `# Where the ideas come from` (`tag := "background"`), direkt vor
  `# Practical matters`. Begruendung des Nutzers: das ist logischer und
  historischer Hintergrund, nicht Grundlage der Werkzeuge, und
  Hintergrund gehoert nach hinten.
- **Zwei Verweise** halten die Teile zusammen: der Opener von "How it
  got here" zeigt mit `{ref "background"}` nach hinten, und der
  Automath-Absatz verlinkt Curry-Howard dorthin. Kein eigenes Kapitel,
  weil Kapitel 1 "Lean and its type theory" den Stoff ohnehin lehrt
  (`01-Lean/05-CurryHoward.lean`).
- **Folien in derselben Reihenfolge**: die fuenf Hintergrundfolien (The
  idea is old / Hilbert / 1936 / The lambda calculus / Checking is not
  finding) stehen jetzt zwischen "Mathlib" und "Goals". Die Notizen der
  ersten sagen, dass der Block uebersprungen werden kann, wenn die
  Stunde weg ist. 28 Folien, keine ueber 700 px.

## 2026-10-13 (2) -- Hintergrundabschnitt nach den Waseda-Folien

- **Vorlage**: `sources/waseda-sils-turing-foundations-slides.pdf`
  ("Alan Turing and the Foundations of Computer Science", MI314,
  Waseda SILS). Nur die erste Haelfte ist brauchbar; die zweite geht
  ueber Shannon und Rechner. Nicht zitiert, nur Vorlage fuer den
  Aufbau. **Fehler darin, nicht uebernommen**: die Folien setzen das
  Entscheidungsproblem mit Hilberts 10. Problem gleich. Das 10.
  Problem ist die Loesbarkeit diophantischer Gleichungen
  (Matiyasevich 1970); das Entscheidungsproblem steht in
  Hilbert-Ackermann 1928.
- **Neu im Abschnitt `background`**: Peano 1889 mit Verweis auf
  `{ref "nat"}`, Russells Paradoxon als Formel, Zermelo 1908, Hilbert
  1917 *Axiomatisches Denken* und das *ignorabimus* von 1900, die drei
  Eigenschaften konsistent / vollstaendig / entscheidbar als Liste,
  Goedels **Vollstaendigkeitssatz 1929** vor den
  Unvollstaendigkeitssaetzen 1931, das Diagonalargument als Faden
  Cantor -> Goedel -> Turing, Turings Maschine mit Band, Kopf und
  Tabelle, Turings Promotion bei Church, und die Church-Turing-These
  als Behauptung ueber das Wort, nicht als Satz.
- **Der Vollstaendigkeitssatz traegt Punkt 2 der Dreiteilung**: Beweise
  aufzaehlen findet einen Beweis genau dann, wenn es einen gibt, weil
  1929 jede gueltige Formel ableitbar ist. Das stand vorher nicht da.
- **Folien 28 -> 29**: "Hilbert's programme, 1920s" ist aufgeteilt in
  "Hilbert's programme" (die drei Fragen) und "Goedel, 1929 and 1931".
  "The idea is old" hat Peano dazubekommen. Keine Folie ueber 700 px.

## 2026-10-13 (3) -- Ueberschriften nach Stichworten, Links auf die Systeme

- **Ueberschriften heissen jetzt nach dem Stichwort**, unter dem man die
  Sache nachschlaegt, nicht nach der Pointe: `1976: the four colour
  theorem`, `1998: the Kepler conjecture`, `2013: Voevodsky`,
  `2020: the Liquid Tensor Experiment`, `Lean, from 2013`,
  `From Frege to Goedel`, `1936: the Entscheidungsproblem`. Die Pointe
  steht ohnehin im jeweils letzten Satz des Abschnitts. **Die `tag`s
  sind unveraendert** (`four-colour-episode`, `kepler-episode`, ...),
  damit keine Links brechen.
- **Dieselben Titel auf den Folien**, dazu `1967: Automath` und
  `Frege, Peano, Russell`. "1936: the Entscheidungsproblem" bricht in
  zwei Zeilen (540 px statt 468) -- passt, sieht geprueft gut aus.
  "Checking is not finding" bleibt, dafuer gibt es kein Stichwort.
- **Links auf die Systeme** in "The first proof assistants": Mizar
  (`mizar.uwb.edu.pl`, `mizar.org` leitet dorthin um), HOL
  (`hol-theorem-prover.org`), Isabelle, Coq/Rocq. Alle vier mit
  HTTP 200 geprueft.

## 2026-10-13 (4) -- Sprechernotizen zum Durchlesen

- **`scripts/slides_notes.py`** zieht die `:::notes` aus einem gebauten
  Deck und gibt sie als Markdown aus, Folie fuer Folie mit Nummer und
  Titel. Liest das erzeugte HTML, nicht die Lean-Quelle, also steht da
  genau das, was reveal unter `S` zeigt.

      lake exe slides _out/html-multi/slides
      python3 scripts/slides_notes.py introduction > _out/notes-introduction.md

  Ohne Argument nimmt es alle Decks.
- **Stand**: Introduction 29 von 29 Folien mit Notizen, Filters 4 von 9
  (ohne Notizen: Learning goal, The three axioms, In Lean, Three
  filters to know, In one line).

## 2026-10-13 (5) -- Herkunft der Typtheorie in Kapitel 1

- **Neuer Abschnitt `# Where types come from`** (`tag :=
  "types-history"`) in `01-Lean/02-Types.lean`, direkt vor
  `# The universe hierarchy`. Russell 1908 als Reparatur seines
  Paradoxons von 1902, Chwistek/Ramsey, Church 1940 (nachdem
  Kleene/Rosser 1935 den ungetypten Kalkuel von 1932 zerlegt hatten),
  abhaengige Typen bei de Bruijn ab 1967 und Martin-Loef ab 1971,
  Coquand/Huet 1985 und Paulin-Mohring 1990.
- **Die Pointe**: dreimal derselbe Zug -- ein System laesst
  Selbstanwendung zu, ein Widerspruch folgt, Typen verbieten sie. Der
  Abschnitt laeuft genau auf `Type 0 : Type 1 : ...` zu, also auf den
  Abschnitt, der danach kommt.
- **Verweise**: `{ref "background"}` zurueck ins Kapitel 0 und
  `{ref "cic"}` nach vorn in `03-Mathematics/00b-UniversesAndAxioms`.
  Die Curry-Howard-Geschichte steht weiter in `05-CurryHoward.lean`
  unter `curry-howard-history`; die beiden ueberschneiden sich nicht.
- Quellen in `sources/history-of-itp.md` unter `## Type theory`, keine
  davon heruntergeladen.

## 2026-10-13 (6) -- LCF-Link repariert, Pressemitteilungen verlinkt

- **Der LCF-Link war kaputt, weil `i.stanford.edu` ueberhaupt kein
  HTTPS spricht** (`curl -I https://...` bricht mit Exit 7 ab). Ueber
  `http://` liefert der Host die richtige PDF, aber auf einer
  HTTPS-Seite stuft der Browser das hoch und es scheitert. Ersetzt
  durch die Wayback-Kopie
  `web.archive.org/web/20240703134244/http://i.stanford.edu/...` --
  geprueft: 2 872 429 Bytes, identisch mit
  `sources/milner-1972-lcf-stanford-aim-169.pdf`. **Achtung bei
  Wayback**: der juengste Schnappschuss (20250217) ist bei genau 1 MiB
  abgeschnitten, der von 2024 ist vollstaendig. Die CDX-API
  (`web.archive.org/cdx/search/cdx?...&fl=timestamp,statuscode,length`)
  zeigt die Laengen. Zwei Stellen betroffen: die Systemliste und der
  `Sources`-Abschnitt.
- **Im ganzen Repo gibt es jetzt keinen `http://`-Link mehr**
  (`grep -rnoE '\]\(http://[^)]*\)' --include=*.lean`).
- **Die 2026-Meldungen sind verlinkt**: Sphere Packing auf
  `math.inc/sphere-packing` (der Autoformalisierer heisst *Gauss*) und
  `github.com/math-inc/Sphere-Packing-Lean`, FLT auf
  `anthropic.com/news/formalizing-fermats-last-theorem`, Navier-Stokes
  auf `openai.com/index/navier-stokes-solution/`, der Katalog auf
  `openai.com/index/sharing-ai-progress-in-mathematics/` und
  `github.com/openai/math`.
- **`openai.com` antwortet curl und WebFetch mit 403** (Bot-Schutz),
  im Browser laeuft es. Beide Seiten ueber die Wayback-API
  gegengeprueft, beide existieren. Gleicher Fall wie der
  IAS-Voevodsky-Link.
- Den Rueckzug vom 7. Oktober habe ich **nicht** auf einen Commit
  verlinkt: der einzige Kandidat
  (`openai/math@3014888`, 2026-10-08) heisst nur "Update manuscripts
  and Lean formalizations" und laesst sich nicht sicher zuordnen.

## 2026-10-14 -- Kapitel 0 chronologisch umgebaut

- **Neue Gliederung**: What formalizing means / Why formalize? / Where
  the field stands / **How we got here** / **Current state of Lean** /
  Landmark formalizations / Other theorem provers / Other courses /
  Practical matters / Sources / Picture credits. Die Abschnitte
  `Where the ideas come from` und `Lean and Mathlib` sind
  aufgegangen und gibt es nicht mehr.
- **`# How we got here` laeuft jetzt strikt chronologisch** und hat
  erstmals **drei Ebenen** (`###` funktioniert in Verso, vorher nie
  benutzt):
  `## The mathematics` -> `### 1879 to 1913: Frege, Peano, Russell`,
  `### 1917 to 1931: Hilbert's programme, and Goedel`,
  `### 1936: the Entscheidungsproblem`;
  `## The proof assistants` -> `### 1967: Automath`,
  `### 1972 to 1991: Mizar, LCF, HOL, Isabelle, Coq`,
  `### 1976`, `### 1998`, `### 2013: Voevodsky`, `### 2020`;
  dann `## 2013: Lean`. Damit kehrt sich die Entscheidung vom
  13.10. ("Hintergrund zuletzt") wieder um -- auf Wunsch des Nutzers.
- **Tags**: `how-it-got-here` -> `how-we-got-here`, `background` faellt
  weg (die drei Verweise darauf zeigen jetzt auf `prehistory` bzw.
  `entscheidungsproblem`), neu `the-mathematics`, `hilbert-programme`,
  `the-assistants`, `lcf-line`, `lean-origin`, `lean-today`. Die alten
  Episoden-Tags sind unveraendert.
- **`# Current state of Lean`** ist neu: Release-Zyklus (monatlich,
  `v4.35.0` am 12.10.2026) und warum nichts von allein aktualisiert
  (`lean-toolchain` + `elan` + `lake`, Kurs auf `v4.34.0` gepinnt);
  Lean FRO (Non-Profit seit Juli 2023 unter Convergent Research,
  21 Leute laut Teamseite, de Moura/Ullrich, Geldgeber);
  Mathlib mit den Zahlen vom 15.09.2026; **Mathlib Initiative**
  (`mathlib-initiative.org`, Programm von Renaissance Philanthropy
  seit September 2025, die zweiten 5 Mio. von Alex Gerko, Ziel u.a.
  Review in einer Woche fuer 90 % der PRs, Commelin arbeitet dort);
  Import-Map und API-Doku.
- **Folien 29 -> 31**, gleiche Reihenfolge wie das Kapitel. Neu:
  `2013: Lean` (de-Moura-Portrait, vorher nur in den Notizen von
  Automath versteckt) und `Lean today`. `How we got here` ist jetzt
  eine Roadmap ueber den ganzen Bogen statt nur ueber die vier
  Episoden; `Mathlib` hat Zahlen und die Initiative dazubekommen.
  Keine Folie ueber 700 px, alle 31 haben Notizen.

## 2026-10-14 (2) -- arXiv-Grafik auf den Stand vom 14.10.2026

- **Nur die arXiv-Grafik hat neue Daten.** Quelle ist
  `~/bwSyncShare/Vortraege/20260720_CRC/arxiv_fulltext_disclosure_weekly.csv`
  (Stand 14.10.2026, 06:23); `scripts/data/arxiv_math_weekly.csv` ist
  der Auszug daraus (`week_start`, `n` -> `papers`, `lean_formalized`,
  `complete`). Geaendert: die Woche 28.09. ist nachgewachsen (2 466 ->
  2 522 Papers, 36 -> 38), die Woche 05.10. ist jetzt vollstaendig
  (2 546 / 60), die Woche 12.10. ist angelaufen und wird vom Skript
  wegen `complete = 0` uebersprungen.
- **Neuer Hoechstwert 2,36 pro 100** (05.10.), vorher 2,03 (07.09.).
  Damit stimmte "still under two in a hundred" im Kapitel, im
  Alt-Text, im Fragment der Folie und im Docstring von
  `make_arxiv_figure.py` nicht mehr -- alle vier nachgezogen.
- **`github_language_monthly.csv` ist unveraendert** (byte-identisch
  mit der Quelle vom 01.10.). Die Grafik waere auch bei neuen Daten
  gleich geblieben: sie zeichnet nur volle Quartale, und Q3 2026 ist
  schon drin. `itp_github_repos_per_million.*` deshalb *nicht* neu
  erzeugt -- ein Lauf haette nur den Stempel "retrieved" auf heute
  gesetzt und damit ein falsches Datum behauptet.

## 2026-10-14 (3) -- Zermelo gegen Russell, die beiden Antworten von 1908

Frage des Nutzers: nach Russells Paradoxie gab es doch zwei Loesungen,
`x ∈ x` verbieten (Zermelo) oder Typtheorie. Die Aufteilung stimmt,
die Zuordnung war vertauscht -- **Zermelo verbietet keinen Ausdruck.**

- **Zermelo 1908** schraenkt ein, *was existiert*: Aussonderung statt
  unbeschraenkter Komprehension, also nur `{x ∈ A : φ(x)}` aus einem
  schon vorhandenen `A`. $R$ wird nie gebildet, und Russells Argument
  wird zum Satz (es gibt keine Allmenge). Die Sprache bleibt
  unangetastet: `x ∈ x` ist eine wohlgeformte Formel. Dass sie fuer
  keine Menge gilt, ist das **Fundierungsaxiom** (von Neumann 1925,
  Zermelo 1930) -- spaeter, und *nicht* die Reparatur der Paradoxie.
- **Russell 1908** schraenkt ein, *was sagbar ist*. `x ∈ x` ist keine
  falsche Aussage, sondern gar keine. Wohlgeformtheit ist damit eine
  Frage an die Syntax und entscheidbar -- genau das, was ein
  Typchecker tut.
- Beide enden in einer Stufung, aber: die **kumulative Hierarchie**
  $V_\alpha$ ist ein *Satz* darueber, welche Mengen es gibt, die
  **Universenhierarchie** `Type 0 : Type 1 : ...` eine *Regel* der
  Grammatik.
- **Quelle** ist das Buch, auf das der Nutzer verwiesen hat:
  Nederpelt/Geuvers, *Type Theory and Formal Proof*, CUP 2014,
  Abschnitt 13.8, S. 298 ("Zermelo chose another way", das System
  "describes which sets exist"). Liegt unter
  `~/bwSyncShare/Papers/`, ist bezahlpflichtig, kommt nicht ins Repo.
  Eintraege dafuer und fuer Zermelo 1908 in `sources/history-of-itp.md`.

**Wo es steht.** Kapitel 0, `### 1879 to 1913`: drei Absaetze plus
eine `:::table` (restricts / `x ∈ x` is / the stratification is), die
der Nutzer ausdruecklich wollte. Kapitel 1, `# Where types come from`:
ein eigener Absatz mit Fundierung, kumulativer Hierarchie und dem
Entscheidbarkeitsargument, dazu ein Absatz, *warum* die Mathematik
Zermelo gefolgt ist (Reduzibilitaetsaxiom, Wiederholung auf jeder
Stufe, Wohlordnungssatz) und warum sich das umdreht, sobald eine
Maschine prueft (Mizar hat soft types ueber TG-Mengenlehre).

**Folien 31 -> 32.** Neu `Two repairs, 1908` direkt nach
`Frege, Peano, Russell`, mit derselben Tabelle (275 px). Die Tabelle
auf der Personen-Folie haette die auf 700 px getrieben, deshalb eine
eigene; `Frege, Peano, Russell` ist damit wieder bei 515 px. Hoechste
Folie im Deck ist `2013: Voevodsky` mit 557 px.

**Nebenbefund:** `static/katex/` und `static/math.js` sind **nicht**
unbenutzt. Verso gibt Inline-Mathe als `<code class="math inline">`
aus, `math.js` laesst KaTeX im Browser darueber laufen. Das Angebot
aus einer frueheren Sitzung, beides zu loeschen, war falsch.

**Messskript** fuer Folienhoehen (war bisher nur im Scratchpad):
Kopie der `index.html` mit angehaengtem Script, das alle Fragmente
sichtbar schaltet (`opacity/visibility/transform`), jede `section` auf
`display:block; position:static` setzt und die Hoehen in ein
`<pre id="RESULT">` schreibt; dann
`google-chrome --headless --virtual-time-budget=12000 --dump-dom`
und den `<pre>` herausfiltern.

## 2026-10-14 (4) -- imprädikatives `Prop`, und warum es konsistent ist

Nutzer: "`Prop` ist imprädikativ, `∀ p : Prop, p → p` ist selbst ein
`Prop` -- und dass es trotzdem konsistent ist, finde ich erstaunlich."
Steht jetzt in `02-Types.lean`, Abschnitt *Why `Prop` is special*.

- **Codeblock erweitert** um die beiden scharfen Faelle, in Lean
  geprueft: `#check (∀ p : Prop, p → p)` und `#check (∀ p : Prop, p)`
  geben beide `Prop`, waehrend `(α : Type 5) → α → α : Type 6`. Die
  bisherigen Beispiele quantifizierten nur ueber `Type`, nicht ueber
  `Prop` selbst -- der Zirkel war also gar nicht zu sehen.
- **Historische Klammer:** genau das verbietet Russells vicious circle
  principle, genau dafuer brauchte er das **Reduzibilitaetsaxiom**
  (jede Definition ist umfangsgleich mit einer praedikativen). Lean
  braucht es nicht, weil es den Zirkel fuer `Prop` zugibt.
- **Warum konsistent:** Imprädikativität in der Syntax ist nicht
  Zirkularitaet in der Bedeutung. `Prop` laesst sich als vorab
  gegebene Menge von Wahrheitswerten modellieren, ein `∀` darueber ist
  ein Infimum ihrer Elemente, also wieder eines. Die Definition waehlt
  aus, sie vergroessert nichts.
- **Beleg statt Behauptung:** Mario Carneiro, *The Type Theory of
  Lean*, MSc CMU 2019 -- das mengentheoretische Modell, Konsistenz
  relativ zu ZFC + `n` unerreichbare Kardinalzahlen fuer jedes endliche
  `n`, und laut Abstract ist diese Annahme optimal, weil Lean selbst
  Modelle von ZFC mit `n` Unerreichbaren liefert. Link geprueft,
  Eintrag in `sources/history-of-itp.md`.
- **Korrigiert:** der alte Schlusssatz "`Prop` is allowed this
  self-reference because proof irrelevance keeps it harmless" war
  falsch begruendet. Rocq hat imprädikatives `Prop` *ohne*
  definitionale Proof-Irrelevanz. Der echte Preis steht eine Zeile
  weiter unten im selben Abschnitt: die **eingeschraenkte Elimination**.
  Imprädikativität *und* beliebiges Auslesen von Daten aus Beweisen
  zusammen waeren widerspruechlich.
- `Type : Type` bleibt tabu (Girard), daher `Type u : Type (u+1)`.
- **Kapitel 0 dazu** (`### 1879 to 1913`): Russells Verbot ist *weiter*
  als die Paradoxie -- es trifft jede Definition, die ueber eine
  Gesamtheit quantifiziert, die das Definierte enthaelt. Beispiel im
  Text: das Supremum einer beschraenkten Menge reeller Zahlen wird
  durch Quantifikation ueber reelle Zahlen definiert und ist unter dem
  Verbot keine reelle Zahl mehr. Deshalb das Reduzibilitaetsaxiom.
  Von dort Verweis auf `{ref "prop-special"}`.
- **Und wie Lean es loest** (Aufgriff in *Why `Prop` is special*):
  nicht eine Regel fuer alles, sondern zwei. Das Supremum ist
  unproblematisch, weil der definierende Schnitt ein Praedikat auf ℚ
  ist, dessen Rumpf ueber ganz ℝ quantifiziert und trotzdem `Prop`
  bleibt. In Lean geprueft und als Codeblock drin:
  `fun (S : Set ℝ) (q : ℚ) => (∃ x ∈ S, (q : ℝ) < x)` ist
  `Set ℝ → ℚ → Prop`, und `fun (S : Set ℝ) => {q : ℚ | ∃ x ∈ S, (q : ℝ) < x}`
  ist `Set ℝ → Set ℚ`. Genau die Stelle, an der imprädikatives `Prop`
  die Arbeit des Reduzibilitaetsaxioms tut.
