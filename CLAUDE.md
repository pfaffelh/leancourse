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
  files, not part of the Verso manual. A worked solution to every
  sheet lives beside it in [Leancourse/Checks/](Leancourse/Checks/).
- Directory and file prefixes are **single digits** since 2026-10-23
  (`1-Lean`, `2-Mathematics/6-b-Filters.lean`), and a sheet's number
  is its chapter: `2-Mathematics/6-b-Filters.lean` is sheet `2.6-b`
  and belongs to chapter 2.6. `0-Logic` is the logic block, which has
  no chapter; `9-Extra` holds the extra sheet.
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
| `01-e-ByCasesHave`    | `01-e-Classical`     | `by_cases` `Classical.em` `by_contra` `push Not`      |
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
`absurd`, `show`, `suffices`, `push Not`, `tauto`, `itauto`, and
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

## 2026-10-14 (5) -- first-order logic erklaert, die beiden Goedel-Saetze getrennt

Nutzerfrage: "First order logic is complete. Was ist first order logic
genau?" -- der Begriff stand im Kapitel unerklaert, und das doppelte
"complete" zwei Absaetze auseinander ist eine Stolperfalle.

- **Kapitel 0, `### 1917 to 1931`:** Halbsatz dazu, was *first-order*
  heisst -- Quantifikation ueber die *Elemente* eines Bereichs, nie
  ueber Teilmengen, Relationen, Funktionen. Beispielpaar im Text:
  `∀x ∃y (x · y = e)` ist erststufig, "jede beschraenkte Menge
  reeller Zahlen hat ein Supremum" nicht.
- **Die Wortklaerung, die eigentlich fehlte:** *complete* bezeichnet
  zwei Dinge. Eine **Logik** ist vollstaendig, wenn alles
  Allgemeingueltige ableitbar ist (1929). Eine **Theorie** ist
  vollstaendig, wenn sie jede Aussage entscheidet -- das ist Hilberts
  zweite Frage, und das toetet 1931. Dazu eine `:::table`
  (Goedel / about / result), wie vom Nutzer gewuenscht.
- **Warum kein Widerspruch:** der Satz von 1931 ist in ℕ wahr, in
  anderen Modellen derselben Axiome falsch, also nicht
  allgemeingueltig -- 1929 verspricht fuer ihn nichts.
- **Kapitel 1, in der Konsistenz-Passage:** fuer eine *erststufige*
  Theorie sind konsistent-sein und ein Modell haben dasselbe (das ist
  gerade 1929). Leans Logik ist nicht erststufig -- Quantifikation
  ueber Typen und ueber Propositionen -- also gibt es diese
  Aequivalenz nicht, und das Modell muss von Hand gebaut werden.
  Damit steht da jetzt auch, *warum* es ueberhaupt ein Modell braucht.
- **Folie `Gödel, 1929 and 1931`:** nur die Sprechernotizen ergaenzt
  (was first-order heisst, die zwei Bedeutungen von complete, dass
  Lean nicht erststufig ist). Kein neues Element auf der Folie -- sie
  hat schon Portrait plus drei Fragmente.

## 2026-10-14 (6) -- die drei Fragen richtiggestellt

Zwei Fehler, beide vom Nutzer gefunden, beide in der Liste
*Three questions about proofs* in Kapitel 0.

- **"by Gödel's completeness theorem every valid statement has one"**
  war doppelt schief. Erstens haengt der Satz an *erststufiger* Logik,
  und Lean ist hoeherstufig. Zweitens wird er fuer die Aussage gar
  nicht gebraucht: Semi-Entscheidbarkeit der *Beweisbarkeit* folgt
  schon aus Frage 1 -- Beweistexte sind endlich, also aufzaehlbar, und
  Pruefen ist entscheidbar. Vollstaendigkeit leistet etwas anderes,
  naemlich den Schritt von *ableitbar* zu *in jedem Modell wahr*, und
  genau der faellt in Lean weg. Steht jetzt so da, mit Verweis auf
  `{ref "hilbert-programme"}` und auf 1931.
- **Fragen 2 und 3 sahen aus wie ein Widerspruch.** "Find a proof:
  semi-decidable" gegen "Decide whether provable: undecidable" -- es
  ist dieselbe Menge. Semi-entscheidbar heisst, die Ja-Faelle werden
  alle gefunden; unentscheidbar heisst, die Nein-Faelle nicht. Die
  Luecke ist einseitig.
- **Darstellung:** dafuer jetzt eine zweizeilige `:::table` (Is there
  a procedure that / confirms it when true / refutes it when false).
  Zeile 2 ist Frage 2 und 3 zugleich, und die beiden Woerter sind die
  beiden Spalten. Das macht sichtbar, was vorher behauptet werden
  musste. Kapitel 0 hat damit fuenf Tabellen.
- **Folie `Checking is not finding`** war inhaltlich schon richtig
  (die Notizen berufen sich nicht auf Vollstaendigkeit). Ergaenzt nur
  um den Absatz, dass Zeile zwei und drei dieselbe Menge sind.
- **Nachtrag: alle Kapitel-0-Tabellen stehen jetzt auch im Deck.**
  Drei waren schon da (1908 -> `Two repairs`, Systemvergleich ->
  `Three systems`, Hardware -> `What your machine needs`), zwei
  fehlten: die Goedel-Tabelle ersetzt auf `Gödel, 1929 and 1931` die
  beiden Jahres-Fragmente (das Cantor-Fragment bleibt), und
  `Checking is not finding` hat statt Frage/Antwort jetzt dieselbe
  Darstellung wie das Kapitel, um eine Spalte *verdict* erweitert.
  Hoechste Folie unveraendert `2013: Voevodsky` mit 557 px.

## 2026-10-14 (7) -- die Luecke 1936-1967 gefuellt: ATP gegen ITP

Nutzerfrage: "Ist zwischen 1936 und 1967 nicht passiert? Warum hat
de Bruijn daran gearbeitet?" -- doch, und zwar das *andere* Fach.

- **Absatz am Kopf von `## The proof assistants`** (ohne eigene
  Ueberschrift, bewusst klein gehalten): Davis 1954 auf der JOHNNIAC,
  Logic Theory Machine 1956 (kuerzerer Beweis fuer Principia *2.85),
  Wang 1959, Robinson 1965 (Resolution und Unifikation). Fuer
  Mathematik skaliert nichts davon.
- **Automath ist der Rueckzug**, nicht die Fortsetzung: von Frage 2
  auf Frage 1, der Mensch beweist und die Maschine prueft. Daher der
  Name des Fachs -- *interactive* theorem proving -- und der Titel
  dieser Vorlesung. Ein Satz dazu im Automath-Abschnitt, derselbe
  Gedanke in den Sprechernotizen der Automath-Folie.
- **Und ATP ist zurueck**, ein Satz hinter der Fragen-Tabelle:
  `omega`, `grind`, `bv_decide` suchen (bei `bv_decide` ein externer
  SAT-Solver), aber das Ergebnis geht als Pruefauftrag an den Kern.
  Dasselbe Prinzip wie beim Autoformalisierer weiter oben im Kapitel:
  unzuverlaessig erzeugen, klein und fest pruefen. Drei Generationen
  von Erzeugern, eine Bauform.
- **Nicht verwechseln** (kam in der Diskussion auf): Autoformalisierung
  erzeugt die *Aussage* aus Prosa, ATP den *Beweis* aus der Aussage.
  Fuer das Erste gibt es gar kein Entscheidbarkeitspraedikat, weil auf
  der Eingabeseite kein formales Objekt steht.
- **Nachtrag zur Fragen-Tabelle:** die zweizeilige Fassung legte 2 und
  3 zusammen und sah dadurch aus, als fehle Frage 2. Jetzt drei
  Zeilen, passend zur Aufzaehlung darueber. Zeilen 2 und 3 haben
  *dieselbe* Frage und dieselbe mittlere Spalte und unterscheiden
  sich nur in "refutes it when false" (not asked / no such procedure).
  Damit ist sichtbar, was vorher im Text behauptet wurde. Folie und
  Kapitel tragen dieselbe Tabelle; Folienhoehen unveraendert, Maximum
  weiterhin `2013: Voevodsky` mit 557 px.

## 2026-10-14 (8) -- Terminierung und Positivitaet, neuer Abschnitt

Nutzerfrage: "Ueber die erste Tuer steht noch nichts im Manuskript,
oder?" -- stimmte, und es war sogar **zweimal angekuendigt**
(`01-Lean.lean:33` und die Gliederung in der Einleitung versprechen
beide "well-foundedness and the avoidance of paradoxes" fuer den
Mathematik-Teil). Jetzt eingeloest.

Neuer Abschnitt `# Why the kernel has no loops` in
`03-Mathematics/00b-UniversesAndAxioms.lean`, direkt vor
`# Constructive vs classical logic`, mit vier Tags: `termination`,
`recursors-not-recursion`, `strict-positivity`, `partial-def`.

- **Warum der Zirkel durchrutschen wuerde:** beim Pruefen von
  `def c : T := e` ist der Name schon in der Umgebung. Jeder Schritt
  ist lokal korrekt, der Zirkel nur global sichtbar. Vergleich mit
  Haskell (`undefined : a` bewohnt jeden Typ; unter Curry-Howard
  heisst das "jede Aussage ist beweisbar").
- **Der Kern hat gar keine Rekursion**, nur Rekursoren. `#check
  @Nat.rec`, und `#print stepTwice` zeigt, dass der
  Gleichungs-Compiler zu `Nat.brecOn` uebersetzt. Terminierung wird
  nicht geprueft, sondern wegkompiliert; sonst wohlfundierte
  Rekursion ueber `WellFounded.fix` mit Beweispflicht.
- **Zweite Tuer, strikte Positivitaet.** Der Nutzer fragte zu Recht
  nach, *warum* das reicht -- der Abschnitt behauptete es nur. Jetzt
  mit Ableitung: aus dem Mustervergleich kommt
  `unmk : Bad → (Bad → False)`, damit ist Selbstanwendung typisierbar,
  `delta b := unmk b b`, `delta (mk delta) : False`. **Keine Rekursion
  noetig.** Als gepruefter Satz im Text, *ohne* Axiome:
  `theorem no_negative_occurrence (Bad : Type) (mk : ...) (unmk : ...)
  : False`. Bewusst so und nicht mit `axiom Bad`, sonst stuende ein
  `False` in der Umgebung des ganzen Manuskripts.
- **`partial def`** ist erlaubt, aber fuer die Logik undurchsichtig
  und verlangt einen bewohnten Zieltyp:
  `partial def spinFalse (_ : Unit) : False` scheitert mit
  "could not prove that the type ∀ (x : Unit), False is nonempty".
  Daran haengt die Pointe des Abschnitts: verboten sind nicht
  Schleifen, verboten ist der *erste* Bewohner eines Typs.
- **Namenskollision:** `twice` gibt es schon in `01-Lean/01-Nat`;
  der Import schlaegt dann mit "environment already contains" fehl.
  Jetzt `stepTwice`. Warnungszahl fuer die Datei vor und nach der
  Aenderung gleich (8), der Abschnitt bringt also keine neuen.

## 2026-10-14 (9) -- Systeme: was jedes besser machte, und ob Lean bleibt

Zwei Nutzerbeobachtungen: das Kapitel lese sich, als werde alle paar
Jahre ein ITP durch einen neuen abgeloest, und es bleibe offen, ob
Lean dasselbe passiert. Dazu die Frage, ob man sagen kann, was jedes
System besser machte als seine Vorgaenger.

- **Die Ablöse-Lesart ist falsch, und das steht jetzt da.** Von den
  sieben genannten Systemen laufen fuenf; nur *Automath* und *LCF*
  haben aufgehoert, und beide haben ihre Architektur vererbt. Grund:
  eine Bibliothek laesst sich nicht umziehen -- *seL4* bleibt in
  Isabelle, der Vierfarbensatz in Rocq.
  **Korrektur unterwegs:** ich hatte erst geschrieben, nur Automath
  habe aufgehoert. LCF laeuft auch nicht mehr.
- **Neue Grafik** `static/figures/itp_lineage.{png,pdf}`, Skript
  `scripts/figures/itp_lineage.py`. Zeitstrahl 1967-2026, ein Balken
  je System, Name darueber, *was es hinzufuegte* darunter, Farbe =
  Tradition (de-Bruijn-Linie blau, LCF-Linie gruen, Mizar orange,
  dieselben Farben wie in der GitHub-Grafik). Gestoppte Systeme mit
  38 % Deckkraft und Vermerk *stopped*.
  **Layout-Falle:** erster Versuch hatte den Text *im* Balken -- bei
  kurzen Balken (Automath, LCF, Lean) laeuft er heraus und kollidiert
  mit dem Vermerk. Jetzt Name ueber, Text unter dem Balken, und
  Zeilenabstand `pitch = 1.5`, sonst stoesst die Unterzeile einer
  Zeile an den Namen der naechsten. Legende oben rechts, wo durch die
  kurzen fruehen Balken Platz frei ist.
- **Die Tabelle, die ich zuerst gebaut hatte, ist wieder weg** -- sie
  hat die Links zu Mizar, LCF, HOL, Isabelle und Coq geschluckt, die
  der Nutzer frueher ausdruecklich wollte. Jetzt: Grafik *und* die
  alte Aufzaehlung mit den Links.
- **`# Current state of Lean`** endet jetzt mit *Will this last?* --
  dagegen: Rocq hatte bis etwa 2023 die groesste Bibliothek und wurde
  in fuenf Jahren ueberholt ({ref "itp-repos"}), Groesse entscheidet
  also nichts. Dafuer: in sechzig Jahren wurde kein Beweisassistent
  ersetzt, nur ergaenzt. Was wirklich bricht, ist die eigene
  Nachfolge: Lean 1 bis 4, und der Mathlib-Port 3 -> 4 hat die
  Community ueber ein Jahr gekostet. Schluss: abhaengige Typen, der
  Unterschied Taktik/Term, Hierarchien und das Lesen formaler
  Aussagen sind nicht Lean-spezifisch.

## 2026-10-14 (10) -- Kapitel 0 umgebaut: Systeme, dann Chronik, dann Lean heute

Nutzervorgabe: alle ITPs zusammen nach oben, ab Automath, inklusive
Lean und der Bibliotheksinformation; danach die ganze Chronik von
Vierfarben bis Equational Theories; danach Current state of Lean,
Practical matters, Other courses.

**Neue Gliederung** von `# How we got here`:

    ## The mathematics      (unveraendert)
    ## The proof assistants
         1967: Automath
         1972 to 1991: Mizar, LCF, HOL, Isabelle, Coq
         2013: Lean                  <- war ## nach den Episoden
         The three systems today     <- war `# Other theorem provers`
    ## What came of it      (tag bleibt `landmarks`)
         1976 Vierfarben / 1998 Kepler / 2013 Voevodsky /
         2019 Perfectoid / 2020 LTE / 2022 Sphere eversion /
         2023 Freiman-Ruzsa / 2024-25 Equational Theories

Danach `# Current state of Lean`, `# Practical matters`,
`# Other courses` (die letzten beiden getauscht).

- **Das war der eigentliche Fehler der alten Fassung:** es gab *zwei*
  Listen von Erfolgen -- vier Episoden unter den Systemen und vier
  Landmarks weiter unten. Jetzt eine chronologische Reihe von acht.
  Die Landmark-Ueberschriften sind auf das Schema der Episoden
  umgestellt (Datum zuerst, dann Stichwort).
- **Alle Tags beibehalten**, auch `landmarks` und `other-provers`,
  obwohl die Abschnitte Ebene und Namen wechseln -- sonst brechen
  Verweise. Geprueft: 31 Anker genau einmal, alle 13 `{ref ...}`
  aufloesbar.
  **Pruef-Falle:** Kapitel-Tags (`introduction`, `projects`,
  `slides`) stehen nur in `html-single` als `id=`; in `html-multi`
  heissen sie `--verso-manual-toc-...`. Der Anker-Check muss gegen
  `_out/html-single/index.html` laufen, sonst meldet er falsche
  Treffer. Skript im Scratchpad.
- **Zwei neue Scharniersaetze:** der Lean-Abschnitt endet auf
  "Where development sits now is Current state of Lean, after the
  record", und `## What came of it` beginnt mit der Einordnung der
  acht ("the first two are about proofs too large to read; the next
  two about proofs nobody had checked; the last four about what a
  library makes possible").

**Deck 32 -> 33**, gleiche Reihenfolge wie das Kapitel. Neu `The
systems` mit der Linien-Grafik (`height := "62vh"`; 46vh war zu
klein, das Bild ist 10x5.6 und damit breitenbegrenzt). `Sphere
packing, dim. 8 and 24` steht im Deck weiterhin am Ende der Chronik,
obwohl das Kapitel es nur oben bei 2026 fuehrt. Hoechste Folie
unveraendert `2013: Voevodsky` mit 557 px, alle 33 mit Notizen.

## 2026-10-15 -- Bildrechte: MIT reicht nicht, Commelin hat zugestimmt

Frage war, ob die Portraits auf
`leanprover-community.github.io/lean3/teams/maintainers.html` frei sind,
weil das Repository eine Lizenz hat.

- Das Repo `leanprover-community/leanprover-community.github.io` steht
  unter **MIT**. Ueber GitHubs inbound=outbound greift das auch fuer
  Beitraege. Zwei Luecken: MIT spricht von "Software and associated
  documentation files" -- ein Portraitfoto ist weder das eine noch das
  andere; und lizenzieren kann nur, wer die Rechte hat. Commit-Historie:
  `img/ocfnash.png` hat Oliver Nash selbst eingestellt (2021-11-01),
  `img/patrick.png` **und** `img/Johan.jpg` hat Patrick Massot in einem
  Sammel-Commit hochgeladen (2020-05-02). Fuer Commelins Bild ist also
  nicht einmal der Fotograf bekannt.
- **Entscheidend ist aber das Recht am eigenen Bild** (§ 22 KunstUrhG,
  dazu DSGVO). Das gehoert der abgebildeten Person, nicht dem Fotografen,
  und keine Urheberrechtslizenz kann es mitlizenzieren. Eine Einwilligung
  ist ausserdem kontextgebunden: Maintainer-Liste ist nicht Vorlesung.
  § 23 KunstUrhG greift nicht (keine Personen der Zeitgeschichte),
  § 60a UrhG auch nicht (verlangt abgegrenzten Teilnehmerkreis, das
  Repository ist oeffentlich). Bei Wikimedia Commons traegt die Kette,
  weil dort die Einwilligung Teil der Upload-Bedingungen ist.
- Praktisch erledigt es sich ohnehin: die drei Bilder sind **100x100**.
  Kleinstes hier verwendetes Foto ist `godel.jpg` mit 212x270, die
  Platzhalter sind 390x390.
- **Stand:** Mails an Massot, Commelin und Nash sind raus. Commelin hat
  zugestimmt. Das Foto liegt noch nicht im Repository, die vier
  Fundstellen (`00-Introduction.lean:380,394`,
  `Slides/Introduction.lean:852,892`) zeigen weiter den Platzhalter.
  Status in `static/figures/portraits/CREDITS.md` unter `## Permissions`.

## 2026-10-15 (2) -- Commelin und Massot eingebaut, zwei tote Verweise repariert

Beide haben zugestimmt, die Platzhalter sind weg.

- `static/figures/portraits/commelin.jpg` -- 600x600, von
  <https://mathlib-initiative.org/team/>, Studio-Headshot, keine EXIF,
  unveraendert uebernommen.
- `static/figures/portraits/massot.jpg` -- 400x340, von seiner Homepage
  <https://www.imo.universite-paris-saclay.fr/~patrick.massot/en/>. EXIF
  entfernt (stand Pentax K-70, GIMP, Aufnahmedatum drin; kein GPS).
  Querformat, aber `img.portrait` schneidet mit `object-fit: cover` auf
  einen Kreis von 16vh, deshalb unkritisch -- im Screenshot sitzt das
  Gesicht mittig.
- Acht Fundstellen umgestellt (4 im Kapitel, 4 im Deck),
  `placeholder_commelin.png` und `placeholder_massot.png` geloescht und
  die beiden Namen aus `PEOPLE` in
  `scripts/figures/portrait_placeholders.py` genommen, sonst erzeugt der
  naechste Lauf sie wieder. Es bleiben fuenf Platzhalter: Gonthier,
  van Doorn, Nash, Manners, Church.
- **Oliver Nash fehlt noch.** Sein Foto liegt auf derselben
  Mathlib-Initiative-Seite (`static/team/oliver.jpg`) -- nicht nehmen,
  bevor er antwortet. Vermerk steht in `CREDITS.md`.
- Im Schlussabsatz der Picture credits sind Commelin und Massot aus der
  Silhouetten-Liste raus. Der Satz heisst jetzt "The set is therefore
  still weighted toward who is *famous* rather than who did this work"
  (vorher "a fair sample of who is famous") und endet auf "Where a
  photograph exists but carries no licence, the remedy is to write and
  ask."

**Zwei tote Verweise aus `3c6c6c9`/`8f053af` gefunden und repariert**, die
beim Rendern als `No destination found` auftauchten:

- `{ref "itp-repos"}` -- **Figure-Tags sind in Verso keine Linkziele.**
  `{ref ...}` sucht nur in `Verso.Genre.Manual.section`. Das `id=` steht
  zwar im HTML, deshalb hat der grep-basierte Anker-Check von gestern das
  nicht gesehen. Jetzt `{ref "field-stands"}[the first figure]`, also auf
  den Abschnitt statt auf die Abbildung. Betraf den einzigen Verweis auf
  eine Abbildung im ganzen Manuskript.
- `{ref "other-provers"}[Other theorem provers]` -- der Abschnitt heisst
  seit dem Umbau `The three systems today`, der Linktext war
  stehengeblieben. Angepasst.

**Lehre:** der Anker-Check muss die Render-Ausgabe von
`lake exe leancourse` auf `No destination found` pruefen, nicht nur
`id=`-Vorkommen zaehlen.

Gemessen: 33 Folien, keine ueber 700 px (hoechste `2013: Voevodsky`),
alle mit Notizen.

## 2026-10-15 (3) -- Nash eingebaut, alle drei Anfragen beantwortet

- `static/figures/portraits/nash.jpg` -- 600x600, von
  <https://mathlib-initiative.org/static/team/oliver.jpg>, unveraendert
  uebernommen. EXIF enthaelt nur Aufloesung und Orientierung, nichts
  Personenbezogenes, kein GPS -- deshalb nicht neu kodiert, anders als
  bei Massot. Vor dem Herunterladen im Seitenquelltext geprueft, dass
  `oliver.jpg` wirklich zu Oliver Nash gehoert und nicht zu einem
  anderen Oliver.
- Zwei Fundstellen (`00-Introduction.lean:410`,
  `Slides/Introduction.lean:938`), `placeholder_nash.png` geloescht,
  `nash` aus `PEOPLE` genommen. Es bleiben vier Platzhalter: Gonthier,
  van Doorn, Manners, Church.
- Satz im Kapitel angepasst: van Doorn steht jetzt als
  "who formalized sphere eversion with Massot and Nash" in der
  Silhouetten-Liste, und der Schluss heisst "Johan Commelin, Patrick
  Massot and Oliver Nash were asked, and all three agreed."

**Offen: Floris van Doorn.** Auf der Folie `Sphere eversion, 2022`
stehen jetzt zwei echte Gesichter und eine Silhouette dazwischen, das
faellt auf. Er wurde nie gefragt. Drei von drei Anfragen waren
erfolgreich, eine vierte waere naheliegend.

Gemessen: 33 Folien, keine ueber 700 px, alle mit Notizen.

## 2026-10-15 (4) -- neues Buzzard-Foto, Auflage: fester Credit

Aus `~/Downloads/840x560.webp`, WebP nach JPEG konvertiert (Qualitaet 92),
840x560, keine EXIF. Ersetzt das bisherige `buzzard.jpg`, den
Wikimedia-Kopfschuss von George Bergman aus **1996** -- frei, aber
dreissig Jahre alt.

**Die Bedingung ist ein wortgenauer Credit:**
`Thomas Angus, Imperial College London`.
Das Urheberrecht liegt beim Imperial College, nicht beim Fotografen und
nicht bei Buzzard. Anders als bei Commelin, Massot und Nash ist das keine
Einwilligung der abgebildeten Person, sondern die Erlaubnis des
Rechteinhabers unter Auflage. **Der Credit darf nicht umformuliert oder
weggelassen werden** -- Vermerk steht fett in `CREDITS.md`.

- Im Kapitel ist Buzzard aus der Commons-Liste in die Permission-Gruppe
  gewandert, Einleitungssatz von "The last three are used with the
  permission of the person shown" auf "The last four are used by
  permission, each with the credit its owner asks for".
- Der Kopfsatz von `CREDITS.md` behauptete noch "All images are from
  Wikimedia Commons" -- stimmte seit heute Vormittag nicht mehr,
  korrigiert.
- Querformat, aber `object-fit: cover` schneidet auf den Kreis; Gesicht
  sitzt leicht links der Mitte, im Screenshot unauffaellig.

**Noch offen:** der Credit steht nur im Kapitel. Der Satz dort sagt zwar
"here and in the {ref "slides"}[slide decks]", aber wer nur das Deck
oeffnet, sieht ihn nicht. Kein Deck hat eine Credits-Folie. Falls die
Decks je einzeln weitergegeben werden, muss das nachgezogen werden.

Gemessen: 33 Folien, keine ueber 700 px, alle mit Notizen.

## 2026-10-15 (5) -- Buzzard nachgeschnitten, van Doorn eingebaut

- **Buzzard neu beschnitten.** Das Gesicht sass links der Kreismitte.
  `object-position` ist eine globale Regel fuer alle Portraits, also
  nicht pro Bild einstellbar -- deshalb stattdessen die Quelle
  beschnitten: aus dem Original-WebP das Quadrat `left=70` statt der
  zentrierten `left=140`, Ergebnis 560x560. Neu aus dem WebP gerechnet,
  nicht aus dem schon konvertierten JPEG, damit es bei einer
  Verlustgeneration bleibt. Credit-Auflage unveraendert:
  `Thomas Angus, Imperial College London`.
- **`vandoorn.jpg`** -- aus `~/Downloads/Floris.jpg` (1666x2500, Canon
  EOS 7D, Lightroom, 2019). Quadrat `side=1500 left=0 top=150`, skaliert
  auf 600x600 wie Commelin und Nash, EXIF dabei weggefallen. Engerer
  Schnitt (1400/200) war oben zu knapp am Haar.
  **Fotograf ungeklaert:** im EXIF-Feld `Artist` stand
  `@dick van- doorn`, vermutlich ein Familienmitglied. Falls ein
  Fotografen-Credit gewuenscht ist, muss er erfragt und in `CREDITS.md`
  ergaenzt werden. Vermerk steht dort.
- Letzter Platzhalter-Abgang: es bleiben **drei** -- Gonthier, Manners,
  Church. Schlussabsatz der Picture credits umgeschrieben, weil die
  alte Pointe ("the set is weighted toward who is famous") nach vier
  Zusagen nicht mehr trug. Jetzt: "Which photographs are freely licensed
  tracks who is *famous*, not who did this work. Where one was missing,
  the remedy was to write and ask."

**Alchetron ist keine Quelle.** Geprueft fuer Gonthier
(<https://alchetron.com/Georges-Gonthier>): der CC-BY-SA-Hinweis dort
lautet woertlich "Georges Gonthier Wikipedia (Text) CC BY-SA" -- er
bezieht sich auf den von Wikipedia uebernommenen **Text**, nicht auf die
Bilder. Zu den beiden Fotos gibt es keinen Fotografen, keine Quelle,
keine eigene Lizenz. Commons hat kein Foto von ihm, der
Wikipedia-Artikel enthaelt nur Icons. Also nicht verwendbar.

Gemessen: 33 Folien, keine ueber 700 px, alle mit Notizen.

## 2026-10-16 -- Hales-Gastbeitrag eingearbeitet

Quelle: Thomas Hales, *What Mathematicians Should Know About the Lean
Theorem Prover: Questions of Reliability and AI*, Gastbeitrag in Terence
Taos Blog, 9.10.2026. **Nicht von Tao** -- Hales ist bei uns ohnehin
schon ein Portrait (Kepler/Flyspeck), das Kapitel kann ihn also direkt
zitieren. Als `hales2026` in `References.lean` eingetragen, zusammen mit
`werner1997` (*Sets in Types, Types in Sets*, TACS 1997, LNCS 1281);
beide in `99-Bibliography.lean` gelistet.

- **Korrektur, keine Ergaenzung.** `01-Lean/02-Types.lean` behauptete,
  Carneiro habe Lean relativ zu ZFC + *n* Unerreichbaren als konsistent
  bewiesen, "the assumption is optimal". Hales: in der Thesis wurde ein
  **Fehler gefunden**, *unique typing* und *Pi-Injektivitaet* sind
  unbewiesen, und es gibt (Stand Oktober 2026) **keinen vollstaendigen
  oeffentlichen Relativkonsistenzbeweis** fuer Leans Typtheorie. Neu
  formuliert plus die beiden Teilresultate, die es gibt: Werner 1997 und
  Breitners *Con-Leche*.
- `03-Mathematics/00b-UniversesAndAxioms.lean`: "Both foundations are
  equiconsistent for most of mathematics" ersetzt. Werner 1997 sagt
  etwas ueber CIC, nicht ueber Lean -- der Unterschied steht jetzt da.
- **Neuer Abschnitt `### 2026: the summer of soundness bugs`** am Ende
  von *What came of it*, mit einer Klappbox `:::example "Bugs in Lean"`
  (siehe oben, `:::example` ist die Projekt-Klappbox). Darin die drei
  geschlossenen Issues, **gegen die GitHub-API geprueft**:
  [#14484](https://github.com/leanprover/lean4/issues/14484) (22.07.),
  [#14576](https://github.com/leanprover/lean4/issues/14576) (28.07.,
  `False` **ohne jedes Axiom**),
  [#14875](https://github.com/leanprover/lean4/issues/14875) (21.08.).
  Die Liste ist bewusst offen angelegt -- neue Bugs kommen dort hinein.
- **Zwei Stellen, die der Bug-Abschnitt relativiert**, beide mit
  `{ref "soundness-bugs"}` verknuepft: "the program that checks it is
  small and fixed" (Zeile ~30) und die FLT-Zeile "machine-checkable, by
  `#print axioms`" -- `#print axioms` sieht Axiome, nicht den Kernel.
- Ergaenzt: Flyspeck-Kosten (ca. 20 Personenjahre, 500 000 Zeilen) in
  der Kepler-Episode; Autoformalisierungs-Meilensteine Sep 2025 (PNT,
  Math Inc.), Maerz 2026 (Kugelpackung Dim. 24, 500k -> 200k Zeilen),
  Mai 2026 (Meta *ATLAS*, 26 Lehrbuecher) und Januar 2026 (Urban, 130k
  Zeilen Topologie, nicht in Lean) in *Why formalize?*.

**Nicht uebernommen:** Thompsons *Reflections on Trusting Trust*, von
Hales auf KI-gefundene Bugs angewandt -- der KI-Faden ist im Kapitel
schon dicht. Unsere Mathlib-Zahlen sind genauer als seine und bleiben.

`{citep ...}[]` rendert als `(Autor, Jahr)`, `{citet ...}[]` als
`Autor (Jahr)`. In Klammern also **citep ohne eigene Klammern**, sonst
steht dort `((Hales (2026)))`.

## 2026-10-18 -- Con-Leche richtiggestellt

Erste Fassung (16.10.) nannte Con-Leche "a Lean kernel written in Lean
whose consistency is proved in Lean, relative to ZF with a hierarchy of
inaccessible cardinals" und stellte es als Teilersatz fuer den fehlenden
Relativkonsistenzbeweis hin. **Beides falsch.** Geprueft an der
README von <https://github.com/leanprover/con-leche>:

- Es ist **kein Kernel**, sondern ein **externer Checker**, der Leans
  Export-Dateien noch einmal liest. Name = *café con leche* =
  **CON**sistent **LE**an **CHE**cker. Rust-Portierung: `con-ron`.
- Bewiesen wird: der Checker akzeptiert nie einen `False`-Beweis; jede
  akzeptierte Umgebung hat ein Modell. Annahmen: ZF **ohne** Unendlichkeit
  und Auswahl, dazu eine ω-Kette von Grothendieck-Universen, instanziiert
  auf Mathlibs `ZFSet` unter ω vielen Unerreichbaren. `Nat`-Arithmetik
  wird der Lean-Runtime geglaubt.
- **Der entscheidende Punkt:** der Beweis laeuft **innerhalb von
  Carneiros Rahmen** -- genau dem, dessen Luecke zwei Saetze vorher
  beschrieben wird. Con-Leche zeigt, dass der Checker dem Modell treu
  ist, nicht dass es das Modell gibt. Es schliesst die Luecke nicht, es
  setzt sie voraus.
- Implementiert und bewiesen von Claude (Fable und Opus) unter Aufsicht
  von Joachim Breitner (Lean FRO). ~0,69x der Instruktionen des
  offiziellen Kernels auf Mathlib, also schneller.

Korrigiert in `01-Lean/02-Types.lean`, in der Bug-Box in
`00-Introduction.lean` und in `Slides/Introduction-SpeakerNotes.md`.

**Lehre:** Hales' Blogpost ist eine Sekundaerquelle. Seine
Zusammenfassung ("a verified Lean kernel") ist knapp genug, um in die
Irre zu fuehren. Bei technischen Aussagen aus dem Post die
Primaerquelle nachschlagen, bevor sie ins Skript wandern.

## Neu: `Slides/Introduction-SpeakerNotes.md` (18.10.2026)

Ausfuehrliche Vortragsnotizen zum ersten Deck, auf Wunsch des Autors:
33 Abschnitte, Ueberschriften **wortgleich mit den Folientiteln** und in
Deck-Reihenfolge. Pruefung:

```
diff <(grep "^# " Slides/Introduction.lean | sed 's/^# //') \
     <(grep "^## " Slides/Introduction-SpeakerNotes.md | sed 's/^## [0-9]*\. //')
```

Format: Stichworte, keine Prosa. Material, das **nicht** im Skript
steht, ist mit `**[Hintergrund]**` markiert. Am Ende zwei Zusatzteile:
Stichworte fuer die noch nicht existierende Bug-Folie (Einschub nach
Folie 27), und zwei Stellen, an denen die Notizen das Skript ueberholen
(Commelin **leitet** die Mathlib Initiative; seine Freiburger
Postdoc-Zeit bei Kebekus fehlt im Skript ganz).

Beim Aendern des Decks **beide Dateien nachziehen** -- der `diff` oben
ist der Test.

## 2026-10-18 (2) -- Decks ohne Fragmente: eine Taste, eine Folie

Wunsch des Autors: "jede Folie gleich komplett aufgebaut, sonst muss ich
zu oft clicken, und ich will mich aufs Sprechen konzentrieren."

**Alle `:::fragment` entfernt**, in beiden Decks: 66 in
`Slides/Introduction.lean`, 7 in `Slides/Filters.lean`. Im gerenderten
HTML **0 Vorkommen von `class="...fragment..."`** -- das ist der Test,
nicht die Quelle.

**Warum nicht per CSS.** Naheliegend waere, die Fragmente per
`.reveal .fragment { opacity: 1 !important }` sichtbar zu schalten.
**Das loest das Problem nicht:** reveal.js zaehlt die Fragmente
weiterhin als Navigationsschritte, die Pfeiltaste muesste also immer
noch N-mal gedrueckt werden, nur ohne sichtbare Wirkung -- schlimmer als
vorher. Die Markup muss wirklich raus.

**Die Pointe bleibt blau.** Die Decks haben dafuer schon die Klasse
`.key` (`#1b91ff`); die Fragmente lagen nur als Huelle darum. Beim
Entfalten bleibt `:::class "key"` stehen, es braucht also keine neue
Klasse. Selektoren sind wie bei `.caption`/`.names` doppelt geschrieben
(`p.key` **und** `.key p`), weil `:::class` die Klasse je nach Kontext
auf das Element oder einen Wrapper legt.

**Hoehen unveraendert.** War zu erwarten -- reveal versteckt Fragmente
mit `visibility:hidden`, das behaelt den Platz --, aber gemessen:
33 Folien, keine ueber 700 px, hoechste weiterhin `2013: Voevodsky`
mit 643 px. Messskript siehe 2026-10-14.

Umbauskript liegt im Scratchpad (`defragment.py`). Falls je wieder
Fragmente gewuenscht sind: das ist von Hand nachzuziehen, die 73
entfalteten Bloecke kommen nicht per `sed` zurueck.

`Slides/Introduction-SpeakerNotes.md` nachgezogen: Hinweis "one key
press is one slide" im Kopf, die beiden Stellen, die "fragment" als
Folienmechanik nannten, umformuliert.

## 2026-10-18 (3) -- `vh` in Folien, Gedankenstriche, Frege

### Bildhoehen nie in `vh`

Folie 6 (*Papers checked in Lean*) schnitt beim Autor die unterste Zeile
ab, auf meinem Testfenster aber nicht. **Ursache:** reveal.js skaliert
die Folie mit einem CSS-`transform`; `vh` wird dagegen gegen das
*Browserfenster* gemessen und von dieser Skalierung nicht erfasst. Eine
`40vh` hohe Grafik ist deshalb relativ zur Folie unterschiedlich gross,
je nach Seitenverhaeltnis des Beamers -- bei breitenbegrenzten Fenstern
(4:3, 5:4) deutlich groesser. `px`, `rem` und `em` skalieren mit, `vh`
und `vw` nicht.

**Regel: Bildgroessen in Folien-Pixeln, nicht in `vh`.** Alle fuenf
Bilder im Deck umgestellt, `(height := ...)` aus der Markup entfernt,
Groessen im CSS-Block: `.chart` 280px, `.chart-arxiv` 240px,
`.lineage` 336px, `.inlinepic` 140px, `.kepler` 154px. Geprueft bei
1280x720, 1280x1024 und 1024x768: identisches Layout. **Kein `vh` mehr
im Deck** -- das ist der Test (`grep 'vh"' Slides/*.lean`).

### `--` durch `—` ersetzt

Verso macht **keine** Smart-Dash-Ersetzung; `--` erschien woertlich als
zwei Bindestriche. 467 Vorkommen in Prosa auf `—` umgestellt, in
`Leancourse/Coursenotes/**` und `Slides/*.lean`.

**Die Gefahr ist `--` als Lean-Kommentar.** Das Skript
(`emdash.py`, im Scratchpad) ersetzt deshalb nur
- **innerhalb der `#doc`-Region** (alles vor `#doc (Manual|Slides)`
  bleibt unberuehrt -- das rettet `/--`-Docstrings in `References.lean`
  und den Kommentar in `03-Terms.lean:5`), und
- **ausserhalb von ```-Codebloecken**.

Gegenprobe nach dem Lauf: `--` in Codebloecken **445, unveraendert**;
in Prosa von 469 auf 2 (genau die beiden Lean-Zeilen oben). Im
gerenderten Kapitel sind die verbliebenen `--` ausschliesslich Versos
eigene CSS-Variablen (`--verso-*`).

Nebenwirkung: `—` ist breiter als `--`, einzelne Folien wachsen leicht
(*Voevodsky* 643 -> 666 px). Weiterhin keine ueber 700.

### Frege: *Begriffsschrift* oder *Grundgesetze*?

Nutzerfrage, und die Notizen waren tatsaechlich uneinheitlich. **Beides,
aber fuer Verschiedenes:**

- ***Begriffsschrift*, 1879** -- die Notation, das erste System, in dem
  ein Beweis selbst ein manipulierbares Objekt ist. **Reine Logik, keine
  Extensionen, von der Paradoxie nicht betroffen.**
- ***Grundgesetze der Arithmetik*, Bd. I 1893, Bd. II 1903** -- die
  Ableitung der Arithmetik aus dieser Logik, mit *einem* Zusatzaxiom
  (Grundgesetz V: Begriffe mit denselben Instanzen haben dieselbe
  Extension). **Das ist, was Russells Brief vom Juni 1902 zerstoert**,
  waehrend Band II im Druck war.

Falsch war die Deck-Notiz "Frege's *Begriffsschrift*, 1879 ... Russell's
letter of 1902 breaks **it**". Vage waren `00-Introduction.lean:101`
("Frege's system") und `02-Types.lean:33` ("Gottlob Frege's system").
Alle drei nennen jetzt die *Grundgesetze* und das Zusatzaxiom; die
Vortragsnotizen haben einen eigenen Unterpunkt "Say which book, the two
get confused".

### Peano von Folie 8 nach `01-Nat.lean`

Nutzerfrage "Was sucht eigentlich Peano auf Folie 8?" -- berechtigt,
gleich doppelt: der Titel nannte drei Namen, die Folie zeigte zwei
Gesichter (ein `peano.jpg` gab es nie), und inhaltlich war seine Zeile
die einzige, die nicht zum Bogen *Frege baut / Russell bricht /
Principia baut neu* gehoerte. Gewaehlt wurde: **ganz streichen und dort
bringen, wo `Nat` eingefuehrt wird.**

- Folie: `# Frege, Peano, Russell` -> `# Frege and Russell`, die
  1889er-Zeile entfernt. 511 px statt 616.
- Kapitel: `### 1879 to 1913: Frege, Peano, Russell` ->
  `### 1879 to 1913: Frege and Russell`, der Peano-Satz samt
  `{ref "nat"}` aus dem Absatz raus. **Mitgezogen, weil das Deck laut
  seinem eigenen Kopfkommentar dem Kapitel Abschnitt fuer Abschnitt
  folgt** -- nur die Folie zu aendern haette beide auseinanderlaufen
  lassen.
- `01-Lean/01-Nat.lean`, Abschnitt `nat-intro`, direkt nach den beiden
  Konstruktoren: Peano 1889, Dedekind 1888, und der Punkt, dass
  Induktion kein dritter Konstruktor ist, sondern der Rekursor des
  naechsten Absatzes. "What was a list of axioms in 1889 is a type
  declaration here."
- In den Vortragsnotizen steht jetzt ausdruecklich **"Peano's axioms are
  deliberately not on this slide"** mit den Fakten fuer den Fall, dass
  jemand fragt -- damit die Streichung nicht als Luecke wirkt.
- Peanos lineare Notation bleibt als Nebensatz in der Frege-Notiz: dort
  erklaert sie, warum Freges zweidimensionale Schrift unterging.

**Beim Umbenennen einer Folie immer den Titel-Abgleich laufen lassen**
(siehe 2026-10-18, Eintrag zu den Vortragsnotizen) -- die Ueberschriften
in `Introduction-SpeakerNotes.md` muessen wortgleich bleiben. Nach
dieser Aenderung wieder 33/33 identisch.

Gemessen nach allen Aenderungen des Tages: 33 Folien, keine ueber
700 px, hoechste `2013: Voevodsky` mit 666 px.

### Folie 9 mathematisch statt abgekuerzt; Folie 10 mit Jahreszahl

**Folie 9, vierte Spalte** war "the stratification is: the cumulative
hierarchy, a *theorem*" gegen "the type hierarchy, a *rule*" -- vom Autor
als unverstaendlich gemeldet, zu Recht: die Pointe ohne das Argument.
**Das Kapitel hatte die mathematische Fassung die ganze Zeit** (Absatz
nach der Tabelle in `00-Introduction.lean`), nur die Folie nicht. Jetzt
nachgezogen:

- Spalte 4 heisst *you may form*: Zermelo
  $`\{x \in A : x \notin x\}`, **never** $`\{x : x \notin x\}`;
  Russell "neither: $`x \notin x` is not a formula".
- Darunter zwei Zeilen mit der Herleitung: $`R = \{x \in A : x \notin x\}`,
  $`R \in R` gdw. $`R \in A` und $`R \notin R`, also $`R \notin R`, also
  $`R \notin A`. **Der Widerspruch wird zum Satz: es gibt keine Menge
  aller Mengen.** 552 px, passt.
- Die Unterscheidung Hierarchie-als-Satz / Hierarchie-als-Regel steht
  weiterhin in den Notizen, nur nicht mehr in der Tabelle.
- **Kapitel-Tabelle bewusst unveraendert gelassen** -- dort ist die
  vierte Spalte ausgeschrieben ($`V_0 \subseteq V_1 \subseteq \dots`)
  und der Absatz darunter liefert dieselbe Rechnung. Die beiden Tabellen
  unterscheiden sich jetzt in dieser einen Spalte, Medium gegen Medium.

**Vortragsnotizen zu Folie 9** um einen eigenen Block erweitert
(*"Russell overshot, and it cost him analysis"*): Vicious-Circle-Prinzip
als die eigentliche, viel weitere Einschraenkung; das Supremum
ausgeschrieben (Klausel (ii) quantifiziert ueber alle Reellen, `sup S`
landet eine Ordnung hoeher, die Supremumseigenschaft faellt *innerhalb*
jeder Ordnung, Analysis steht); Reduzibilitaetsaxiom als Rueckkauf ohne
Begruendung; dazu Russells eigenes Eingestaendnis 1925, Weyls
*Das Kontinuum* 1918 und Ramseys Trennung logischer und semantischer
Antinomien. Abschluss ist Leans asymmetrische Loesung (imprädikativ in
`Prop`, nicht fuer Daten).

**Folie 10** heisst jetzt `Hilbert's programme, 1917` -- Jahreszahl wie
im Kapitel (`### 1917 to 1931`) und nach dem Muster der Nachbarfolien
(*Two repairs, 1908*, *Gödel, 1929 and 1931*). In den Notizen steht
dazu, dass 1917 der Startschuss ist (*Axiomatisches Denken*) und die
scharfe Fassung der drei Fragen Hilbert/Ackermann 1928 ist.

## 2026-10-19 -- Decks fuer Kapitel 1, Bool-Blatt

- **Sieben neue Decks**, eins pro Unterkapitel von *Lean and its type
  theory*: `Slides/{Nat,Types,Terms,Typeclasses,CurryHoward,
  DependentTypes,Notation}.lean`, Verzeichnisse `slides/{nat,types,
  terms,typeclasses,curry-howard,dependent-types,notation}/`. 12-19
  Folien, **noch ohne Sprechernotizen** (kommen spaeter). Verlinkt aus
  jedem Kapitel (Satz direkt vor dem ersten `#`) und aus `06-Slides`.
- **Namenskollisionen:** alle Decks landen in *einer* Binary. Jedes Deck
  hat deshalb `namespace Slides<Name>` direkt vor `#doc` (geprueft:
  wirkt auf die Lean-Bloecke). Notation im Notation-Deck ist `local`
  bzw. `scoped`.
- **VersoSlides-Tabellen:** `+header` gibt es nicht ("Unexpected
  argument"), richtig ist `+colHeaders`. Leere Zellen parsen nicht.
- **Link-Falle:** jede Manual-Seite hat `<base href="./../">`, relative
  Links gehen also vom Site-Root aus. Richtig ist `slides/<deck>/`.
  Der Filter-Kapitel-Link `../slides/filters/` war live ein 404,
  korrigiert.
- Folienhoehen gemessen, Maximum 664 px (*Defining and evaluating
  functions*, Terms-Deck).
- Das Kapitel `01-Nat.lean` heisst im `#doc` noch `"Introduction"`, nicht
  "The natural numbers and reduction rules" wie oben behauptet. Das Deck
  traegt den langen Titel.
- Neues Blatt `Exercises/02-Numbers/02-00-Bool.lean` (16 Aufgaben,
  Zeuge in `Checks/`), Woche 5 in `plan.md`.

## 2026-10-22 -- Zwei Branches: preparation und main

- **`preparation` traegt immer den vollen Text**, in beiden Repos
  (`leancourse` und `leancourse_exercises`). Dort wird gearbeitet.
- **`main` ist die Veroeffentlichung** und baut die GitHub-Pages-Seite
  (`deploy.yml` haengt an `main`). Dort steht nur, was drankam:
  Introduction, 1.1 Nat, 1.2 Types, Appendix, Bibliographie, Slides
  vollstaendig; **1.3 bis 2.9 und die Projekte nur als
  Ueberschriftenbaum**, Text ersetzt durch einen Platzhalter.
- **Warum Ueberschriften bleiben:** alle 250 `{ref}`-Ziele sind
  Ueberschriften-Tags. Die einzigen Tags im Fliesstext sind die 15
  Abbildungen, und die liegen alle in der Introduction, die nie
  gestrippt wird. Deshalb kann das Strippen keinen Link brechen --
  gemessen und gebaut, `lake exe leancourse` meldet null
  `No destination found`.
- **Freigeben:** auf `preparation` arbeiten, dann
  `git checkout main && git merge preparation`, Datei aus
  `WITHHELD` in `scripts/strip_unreleased.py` streichen,
  `python3 scripts/strip_unreleased.py`, committen, pushen.
  Nie `main` nach `preparation` mergen -- das traegt die gestrippten
  Dateien zurueck.
- **Uebungen:** `main` hat momentan nur `Exercises/01-Logic`.
  `scripts/export_exercises.sh` rsynct mit `--delete` und weigert
  sich jetzt, wenn das Zielrepo nicht auf `preparation` steht.
  Freigeben mit `git checkout preparation -- Exercises/<Kapitel>`.

## 2026-10-22 -- 02-Numbers neu nummeriert, Blatt zum Rekursor

- Reihenfolge jetzt (wie in der Vorlesung: erst Nat, dann Bool):
  `02-a-NatRec` (*neu*), `02-b-Bool`, `02-c-Naturals`,
  `02-d-Induction`, `02-e-Limits` (vorher `02-00-Bool`,
  `02-a-Naturals`, `02-b-Induction`, `02-c-Limits`). `git mv` in `Exercises/` und `Checks/`; `plan.md` und
  `Checks/README.md` nachgezogen.
- `02-a-NatRec` (13 Aufgaben, Zeuge in `Checks/`): Funktionen nur ueber
  `Nat.rec`, Beweise nur mit `rfl`, `show`, `induction`, `rw [ih]`,
  keine Mathlib-Lemmata. Deshalb steht es vor `02-c`, das Mathlib-Saetze
  benutzt. `myDouble` und `myAdd` sind vorgegeben (das vorgerechnete
  `myAdd_zero_left` braucht `myAdd`); `myPred`, `myMul`, `myFact`,
  `myEven` definieren die Studierenden.
- Das Export-Repo `leancourse_exercises` hat noch die alten Namen;
  beim naechsten Export spiegelt `--delete` die Umbenennung.
- `02-b-Bool` hat jetzt einen Teil "`True` and `False` as types"
  (Aufgaben 17-22): `False.rec` per Hand, `exfalso`/`False.elim`/
  `cases h` (null Ziele), `cases` auf `True`, `true = false` und
  `0 = 1` per `cases`, `Empty.elim`.
- Glossar `Tactics/Exfalso.lean`: falsche Bemerkung entfernt, `exfalso`
  verlasse die konstruktive Mathematik (ex falso ist intuitionistisch
  gueltig); `false` → `False`.

## 2026-10-23 -- Einstellige Praefixe, 1.2-a, fuenf fehlende Taktiken

- **Alle zweistelligen Praefixe sind einstellig.** 86 `git mv` in
  `Coursenotes/`, `Exercises/`, `Checks/`: `01-Lean` -> `1-Lean`,
  `02-Mathematics/09-Probability` -> `2-Mathematics/9-Probability`,
  `99-Extra` -> `9-Extra`, `99-Bibliography` -> `9-Bibliography`.
  Danach Textersatz ueber alle Namenskomponenten in `Leancourse/`,
  `Slides/`, `scripts/`, `Leancourse.lean`, `plan.md`, `README.md`.
  **Nicht angefasst:** `old/`, `Exercises/MyExercises/`,
  `Leancourse/Misc/` (tote bzw. private Baeume mit eigenem Schema),
  und die datierten Log-Eintraege hier -- die beschreiben den Stand
  von damals.
- **`1.5-a-Quantifiers` heisst jetzt `1.2-a-Quantifiers`.** Es lief in
  Woche 3 und damit drei Wochen vor seinem Kapitel, was der Regel
  "die Nummer gibt die Reihenfolge" widersprach. Kapitel 1.2 benutzt
  `∀` 29-mal und `∃` achtmal, mehr als jedes andere Kapitel des
  ersten Teils, also gehoert das Blatt dorthin. Die Luecke wurde
  geschlossen: `1.5-b-Predicates` -> `1.5-a`, `1.5-c-CurryHoward` ->
  `1.5-b`. Damit laeuft **kein** Blatt mehr vor seinem Kapitel.
- **`scripts/strip_unreleased.py` war seit dem Umbau vom 22.10. kaputt:**
  die `WITHHELD`-Liste zeigte noch auf `03-Mathematics/00-SetsAndTypes`
  usw. Ein Release haette die neun Mathematik-Kapitel und die fuenf
  Projekte **unbemerkt ungestrippt** nach `main` gelassen. Liste
  korrigiert, `--check` laeuft ueber alle 19 Dateien.
- **Fuenf Taktiken waren nirgends eingefuehrt**, obwohl jede eine
  Anhangseite hat: `contrapose` (jetzt `L-e`), `simp_all` (`L-g`),
  `congr`/`convert` (`A-a`, Teil D), `filter_upwards` (`2.6-b`,
  Teil 3), `fun_prop` (`2.7-a` Teil 1, Hinweis auf `2.8-a`).
  Jeweils Tabellenzeile bzw. Absatz, ein vorgerechnetes Beispiel und
  eine Aufgabe; Aufgabennummern nachgezogen.
- `simp_rw` wurde auf `2.1-c` benutzt, ohne benannt zu werden.
- Audit: `audit2.py` (benutzt eine Taktik etwas, das bis zu dieser
  Woche nirgends erklaert wurde?) meldet jetzt fuer alle 33 Blaetter
  nichts. `audit5.py` haelt die Anhangseiten gegen die Blaetter.
  Beide im Scratchpad, Quelle der Wahrheit ist `sheets.py`.
- Stand: 33 Blaetter ohne Fehler, 25 Zeugen ohne `sorry` (ausser dem
  einen gewollten auf `L-a`), `lake build Leancourse`, `lake build
  slides` und `lake exe leancourse` sauber, null tote Verweise.

## 2026-10-23 (2) -- Alle Zeugen, zwei Blaetter neu, Folien geprueft

- **Die acht fehlenden Zeugen sind geschrieben**: `A-a` (39), `2.4-a`
  (37), `2.5-a` (28), `2.6-b` (46 inkl. der 15 Strukturfelder),
  `2.7-a` (25), `2.8-a` (22), `2.9-a` (24), `2.9-b` (28). Damit
  **33 von 33 Blaettern** einen Zeugen, alle `sorry`-frei bis auf das
  eine gewollte auf `L-a`.
- Dabei gefunden: `PMF.bernoulli` ist deprecated (neuer Name hat einen
  anderen Typ) -- `coin` auf `2.9-b` ist jetzt
  `PMF.uniformOfFintype Bool`. `2.8-a` Aufgabe 16 trug eine Hypothese
  `a ≤ b`, die `Real.volume_Icc` nicht braucht. `A-a` E1 ist mit
  `field_simp` allein fertig, das verlangte `ring` hat nichts mehr zu
  tun; im Zeugen vermerkt.
- **`1.2-a` und `1.5-a` sind neu geschrieben** (die letzten beiden im
  alten Stil): Taktiktabelle, Abschnitte, `cases'` raus. Die
  dokumentierten Fehler sind weg -- die `xxx`-Autorennotiz, das
  `library_search`, und das `rw [l1]`-Geruest, dem der Zeuge nicht
  folgte. `l1` **ist** `imp_iff_or_not`, also traegt das Geruest.
  Aufgabe 8 auf `1.2-a` braucht `by_contra` (Woche 4), das Blatt
  laeuft in Woche 3 -- als Extra markiert.
- **Foliensaetze geprueft** (`audit7.py` im Scratchpad: Lean-Bloecke
  gegen alles, was bis zur Woche des Decks dran war). Keine einzige
  Taktik zu frueh. Sechs Folien trugen absatzlange Aufzaehlungen und
  sind gekuerzt; was jetzt noch hoch zaehlt, sind Tabellen.

## 2026-10-23 (3) -- Kapitel `Slides` wird `Organization`

- `Coursenotes/5-Slides.lean` -> `5-Organization.lean`, Titel
  *Organization*, `tag := "organization"`, `file := "Organization"`,
  `htmlSplit := .never` (alles auf einer Seite). Der Decklisten-Teil
  behaelt `tag := "slides"`, also bleiben die vorhandenen
  `{ref "slides"}` gueltig.
- **Wichtig:** der Rueck-Link in jedem Deck steht in `SlidesMain.lean`
  und zeigte auf `../../Lecture-slides/`; mit dem neuen `file` ist das
  jetzt `../../Organization/`. Wer `file` aendert, muss diese Zeile
  mitaendern, sonst laufen alle Decks ins Leere.
- Inhalt: Wochentabelle (was wann, mit `{ref}` auf jedes Kapitel),
  Kurztests, Folien, Aufzeichnungen. Die Tabelle ist die aus
  `plan.md`, aber nur der studierendenrelevante Teil -- Workload,
  Tutor und die KI-Messungen bleiben intern.
- **Die Kurztests dauern jetzt 20 Minuten**, nicht 10. In `plan.md`
  und im neuen Kapitel.

## 2026-10-23 (4) -- Decks nach Kapiteln benannt

- `Slides/*.lean` heissen jetzt nach ihrem Kapitel und sortieren in
  Kapitelreihenfolge: `0-Introduction`, `1-1-Nat` ... `1-7-Notation`,
  `2-6-Filters` (plus `0-Introduction-SpeakerNotes.md`). Modulnamen
  brauchen dadurch Guillemets: `import Slides.«1-1-Nat»`.
- **Die URL eines Decks kommt nicht aus dem Dateinamen**, sondern aus
  dem ersten Element der `decks`-Liste in `SlidesMain.lean`. Beides
  ist jetzt gleich benannt, also `<site>/slides/1-1-nat/`. Wer eins
  aendert, muss das andere mitaendern.
- Alle `(slides/<deck>/)`-Links in den Kapiteln nachgezogen.
  **Achtung beim Pruefen:** die Seiten tragen `<base href="./../">`,
  diese Links gehen also vom Site-Root aus, nicht vom Verzeichnis der
  Seite. Ein Checker, der das ignoriert, meldet 16 Fehlalarme.
- Geprueft: 16 von 16 Deck-Links aufloesbar, Rueck-Link jedes Decks
  (`../../Organization/`) vorhanden.

## 2026-10-23 (5) -- `old/` weg, `Misc/` bis auf `Defs.lean`

- `old/` geloescht: 819 getrackte Dateien, 49 MB, seit April 2025
  nicht angefasst, von nichts referenziert. Davon waren 748 `.pygtex`
  in `_minted-*` reiner LaTeX-Cache. Inhalt war das Vorgaenger-Skript
  (`Manuskript/skript.tex`, `skript.md`) und die Lean-3-Blaetter in
  `src/`. Alles ueber die Historie zurueckholbar.
- **Vier Dateien in `old/` waren gitignored**, standen also in keiner
  Historie: `01- collection.lean`, `01-lean3.lean`, `03-c.lean`,
  `A_Logic.lean` (Lean 3 bzw. ein Blatt von Mehta/Buzzard). Gesichert
  nach `~/leancourse-old-untracked-20261023/`. `old/skript` war
  bytegleich mit dem getrackten `Manuskript/skript.tex`.
  **Merke:** vor `rm -rf` eines Ordners immer
  `git ls-files --others --ignored --exclude-standard <dir>` laufen
  lassen -- `git rm -r` fasst ignorierte Dateien nicht an, `rm -rf`
  schon.
- `Leancourse/Misc/` ist ganz weg: `Basic.lean`, `example.lean` und
  `02-Math/` importierte niemand. Die eine gebrauchte Datei,
  `Misc/Defs.lean`, heisst jetzt **`Leancourse/Markup.lean`**
  (`import Leancourse.Markup`, 90 Dateien umgestellt). Sie ist nicht
  optional: sie definiert die `{br}`-Rolle fuer Zeilenumbrueche in
  den Tabellen des Taktik-Anhangs, und ihr `open MyDef` am Dateiende
  ist es, was `{br}` bei den Importeuren sichtbar macht.
- **Die Teilnehmerliste SS 2025 (`.xlsx`, Klarnamen) lag im
  oeffentlichen Repo** und liegt weiterhin auf `main` und in der
  Historie beider Branches. Aus dem Arbeitsbaum von `preparation` ist
  sie raus; das allein beendet die Veroeffentlichung **nicht**.
  Offen: Loeschen auf `main` und `git filter-repo` + Force-Push.


## 2026-10-27 -- 1.2 und 1.6 zu *Typen I* und *Typen II*

- **Notation bekommt keine eigene Vorlesung** (Nutzer: Studierende
  fuehren kaum eigene Notation ein). Die gewonnene Woche geht an die
  Grundlagen. Die Kapitelzahl bleibt bei sieben.
- **Schnitt:** `1.2 Types I: rules and universes` (tag `types`) endet
  jetzt vor `# Inductive types`. Alles ab dort plus der Inhalt des
  alten 1.6 steht in `1-Lean/3-TypeFormers.lean`, *Types II: type
  formers*, tag `type-formers`: Π (mit Konvention `→` fuer Daten,
  `∀` fuer Propositionen, `Fin.last`), inductive, structures,
  **Σ (neu, als Struktur, disjunkte Vereinigung, Zaehlbeispiel mit
  `Fin 4`: 10 gegen 24)**, Subtypen, Typfamilien, Vektoren,
  Matrizen, Quotienten. *Σ und ∃* (tag `sigma-vs-exists`) steht
  jetzt in Curry-Howard bei `Nonempty`.
- Altes 1.6 hatte zwei falsche "Σ-Beispiele", die Subtypen waren;
  korrigiert. "What makes" und "Why dependent types matter" sind weg
  (`safeDiv` steht im Π-Abschnitt). Tag `dependent-types` gibt es
  nicht mehr.
- **Umnummerierung** (`git mv`, Tags unveraendert): Kapitel
  `3-Terms`→`4`, `4-Typeclasses`→`5`, `5-CurryHoward`→`6`; Decks
  gleich, URLs `slides/1-3-type-formers/` ... `1-6-curry-howard/`;
  Blaetter `1.6-a`→`1.3-a` (Woche 5), `1.4-a/b`→`1.5-a/b`,
  `1.5-a/b`→`1.6-a/b`. `WITHHELD`, Organization, `plan.md`,
  `Checks/README.md` nachgezogen.
- Deck 1.2 endet jetzt nach "The tag has to stay hidden"; die Folien
  ab "Inductive types" stehen im Deck 1.3. Hoechste Folie 642 px.

## 2026-10-27 (2) -- Typen I/II umgedreht: erst bauen, dann Regeln

- Auf Wunsch des Autors ("einfach anfangen, danach spezieller,
  moeglichst wenig Vorwaertsreferenzen") ist die Reihenfolge der
  beiden Typkapitel vertauscht:
  **1.2 `2-Types.lean` "Types I: building types"** (tag `types`):
  Π, inductive, structures, Σ, Subtypen, Typfamilien,
  Quotienten, Universenhierarchie, dazu die Geschichtsbox "Where
  types come from". **1.3 `3-Rules.lean` "Types II: the rules"** (tag
  `rules`): die Regeln, `imax`, `Prop`. Die Regel-Unterabschnitte
  *Quotients* und *Axioms* in 1.3 verweisen zurueck auf 1.2. Der Tag `type-formers` ist
  weg. Montag 02.11. wird ueber das neue 1.2 gelesen.
- 1.2.1.8 *Without inductive types* (Church-Kodierungen, `ChNat`) ist
  ersatzlos gestrichen, im Kapitel und im Deck.
- Decks: `slides/1-2-types/` (Bauen) und `slides/1-3-rules/`
  (Regeln); Blatt `1.3-a` heisst jetzt `1.2-b`
  (`2-b-DependentTypes.lean`), weiter in Woche 5.

## 2026-10-27 (3) -- Typen und Terme zusammen, Regeln danach

- Auf Wunsch des Autors ("Terme und Typen kann man nicht trennen")
  ist das Kapitel *Terms* aufgeloest. Neue Ordnung:
  **1.2 `2-Types.lean` "Types and terms I: functions and inductive
  types"** (tag `types`): Befehle `#check`/`def`/`example`/`#eval`
  (tag `naming-terms`), Universen (jetzt *vorn*), Funktionstypen mit
  `def`, Currying, `fun`/`·`, abhaengigen und polymorphen Funktionen,
  induktive Typen mit Mustervergleich, Rekursion/Terminierung,
  Rekursor, strikter Positivitaet, Geschichte.
  **1.3 `3-TypeFormers.lean` "Types and terms II: structures, pairs,
  subtypes, quotients"** (tag `type-formers`): Strukturen mit
  Strukturwerten, Σ, Subtypen, Typfamilien, Quotienten, dazu die
  Tabelle `four-steps`. **1.4 `4-Rules.lean` "Types III: the rules"**
  (tag `rules`). Tag `terms` gibt es nicht mehr; die Abschnitts-Tags
  aus Terms (`structure-values`, `pure-functions`,
  `polymorphic-functions`, `anonymous-functions`, `pattern-matching`,
  `recursion`) leben an der neuen Stelle weiter.
- **Jeder Typbildner in vier Schritten**: Formation, Construction,
  Use, Computation (Idee des Autors). In 1.4 heissen sie formation /
  introduction / elimination / computation rules, und die Regeln
  verweisen darauf zurueck.
- Decks: `slides/1-2-types/`, `slides/1-3-type-formers/`,
  `slides/1-4-rules/` (Terms-Deck aufgeteilt). Blatt `1.2-b` heisst
  `1.3-a` (`3-a-DependentTypes.lean`), weiter Woche 5. Wochen: 3 = 1.2,
  4 = 1.3, 5 = 1.4.
- **Vorwaertsverweise in 1.2-1.6**: Pruefskript im Scratchpad
  (`fwd.py`: jeder `{ref}`, dessen Ziel spaeter im Dokument steht).
  Vorher 37, jetzt 21; uebrig sind Orientierungssaetze und
  Nachschlage-Verweise in Anhang und Teil 2. Dazu ein inhaltliches
  Audit (Begriffe vor ihrer Erklaerung); die Funde in 1.2-1.4 sind
  eingearbeitet (`norm_num` -> `simp`/`rfl`, `[Add α]` -> konkretes
  `IntAddMap`, `![…]`, `%`, abhaengiges `if`, `omega`, `_`, `List`-
  Konstruktoren, Beweisirrelevanz, `@` erklaert). In 1.5/1.6 nur die
  drei falschen Saetze ("previous section" zu `CoeSort` und
  `Bool → Prop`) und die Beispiele mit `Monoid`/`Set ℝ` ersetzt; der
  Rest der 1.5/1.6-Funde ist offen.

## 2026-10-27 (4) -- Luecken gegenueber dem Lean Reference Manual

Abgleich des Inhaltsverzeichnisses des Reference Manual mit dem Skript
(Agent, Ergebnis stichprobenartig geprueft). Eingearbeitet:

- 1.3 *Indexed families and inductive predicates* (tag
  `indexed-families`): Parameter gegen Index (`Vec α n`, `Vec.head`
  ohne `nil`-Fall), `MyEven` mit `cases`, `#print Nat.le`/`Eq`, warum
  `cases h` auf `h : a = b` ersetzt. Zeile in der Vier-Schritte-
  Tabelle. Der `Vec`-Verweis in Kapitel 0 zeigt jetzt hierher.
- 1.2 *Proving things about recursive definitions* (tag
  `recursive-proofs`): strukturell -> `rfl`; wohlfundiert -> `rfl`
  scheitert (`+error`-Block), Gleichungslemma `log2.eq_1`,
  `rw`/`unfold`/`simp [f]`; `decreasing_tactic` als Voreinstellung.
- Anhang: `induction` mit `using Nat.strong_induction_on`,
  `Nat.le_induction`, `generalizing`, `fun_induction`; `simp` mit
  `@[simp]`, Normalform, Varianten-Tabelle; *File structure* mit
  `include`/`omit` (der alte Satz "nur wo benutzt" war fuer Theoreme
  falsch); *Common pitfalls*: `rw`/`simp` falten nicht auf,
  Reduzierbarkeits-Tabelle (`abbrev`, `def`, `irreducible_def`,
  `theorem`) -- und der Fehler "Nat.add rekursiv im ersten Argument"
  korrigiert (es ist das zweite); Taktik-Kombinatoren (`<;>`,
  `all_goals`, `any_goals`, `first`, `case`, `rename_i`, `x✝`) in der
  Einleitung des Taktik-Anhangs.
- 1.4: `lean4checker`. 1.5: Schritt 4 der Instanzsuche war falsch
  ("mehrere Loesungen -> Fehler"); Lean nimmt die erste. Prioritaeten-
  Satz korrigiert.
- Offen aus dem Abgleich: Koerzion gebuendelter Morphismen
  (`DFunLike`), `@[ext]` fuer Strukturen, `autoImplicit`, `#synth`,
  mutual/nested inductives, Modulsystem.

## 2026-10-27 (5) -- Decks nachgezogen, Durchgang

- Nat-Deck und seine Sprechernotizen, Einleitungs-Deck, Kapitel 0 und
  2.2 nannten noch die alten Kapitelnummern bzw. "the Types chapter";
  angepasst (inductive/Mustervergleich = 1.2, Regeln/`Prop` = 1.4,
  Typklassen = 1.5, Quotienten = 1.3).
- Deck 1-3 hat eine Summary-Folie; die Uebersichtstabelle dort braucht
  `:::class "small"`, und die CSS-Regel muss **beide** Formen
  abdecken (`.small table` und `table.small`): VersoSlides haengt die
  Klasse hier an die Tabelle selbst.
- `rw` sieht **nicht** durch ein `abbrev`, `simp` schon (getestet);
  die Reduzierbarkeits-Tabelle im Pitfalls-Kapitel sagt das jetzt so.
- `#eval` laeuft kompiliert, `rfl` im Kernel; bei wohlfundierter
  Rekursion gehen die beiden auseinander (1.2 sagt das jetzt).

## 2026-10-27 (6) -- Curry-Howard-Kapitel aufgeloest

- Das alte 1.6 *Propositions and proofs* war nach dem Umbau zu zwei
  Dritteln doppelt (Π/∀ in 1.2, Σ/∃ in 1.3, `#print And/Or/Exists`
  und eingeschraenkte Elimination in 1.4) und an zwei Stellen schief
  ("∨ = Summentyp", "∃ = Σ" ohne den `Prop`-Vorbehalt). Aufgeteilt:
  - 1.2, neuer Unterabschnitt *Proofs of implications* (tag `term`,
    Name beibehalten wegen `Exact.lean` und Organization): Modus
    ponens = Anwendung, Taktik- vs. Termmodus, `intro` = `fun`,
    `exact`, `show_term`. Curry/Howard in *Some history*.
  - 1.3, neuer Abschnitt *Propositions as types* (tag `curry-howard`,
    damit die sechs Verweise bleiben) vor den Quotienten: `¬`,
    `True`/`False` mit `nomatch`, `∧` als Struktur, `∨` und `∃` als
    induktive Typen in den vier Schritten, Vergleich mit Subtyp und
    Zaehlargument, Woerterbuch-Tabelle, Goldbach als `Prop`.
  - 1.4 *Axioms*: Absatz `Nonempty`/`Classical.choice`/
    `Classical.choose`/`noncomputable`. `Squash` und `PLift` sind weg.
- `7-Notation` -> `6-Notation`, Deck `slides/1-6-notation/`.
  Blaetter: `1.6-a` -> `1.3-b` (Predicates), `1.6-b` -> `1.3-c`
  (CurryHoward), `1.7-a` -> `1.6-a` (Notation), alle weiter Woche 7.
  Die Kopfzeilen des Logikblocks verweisen jetzt auf 1.3 statt 1.6.
- **Die Vorlesung am 30.11. (W7) ist frei**; in Organization und
  `plan.md` steht dort vorlaeufig nur Notation.

## 2026-10-27 (7) -- Blaetter fuer 1.2 bis 1.4

- Neu `1.2-b` (`2-b-Inductive`, Woche 4): eigener Aufzaehlungstyp
  `Weekday`, Baum `MyTree` (`Tree` ist in Mathlib belegt) mit
  `size`/`leaves`/`sum`/`mirror` und Induktion, `digits`/`digitSum`/
  `binLength` mit `termination_by`/`decreasing_by omega`, Beweise mit
  `rw [f]`/`simp [f]` (`rfl` scheitert bei wohlfundierter Rekursion,
  getestet). Benutzt nur Taktiken bis Woche 4 (`simp`, `omega` aus
  `1.1-c`); `simp_all` (erst `L-g`) bewusst vermieden.
- Neu `1.3-d` (`3-d-Structures`, Woche 7): `NatInterval` (`Interval`
  ist belegt) mit Beweisfeld, `with`, Gleichheit per `cases` auf den
  Gleichungen; `MyEven` mit `cases`/`induction h`; ℤ als `Quot R` auf
  ℕ × ℕ mit `Quot.sound rfl`, `Quot.lift`, `induction x using
  Quot.ind`.
- `1.3-b` -> `1.4-a` (Predicates and equality: `ext`, `choose`,
  `change` sind Stoff von 1.4). `1.3-c` neu geschrieben (Tabelle
  Term/Taktik, `show_term`), gleiche Aussagen, jetzt Woche 5.
- Wochen: W4 `L-e`, `L-f`, `1.1-c`, `1.2-b`; W5 `L-g`, `1.3-a`,
  `1.3-c` (+ `X-a`); W7 `1.3-d`, `1.4-a`, `1.6-a`. 34 Pflichtblaetter,
  35 Zeugen, alle sorry-frei (`check_solvable.sh`).

## 2026-10-27 (8) -- Deck 1-2 nach Durchsicht des Autors

- Inline-Code auf allen Folien kleiner und mit engeren Leerzeichen
  (`SlidesMain.lean`, `backLinkCss`): in Monospace in Textgroesse
  wirkte `x : α` groesser als der Text, mit breiten Luecken um `:`.
- Folie 2: `∀ n : ℕ, n < n + 1 : Prop` als Beispiel, `Fin n` als Paar
  `⟨i, h⟩` erklaert (im Skript ebenso, mit Verweis auf 1.3).
  Universen-Folie: Tabelle statt Lean-Kasten, `Prop : Type` steht da.
  `safeDiv … (by simp)` -> `(by decide)` (simp kommt erst auf `1.1-c`).
  Neue Folie/Absatz `MyAnd` als induktiver Typ; `List`-Definition vor
  den Funktionen auf Listen; Rekursions-Folie erklaert strukturelle
  Rekursion -> `Nat.rec` mit Rechnung `fib 3` und `bad`; die
  Rekursor-Folie ist weg (stand ausfuehrlich in 1.1).

## 2026-10-27 (9) -- Strukturen nach 1.2

- *Structures* (tags `structures`, `structure-values`) steht jetzt in
  1.2 vor *Inductive types*; dazu ein Unterabschnitt *Conjunction*
  (`And` als Struktur). In *Inductive types* ersetzt `MyOr` das
  vorige `MyAnd`; der alte Abschnitt *Inductive types vs structures*
  (tag `inductive-vs-structure`) ist jetzt der Unterabschnitt
  *Structures and inductive types* mit der Tabelle der Grundtypen
  (Empty/False, Unit/True, Bool, ×/∧, ⊕/∨, Subtyp/∃, ℕ/≤).
- Titel: 1.2 *Types and terms I: functions, structures, inductive
  types*, 1.3 *Types and terms II: pairs, subtypes, families,
  quotients*. In 1.3 verweisen ∧ und ∨ unter *Propositions as types*
  zurueck. Decks entsprechend (1-2: 31 Folien, 1-3: 17).

## 2026-10-27 (10) -- Taktik-/Termmodus nach 1.3, Rekursor, `Type*`

- *Proofs of implications* und Taktik-/Termmodus (tag `term`) stehen
  jetzt in 1.3 unter *Propositions as types* (Unterabschnitte
  *Implication, negation, and ∀* und *Tactic mode and term mode*);
  in 1.2 wirkten sie zwischen Funktionen und Strukturen themenfremd.
  Die beiden Folien sind entsprechend von Deck 1-2 nach 1-3 gewandert.
- 1.2: Funktion per Rekursor (`MyNat.double'` mit `MyNat.rec`). Der
  Compiler kann Rekursoren eigener Typen nicht ausfuehren ("code
  generator does not support recursor"), also `noncomputable`;
  `rfl` geht, `#eval` nicht. `Nat.rec` hat Sonderunterstuetzung.
  Neue Folie "Or with the recursor".
- Universen-Folie und -Abschnitt erklaeren `{α : Type*}`.
- 1.3 *Quotient types*: ℝ steht nicht mehr in einer Klappbox, sondern
  als Unterabschnitt *Example: the real numbers* (tag
  `reals-quotient`): Subtyp `CauSeq ℚ abs` -> Quotient
  `CauSeq.Completion.Cauchy abs` (`Quotient.sound`) -> Struktur
  `Real`; Addition per Repraesentanten (`mk_add`). Deck 1-3: zwei neue
  Folien ("The real numbers as a quotient", "Adding real numbers").

## 2026-10-28 -- Befehle, Suche, Inhaltsverzeichnis

- 1.2.1 *Commands for terms*: sechs Befehle, jetzt mit `theorem`
  (Mathlib: `lemma`) und `#print` (zeigt bei Theoremen den
  Beweisterm, auch nach Taktiken). *Warum* `theorem` getrennt von
  `def` ist (Beweisirrelevanz, kein Code, Typ muss `Prop` sein),
  steht in 1.4 *Why `Prop` is special*.
- Neu 1.2.1.1 *Finding theorems* (tag `finding-theorems`):
  `exact?`/`apply?`/`rw?`, `#loogle`, `#leansearch`; Details bleiben
  im Anhang *Navigating Mathlib*.
- **Moogle gibt es nicht mehr** (`moogle.ai` antwortet nicht), und
  `#moogle` existiert in LeanSearchClient nicht (nur `#loogle`,
  `#leansearch`, `#search`, `#statesearch`). Aus Anhang und `L-g`
  entfernt.
- **Seitenmenue nur bis 1.2.3.** Verso hat dafuer keine Option: jeder
  Teil ist eine Seite (`htmlSplit := .never`), und dann listet die
  lokale ToC alle Ebenen (`includeSubparts := .all`). Geloest per CSS
  am Ende von `static/theme.css`: `li:has(> .header.head-3)` usw.
  ausgeblendet, ebenso die `{docstring}`-Eintraege (`li:has(> a)`).
  `head-1` ist ein Kapitel, `head-2` ein Abschnitt. Im Text bleiben
  die Nummern 1.2.3.4 stehen.

## 2026-10-28 (2) -- Rekursion in 1.2, Rekursor am Baum, Nummerierung

- *Recursion and termination* definiert jetzt strukturelle und
  wohlfundierte Rekursion. Strukturell: `fib`, `BinTree.height`
  (`BinTree` ist hier deklariert). Wohlfundiert: `log2` (Lean findet
  alles selbst), Cantors `pairIndex` (braucht `termination_by m n =>
  (m + n, m)` und `decreasing_by all_goals (rw [Prod.lex_def];
  omega)`), `logb` (braucht `decreasing_by` mit `Nat.div_lt_self`).
  `euclidGcd` ist raus (Autor mag es nicht) und steht als Aufgabe 10
  auf `1.2-b`.
- **Lean findet Terminierung inzwischen fast immer selbst** (v4.34):
  `n / 2`, `n / 10`, Hochzaehlen `i + 1` bis `n` (es raet `n - i`),
  `m - n`. Hilfe braucht es nur bei vertauschten/umverteilten
  Argumenten (`gcd`, Cantor) oder nichtlinearen Zielen (`n / b < n`,
  `n % m < m`). Vor einem neuen Beispiel testen.
- Struktur vs. wohlfundiert ist eine Eigenschaft der *Definition*:
  mit einem Zaehlerargument geht `log2` strukturell (`rfl` geht dann).
- Vollstaendigkeit der Muster bei `fib` erklaert ("Missing cases",
  "Redundant alternative").
- *The recursor*: Beispiel `BinTree.rec` statt `MyNat.rec`, dazu die
  Bauanleitung (Parameter, Motiv, ein Fall je Konstruktor mit
  `motive aᵢ` fuer rekursive Argumente, ι-Regeln) mit `Colour`,
  `MyOption`, `List`, `Point`. Folie "How the recursor is built".
- Ueberschriften der vierten Ebene (`##` in Kapiteldateien) tragen
  `number := false`; im Text also "Finding theorems" ohne 1.2.1.1.

## 2026-10-29 -- 1.2 umsortiert: induktiv vor Struktur, `ZMod` statt `Fin` bei Π

- 1.2 heisst jetzt *Types and terms I: functions, inductive types,
  structures*. Reihenfolge: Π -> `# Inductive types` -> `# Structures`
  ("ein induktiver Typ mit genau einem Konstruktor"; die Gleichsetzung
  `structure Point` = `inductive Point | mk …` steht jetzt am Anfang)
  -> neuer `# Pattern matching and recursion` (tag
  `pattern-matching-and-recursion`) mit den alten `##`-Unterabschnitten
  Pattern matching ... Strict positivity. Tags unveraendert.
- Σ und Subtypen bleiben am Anfang von 1.3: sie haengen von den
  Strukturen ab, nicht von Π, und stehen so direkt dahinter.
- Abhaengige Funktion mit Daten in Π ist jetzt `sevenMod : (n : ℕ) →
  ZMod n := fun _ => 7` statt `Fin.last` (kein Vorgriff auf Strukturen;
  der Autor mag, dass man nicht meint, die Werte seien "dieselben").
  `Fin n` und `Fin.last`, `Fin.ext` kommen unter *Data with a property*.
- `ZMod` wieder aufgenommen: 1.3 *Example: the integers mod n* (tag
  `zmod-quotient`, `Quot` von Hand, `Quot.lift` mit dem Relationsbeweis
  als Wohldefiniertheit, Abbildung nach `ZMod`), 2.5 Ringe/Koerper
  (`CommRing (ZMod n)`, `Field` mit `[Fact p.Prime]`) und Quotienten
  (`Int.quotientSpanNatEquivZMod`). `decide` scheitert an `(3 : ZMod 7)⁻¹`.
- **Falsch war:** "ℤ, ℚ und `ZMod n` are quotients too" in 1.3. In Lean
  ist `Int` induktiv (`ofNat`/`negSucc`), `Rat` eine Struktur mit
  `reduced`, `ZMod` per Mustervergleich `ℤ`/`Fin n`. Nur `Multiset` ist
  ein Quotient.
- `{ref "x"}` braucht immer einen Linktext `[...]`, sonst Parsefehler
  "'['; expected ...".
- Blatt `1.2-b`: Teil 5 `Fin n` (Aufgaben 16-20: `two`, `myLast`,
  `embed`, `rev`, `rev (rev i) = i` mit `Fin.ext`/`omega`), Teil 6
  `natSelf : (n : ℕ) → ZMod n` (Aufgabe 21, ueberall `0`). `omega` kennt
  `i.val < n` von selbst. Pruef-`example`s unter einer `sorry`-Definition
  muessen selbst `sorry` sein, sonst Fehler beim Export-Check.
- *Some history* (tag `types-history`) steht jetzt am Ende von 1.3
  (nach der Vier-Schritte-Tabelle), die Folie entsprechend in Deck 1-3
  vor *Summary*. Sie erzaehlt auch Curry-Howard, das in 1.3 behandelt
  wird. 1.4 hat keinen eigenen Geschichtsabschnitt.

## 2026-10-29 (2) -- Blaetter nach dem Audit umgebaut

- Audit aller Blaetter: Taktik-Reihenfolge stimmt ueberall (Skript im
  Scratchpad `audit/tac.py`). Inhaltliche Luecken in Teil 2 (Bild/
  Urbild und injektiv/surjektiv stehen in keinem Kapitel, 2.6-b
  benutzt Topologie vor 2.7, 2.8 ohne Integration/Konvergenzsaetze,
  2.7 ohne Abschluss/Inneres) sind **noch offen**.
- Neues Blatt `1.2-c` (`2-c-Structures`, Woche 5): `NatInterval` aus
  dem alten `1.3-d`, dazu `NatInterval.Contains` (Punktnotation) und
  `PointedInterval extends NatInterval` (`mid.length`, `I.Contains
  I.pt` gehen ueber die Elternstruktur); `Fin` und `ZMod` aus `1.2-b`.
- `1.2-b` hat jetzt eine Rekursor-Aufgabe (`MyTree.size'` mit
  `MyTree.rec`, `noncomputable`, Gleichheit per Induktion), 17 Aufgaben.
- Umbenannt (`git mv`): `1.3-c` -> `1.3-b` (`3-b-CurryHoward`),
  `1.3-d` -> `1.3-c` (`3-c-Predicates`, nur noch induktive Praedikate
  und Quotient). 35 Pflichtblaetter.
- `1.1-c`: `cases'` ersetzt durch `cases n with | zero | succ k` und
  `obtain (h | h)`. `A-a` D1: Addition rekursiert im *zweiten*
  Argument (war falsch).

## 2026-10-29 (3) -- Teil 2: Kapitel 2.1 ergaenzt, vier Blaetter umgebaut

- 2.1 hat zwei neue Abschnitte vor *From a set back to a type*:
  *Image and preimage* (tag `image-preimage`: Mitgliedschaft im Bild
  ist ein `∃`, im Urbild `f x ∈ t`; `obtain ⟨x, hx, rfl⟩`;
  `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`; Urbild vertraegt sich per `rfl` mit
  allen Operationen, Bild mit `∩` nur `⊆`) und *Injective and
  surjective functions* (tag `injective-surjective`: Definitionen per
  `Iff.rfl`, `n + 1` injektiv und nicht surjektiv, Komposition,
  `Set.range_eq_univ`, `Set.image_inter`, `Bijective`, `≃`,
  `Equiv.ofBijective` noncomputable). Notationstabelle um `''` und
  `⁻¹'`. Vorher standen beide Begriffe in keinem Kapitel.
- `2.1-b`: Kopf neu, Musterbeispiele mit `rintro ⟨x, hx, rfl⟩`, die
  schon geloeste Aufgabe 1 ersetzt durch
  `f '' (f ⁻¹' t) = t ∩ Set.range f`. `2.1-c`: Leseverweis.
- `2.6-b`: keine Topologie mehr. Aufgabe 20 ist jetzt `a (n + 1) → l`
  per `Tendsto.comp` und `tendsto_add_atTop_nat`; `nhds'` von Hand
  ist raus, 30 Aufgaben.
- `2.7-a`, 38 Aufgaben: neue Teile *Closure, interior, frontier* (9,
  u.a. `closure_Ioo`, `interior_Icc`, `frontier_Icc`,
  `Metric.mem_closure_iff`) und *Connected sets* (2); in Teil 7 die
  beiden Aufgaben aus `2.6-b` (`ContinuousAt` mit Folgen, `nhds` von
  Hand).
- `2.8-a`, 33 Aufgaben: Teile *Integration* (8, `∫ x in a..b`,
  `integral_add`/`_mono`/`_nonneg`, `lintegral_indicator_one`,
  `integral_congr_ae`) und *Convergence theorems* (monotone Konvergenz,
  Fatou, dominierte Konvergenz -- Hypothesen lesen).
- `2.3-a` neu: *Well-foundedness and paradoxes*. `Acc` von Hand fuer 0
  und 1, `>` auf ℕ nicht fundiert (`WellFounded.has_min`),
  wohlfundierte Induktion mit `Nat.strong_induction_on`/`split_ifs`,
  `#check_failure (s ∈ s)`, Russell als Barbier-Relation, Cantor von
  Hand. Die Rekursionsaufgaben (Doppel zu `1.2-b`) und
  `#print axioms` (steht auf `2.2-a`) sind raus; Beweisirrelevanz ist
  jetzt `2.2-a` Aufgaben 13-14.
- Offen in den Kapiteln: `xxx`-Notizen in 2.7 (nontrivial filter,
  cluster point, connected vs. preconnected) und 2.8 (Konstruktion
  des Integrals, `SigmaFinite`).


## 2026-10-29 (4) -- Suchen gehoert ins Blatt: `2.0-a`, *Finding theorems* aus 1.2 raus

- Der Abschnitt *Finding theorems* (tag `finding-theorems`) in 1.2 ist
  geloescht; niemand verwies darauf. Die Referenz bleibt der Anhang
  *Navigating Mathlib*.
- Neu `2.0-a` (`Exercises/2-Mathematics/0-a-Search.lean`, Woche 8,
  Zeuge in `Checks/`), 20 Aufgaben. Kein Kapitel, eroeffnet den
  Mathematikteil. Teile: `exact?` und seine Antwort lesen; wenn
  `exact?` scheitert (zwei Schritte, falsche Aussage
  `√x ^ 2 = x` ohne `0 ≤ x`); `rw?` (fuehrt den *ersten* Treffer aus,
  der oft falsch ist -- bei `exp (2x) = exp x ^ 2` ist es
  `Real.exp_mul`); Namen raten; `apply?` (Liste lang, `mul_pos` steht
  etwa an 20. Stelle); `#loogle`/`#leansearch` (auskommentiert, brauchen
  Netz), Zwischenwertsatz ueber `intermediate_value_Icc`.
- Damit Woche 8 bei drei Blaettern bleibt, liegt `2.1-c` jetzt in
  Woche 9 (`2.1-c`, `2.2-a`, `2.3-a`). 36 Pflichtblaetter.
- Gemessen (v4.34): `add_pos` ist verallgemeinert zu
  `b < c → 0 < a → b < c + a` -- als Namensbeispiel ungeeignet. Der
  alte Name `abs_add` existiert nicht mehr (`abs_add_le`).
  `exact?` scheitert an `0 < x ^ 2 + 1` und am Zwischenwertsatz.
- Ueberschneidung: `A-a` Teil B (Lemmata finden) deckt sich jetzt
  teilweise mit `2.0-a`; nicht angefasst.

## 2026-10-29 (4) -- 1.2/1.3 umbenannt, Taktik-/Termmodus nach 1.4

- **Dateinamen nach Titeln** (`git mv`): `1-Lean/2-Types` ->
  `2-FunctionsInductiveStructures`, `3-TypeFormers` ->
  `3-PairsSubtypesQuotients`, Decks gleich. **Deck-URLs geaendert**:
  `slides/1-2-functions-inductive-structures/`,
  `slides/1-3-pairs-subtypes-quotients/`; alte Links brechen.
- *Tactic mode and term mode* (tag `term`) steht jetzt am Ende von
  1.4 *Why `Prop` is special*: Beweise im Taktikmodus wegen
  Beweisirrelevanz, Daten im Termmodus (geht per `by`, ist unueblich).
  Folie ins Deck 1-4. In 1.2 und 1.3 nur Verweise.
- 1.2: `ℕ∞ = WithTop ℕ = Option ℕ` nach `MyOption` (alles `rfl`),
  `ArithProg` statt `MyConfig`, `Fin.ext` ohne Axiom erklaert,
  `MyNat.double'` raus (doppelt zu `1.1-a`/`1.2-b`; `noncomputable`
  jetzt bei `BinTree.sum`), `bad` -> `loop` (Kollision mit `Bad`),
  `log2` mit gewoehnlichem `if` (Lean nutzt die Bedingung selbst;
  abhaengiges `if` erst bei `logb`), Grafik `cantor_pairing`
  (`scripts/figures/cantor_pairing.py`) zu `pairIndex`.
- 1.5: `(7 : ZMod 5) = 2` als Beispiel fuer `OfNat` -> `Nat.cast` ->
  `Fin.ofNat`.
- **Abbildungen in zurueckgehaltenen Kapiteln ohne `tag`**: sonst
  bricht `strip_unreleased.py --check` ab ("would lose tags").

## 2026-10-29 (5) -- Rekursion als eigenes Kapitel 1.3

- 1.2 war auf 922 Skriptzeilen (5 856 Woerter, 31 Folien) gewachsen,
  44 % davon *Pattern matching and recursion*. Der Block ist jetzt
  Kapitel 1.3 `3-PatternMatchingRecursion.lean` (tag
  `pattern-matching-and-recursion`, vorher Abschnitts-Tag), mit den
  Abschnitten Pattern matching / Recursion and termination / Proving
  things about recursive definitions / The recursor / Strict
  positivity (Tags unveraendert). Es importiert das 1.2-Modul
  (`MyNat`, `BinTree`, `Colour`, `MyOption`, `Point`).
- Ein Satz zu `mutual` mit Link ins Reference Manual, sonst nichts
  (Mathlib: 4 Mathematik-Dateien von 8 529 benutzen es).
- Umnummeriert (`git mv`): Kapitel 1.3-1.6 -> 1.4-1.7, Decks gleich,
  URLs `slides/1-3-pattern-matching-recursion/` (neu),
  `1-4-pairs-subtypes-quotients/`, `1-5-rules/`, `1-6-typeclasses/`,
  `1-7-notation/`. Das neue Deck importiert das Deck 1-2 und oeffnet
  dessen Namespace `SlidesTypes` wieder (wegen `MyNat`).
- Blaetter: `1.2-b` (Inductive) -> `1.3-a` (`3-a-Recursion`),
  `1.2-c` -> `1.2-b`, `1.3-a/b/c` -> `1.4-a/b/c`, `1.4-a` -> `1.5-a`,
  `1.5-a/b` -> `1.6-a/b`, `1.6-a` -> `1.7-a`; Zeugen in Lockstep.
- Wochen: W4 Rekursion (1.3), W5 Paare/Subtypen (1.4), W6 Regeln
  (1.5), W7 Typklassen und Notation (1.6, 1.7). Die freie Vorlesung
  am 30.11. ist damit belegt. Blaetter W6: `1.4-c`, `1.5-a`; W7:
  `1.6-a`, `1.6-b`, `1.7-a`. Test 2 (02.12.) liegt jetzt nach den
  Typklassen statt nach den Regeln.
- Relative Verweise ("previous chapter", "next chapter") in 1.1, 1.2
  und 1.4 auf Nummern umgestellt, wo sich ihr Ziel verschoben hat.
  Vorher schon falsch und mitkorrigiert: 1.1 verwies fuer
  *Conversion* auf "the next chapter" (steht in den Regeln, jetzt
  1.5); Folie 1-2 und die Nat-Sprechernotizen nannten 1.4 statt der
  Regeln usw.

## 2026-10-30 -- Kapitel 2.1 *Numbers*, 2.2 und 2.3 zusammengelegt

- Neu `2-Mathematics/1-Numbers.lean` (tag `numbers`): wie die
  Zahlbereiche gebaut sind (ℤ induktiv `ofNat`/`negSucc`, ℚ Struktur
  mit `den_nz`/`reduced`, ℝ Struktur um den Quotienten, ℂ Struktur,
  `ℝ≥0` Subtyp, `ℝ≥0∞ = WithTop ℝ≥0 = Option`), Arithmetik in ℕ/ℤ
  (`(-7)/2 = -4`, `%` nie negativ), *Total functions and junk values*
  (tag `junk-values`, Tabelle `deriv`/`∑'`/`∫`/`sSup`/`Nat.card`),
  drei Potenzen (tag `powers`; `x ^ (1 / 2) = 1`, weil `1 / 2 : ℕ`),
  `ℝ≥0∞`-Arithmetik, Casts (verweist auf `1.6-b`, das unveraendert
  bleibt). `#eval (1 : ℝ) + 1` scheitert *nicht*, es zeigt
  `Real.ofCauchy (sorry /- 2, 2, ... -/)`; `decide` scheitert.
- Teil 2 bleibt bei neun Kapiteln: `1-SetsAndTypes` -> `2-SetsAndTypes`,
  `2-UniversesAndAxioms` + `3-Logic` -> `3-Foundations.lean` (Titel
  *Foundations: universes, axioms, well-foundedness*; der alte
  Logic-Teil ist der Abschnitt `logic-wf` vor *Constructive vs
  classical logic*, alle Tags unveraendert). 2.4-2.9 und das
  Filter-Deck unveraendert.
- 2.2 hat einen Abschnitt *Finite sets and sums* (tag `finite-sets`:
  `Finset` = Struktur aus `Multiset` (Quotient von `List`) und
  `nodup`, `Finset.range`, `∑`/`∏`, Induktion mit
  `Finset.sum_range_succ`, Tabelle der Kardinalitaeten).
- Anhang *Common pitfalls*, neuer Abschnitt *How an object is
  represented* (tag `representation-pitfalls`): `Fin n` modulo,
  Maximumsnorm auf `Fin n → ℝ` gegen `EuclideanSpace` (4 gegen 5 fuer
  `![3, -4]`), `degree 0 = ⊥` gegen `natDegree 0 = 0`, Morphismen als
  Strukturen mit `DFunLike`.
- Blaetter: neu `2.1-a` (`1-a-Numbers`, 22 Aufgaben, Woche 8);
  `2.1-a/b/c` -> `2.2-a/b/c`, `2.2-a` -> `2.3-a`, `2.3-a` -> `2.3-b`.
  W8: `2.0-a`, `2.1-a`, `2.2-a`; W9: `2.2-b`, `2.2-c`, `2.3-a`,
  `2.3-b`. 37 Pflichtblaetter.
- Ueberschneidung, nicht bereinigt: *Why the kernel has no loops* in
  2.3 (Rekursoren, strikte Positivitaet, `partial def`) doppelt sich
  teilweise mit dem neuen Kapitel 1.3.
- Deck 1-2, Folie 3: die Vier-Schritte-Tabelle hat jetzt Spalten fuer
  Funktion, induktiven Typ und Struktur (467 px).
- Kapiteltitel in Teil 1 ohne "Types and terms I/II": 1.2
  *Functions, inductive types, structures*, 1.4 *Pairs, subtypes,
  families, quotients*, 1.5 *Rules for building types* (vorher
  "Types III: the rules"). Tags, Dateinamen und Deck-URLs unveraendert.

## 2026-10-30 (2) -- Typklassen in zwei Vorlesungen, Monaden nach 1.6, Masstheorie nur Lesestoff

- **1.6 *Typeclasses* wird in zwei Vorlesungen gelesen** (Wunsch des
  Autors: "nicht an den Grundlagen sparen"). W7: bis `Decidable` und
  die Taktik `classical`; W8 ab `# Classes over type constructors`
  (tag `type-constructor-classes`): `Functor`, `Monad`, `do`,
  Listenmonade, Gesetze (`id_map`, `comp_map`, `pure_bind`,
  `bind_pure`, `bind_assoc`), Kategorientheorie in einem Satz; dann
  Koerzionen mit `DFunLike`, Hierarchie mit `extends`/`#synth`,
  Instanzen verwalten. Notation (1.7) laeuft in W8 mit. Ein Kapitel,
  zwei Decks: `slides/1-6-typeclasses/` und
  `slides/1-6b-functors-monads/` (`Slides/1-6b-FunctorsMonads.lean`).
- **Die Masstheorie-Vorlesung entfaellt.** Kapitel 2.8 bleibt als
  Lesestoff, `2.8-a` ist Extrablatt. Alles ab W8 rueckt eine Woche
  nach (Grundlagen am 21.12., Proof Engineering am 11.01.).
- **2.9 ohne `IO`/`StateM`/`Except`.** Der Monadenteil heisst
  *Monads in mathematics* (tag `monads`): Tabelle `pure`/`map`/`bind`
  fuer `Set`, `Finset`, `Filter`, `PMF`, dann Sets (`Set.monad` nur
  lokal), Finsets (brauchen `DecidableEq`; `Monad Finset` nur unter
  `[∀ P, Decidable P]`), Filter (`Filter.monad` ist kein Instance, weil
  sein `seq` nicht `Filter.seq` ist). Rueckverweise auf 1.6 in 2.2
  (Bild = `map`, `Finset.image`) und 2.6 (`Filter.map`).
- **`classical` erklaert**: Abschnitt `classical-tactic` in 1.6, Glossar
  `Tactics/Classical.lean` (tag `classical`), Cheatsheet-Zeile. Regeln:
  im Beweis `classical`; braucht schon die *Aussage* die Instanz, gehoert
  `[DecidableEq β]` in die Hypothesen; fuer Definitionen
  `open Classical in`. `by_cases` braucht nichts davon. 2.3 behauptete,
  Mathlib benutze `open Classical` -- korrigiert.
- **`noncomputable` erklaert**: in 1.3 beim Rekursor (Compiler gegen
  Kern, nur `#eval` faellt weg), in 2.1 mit dem Fehler fuer
  `def recip (x : ℝ) : ℝ := 1 / x` (`Real.instDivInvMonoid`) und
  `noncomputable section`. `x + 1` auf ℝ ist berechenbar.
- Blaetter: neu `1.6-c` (`6-c-Monads`, 17 Aufgaben, W8); `2.9-a` neu
  als *Monads in mathematics* (17 Aufgaben); die alten Typklassen-
  Aufgaben (`Day`, `IntVec`, `Describable`) und `StateM`/`Except` sind
  weg. `1.6-a` Aufgabe 18 uebt `classical`. 37 Pflichtblaetter,
  39 Zeugen.
- **`Fact` erklaert und geuebt** (Wunsch des Autors): Abschnitt
  *Propositions as instances: `Fact`* (tag `fact`) in 1.6 vor `OfNat`,
  mit `{docstring Fact}`; drei Verwendungen (fordern `[Fact p.Prime]`
  + `Fact.out`, global `instance : Fact (Nat.Prime 7)`, lokal per
  `have : Fact p.Prime := ⟨hp⟩`). Ohne Instanz meldet
  `mul_inv_cancel₀ ha` auf `ZMod p` einen *type mismatch* zwischen
  `ZMod.instInv` und dem Koerper-`⁻¹`, nicht "failed to synthesize
  Fact" -- steht als `+error`-Block im Text. `1.6-a` Aufgaben 19-23,
  Folie *Propositions as instances* im Deck 1-6, Rueckverweis aus 2.5.
  Mathlib benutzt `Fact` vor allem fuer `1 ≤ p` (Lᵖ, 129 Stellen),
  Dimensionen und Primalitaet.
- **`deriving` intern** (1.6, nach dem `Pair`-Beispiel): pro Klasse ein
  *deriving handler*, ein Lean-Programm, das die Konstruktoren liest und
  den Quelltext einer `instance` schreibt; der wird normal elaboriert und
  vom Kern geprueft. `trace.Elab.Deriving.repr`/`.decEq` zeigen den
  Code. **Achtung:** Mathlibs `deriving Fintype` ist in v4.34 kaputt
  (Typfehler `Suit.enumList_nodup`) -- deshalb im Text nicht als
  Beispiel genannt.
- **Typklassen und Logik** (1.6, nach der Tabelle *Instances are
  terms*): der Kern kennt weder `class` noch `instance`; Instanzsuche
  laeuft im Elaborator (`pp.explicit` zeigt `@instHAdd ℕ instAddNat`).
  Keine Axiome, keine Inkonsistenz moeglich; aber die Instanz bestimmt,
  was ein Satz *bedeutet*: `(1, 5) ≤ (2, 0)` ist auf `ℕ × ℕ` falsch
  (komponentenweise), auf `Lex (ℕ × ℕ)` wahr.
- **Kern und Elaborator: 1.5 ist die Hauptstelle.** Der Unterabschnitt
  heisst *The kernel and the elaborator* (tag `kernel-elaborator`,
  vorher *How Lean implements the rules* ohne Tag): was der Elaborator
  tut (Notation, Unifikation, Instanzen, Koerzionen, `match`, Taktiken),
  `#print` eines Taktikbeweises, Fehler vom Elaborator vs. `(kernel)`,
  der Compiler als drittes Programm. 1.1 fuehrt die beiden Woerter in
  drei Saetzen ein (vorher nur Link in den Anhang); dort war auch
  "`#eval` runs the same reduction" falsch -- `#eval` laeuft kompiliert.
  Anhang *The kernel and the elaborator* (tag `elaborator`, bleibt) ist
  auf einen Verweis geschrumpft; er behauptete, lean4lean sei "formally
  verified" -- laut README ist es aus dem C++-Kern abgeleitet ("not
  really an independent implementation"), der Korrektheitsbeweis ist
  ein Teilprojekt. Strikte Positivitaet in 1.3 hat jetzt den Tag
  `positivity-rule` (`strict-positivity` ist der Abschnitt in 2.3).
  Neue Folie im Deck 1-5, Zeile im Deck 1-1 und in dessen Notizen.
- **`Decidable` praezisiert** (1.6, Nutzerfrage "ist P mit Beweis
  entscheidbar?"): fuer eine *einzelne* Aussage ist `Decidable P` nur
  ein Beweis von `P` oder `¬P` (`isTrue h`, ohne Axiom); Entscheidbarkeit
  sagt erst etwas fuer *Familien* (`DecidablePred`, `DecidableEq`).
  Beispiel: `x = 0` auf ℝ; Mathlibs `Real.decidableEq` haengt an
  `Classical.choice`, `def realIsZero` scheitert als nicht kompilierbar.
  Die Formulierung in 2.3 ist mitgezogen.
- Offen, nur besprochen: `{_ : Decidable p}` statt `[Decidable p]` in
  `@[simp]`-Lemmas (Docstring von `Decidable`). In v4.34 greift `simp
  [lemma]` auch mit `[…]` bei nicht-kanonischen Instanzen; scheitern
  tut erst `simp only [lemma h]`, weil der Term vor dem Matchen
  elaboriert wird. Kandidat fuer *Common pitfalls*.

## 2026-10-30 (3) -- Decks 1-2 bis 1-4 nach Durchsicht, ℝ nach 2.1, Deck 2-1

- **Deck und Kapitel 1.2**: Beispiele als Definitionen (`RVec n := Fin n → ℝ`
  als Typ, der von einem Term abhaengt); Befehle sortiert (`def`/`theorem`/
  `example`, dann `#check`/`#eval`/`#print`), neue Folie *`#print` shows the
  proof term*; Folie *Function types and Π-types* fuehrt den Begriff ein
  (`α → β` ist der Π-Typ mit konstantem `β`, `rfl`); `id` aus der Prelude
  (`Sort u`); `def MyENat : Type := Option ℕ` mit `ℕ∞ = MyENat := rfl`;
  `structure Fin`/`And` als Quelltext abgedruckt (`intro ::`).
- **Folien: Lean-Bloecke zeigen ihre Ausgabe als Panel.** Ein `#print`
  mit langer Ausgabe sprengt die Folie; dort lieber die Definition als
  ungeprueften Block abdrucken. Kommentare mit der Ausgabe sind doppelt.
- **Deck und Kapitel 1.3**: *Structural recursion* definiert; *Are all
  cases covered?* (Muster -> verschachtelte `Nat.casesOn`); *The recursor
  behind `fib`*: `#print fib` = `Nat.brecOn x fib._f`, `Nat.brecOn` reicht
  alle kleineren Werte durch (`Nat.below`), von Hand `fibPair` mit
  `Nat.rec`. Lexikografisch, weil die Ordnung per Instanzsuche aus dem Typ
  des Masses kommt (`#synth WellFoundedRelation (ℕ × ℕ)` =
  `Prod.instWellFoundedRelation` = `Prod.lex`). `termination_by?` zeigt
  bei `logb` das Mass `n`. `Bad`: `app` heisst `unmk`, zwei Folien, das
  Argument als geprueftes `example` mit `mk`/`unmk` als Hypothesen.
- **Deck 1-4**: Subtyp-Folie mit `structure Subtype` (zweite Komponente ein
  Beweis), geteilt; Geschichtsfolie als Zeitleiste (Klasse `timeline`).
- **ℝ als Quotient steht jetzt in 2.1** (`## The real numbers`, tag
  `reals-quotient` unveraendert), *How the number types are built* hat drei
  Unterabschnitte und die Tabelle vorn. 1.4 verweist nur noch dorthin.
- **Neues Deck `Slides/2-1-Numbers.lean`** (`slides/2-1-numbers/`,
  namespace `SlidesNumbers`), 14 Folien, in `SlidesMain` und Organization
  (neue Unterliste *Mathematics*) eingetragen.
