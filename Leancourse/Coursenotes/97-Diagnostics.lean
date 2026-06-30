import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Diagnostic Commands" =>
%%%
htmlSplit := .never
tag := "diagnostics"
%%%

These commands *inspect* your work without changing it: they report a
theorem's logical dependencies, suggest where a definition should
live, and run the library's quality checks.  Unlike the `#`-commands
in the Lean basics chapter (`#check`, `#eval`, `#print`), these are
mostly about *engineering* a clean, well-placed, axiom-honest
development.

# `#print axioms` -- the axiom footprint
%%%
tag := "diag-print-axioms"
%%%

`#print axioms name` traces a declaration back to the axioms it
ultimately depends on.  Recall (see {ref "lean-axioms"}[Lean's three
axioms]) that Lean has exactly three: `propext`, `Quot.sound`, and
`Classical.choice`.

```lean
theorem my_classical (p : Prop) : ¬¬p → p :=
  fun h => Classical.byContradiction (fun hn => h hn)

theorem my_constructive (n : ℕ) : n + 0 = n := rfl

#print axioms my_classical
-- 'my_classical' depends on axioms:
--   [propext, Classical.choice, Quot.sound]

#print axioms my_constructive
-- 'my_constructive' does not depend on any axioms
```

The main use is a *constructivity check*: if `Classical.choice` does
not appear, the proof is constructive.  Two caveats are worth
stating:

- It is a *constructivity* detector, not an *excluded-middle*
  detector.  Because the law of excluded middle is a
  {ref "em-derived"}[theorem] derived from `Classical.choice` (and not
  an axiom in its own right), using it leaves no separate token: a
  proof
  that uses `Classical.em` and one that uses `Classical.choice`
  directly are indistinguishable -- both simply show
  `Classical.choice`.
- If a proof contains a `sorry` (even indirectly, through a lemma it
  calls), the marker `sorryAx` appears.  This makes `#print axioms` a
  reliable way to detect unfinished proofs hiding in a development.

There is no `#used_axioms` command; `#print axioms` is the tool.

# `#find_home` -- where should this live?
%%%
tag := "diag-find-home"
%%%

`#find_home name` (from the `ImportGraph` library) suggests the files
*highest* in the import hierarchy where a declaration could live,
based on which files its own dependencies come from.  It is the tool
for *upstreaming* a lemma to the right place -- e.g. when contributing
to Mathlib.  `#find_home!` additionally refuses to suggest the
current file.

```
-- best used in a file with `import Mathlib`
#find_home my_lemma
-- ⇒ a list of candidate modules where `my_lemma` could go, e.g.
--   [Mathlib.Order.Basic, Mathlib.Data.Nat.Defs]

#find_home! my_lemma   -- same, but never suggests THIS file
```

Two points to keep in mind: it works best with `import Mathlib`, and
it may legitimately return only the current file (if the lemma's
dependencies are spread across incomparable files).  A related
command, `#min_imports`, computes the minimal set of imports a
declaration needs and additionally accounts for notation and tactics.

# `#lint` -- the environment linters
%%%
tag := "diag-lint"
%%%

`#lint` runs Mathlib's *environment linters* over declarations,
flagging quality problems such as undocumented definitions
(`docBlame`), unused arguments (`unusedArguments`), non-confluent simp
lemmas (`simpNF`), and uses of deprecated names.

```
#lint                 -- lint the current file's declarations
#lint in all          -- the whole environment (slow)
#lint only docBlame   -- run a single named linter
#lint+ in Batteries   -- verbose: report each linter's result
#list_linters         -- print every available linter
```

You can also append `*` to skip slow tests (`#lint*`), `-` for a
silent run that fails on any problem (handy in CI), or extra linter
names to add to the default set.

These are *not* the same as the build-time linters that produce the
warnings you see when this manual compiles (the `*`-emphasis and
60-column warnings): those check the Verso *markup source*, whereas
`#lint` checks the *Lean environment*.
