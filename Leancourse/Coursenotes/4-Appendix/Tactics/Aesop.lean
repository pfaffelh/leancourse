import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`aesop`" =>
%%%
tag := "aesop"
%%%

*Summary:* `aesop` (Automated Extensible Search for Obvious Proofs)
performs a best-first tree search using a configurable set of rules.
In the course of a search it can apply lemmas, split goals, call
`simp`, and more.  It is particularly effective on goals involving
set membership, basic logic, and routine structural reasoning.

*Examples:*

::::keepEnv
:::example " "
```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  aesop

example (x : ℕ) (s t : Set ℕ) (hs : x ∈ s) :
    x ∈ s ∪ t := by aesop
```
:::
::::

*Remarks:*

* You extend `aesop` by registering your own lemmas as rules with the
  `@[aesop]` attribute, e.g. `@[aesop safe apply]` (always try this
  rule) or `@[aesop unsafe 50% apply]` (try it with lower priority in
  the search).
* `aesop` is a *search* tactic: it explores many branches, so it can
  be slower than a targeted tactic and its failures are less
  predictable.  It is a good first thing to try on an "obvious" goal.
* For goals dominated by equalities, congruence, and arithmetic,
  {ref "grind"}[`grind`] is often the better general tool; the two
  complement each other.
