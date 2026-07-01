import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`grind`" =>
%%%
tag := "grind"
%%%

*Summary:* `grind` is a powerful general-purpose automation tactic
introduced into Lean 4 by the Lean FRO team.  It is designed to close
goals that mix *equational*, *propositional*, and *arithmetic*
reasoning -- the kind of "obvious" side goals that a human would
consider routine but that no single specialized tactic handles.  Its
design is inspired by SMT solvers (think of the engines inside Z3):
it does not search for a proof term by trial and error the way
`aesop` does, but runs a set of cooperating decision procedures until
they either close the goal or get stuck.

Under the hood `grind` combines several engines:

* *Congruence closure* -- it maintains equivalence classes of terms
  and knows that equal inputs give equal outputs, so from `a = b` it
  derives `f a = f b` automatically.
* *Constraint propagation and case splitting* -- it propagates the
  consequences of hypotheses and splits on disjunctions,
  `if`-conditions, and the constructors of inductive types.
* *A linear arithmetic procedure* over `Nat`, `Int`, and ordered
  fields, similar in spirit to `omega`/`linarith`.
* *E-matching* -- it instantiates quantified lemmas by matching their
  left-hand sides against terms present in the goal, using
  *patterns*.  This is how you teach `grind` new facts.
* *Constructor reasoning* -- injectivity and no-confusion, so
  `some a = some b` yields `a = b`, and `some a = none` is a
  contradiction.

*Examples:*

::::keepEnv
:::example " "
```lean
-- congruence: equal arguments give equal results
example (f : Nat → Nat) (a b : Nat) (h : a = b) :
    f a = f b := by grind

-- chaining equalities
example (a b c : Nat) (h1 : a = b) (h2 : b = c) :
    a = c := by grind

-- propositional reasoning with case splits
example (p q : Prop) (h : p ∨ q) (hp : ¬p) : q := by
  grind

-- injectivity of constructors
example (a b : Nat) (h : some a = some b) : a = b := by
  grind

-- a little linear arithmetic
example (a b : Int) (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b := by grind
```
:::
::::

*Remarks:*

* *When to reach for it.* `grind` shines on goals that interleave a
  handful of hypotheses, some case analysis, equalities, and a bit of
  arithmetic -- exactly the situations where you would otherwise
  write a tedious chain of `rcases`, `simp`, and `omega`.  It is a
  *finishing* tactic: point it at a goal you believe is true "for
  obvious reasons".
* *Extending it.* You register facts for `grind` with the `@[grind]`
  attribute family; the tactic then instantiates them by E-matching
  during the search.  This is the analogue of `@[simp]` for the
  simplifier, but the lemmas are used as logical facts rather than
  rewrite rules.
* *What it does not do.* `grind` does **not** perform induction, and
  it is not a general nonlinear arithmetic engine.  For goals needing
  induction use `induction`; for polynomial identities use `ring`;
  for pure linear arithmetic `omega` (over `ℤ`/`ℕ`) or `linarith`
  (over `ℝ`/`ℚ`) are lighter and faster.
* *Cost.* Because it runs several procedures and may split into many
  cases, `grind` can be noticeably slower than a targeted tactic.
  Prefer the specialized tactic when you already know which one
  applies; keep `grind` for when the goal genuinely mixes several
  kinds of reasoning.
* *Relation to `aesop`.* Both are general automation, but with
  different philosophies: `aesop` runs a customizable best-first
  *proof search* applying registered rules, while `grind` runs
  *decision procedures* with congruence closure and E-matching.  When
  one fails, the other is often worth a try.
