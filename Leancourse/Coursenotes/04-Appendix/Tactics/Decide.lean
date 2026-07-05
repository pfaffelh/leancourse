import Lean
import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`decide`" =>
%%%
tag := "decide"
%%%

*Summary:* `decide` closes a goal whose statement is *decidable* --
i.e. the typeclass `Decidable P` finds a proof or refutation of `P`
by computation.  Typical candidates are concrete arithmetic
equalities and inequalities, membership in a finite set, divisibility,
and propositional logic on concrete inputs.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ (2 + 2 : ℕ) = 4`
  + `decide`
  + (no goals)
* + `⊢ (3 : ℕ) ∣ 12`
  + `decide`
  + (no goals)
:::

*Remarks:*

* `decide` performs *reduction*: it reduces the decision procedure
  on the given inputs.  For large inputs it can be slow (or time
  out); for general arithmetic, prefer `omega` or `norm_num`.
* For propositions that depend on a variable (e.g. `∀ n, P n`),
  `decide` will not work -- it needs concrete inputs.
* `decide` reduces the `Decidable` instance in the *kernel*, so whether
  it succeeds depends on *how that instance is implemented*, not just on
  the proposition being decidable. Mathlib's `Decidable (IsSquare n)`,
  for instance, uses `Nat.sqrt`, which the kernel does not reduce, so
  `decide` gets stuck on `IsSquare 2` -- even though it is perfectly
  decidable. Giving the same proposition a kernel-reducible instance (a
  bounded search) makes `decide` work again (see below). The underlying
  class is the {ref "decidable-typeclass"}[`Decidable` typeclass].
* `native_decide` uses the *compiled* evaluator instead of kernel
  reduction, so it closes goals like `¬ IsSquare 2` that `decide`
  cannot -- at the cost of trusting the compiler (it enlarges the
  trusted base).



::::keepEnv
:::example " "
```lean
example : (2 + 2 : ℕ) = 4 := by decide
example : (3 : ℕ) ∣ 12 := by decide
example : ¬ ((10 : ℕ) = 20) := by decide
```

:::
::::

Whether `decide` succeeds is a property of the *instance*, not just of the proposition. Mathlib's `Decidable (IsSquare n)` uses `Nat.sqrt`, which the kernel cannot reduce, so `decide` gets stuck. Supplying a *kernel-reducible* instance (a bounded search, here made to win by priority) closes the very same goals:

::::keepEnv
:::example " "
```lean
def decSquare (n : ℕ) : Decidable (IsSquare n) :=
  decidable_of_iff (∃ k, k ≤ n ∧ k * k = n) <| by
    constructor
    · rintro ⟨k, -, hk⟩; exact ⟨k, hk.symm⟩
    · rintro ⟨r, hr⟩; exact ⟨r, by nlinarith [hr], hr.symm⟩

attribute [local instance 10000] decSquare

example : ¬ IsSquare (2 : ℕ) := by decide
example :   IsSquare (9 : ℕ) := by decide
```

:::
::::
