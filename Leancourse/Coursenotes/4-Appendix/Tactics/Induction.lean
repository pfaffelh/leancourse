import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`induction`" =>
%%%
tag := "induction"
%%%

*Summary:*

Inductive types allow the possibility of proving statements about them by means of induction. This includes, for example, the usual case of complete induction over natural numbers.

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `n : ℕ` {br}[] ⊢ n = 0 + n
  + induction n with {br}[] `| zero ↦ ?_` {br}[] | `succ n hn ↦ ?_`
  + ⊢ 0 = 0 + 0 {br}[] hn : n = 0 + n {br}[] ⊢ n + 1 = 0 + (n + 1)
:::

::::keepEnv
:::example " "
```lean
example (n : ℕ) : n = 0 + n := by
  induction n with
  | zero =>
    rfl
  | succ n hn =>
    rw [← add_assoc, ← hn]
```
:::
::::

*Remarks:*

The goals show `0` and `n + 1` rather than `Nat.zero` and `Nat.succ n`, because Lean uses a variant of the recursor `Nat.rec` for `ℕ` that is stated with `0` and `n + 1`. The variant used by `induction` can be chosen with `using`, and three variants come up constantly in mathematics.

*Strong induction.* With `Nat.strong_induction_on`, the hypothesis is the statement for *all* smaller numbers, not only for the predecessor:

```lean
example (n : ℕ) (h : 0 < n) : 1 ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => omega
```

Here `ih` is the statement for every `m < n`.

*Induction from a starting value.* With `Nat.le_induction`, a statement about all `n ≥ k` is proved for `k` and then from `n` to `n + 1`:

```lean
example (n : ℕ) (hn : 2 ≤ n) : 2 ≤ n * n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => nlinarith
```

*Generalizing.* `induction n generalizing m` keeps `m` universally quantified in the induction hypothesis. This is needed when the step uses the hypothesis for a different `m` than the one in the goal:

```lean
example (m n : ℕ) (h : m + n = 0) : m = 0 := by
  induction n generalizing m with
  | zero => simpa using h
  | succ k ih => omega
```

*Functional induction.* For a statement about a recursive function, `fun_induction f x` follows the branches of the definition of `f`: one goal per branch, with an induction hypothesis for each recursive call.

```lean
def sumUpTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumUpTo n

example (n : ℕ) : 2 * sumUpTo n = n * (n + 1) := by
  fun_induction sumUpTo n with
  | case1 => rfl
  | case2 n ih => linarith
```

For a function with several base cases or a recursion that is not structural (`fib`, Euclid's algorithm), this saves the work of finding the right induction by hand.
