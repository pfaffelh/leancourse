import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Proofs in Lean" =>
%%%
htmlSplit := .never
tag := "proof"
%%%


In Section 1, we have already dealt with the installation of Lean and `vscode`. Here follows a short, incoherent introduction. We start with a very simple example. The tactics `intro` and `exact` can be found in
Chapter. If we want to prove the statement `P → P` (i.e. `P` implies `P`) we enter the following on the left side in `vscode`:
```
example (P : Prop) : P → P := by
  sorry
```
On the right side, depending on the position of the cursor, you will find the *proof state*. If the cursor is directly after `by`, the *proof state* is seen. It is important to know that behind `⊢` stands the assertion, and everything above are hypotheses. (In the case shown, this is only the fact that `P` is an assertion/proposition.) This representation thus corresponds exactly to the assertion. If the cursor is after the `sorry`, there is now **no goals**, but the `sorry` tactic is only there to prove unproven assertions without further action, and a warning is issued in `vscode`. If you delete the `sorry` and replace it with an `intro hP`, we get
```lean
example : P → P := by
  intro hP
  exact hP
```
So we have transformed the statement `P → P` into a state where we have to assume `hP : P` and conclude `P`. This can now easily be solved using `assumption`, and the desired **no goals** appears. The `assumption` tactic searches for a hypothesis that is identical to the statement and concludes the proof. The `exact` tactic is somewhat different. Here you have to know exactly which hypothesis is meant and can use `exact hP` to conclude the proof.

```lean
#print Even
#print Odd

example (n : ℕ) :  (Even n) ∨ (Odd n) := by
  apply? -- gives exact Nat.even_or_odd n
```


```lean
example : ∃ (x : ℕ), x^2 = 9 := by
  exact ⟨3, by rfl⟩
```

```lean
example : ∃ (x : ℕ), x^2 = 9 := by
  use 3
  rfl
```

```lean
example : ∀ (x : ℝ), 0 ≤ x^2 := by
  intro x
  exact sq_nonneg x
```




intro apply exact simp refine obtain apply?

sets functions

forall as applying function

exists as a pair/tuple

subtypes

use

# Names of `Mathlib` Results
%%%
tag := "names"
%%%

Names like `zero_add, add_zero, one_mul, add_assoc, succ_ne_zero, lt_of_succ_le,...` seem cryptic. It is clear that individual relatively understandable abbreviations (`zero, one, mul, add, succ,...`) are separated by `_`. In general, the following two rules apply to naming:

- The goal of the statement to be proven is described; if hypotheses are added in the name, then with `of_`. The statement `lt_of_succ_le` is therefore an `<` statement, where `succ ≤` applies. In fact:
```
#check @lt_of_succ_le
```
results in
```
  lt_of_succ_le : ∀ {a b : ℕ}, a.succ ≤ b → a < b
```
This way, you can often guess the names of statements that you want to use.
