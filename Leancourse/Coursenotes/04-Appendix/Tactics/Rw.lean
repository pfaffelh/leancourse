import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`rw`" =>
%%%
tag := "rw"
%%%

*Summary:* `rw` stands for *rewrite*. For `rw h` to work, `h` must be an expression of the type `h : x=y` or `h : A↔B`. In this case, `rw h`  replaces every term that is syntactically identical to `x` (or `A`) is replaced by `y` (or `B`). This also works if `h` is an already proven result (i.e. a `lemma` or `theorem`). With `rw ← h` is applied from right to left. (In the above example, `y` is replaced by `x` and `B` by `A`.)

*Examples*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + h : P ↔ Q {br}[] ⊢ P
  + `rw [h]`
  + h : P ↔ Q {br}[] ⊢ Q
* + h : P ↔ Q {br}[] ⊢ Q
  + `rw [← h]`
  + h : P ↔ Q {br}[]  ⊢ P
* + h : P ↔ Q {br}[] hP : P
  + `rw [h] at hP`
  + h : P ↔ Q {br}[] hP : Q
* + h : P ↔ Q {br}[] hQ : Q
  + `rw [← h] at hQ`
  + h : P ↔ Q {br}[] hQ : P
* + k m: ℕ {br}[] ⊢ k + m + 0 = m + k + 0
  + `rw [add_comm]`
  + k m : ℕ {br}[] ⊢ 0 + (k + m) = m + k + 0
* + k m : ℕ {br}[] ⊢ k + m + 0 = m + k + 0
  + `rw [add_comm k m]`
  + ⊢ m + k + 0 = m + k + 0
* + k m : ℕ {br}[] ⊢ k + m + 0 = m + k + 0
  + `rw [← add_comm k m]`
  + ⊢ k + m + 0 = k + m + 0
* + k m : ℕ {br}[] ⊢ k + m + 0 = m + k + 0
  + `rw [add_zero, add_zero]`
  + k m : ℕ {br}[] ⊢ k + m = m + k
:::


For the last four examples, you first need to know that add_comm and add_zero are the statements

```
lemma add_comm : ∀ {G : Type} [_inst_1 : add_comm_semigroup G] (a b : G),
a + b = b + a
add_zero : ∀ {M : Type} [_inst_1 : add_zero_class M] (a : M), a + 0 = a
```

In the first of the four examples, `rw` applies to the first occurrence of a term of type `a + b`. Due to the internal bracketing, `(k + m) + 0` is on the left side, so that the `rw` results in a `0 + k + m`. If you want to use the commutativity in the term `k + m`, you need the second (or third) example, where `rw add_comm k m` leads to the desired progress. In the last example, the two `+ 0` terms are first eliminated by `rw add_zero`.

*Notes*

* `rw` is used very often in practice to apply statements from the `mathlib` (at least if they are of the type `=` or `↔`).
* If you want to combine several `rw` commands, you can do so in square brackets, for example `rw [h1, h2]` or `rw [h1, ←h2, h3]`.
* `rw` immediately executes a `refl` after its application. This leads to the second and third examples of the applications of `add_comm` and `add_zero` that the new proof state is not as specified, but *no goals*.
* If you do not want to perform a `rw` in sequence (as in the double elimination of the `+0` above), you can use `nth_rewrite` to rewrite the second occurrence of a term.
* The `rw` tactic does not work when it comes after a *binder*, which could be a `∀ ∃ ∑`. In this case, `simp_rw` will hopefully help.
* `rw?` *searches* for a rewrite that applies to the goal: it lists library equations and `↔`-statements whose left- (or, with `←`, right-) hand side matches a subterm, and you pick one. Useful when you are sure a rewrite should exist but do not know its name.

::::keepEnv
:::example " "
```lean
example (P : Prop) : False → P := by
  exact False.elim
```
:::
::::
