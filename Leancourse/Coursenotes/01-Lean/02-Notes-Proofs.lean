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

# Foundation
%%%
tag := "foundation"
%%%

In Lean every object has a type. Types itself fall into several categories, called universes. There are two main universes, called `Prop` and `Type`. Any mathematical statement comes with a claim and its proof. Say we want to claim something, such as [Goldbach's conjecture](https://en.wikipedia.org/wiki/Goldbach%27s_conjecture):

```lean
theorem goldbach : ∀ (n : ℕ) (h₁ : n > 2) (h₂ : Even n),
    ∃ (i j : ℕ), (Prime i) ∧ (Prime j) ∧ (n = i + j) := by
  sorry
```

we speak about a term `∀ (n : ℕ) (h₁ : n > 2) (h₂ : Even n), ∃ (i j : ℕ), Prime i ∧ Prime ∧ (n = i + j)` of type `Prop`, which constitutes its own type. A term of this type (which sould repalce the `sorry` in the above Lean code) is equivalent to a `proof` of Goldbach's conjecture.

This is to say:

**Types as theorems, terms as proofs!**

Constructing a term of type `ℕ` is easier (`0 : ℕ` is accepted by Lean for this construction) than constructing a term of type `∀ (n : ℕ) (h₁ : n > 2) (h₂ : Even n), ∃ (i j : ℕ), (Prime i) ∧ (Prime j) ∧ (n = i + j)`, for which we would require proving Goldbach's conjecture and implementing the proof in Lean.

Since we are already speaking about fundamentals: For a large part, it is safe to think of Types as Sets. Recall that it leads to [logical self-inconsistencies](https://en.wikipedia.org/wiki/Russell%27s_paradox) if we allow for something like the set/type of all sets/types. For this reason, the `Type` universe is split into levels, such as `Type 0 : Type 1`, saying that the type `Type 0` (of all objects in level 0) is of `Type 1`, i.e., we are moving up a ladder when constructing more complex types. The coresponding [idea](https://en.wikipedia.org/wiki/Von_Neumann_universe)  goes back to [von Neumann](https://en.wikipedia.org/wiki/John_von_Neumann) and [Ernst Zermelo](https://en.wikipedia.org/wiki/Ernst_Zermelo).

# Mathlib
%%%
tag := "mathlib"
%%%

The Lean-library which contains many mathematical results is called _Mathlib_. On its [documentation page](https://leanprover-community.github.io/mathlib4_docs/index.html) you can search for some results and concepts. (More precisely, you can search names of definitions, lemmas and theorems.) You will find results about e.g. [Real numbers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html#Real), [Groups](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#Group) in algebra, [Topology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html#TopologicalSpace) and [Measure Theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Defs.html).

Another way to search Mathlib is [Moogle](https://www.moogle.ai/) and [Loogle](https://loogle.lean-lang.org/) (which you also have in `vscode` when clicking on the `∀` sign.)

# Some keywords
%%%
tag := "keywords"
%%%

Let us start with a very simple `example` and the
tactics `intro` and `exact`. If we want to prove the statement `P → P` (i.e. `P` implies `P`) we enter the following:

```lean
example (P : Prop) : P → P := by
  sorry
```

On the right side, depending on the position of the cursor, you will find the *proof state*. If the cursor is directly after `by`, the initial *proof state* is seen. It is important to know that behind `⊢` (called [turnstile](https://en.wikipedia.org/wiki/Logical_consequence)) stands the assertion, and everything above are hypotheses. (In the case shown, this is only the fact that `P` is an assertion/proposition.) This representation thus corresponds exactly to the assertion. If the cursor is after the `sorry`, there is now **no goals**, but the `sorry` tactic is only there to prove unproven assertions without further action, and a warning is issued in `vscode`. If you delete the `sorry` and replace it with an `intro hP` followed by `exact hP`, we get
```lean
example : P → P := by
  intro hP
  exact hP
```
So we have transformed the statement `P → P` into a state where we have to assume `hP : P` and conclude `P`. This can now easily be solved using `assumption`, and the desired **no goals** appears.


```lean (name := even)
#print equations Even
```


#print Odd


example (n : ℕ) :  (Even n) ∨ (Odd n) := by
  apply? -- gives exact Nat.even_or_odd n

```lean (name := singletonList)
#check fun x => [x]
```
```leanOutput singletonList
fun x => [x] : ?m.9 → List ?m.9
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
