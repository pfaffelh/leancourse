import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

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

Constructing a term of type `ℕ` is easier (`0 : ℕ)` is accepted by Lean for this construction) than constructing a term of type `∀ (n : ℕ) (h₁ : n > 2) (h₂ : Even n), ∃ (i j : ℕ), (Prime i) ∧ (Prime j) ∧ (n = i + j)`, for which we would require proving Goldbach's conjecture and implementing the proof in Lean.

Since we are already speaking about fundamentals: For a large part, it is safe to think of Types as Sets. Recall that it leads to [logical self-inconsistencies](https://en.wikipedia.org/wiki/Russell%27s_paradox) if we allow for something like the set/type of all sets/types. For this reason, the `Type` universe is split into levels, such as `Type 0 : Type 1`, saying that the type `Type 0` (of all objects in level 0) is of `Type 1`, i.e., we are moving up a ladder when constructing more complex types. The coresponding [idea](https://en.wikipedia.org/wiki/Von_Neumann_universe)  goes back to [von Neumann](https://en.wikipedia.org/wiki/John_von_Neumann) and [Ernst Zermelo](https://en.wikipedia.org/wiki/Ernst_Zermelo).

# Mathlib
%%%
tag := "mathlib"
%%%

The Lean-library which contains many mathematical results is called _Mathlib_. On its [documentation page](https://leanprover-community.github.io/mathlib4_docs/index.html) you can search for some results and concepts. (More precisely, you can search names of definitions, lemmas and theorems.) You will find results about e.g. [Real numbers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html#Real), [Groups](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#Group) in algebra, [Topology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html#TopologicalSpace) and [Measure Theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Defs.html).

Another way to search Mathlib is [Moogle](https://www.moogle.ai/) and [Loogle](https://loogle.lean-lang.org/) (which you also have in `vscode` when clicking on the `∀` sign.)

# First steps
%%%
tag := "firststeps"
%%%

Let us start with some simple examples in order to explain the first tactics in Lean. We will deal here with
* intro
* exact
* apply
* rw
* simp
* apply?
* have
* refine
* obtain

More tactics are found in Chapter xxx.

## `intro`, `exact`, `apply` and `rw`

:::paragraph
Let us start with a very simple `example`. If we want to prove the statement `P → P` (i.e. `P` implies `P`) we enter the following:

```lean
example (P : Prop) : P → P := by
  sorry
```
Depending on the position of the cursor, you will find the corresponding *proof state*. If the cursor is directly after `by`, the initial *proof state* is seen. It is important to know that behind `⊢` (called [turnstile](https://en.wikipedia.org/wiki/Logical_consequence)) stands the assertion, and everything above are hypotheses. (In the case shown, this is only the fact that `P` is an assertion/proposition.) This representation thus corresponds exactly to the assertion. If the cursor is after the `sorry`, there is now **no goals**, but the `sorry` tactic is only there to prove unproven assertions without further action, and a warning is issued in `vscode`. If you delete the `sorry` and replace it with an `intro hP` followed by `exact hP`, we get
```lean
example : P → P := by
  intro hP
  exact hP
```
So we have transformed the statement `P → P` into a state where we have to assume `hP : P` and conclude `P`. The desired **no goals** appears.
:::

:::paragraph
The `apply` tactics is similar, but does not necessarily need to close the goal. Let us see how it works:
```lean
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR
  apply hPQ
  exact hP
```
Here, if the goal is `R`, and you have a proof `hQR : Q → R`, we only have to show `Q` and this transformation is done using `apply hQR`.

In fact, apply works iteratively. This means that `apply hQR; apply hPQ; exact hP` can be combined into
```lean
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  apply hQR (hPQ hP)
```
(Here, `hPQ hP` is a proof for `Q`, since we apply `P → Q` to a proof of `P`, which gives `Q`.)
:::

:::paragraph
We note that the above example is equivalent to
```lean
example : ∀ (P : Prop), P → P := by
  intro P
  intro hP
  exact hP
```
So if we have a ∀ in the goal, we make progress by using `intro`.
:::

:::paragraph
Sometimes, we have statements of equality `x = y` or `P ↔ Q`, so we would like to use the one instead of the other. This works using `rw`:
```lean
example (hQ : Q) (hPQ : P ↔ Q) : P := by
    rw [hPQ]
    exact hQ
```
Here, we use `rw` to transform the goal `P` to the rewritten goal `Q`. If we want to use `rw` reversely, we write `rw [← hPQ]`, and we can use `rw` also in hypothesis by writing e.g. `rw [hPQ] at hP`. Here is an example.
```lean
example (hQ : Q) (hPQ : P ↔ Q) : P := by
    rw [← hPQ] at hQ
    exact hQ
```
:::

## `apply?` and `simp`

Of course, we want to make use of known facts when proving new ones. There are two main search functions built into our work: `simp?` and `apply?`. The first is based on `simp`, which works using a collection of simplification rules, which are searchable using `simp?`. Here is an example:
```lean
example : (0 < 1) := by
  simp?
```
Lean suggests `Try this: simp only [Nat.lt_one_iff, pos_of_gt]`, which is taken to our code when we click on it.

In fact, the same example can be solved using library search using `apply?`. Here, Lean searches its library for possible results, and often outputs very many results and the remaining goals. Here, it is simple:
```lean
example : (0 < 1) := by
  apply?
```
where Lean suggests `Try this: exact Nat.one_pos`.

## `have`, `refine`, and `use`

:::paragraph
In order to have some proper example, let us introduce `Even` and `Odd`. In fact, for a definition of `Even`, we can type
```lean (name := even)
#print Even
```
which results in
```leanOutput even
def Even.{u_2} : {α : Type u_2} → [inst : Add α] → α → Prop :=
fun {α} [Add α] a => ∃ r, a = r + r
```
:::

:::paragraph
Assume we cannot prove our goal in one step, but need some intermediate result. In this case, we have the `have` tactics. We simply claim what we need as an intermediate step. At the moment, we leave the rest using `sorry`.
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    sorry
  sorry
```
We come to our intermediate result later, but first want to use it in the rest of the proof. However, we have to disentangle the ∃ statement in `h`. Often, we have to take apart what we are given. Note that `∃ (n : ℕ), Even n` consists of `(n : ℕ)` and a proof of `Odd `, i.e. a pair of objects, and pairs in Lean are gives using `⟨_, _⟩`. We use `obtain` in order to get the two elements of the pair:
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    sorry
  obtain ⟨n, hn⟩ := h
  sorry
```
Recall that `hn` itself is an ∃-statement. This means we can use a nested version:
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    sorry
  obtain ⟨n, ⟨k, hk⟩⟩ := h
  sorry
```
Now we can use that `n` is `Even` and therefore would like to `use` that `n * n = (2*k) * (2*k) = 4*k*k` for showing that `n * n` is even. In order to see what we have to show, let us simplify using the definition of `Even`:
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    sorry
  obtain ⟨n, ⟨k, hk⟩⟩ := h
  simp [Even]
  sorry
```
Now we can use `n` from above, and `r = 2*k*k`. This works with `use`:
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    sorry
  obtain ⟨n, ⟨k, hk⟩⟩ := h
  simp [Even]
  use n
  use 2*k*k
  sorry
```
:::

:::paragraph
The rest should be easy, since it only remains a calculation. Here, we use `rw` and the `ring` tactics, which can do calculations within a `ring` (in fact in a monoid):
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    sorry
  obtain ⟨n, ⟨k, hk⟩⟩ := h
  simp [Even]
  use n
  use 2*k*k
  rw [hk]
  ring
```
It remains to show the intermediate step. Here, we have to give Lean a pair, i.e. some `n` as well as a proof that `Even n`. This can not only be done using `use` as above, but also using `refine`, which is able to make a pair from two separate objects. Assume ww want to use that `Even 48`, but do not have a proof yet. Then we write a `?_`, which stands for a hole in the proof which is to be filled in later:
```lean
example : ∃ (n : ℕ), Even n := by
  refine ⟨48, ?_⟩
  sorry
```
For a proof of `Even 48`, we need to find `24` and a proof that `48 = 24 + 24`. Let us again work with `?_`:
```lean
example : ∃ (n : ℕ), Even n := by
  refine ⟨48, ⟨24, ?_⟩⟩
  ring
```
(In fact, the last step can also be solved by `rfl`, which means that the goal is true by definition.)

In total, we have the full example:
```lean
example : ∃ (n : ℕ), Even (n * n) := by
  have h : ∃ (n : ℕ), Even n := by
    refine ⟨48, ⟨24, by rfl⟩⟩
  obtain ⟨n, ⟨k, hk⟩⟩ := h
  use n, 2*k^2
  rw [hk]
  ring
```
:::


# Names of `Mathlib` Results
%%%
tag := "names"
%%%

Names like `zero_add, add_zero, one_mul, add_assoc, succ_ne_zero, lt_of_succ_le,...` seem cryptic. It is clear that individual relatively understandable abbreviations (`zero, one, mul, add, succ,...`) are separated by `_`. In general, the following two rules apply to naming:

- The goal of the statement to be proven is described; if hypotheses are added in the name, then with `of_`. The statement `lt_of_succ_le` is therefore an `<` statement, where `succ ≤` applies. In fact:
```lean (name := lt_of_succ_le)
#check Nat.lt_of_succ_le
```
results in
```leanOutput lt_of_succ_le
Nat.lt_of_succ_le {n m : ℕ} (h : n.succ ≤ m) : n < m
```
This way, you can often guess the names of statements that you want to use.

# Exercises
%%%
tag := "exercises"
%%%

It is now time to move to the exercises. So, proceed to `vscode` (or `gitpod`), copy the exercises folder and start coding. Further hints on tactics etc is given within the exercises. Tactics are given in alphabetical order in the next chapter.
