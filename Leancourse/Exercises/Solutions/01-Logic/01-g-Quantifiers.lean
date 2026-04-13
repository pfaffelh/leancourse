import Mathlib

/-
  At the beginning of your studies in mathematics, you learn the symbols ∀ and ∃. These are also available here. To be able to use them, we need the tactics `intro`, `specialize` and `use`.

  In the sequel, we consider logical statements (of type `Prop`) that depend on a variable. This variable, in turn, has a type that we call `α`:
  -/


variable (α : Type)

/- To use the ∃-quantifier in a meaningful way, we have to assume that `α` is not an empty type, that there is at least one term of type `α`. We do this in the statements with the assumption `Inhabited α`.
To understand this, let's take a look at `Init/Logic.lean`:
```
class Inhabited (α : Sort u) :=
(default : α)
```
(where `Sort u` is shorthand for a type, which could also be `Prop`.) This means that if `Inhabited α` is true, then `α` has an element, which is called `default`. We will see below how we can use this.

-/

-- We start by introducing some terms:
variable (P Q : α → Prop )
variable (R : α → α → Prop )
variable (S T: Prop)

-- First, we introduce the ∀ quantifier. If it appears in a goal, we can use `intro` to introduce a term of the corresponding type. This leads to a situation that we already know:

example : (∀ (x : α), True) := by
  intro x
  trivial

-- If `∀ x` occurs in a hypothesis `h`, then `h x` means the evaluation of the hypothesis for the concrete `x`.
example (inh : Inhabited α) (h : ∀ x, P x) : (P default) := by
  exact h default

-- Alternatively, we can change the corresponding assumption by replacing `∀ x` with the substitution of a specific `x`. This is done with `specialize`.
example (inh : Inhabited α) (h : ∀ x, P x) : (P default) := by
  specialize h default
  exact h

-- By the way, an easy way to keep the old hypothesis is to use the already-known `obtain` tactic:
example (inh : Inhabited α) (h : ∀ x, P x) : (P default) := by
  obtain h1 := h default
  exact h1

-- The resolution of a goal with `∃ x` is done with the tactic `use`. Here, a specific `x` is used that is known to satisfy the subsequent proposition.
example (inh : Inhabited α) (h : P default) : (∃ x, P x) := by
  use default

-- Alternatively, we use the fact that for a statement `∃ x, P x`, there must be an `x` as well as a proof of `P x`. This is because an ∃-statement is a product (or logical ∧-link), and we can use the `⟨ , ⟩` notation:
example (inh : Inhabited α) (h : P default) : (∃ x, P x) := by
  exact ⟨default, h⟩

-- Of course, quantifiers can also be connected in series. In the following example, ∃ is also in an assumption. This is resolved using the `cases'` tactic.
example (_ : Inhabited α) (h : ∃ x, ∀ y, R x y) : ∃ x, R x x := by
  cases' h with x h
  use x
  exact h x   -- or exact ⟨ x, h x ⟩,

-- In fact, the `∃` in an assumption is equvalent to a pair: It gives an object which is assumed to exists, and a proof that it satisfies what comes after the `∃`.
-- In addition, the proof in the last step can be abbreviated_
example (inh : Inhabited α) (h : ∃ x, ∀ y, R x y) : ∃ x, R x x := by
  obtain ⟨x, hx⟩ := h
  use x, (hx x)

-- Exercise 1: If `P x` is true for all `x`, then it is also true for one.
example (inh : Inhabited α) : (∀ x, P x) → (∃ x, P x) := by
  intro h
  use default
  exact h default

-- Exercise 2:
example (h : ∀ x, R x x) : (∀ x, ∃ y, R x y) := by
  intro x
  use x
  exact h x

/-
  In the following example, you should note the following example of how to extract the two directions from a `↔`-statement. Here, instead of using the noation `.1` and `.2`, you can use `.mp` (modus ponens) and `mpr` (modus ponens reverse):
  -/
example (hS : S) (hST : S ↔ T) : T := by
  exact hST.mp hS
  -- or exact hST.1 hS,

example (hT : T) (hST : S ↔ T) : S := by
  exact hST.mpr hT
  -- or exact hST.2 hT,

-- Exercise 3:
example (f : α → α) (h : ∃ x, P x) (hx : ∀ x, (P x ↔ Q (f x))) : (∃ y, Q y) := by
  obtain ⟨x, hx'⟩ := h
  use f x
  exact (hx x).mp hx'

-- Exercise 4:
example  (h : ∀ (x : α), P x ↔ ∃ (y : α), R x y) : (∀ (y : α), ( ∀ (x : α), R x y → P x )) := by
  intro y x h'
  specialize h x
  apply h.mpr
  use y

-- A few exercises follow in which you recalculate the usual rules for negating quantifiers. One tactic that automatically provides this is `push_neg`. However, you are not allowed to use this here.

-- Exercise 5:
example (P : α → Prop) : (∀ (x : α), ¬ P x) → ¬(∃ (x : α), P x ) := by
  intro h1 h2
  obtain ⟨x, hx⟩ := h2
  exact h1 x hx

-- Exercise 6:
example (P : α → Prop) : ¬(∃ (x : α), P x ) → (∀ (x : α), ¬(P x) ) := by
  intro h x hP
  apply h
  use x

-- Exercise 7:
example (P : α → Prop) : (∃ (x : α), ¬(P x) ) → ¬(∀ (x : α), P x ) := by
  intro h h1
  obtain ⟨x, hx⟩ := h
  apply hx
  exact h1 x

-- Exercise 8:
example (P : α → Prop) : ¬(∀ (x : α), P x ) → (∃ (x : α), ¬P x ) := by
  intro h
  by_contra h1
  apply h
  intro x
  by_contra h2
  apply h1
  use x
