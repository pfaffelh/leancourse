import Mathlib

/-!
# (witness) 1.2-a -- The quantifiers `∀` and `∃`

*Notes chapter 1.2, week 3.*

Chapter 1.2 reads `∀ (n : ℕ), n < n + 1` as a *dependent function
type*: a proof of it is a function taking `n` to a proof of
`n < n + 1`. This sheet is the practical side of that. Everything is
a statement about terms of some type `α`.

## Tactics introduced here

| tactic                | use it when                                    |
|-----------------------|------------------------------------------------|
| `intro x`             | goal `∀ x, P x`: fix an `x`, prove `P x`       |
| `h a`                 | `h : ∀ x, P x`: a proof of `P a`               |
| `specialize h a`      | the same, replacing `h` in place               |
| `use a`               | goal `∃ x, P x`: offer `a` as the witness      |
| `⟨a, h⟩`              | the same, as a term                            |
| `obtain ⟨x, hx⟩ := h` | `h : ∃ x, P x`: name the witness and its proof |
-/

variable (α : Type) [Inhabited α]
variable (P Q : α → Prop)
variable (R : α → α → Prop)
variable (S T : Prop)

/-! ## A type to quantify over

`P : α → Prop` is a *predicate*: for each `x : α` it gives a
proposition `P x`.

For `∃` to say anything we need `α` to have at least one element.
`[Inhabited α]` above guarantees that, and names the element
`default`. The square brackets are a *typeclass* argument, chapter
1.4 and sheet `1.4-a`; here you need nothing beyond the name. -/

/-! ## `∀` in the goal

`intro x` fixes an arbitrary `x` and leaves the goal `P x`. This is
the same `intro` as on `L-a`, because `P → Q` is the special case of
`∀` where the body does not mention the bound variable. -/

example : ∀ x : α, x = x := by
  intro x
  rfl

/-! ## `∀` in a hypothesis

`h : ∀ x, P x` *is* a function. Apply it: `h a : P a`. -/

example (h : ∀ x, P x) : P default := by
  exact h default

/-! `specialize h default` does the same but overwrites `h`, which is
shorter when you need the instance once and the general statement no
longer. -/

example (h : ∀ x, P x) : P default := by
  specialize h default
  exact h

/-! ## `∃` in the goal

`use a` offers `a` as the witness and leaves `P a`. -/

example (h : P default) : ∃ x, P x := by
  use default

/-! A proof of `∃ x, P x` is a pair: a witness, and a proof about it.
So the anonymous constructor works too. -/

example (h : P default) : ∃ x, P x :=
  ⟨default, h⟩

-- Exercise 1) Where there is one for all, there is one.
example : (∀ x, P x) → (∃ x, P x) := by
  intro h
  exact ⟨default, h default⟩

-- Exercise 2) Quantifiers in series.
example (h : ∀ x, R x x) : ∀ x, ∃ y, R x y := by
  intro x
  exact ⟨x, h x⟩

/-! ## `∃` in a hypothesis

Being a pair, it is taken apart with `obtain`, exactly as `∧` was on
`L-b`. You get a name for the witness and a name for its proof. -/

example (h : ∃ x, ∀ y, R x y) : ∃ x, R x x := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx x⟩

/-! ## Both directions of an `↔`

`hST : S ↔ T` splits into `hST.mp : S → T` and `hST.mpr : T → S`
(also written `.1` and `.2`). -/

example (hS : S) (hST : S ↔ T) : T := by
  exact hST.mp hS

-- Exercise 3) One `obtain`, one `.mp`.
example (f : α → α) (h : ∃ x, P x) (hx : ∀ x, P x ↔ Q (f x)) :
    ∃ y, Q y := by
  obtain ⟨x, hxP⟩ := h
  exact ⟨f x, (hx x).mp hxP⟩

-- Exercise 4) Three `intro`s, then one `.mpr`.
example (h : ∀ x, P x ↔ ∃ y, R x y) : ∀ y, ∀ x, R x y → P x := by
  intro y x hxy
  exact (h x).mpr ⟨y, hxy⟩

/-! ## Negating a quantifier

The four rules below are the quantifier half of what `L-e` did for
`∧`, `∨` and `→`. The tactic `push Not` applies them for you; here
you prove them, so do not use it.

Three of the four are constructive. The fourth is exercise 8. -/

-- Exercise 5) Push the `¬` inwards.
example : (∀ x, ¬ P x) → ¬(∃ x, P x) := by
  intro h ⟨x, hx⟩
  exact h x hx

-- Exercise 6) And back out again.
example : ¬(∃ x, P x) → ∀ x, ¬ P x := by
  intro h x hx
  exact h ⟨x, hx⟩

-- Exercise 7) One witness is enough to refute a `∀`.
example : (∃ x, ¬ P x) → ¬(∀ x, P x) := by
  intro ⟨x, hx⟩ h
  exact hx (h x)

-- Exercise 8) *Extra, for after `L-e` in week 4.* This is the one
-- direction that is not constructive: knowing that not every `x`
-- satisfies `P` does not hand you an `x` that fails it. You need
-- `by_contra` twice.
example : ¬(∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  by_contra hc
  apply h
  intro x
  by_contra hx
  exact hc ⟨x, hx⟩
