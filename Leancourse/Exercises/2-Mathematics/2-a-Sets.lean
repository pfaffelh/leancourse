import Mathlib

/-!
# 2.2-a -- Sets

*Notes chapter 2.2, week 11.*

## Introduced here

| notation                    | meaning                                        |
|-----------------------------|------------------------------------------------|
| `s ⊆ t`, `s ∩ t`, `s ∪ t`   | subset, intersection, union                    |
| `sᶜ`, `s \ t`               | complement, difference                         |
| `⋃ i, s i`                  | union of a family; `Set.mem_iUnion`            |
| `∑ i ∈ Finset.range n, f i` | `f 0 + ⋯ + f (n - 1)`; `Finset.sum_range_succ` |

## Tactics from earlier sheets

| sheet   | tactics                     |
|---------|-----------------------------|
| `L-a`   | `intro`, `exact`            |
| `L-b`   | `constructor`, `obtain`     |
| `1.1-a` | `rfl`, `rw`, `induction`    |
| `L-e`   | `by_contra`                 |
| `L-f`   | `rintro`                    |
| `L-g`   | `simp only`                 |
| `1.1-c` | `simp`, `ring`              |
| `1.5-a` | `ext`                       |
-/

variable (α β : Type)

/- # Sets in Lean

Informally, types and sets are similar things, both are collections of some kind. However, since Lean is strict, we have to be careful with the details. Let us see what a Set is in Lean:

-/

#print Set

/- Most importantly, `s : Set α` is equivalent to some function `s : α → Prop`. The idea is that `x ∈ s` iff `s x` is True. In this sense, you can apply the set `s` to some `x : α` and will hear back `True` if `x ∈ s` and `False` otherwise. -/

variable (s t u v : Set α) -- s t u v are sets within type `α`:

open Set

/- # Subset, intersection, union, etc


Here are some mathematical facts, which are true by definition:

-/
theorem subset_def : s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := by
  rfl

theorem mem_union (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  rfl

theorem mem_inter (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  rfl

theorem empty_def : ∅ = { _x : α | False }  := by
  rfl

theorem univ_def : Set.univ = { _x : α | True }  := by
  rfl

theorem mem_def (p : α → Prop) : x ∈ {x | p x } ↔ p x := by
  rfl

theorem mem_complement_def (s : Set α) : x ∈ sᶜ ↔ x ∉ s := by
  rfl

theorem setdiff_def (s t : Set α) : s \ t = s ∩ tᶜ := by
  rfl

-- Exercise 1
example : s ⊆ s := by
  sorry

-- Exercise 2
example : s ∩ t ⊆ s := by
  sorry

-- Exercise 3
example : s ⊆ s ∪ t := by
  sorry

-- Exercise 4
example (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  sorry

-- Exercise 5
example : s \ t ⊆ s := by
  sorry

-- Exercise 6
example : s \ t ⊆ tᶜ := by
  sorry

-- Exercise 7
example : (∀ x, x ∈ s) ↔ ¬∃ x, x ∈ sᶜ := by
  sorry

/-
# Extensionality

When are two sets equal? Well, if they contain the same elements. This is what extensionality is about.

If the goal is `⊢ s = t` where `s` and `t` are `Set α`, then `ext x` creates `x : α` and changes
the goal to `x ∈ s ↔ x ∈ t`.

Since we will be dealing with sets below anyway, we start with a different example. Two functions are equal, if all values are equal.

-/

example (f g : α → β) : f = g ↔ ∀ x, f x = g x := by
  constructor
  · intro h x
    rw [h]
  · intro h
    ext x
    exact h x

/- For sets this is similar, and the proof is the same, letter by letter: -/

example : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by
  constructor
  · intro h x
    rw [h]
  · intro h
    ext x
    exact h x

-- Exercise 8
example : s = t ↔ (s ⊆ t ∧ t ⊆ s) := by
  constructor
  · sorry
  · sorry

-- Exercise 9
example : s = sᶜᶜ := by
  sorry

-- Exercise 10
example : s = ∅ ↔ s ⊆ ∅ := by
  sorry

/-! # Unions of families and finite sums

`⋃ n, s n` is the union of the sets `s 0, s 1, …`. Membership is an
`∃`: `x ∈ ⋃ n, s n ↔ ∃ n, x ∈ s n`, which is `Set.mem_iUnion`.
`∑ i ∈ Finset.range n, f i` is the finite sum `f 0 + ⋯ + f (n - 1)`
from section *Finite sets and sums* of chapter 2.2. -/

-- Exercise 11) `ext x`, `simp only [Set.mem_iUnion, Set.mem_Icc,
-- Set.mem_Ici]`, then `exists_nat_ge`.
example : (⋃ n : ℕ, Set.Icc (0 : ℝ) n) = Set.Ici 0 := by
  sorry

-- Exercise 12) Induction on `n`, with `Finset.sum_range_succ`.
example (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  sorry
