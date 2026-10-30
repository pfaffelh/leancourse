import Mathlib

/-
# 2.3-b -- Well-foundedness and paradoxes

*Notes chapter 2.3, week 10.*

Read the chapter *Well-Foundedness and Paradoxes* first. It separates
two mechanisms: `Acc` and `WellFounded` rule out infinite descent
*inside* a type, and typing rules out `s ∈ s`. This sheet has a part
for each.

| name / tactic                         | use it when                         |
|---------------------------------------|-------------------------------------|
| `constructor` on `Acc r x`            | show all predecessors accessible    |
| `WellFounded.has_min`                 | a nonempty set has a minimal element|
| `induction n using Nat.strong_induction_on` | induct along `<` on `ℕ`       |
| `split_ifs with h`                    | split an `if` in the goal           |
| `#check_failure t`                    | `t` should not elaborate            |
-/

/- ## Part 1: Accessibility

`Acc r x` has one constructor: `x` is accessible once every `y` with
`r y x` is. `constructor` reduces `Acc r x` to that goal. -/

-- Exercise 1: `0` has no predecessor under `<`, so this is vacuous.
-- After `constructor` and `intro y hy`, `omega` sees `hy : y < 0`.
example : Acc (· < ·) (0 : ℕ) := by
  sorry

-- Exercise 2: One step further. The only `y < 1` is `0`.
example : Acc (· < ·) (1 : ℕ) := by
  sorry

-- Exercise 3: Mathlib proves it for every `n`: `Nat.lt_wfRel.wf` is
-- a `WellFounded` proof, and `.apply n` gives `Acc (· < ·) n`.
example (n : ℕ) : Acc (· < ·) n := by
  sorry

-- Exercise 4: `>` on `ℕ` is not well-founded. A well-founded relation
-- gives every nonempty set a minimal element:
-- `WellFounded.has_min : WellFounded r → ∀ s, s.Nonempty →
--    ∃ a ∈ s, ∀ x ∈ s, ¬ r x a`.
-- Apply it to `Set.univ`; then `a + 1` contradicts minimality.
example : ¬ WellFounded (· > · : ℕ → ℕ → Prop) := by
  sorry

/- ## Part 2: Well-founded induction

A function defined by well-founded recursion is reasoned about by
well-founded induction: to prove `P n`, assume `P m` for all `m < n`.
On `ℕ` this is `induction n using Nat.strong_induction_on`. After
`rw [steps2]` the goal contains an `if`; `split_ifs with h` gives one
goal per branch. -/

def steps2 (n : Nat) : Nat :=
  if h : 2 ≤ n then 1 + steps2 (n - 2) else 0

example (n : ℕ) : steps2 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [steps2]
    split_ifs with h
    · have := ih (n - 2) (by omega)
      omega
    · omega

-- Exercise 5: The same pattern.
example (n : ℕ) : 2 * steps2 n ≤ n := by
  sorry

/- ## Part 3: Self-membership and the diagonal

`∈` is typed: `x ∈ s` needs `x : α` and `s : Set α`. So `s ∈ s` is
not false but ill-formed. Uncomment and look at the message: -/

def mySet : Set ℕ := {0}
-- #check_failure (mySet ∈ mySet)

-- Exercise 6: Membership one level up is fine. `{0}` is a `Set ℕ`,
-- the right side a `Set (Set ℕ)`. Which tactic proves it?
example : ({0} : Set ℕ) ∈ ({{0}} : Set (Set ℕ)) := by
  sorry

-- Exercise 7: Russell's argument, typed. No relation `r` on `α` has an
-- element `a` whose `r`-predecessors are exactly the `x` with
-- `¬ r x x`. (The barber who shaves exactly those who do not shave
-- themselves.) Hint: specialise to `x = a`, then `by_cases`.
example {α : Type*} (r : α → α → Prop) :
    ¬ ∃ a, ∀ x, r x a ↔ ¬ r x x := by
  sorry

-- Exercise 8: Cantor's theorem. There is no surjection `α → Set α`.
-- Take the diagonal set `{x | x ∉ f x}` and a preimage `a` of it.
-- `Set.ext_iff.mp ha a : a ∈ f a ↔ a ∈ {x | x ∉ f x}`, and the
-- right side is `a ∉ f a` by definition. Then argue as in exercise 7.
-- (Mathlib: `Function.cantor_surjective`. Do not use it.)
example {α : Type*} (f : α → Set α) :
    ¬ Function.Surjective f := by
  sorry
