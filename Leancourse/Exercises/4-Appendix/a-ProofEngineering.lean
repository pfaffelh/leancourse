import Mathlib

open Set Nat

/-
# A-a -- Proof engineering

*Appendix, week 12.*

In this exercise sheet, you will practice:
- Choosing the right automation tactic
- Fixing broken proofs (definitional equality, the wrong tactic)
- Combining several tactics in one proof

Finding lemmas is practised on `2.0-a`, casts on `2.1-a`.

Prerequisites: You should be familiar with basic Lean tactics (intro, apply, exact,
rw, simp, ring, linarith, omega) from earlier chapters.

## Introduced here

| tactic        | use it when                                                    |
|---------------|----------------------------------------------------------------|
| `aesop`       | goals of logic and sets, by search over `simp` and rules       |
| `nlinarith`   | `linarith` with products of hypotheses: nonlinear inequalities |
| `gcongr`      | `f a ≤ f b` from `a ≤ b`, when `f` is monotone in its shape    |
| `field_simp`  | clear denominators, given that they are nonzero                |
| `congr 1`     | goal `f a = f b`: prove `a = b`                                |
| `convert e`   | `e` almost proves the goal; the differences become new goals   |

## Tactics from earlier sheets

| sheet   | tactics                                                              |
|---------|----------------------------------------------------------------------|
| `L-a`   | `exact`                                                              |
| `1.1-a` | `rw`                                                                 |
| `1.1-b` | `decide`                                                             |
| `1.1-c` | `calc`, `ring`, `norm_num`, `linarith`, `simp`, `omega`, `push_cast` |
| `2.1-a` | `norm_cast`, `positivity`                                            |
-/

/-
## Part A: Choosing the right automation tactic

For each exercise, find the ONE tactic that closes the goal.
Possible tactics: simp, aesop, omega, decide, norm_num, ring, linarith,
nlinarith, positivity, field_simp, gcongr, push_cast, norm_cast.
-/

-- Exercise A1: Which tactic works here?
example : Nat.Prime 37 := by
  sorry

-- Exercise A2:
example (n : ℕ) (h : n ≥ 5) : n ≥ 2 := by
  sorry

-- Exercise A3:
example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  sorry

-- Exercise A4:
example (x : ℝ) (hx : x > 0) : x + 1/x ≥ 0 := by
  sorry

-- Exercise A5:
example : (7 : ℚ) / 3 + 5 / 6 = 19 / 6 := by
  sorry

-- Exercise A6:
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  sorry

-- Exercise A7:
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x^2 * y + x * y^2 := by
  sorry

-- Exercise A8:
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  sorry

-- Exercise A9:
example (P Q : Prop) (hP : P) : P ∨ Q := by
  sorry

-- Exercise A10:
example (x : ℝ) (hx : x ≠ 0) : x * (1 / x) = 1 := by
  sorry

/-
## Part B: Fix the broken proof

Each of the following "proofs" has an issue. Your task is to fix it.
The comment above each exercise describes what went wrong.
-/

-- Exercise B1: The tactic `rfl` does not work here because `0 + n` is not
-- definitionally equal to `n`: addition on ℕ recurses on the second
-- argument, and here the second argument is the variable `n`.
-- Fix the proof by using an appropriate tactic.
example (n : ℕ) : 0 + n = n := by
  sorry

-- Exercise B2: `ring` fails here because the goal involves an inequality, not an equality.
-- Use a different tactic.
example (x : ℝ) : x^2 + 1 > 0 := by
  sorry

-- Exercise B3: `linarith` fails because the goal is nonlinear (involves x^2).
-- Fix the proof. Hint: what tactic handles nonlinear arithmetic?
example (x : ℝ) (hx : x ≥ 2) : x^2 ≥ 4 := by
  sorry

-- Exercise B4: `simp` alone cannot close this because it needs a hypothesis.
-- Provide the right simp call.
example (s : Set ℝ) (hs : s = ∅) : s ∪ s = ∅ := by
  sorry

-- Exercise B5: The `omega` tactic does not work over ℝ.
-- Choose a tactic that does work for real-valued linear arithmetic.
example (x y : ℝ) (h1 : x + y ≤ 10) (h2 : x ≥ 3) (h3 : y ≥ 1) :
    x ≤ 9 := by
  sorry

-- Exercise B6: `decide` fails here: the goal contains the variable `n`.
-- Fix this proof with a tactic for arithmetic with variables.
example (n : ℕ) : n + 10 ≥ 10 := by
  sorry

/-
### `congr` and `convert`

Two tactics for the case "the goal is almost the lemma I have".

`congr` peels a goal `f a = f b` down to the arguments that differ,
leaving `a = b`. `congr 1` stops after one layer, which is usually
what you want -- a bare `congr` can dig too deep and leave unusable
goals.
-/

example (f g : ℕ → ℕ) (h : ∀ n, f n = g n) (a : ℕ) : f a + 1 = g a + 1 := by
  congr 1
  exact h a

/-
`convert e` is the same idea applied to a *term*: it unifies the goal
with the type of `e` and hands you the mismatches as new goals. Use it
when a lemma is the right shape but not literally the goal. `using k`
limits how deep it looks.
-/

example (a b : ℝ) (hab : a = b) : Real.exp a ≤ Real.exp b := by
  convert le_refl (Real.exp a)
  exact hab.symm

-- Exercise B7: One `congr 1`.
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  sorry

-- Exercise B8: Same tactic. It discharges the two remaining goals
-- from the hypotheses by itself.
example (a b c d : ℕ) (h1 : a = c) (h2 : b = d) : a + b = c + d := by
  sorry

-- Exercise B9: `Set.mem_univ x` is the right lemma, but not the goal.
example (s : Set ℕ) (h : s = Set.univ) (x : ℕ) : x ∈ s := by
  sorry

/-
## Part C: Multi-step proofs using automation

These exercises require combining several tactics.
-/

-- Exercise C1: Prove this using `field_simp` followed by `ring`.
example (x : ℝ) (hx : x ≠ 0) :
    (x^2 - 1) / x = x - 1 / x := by
  sorry

-- Exercise C2: Use `push_cast` to normalize, then `ring` to finish.
example (n : ℕ) :
    ((n^2 + 2*n + 1 : ℕ) : ℤ) = ((n : ℤ) + 1)^2 := by
  sorry

-- Exercise C3: Combine `have` with automation.
-- Hint: `have h2 : n * 1 ≤ n * n := Nat.mul_le_mul_left n h`, then `omega`.
example (n : ℕ) (h : n ≥ 1) : n * n ≥ n := by
  sorry

-- Exercise C4: Use `gcongr` and a helper lemma.
example (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : a^2 ≤ b^3 := by
  sorry

/-
## Part D: Challenge problems

These require combining multiple techniques from the chapter.
-/

-- Exercise D1: A calculation mixing cast, ring, and linarith.
-- Show that for natural numbers, the arithmetic-geometric mean inequality
-- holds in a special case.
-- Hint: in `ℕ`, `a - b` truncates; use `nlinarith [sq_nonneg ((a : ℤ) - b)]`.
example (a b : ℕ) : 4 * a * b ≤ (a + b)^2 := by
  sorry

-- Exercise D2: Find the right Mathlib lemma and apply it.
-- Hint: this is about List.length and List.map.
example (f : ℕ → ℕ) (l : List ℕ) : (l.map f).length = l.length := by
  sorry

-- Exercise D3: A proof that requires careful use of simp lemmas.
example (s t : Set ℕ) (h : s ⊆ t) (x : ℕ) (hx : x ∈ s ∩ t) :
    x ∈ t := by
  sorry
