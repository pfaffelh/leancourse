import Mathlib

open Set Nat

/-
# (witness) A-a -- Proof engineering

*Appendix, week 10.*

In this exercise sheet, you will practice:
- Choosing the right automation tactic
- Searching for Mathlib lemmas
- Fixing common proof issues (coercions, casts, definitional equality)
- Debugging broken proofs

Prerequisites: You should be familiar with basic Lean tactics (intro, apply, exact,
rw, simp, ring, linarith, omega) from earlier chapters.
-/

/-
## Part A: Choosing the right automation tactic

For each exercise, find the ONE tactic that closes the goal.
Possible tactics: simp, aesop, omega, decide, norm_num, ring, linarith,
nlinarith, positivity, field_simp, gcongr, push_cast, norm_cast.
-/

-- Exercise A1: Which tactic works here?
example : Nat.Prime 37 := by
  decide

-- Exercise A2:
example (n : ℕ) (h : n ≥ 5) : n ≥ 2 := by
  omega

-- Exercise A3:
example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring

-- Exercise A4:
example (x : ℝ) (hx : x > 0) : x + 1/x ≥ 0 := by
  positivity

-- Exercise A5:
example : (7 : ℚ) / 3 + 5 / 6 = 19 / 6 := by
  norm_num

-- Exercise A6:
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  omega

-- Exercise A7:
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x^2 * y + x * y^2 := by
  positivity

-- Exercise A8:
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  gcongr

-- Exercise A9:
example (P Q : Prop) (hP : P) : P ∨ Q := by
  simp [hP]

-- Exercise A10:
example (x : ℝ) (hx : x ≠ 0) : x * (1 / x) = 1 := by
  field_simp

/-
## Part B: Finding the right Mathlib lemma

For each exercise, you need to find an appropriate Mathlib lemma.
Hints: use `exact?`, `apply?`, `#check`, or try to guess the name
using Mathlib naming conventions.
-/

-- Exercise B1: Find a lemma that says the square of a real number is nonneg.
-- Hint: the name involves `sq` and `nonneg`.
example (x : ℝ) : 0 ≤ x^2 := by
  exact sq_nonneg x

-- Exercise B2: Find a lemma that says abs(x * y) = abs(x) * abs(y).
-- Hint: try `#check abs_mul`
example (x y : ℝ) : |x * y| = |x| * |y| := by
  exact abs_mul x y

-- Exercise B3: The triangle inequality for absolute value.
-- Hint: naming convention uses `abs` and `add`.
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add_le x y

-- Exercise B4: Monotonicity of Nat.succ
-- Hint: try searching for `Nat.succ_le_succ`
example (n m : ℕ) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  exact Nat.succ_le_succ h

-- Exercise B5: If a function is monotone and x ≤ y, then f x ≤ f y.
-- This is just the definition of monotone. How do you "unfold" it?
example (f : ℝ → ℝ) (hf : Monotone f) (x y : ℝ) (h : x ≤ y) :
    f x ≤ f y := by
  exact hf h

-- Exercise B6: The image of a union is the union of images.
-- Hint: naming convention: `Set.image_union`
example (f : ℝ → ℝ) (s t : Set ℝ) : f '' (s ∪ t) = f '' s ∪ f '' t := by
  exact Set.image_union f s t

-- Exercise B7: Find a lemma to show that ℕ → ℕ → ℕ is not empty.
-- Hint: there is an instance that says this type is `Nonempty` or `Inhabited`.
example : Nonempty (ℕ → ℕ → ℕ) := by
  infer_instance

/-
## Part C: Coercions and casts

These exercises deal with the common headache of working with mixed numeric types.
-/

-- Exercise C1: Use `push_cast` or `norm_cast` to prove this.
example (n m : ℕ) (h : n ≤ m) : (n : ℤ) ≤ (m : ℤ) := by
  exact_mod_cast h

-- Exercise C2: The cast of a sum is the sum of casts.
example (n m : ℕ) : ((n + m : ℕ) : ℤ) = (n : ℤ) + (m : ℤ) := by
  push_cast
  ring

-- Exercise C3: A mixed-type inequality.
-- Hint: `exact_mod_cast` or `norm_cast` may help.
example (n : ℕ) (h : n > 0) : (n : ℝ) > 0 := by
  exact_mod_cast h

-- Exercise C4: Work with coercions in a calculation.
example (n : ℕ) : ((n * (n + 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) + 1) := by
  push_cast
  ring

-- Exercise C5: Cast and divisibility.
-- This one requires some care with the direction of casting.
example (n : ℕ) (h : 2 ∣ n) : (2 : ℤ) ∣ (n : ℤ) := by
  exact_mod_cast h

/-
## Part D: Fix the broken proof

Each of the following "proofs" has an issue. Your task is to fix it.
The comment above each exercise describes what went wrong.
-/

-- Exercise D1: The tactic `rfl` does not work here because `0 + n` is not
-- definitionally equal to `n` (addition on ℕ recurses on the first argument).
-- Fix the proof by using an appropriate tactic.
example (n : ℕ) : 0 + n = n := by
  omega

-- Exercise D2: `ring` fails here because the goal involves an inequality, not an equality.
-- Use a different tactic.
example (x : ℝ) : x^2 + 1 > 0 := by
  positivity

-- Exercise D3: `linarith` fails because the goal is nonlinear (involves x^2).
-- Fix the proof. Hint: what tactic handles nonlinear arithmetic?
example (x : ℝ) (hx : x ≥ 2) : x^2 ≥ 4 := by
  nlinarith

-- Exercise D4: `simp` alone cannot close this because it needs a hypothesis.
-- Provide the right simp call.
example (s : Set ℝ) (hs : s = ∅) : s ∪ s = ∅ := by
  simp [hs]

-- Exercise D5: The `omega` tactic does not work over ℝ.
-- Choose a tactic that does work for real-valued linear arithmetic.
example (x y : ℝ) (h1 : x + y ≤ 10) (h2 : x ≥ 3) (h3 : y ≥ 1) :
    x ≤ 9 := by
  linarith

-- Exercise D6: `norm_num` does not know about variables, only concrete numbers.
-- Fix this proof using the right combination of tactics.
example (n : ℕ) : n + 10 ≥ 10 := by
  omega

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

-- Exercise D7: One `congr 1`.
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  congr 1

-- Exercise D8: Same tactic. It discharges the two remaining goals
-- from the hypotheses by itself.
example (a b c d : ℕ) (h1 : a = c) (h2 : b = d) : a + b = c + d := by
  congr 1

-- Exercise D9: `Set.mem_univ x` is the right lemma, but not the goal.
example (s : Set ℕ) (h : s = Set.univ) (x : ℕ) : x ∈ s := by
  convert Set.mem_univ x

/-
## Part E: Multi-step proofs using automation

These exercises require combining several tactics.
-/

-- Exercise E1: Prove this using `field_simp` followed by `ring`.
example (x : ℝ) (hx : x ≠ 0) :
    (x^2 - 1) / x = x - 1 / x := by
  -- `field_simp` already closes this; the `ring` the exercise asks
  -- for has nothing left to do.
  field_simp

-- Exercise E2: Use `push_cast` to normalize, then `ring` to finish.
example (n : ℕ) :
    ((n^2 + 2*n + 1 : ℕ) : ℤ) = ((n : ℤ) + 1)^2 := by
  push_cast
  ring

-- Exercise E3: Combine `have` with automation.
-- Hint: First establish that n ≥ 1 using omega, then use nlinarith.
example (n : ℕ) (h : n ≥ 1) : n * n ≥ n := by
  nlinarith

-- Exercise E4: Use `gcongr` and a helper lemma.
example (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) : a^2 ≤ b^3 := by
  calc a ^ 2 ≤ b ^ 2 := by gcongr
    _ ≤ b ^ 3 := by nlinarith

-- Exercise E5: Use `conv` to rewrite in a specific location, then finish.
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  conv_lhs => rw [mul_add, add_mul, add_mul]
  ring

/-
## Part F: Challenge problems

These require combining multiple techniques from the chapter.
-/

-- Exercise F1: A calculation mixing cast, ring, and linarith.
-- Show that for natural numbers, the arithmetic-geometric mean inequality
-- holds in a special case.
example (a b : ℕ) : 4 * a * b ≤ (a + b)^2 := by
  zify
  nlinarith [sq_nonneg ((a : ℤ) - b)]

-- Exercise F2: Find the right Mathlib lemma and apply it.
-- Hint: this is about List.length and List.map.
example (f : ℕ → ℕ) (l : List ℕ) : (l.map f).length = l.length := by
  simp

-- Exercise F3: A proof that requires careful use of simp lemmas.
example (s t : Set ℕ) (h : s ⊆ t) (x : ℕ) (hx : x ∈ s ∩ t) :
    x ∈ t := by
  exact h hx.1
