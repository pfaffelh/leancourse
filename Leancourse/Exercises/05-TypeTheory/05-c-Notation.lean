import Mathlib

/-
# Exercises 05-c: Defining your own notation

These exercises accompany the "Defining new notation" section in
the Lean chapter. You will practice `notation`, `infixl`, `infixr`,
`prefix`, `postfix`, and `scoped` notation.

Each exercise is stated as a comment.  Write the requested notation
declaration, then uncomment the `example` check lines below it to
verify that your declaration has the intended effect.

Because notation declarations are *commands* (not tactics), you
cannot leave them as `sorry`; instead, replace the template with a
real declaration.
-/

/- ## Part 1: Simple `notation` -/

-- Exercise 1.
-- Introduce a 0-ary symbol `π₂` that stands for `(2 : ℕ)`.
-- Template:
--   notation "π₂" => (2 : ℕ)
-- Then uncomment to check:
--   example : π₂ = 2 := rfl

-- Exercise 2.
-- Introduce a unary notation `sq x` meaning `x * x` on ℕ.
-- Template (fill in the right-hand side):
--   notation "sq " x => ?_
-- Then uncomment to check:
--   example : sq 5 = 25 := rfl

-- Exercise 3.
-- Introduce a binary notation `avg a b` meaning `(a + b) / 2` on ℕ.
-- Template:
--   notation "avg " a " " b => ?_
-- Then uncomment:
--   example : avg 4 6 = 5 := rfl

/- ## Part 2: Infix operators -/

-- Exercise 4.
-- Introduce a left-associative infix `⊙` at precedence 65 meaning
-- `fun (a b : ℕ) => a + 2 * b`.
-- Template:
--   infixl:65 " ⊙ " => fun (a b : ℕ) => ?_
-- Then uncomment:
--   example : (1 ⊙ 2 : ℕ) = 5 := rfl
--   -- Left-associativity: (1 ⊙ 2) ⊙ 3 = 5 + 2 * 3 = 11
--   example : (1 ⊙ 2 ⊙ 3 : ℕ) = 11 := rfl

-- Exercise 5.
-- Introduce a right-associative infix `▷` at precedence 65 with the
-- same underlying operation as in Exercise 4.
-- Template:
--   infixr:65 " ▷ " => fun (a b : ℕ) => a + 2 * b
-- Right-associativity: 1 ▷ 2 ▷ 3 = 1 ▷ (2 + 2*3) = 1 + 2*(2 + 6) = 17
--   example : (1 ▷ 2 ▷ 3 : ℕ) = 17 := rfl

/- ## Part 3: `prefix` and `postfix` -/

-- Exercise 6.
-- Introduce a prefix operator `‼` at precedence 80 that doubles a
-- natural number.
-- Template:
--   prefix:80 "‼" => fun n : ℕ => ?_
-- Then uncomment:
--   example : ‼7 = 14 := rfl

-- Exercise 7.
-- Introduce a postfix operator `⁺⁺` at precedence 90 that adds 1 to
-- a natural number.  (Think of C's `++`.)
-- Template:
--   postfix:90 "⁺⁺" => fun n : ℕ => ?_
-- Then uncomment:
--   example : (3 : ℕ)⁺⁺ = 4 := rfl

/- ## Part 4: `scoped` notation -/

-- Exercise 8.
-- Inside the namespace below, declare a *scoped* notation `↯` for
-- `(100 : ℕ)`.  After your declaration and `open scoped MyArith`,
-- uncomment the `example` line.

namespace MyArith
  -- Your scoped notation goes here.
  -- scoped notation "↯" => (100 : ℕ)
end MyArith

-- open scoped MyArith
-- example : ↯ = 100 := rfl

/- ## Part 5: Mixing notation -/

-- Exercise 9.
-- Introduce a prefix-like notation `‖x‖₁` for `Int.natAbs x`, valid
-- on integers.  Then uncomment:
-- Template:
--   notation "‖" x "‖₁" => Int.natAbs x
--   example : ‖(-3 : ℤ)‖₁ = 3 := rfl
--   example (n : ℤ) : 0 ≤ (‖n‖₁ : ℤ) := by positivity

-- Exercise 10.
-- Introduce a ternary notation `if! c then! a else! b` (with
-- `c : Bool`) meaning `bif c then a else b`.
-- Template:
--   notation "if! " c " then! " a " else! " b => bif c then a else b
-- Then uncomment:
--   example : (if! true  then! 1 else! 2 : ℕ) = 1 := rfl
--   example : (if! false then! 1 else! 2 : ℕ) = 2 := rfl
