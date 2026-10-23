import Mathlib

/-!
# (witness) 1.4-b -- Coercions and casts

*Notes chapter 1.4, week 5.*
-/

/- ## Part 1: The silent arrow -/

example (n : ℕ) : ℤ := n
example (n : ℕ) : ℤ := ↑n
example (n : ℕ) : ℤ := (n : ℤ)

/- ## Part 2: `Coe` -- a value becomes another value -/

example (s : {n : ℕ // n > 0}) : ℕ := s

example (s : {n : ℕ // n > 0}) : (s : ℕ) > 0 := s.2

/- ## Part 3: `CoeSort` -- a value becomes a type -/

example (b : Bool) (h : b = true) : (b : Prop) := h

example (s : Set ℕ) : Type := s

example (s : Set ℕ) (x : s) : ℕ := x

/- ## Part 4: `CoeFun` -- a value becomes a function -/

example (f : ℕ →+ ℕ) (n : ℕ) : ℕ := f n

example (f : ℕ →+ ℕ) : f 0 = 0 := map_zero f

/- ## Part 5: The numeric chain -/

example (n m : ℕ) (h : (n : ℤ) + m = 10) : (↑(n + m) : ℤ) = 10 := by
  push_cast
  exact h

example (n m : ℕ) : ((n + m : ℕ) : ℤ) ^ 2
    = (n : ℤ) ^ 2 + 2 * n * m + (m : ℤ) ^ 2 := by
  push_cast
  ring

example (n : ℕ) (h : n < 5) : (n : ℤ) < 5 := by
  exact_mod_cast h

example (n : ℕ) : ((n : ℤ) = 0) ↔ n = 0 := by
  norm_cast

example (a b : ℕ) (h : (a : ℚ) = b) : a = b := by
  exact_mod_cast h

example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  omega

/- ## Part 6: `OfNat` -- where numerals come from -/

#check @OfNat.ofNat

example : (2 : ℤ) = OfNat.ofNat 2 := rfl

structure Pt where
  x : ℤ
  y : ℤ
deriving Repr, DecidableEq

instance : OfNat Pt 0 := ⟨⟨0, 0⟩⟩

example : (0 : Pt) = ⟨0, 0⟩ := rfl

#eval (0 : Pt)
