import Mathlib

/-!
# (witness) 1.7-b -- Coercions and casts

*Notes chapter 1.7, week 9.*
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

/- ## Part 6: Your own coercions -/

structure Pos where
  val : ℕ
  pos : 0 < val

instance : Coe Pos ℕ := ⟨Pos.val⟩

example (p q : Pos) : 0 < (p : ℕ) + q := by
  have := p.pos
  omega

/-- The map `x ↦ a * x + b`, stored as its two coefficients. -/
structure Affine where
  a : ℤ
  b : ℤ

instance : CoeFun Affine (fun _ => ℤ → ℤ) :=
  ⟨fun f x => f.a * x + f.b⟩

def Affine.comp (f g : Affine) : Affine :=
  ⟨f.a * g.a, f.a * g.b + f.b⟩

example (f g : Affine) (x : ℤ) : f.comp g x = f (g x) := by
  show f.a * g.a * x + (f.a * g.b + f.b) = f.a * (g.a * x + g.b) + f.b
  ring

/- ## Part 7: Hierarchies with `extends` -/

class MyMonoid (α : Type) extends Mul α, One α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a

instance : MyMonoid ℕ where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

theorem MyMonoid.one_unique {α : Type} [MyMonoid α] (e : α)
    (h : ∀ a : α, e * a = a) : e = 1 := by
  calc e = e * 1 := by rw [MyMonoid.mul_one]
    _ = 1 := h 1
