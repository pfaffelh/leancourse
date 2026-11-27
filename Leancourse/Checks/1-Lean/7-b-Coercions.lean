import Mathlib

/-!
# (witness) 1.7-b -- Coercions

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

/- ## Part 5: Your own coercions -/

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

/- ## Part 6: Hierarchies with `extends` -/

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

/- ## Part 7: Chains of coercions -/

def posToInt (p : Pos) : ℤ :=
  p

#print posToInt   -- fun p => ↑p.val

example (p : Pos) : (0 : ℤ) < p := by
  have := p.pos
  omega

example (n : ℕ) : (n : ℤ) = Nat.cast n := by
  rfl

example (s : {n : ℕ // n > 0}) : (s : ℕ) = s.val := by
  rfl

/- ## Part 8: `CoeDep` -/

def isSmall (n : ℕ) : Bool :=
  n < 5

example : isSmall 3 = true := by
  rfl

example : isSmall 7 = false := by
  rfl

example (n : ℕ) : isSmall n = decide (n < 5) := by
  rfl

-- Exercise 19 changes the statement as the sheet asks.
example (p : Prop) [Decidable p] : Bool :=
  p

/- ## Part 9: Where the arrow goes -/

example : ((5 - 7 : ℕ) : ℤ) = 0 := by
  decide

example : ((5 : ℕ) - 7 : ℤ) = -2 := by
  decide

example : ((7 / 2 : ℕ) : ℚ) = 3 := by
  rfl

example : ((7 : ℕ) / 2 : ℚ) = 7 / 2 := by
  rfl

-- Without `h` the statement fails at `n = 0`: `0` against `-1`.
example (n : ℕ) (h : 1 ≤ n) :
    ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  omega
