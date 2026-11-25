import Mathlib

/-!
# (witness) 1.4-a -- Dependent types

*Notes chapters 1.2 and 1.4, week 7.*
-/

/-! ## Part 1: Σ-types -/

def aPair : (n : ℕ) × Fin (n + 1) := ⟨3, 2⟩

-- Exercise 1)
def sigmaShift : (n : ℕ) × Fin (n + 1) → (n : ℕ) × Fin (n + 1)
  | ⟨n, k⟩ => ⟨n + 1, ⟨k.val, by omega⟩⟩

example : sigmaShift ⟨2, 1⟩ = ⟨3, 1⟩ := by
  rfl

example : sigmaShift ⟨0, 0⟩ = ⟨1, 0⟩ := by
  rfl

example : Fintype.card ((n : Fin 4) × Fin (n + 1)) = 10 := by decide
example : Fintype.card ((n : Fin 4) → Fin (n + 1)) = 24 := by decide

-- Exercise 2) 0 + 1 + 2 + 3 + 4 = 10, and 0 · 1 · 2 · 3 · 4 = 0:
-- there is no function at all, since `Fin 0` is empty.
example : Fintype.card ((n : Fin 5) × Fin n) = 10 := by
  decide

example : Fintype.card ((n : Fin 5) → Fin n) = 0 := by
  decide

/-! ## Part 2: Type families and dependent functions -/

def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

def boolFamilyExample : (b : Bool) → BoolFamily b
  | true  => (42 : ℕ)
  | false => ("hello" : String)

-- Exercise 3)
def size : (b : Bool) × BoolFamily b → ℕ
  | ⟨true, n⟩ => n
  | ⟨false, s⟩ => s.length

example : size ⟨true, (7 : ℕ)⟩ = 7 := by
  rfl

example : size ⟨false, ("abc" : String)⟩ = 3 := by
  decide

def NTuple : ℕ → Type
  | 0     => Unit
  | n + 1 => ℕ × NTuple n

example : NTuple 2 := (5, 7, ())

-- Exercise 4)
def countDown : (n : ℕ) → NTuple n
  | 0     => ()
  | n + 1 => (n, countDown n)

example : countDown 3 = ((2, 1, 0, ()) : NTuple 3) := by
  rfl

/-! ## Part 3: Subtypes -/

def four : {n : ℕ // n % 2 = 0} := ⟨4, by decide⟩

-- Exercise 5)
def nextEven (n : {n : ℕ // n % 2 = 0}) : {m : ℕ // m % 2 = 0} :=
  ⟨n.val + 2, by have h := n.property; omega⟩

example : (nextEven four).val = 6 := by
  rfl

-- Exercise 6)
example (n : ℕ) (h₁ : (n + n) % 2 = 0) (h₂ : (2 * n) % 2 = 0) :
    (⟨n + n, h₁⟩ : {m : ℕ // m % 2 = 0}) = ⟨2 * n, h₂⟩ := by
  apply Subtype.ext
  show n + n = 2 * n
  omega

-- Exercise 7)
theorem subtypeToExists {α : Type} {P : α → Prop}
    (s : {x : α // P x}) : ∃ (x : α), P x :=
  ⟨s.val, s.property⟩

-- Exercise 8)
def safeHead {α : Type} : {l : List α // l ≠ []} → α
  | ⟨a :: _, _⟩ => a
  | ⟨[], h⟩ => absurd rfl h

example : safeHead ⟨[1, 2, 3], by simp⟩ = 1 := by
  rfl

/-! ## Part 4: An indexed family -/

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n → Vec α (n + 1)

namespace Vec

def head {α : Type} {n : ℕ} : Vec α (n + 1) → α
  | .cons a _ => a

-- Exercise 9) Both vectors have the same index `n`. If one is `nil`,
-- then `n = 0`, and the other cannot be a `cons`, whose index is a
-- successor; so the mixed cases cannot occur.
def zip {α β : Type} {n : ℕ} : Vec α n → Vec β n → Vec (α × β) n
  | .nil, .nil => .nil
  | .cons a v, .cons b w => .cons (a, b) (zip v w)

example : zip (cons 1 (cons 2 nil)) (cons true (cons false nil)) =
    cons (1, true) (cons (2, false) nil) := by
  rfl

-- Exercise 10)
def toList {α : Type} {n : ℕ} : Vec α n → List α
  | .nil => []
  | .cons a v => a :: v.toList

example : (cons 1 (cons 2 (cons 3 nil))).toList = [1, 2, 3] := by
  rfl

-- Exercise 11)
theorem length_toList {α : Type} {n : ℕ} (v : Vec α n) :
    v.toList.length = n := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [toList, ih]

end Vec
