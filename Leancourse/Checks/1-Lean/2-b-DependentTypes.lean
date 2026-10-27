import Mathlib

/-!
# (witness) 1.2-b -- Dependent types

*Notes chapter 1.2, week 5.*
-/

/- ## Part 1: Sigma types -/

def lengthAndVec : Σ (n : ℕ), Fin n → ℕ :=
  ⟨3, fun i => i.val⟩

def withPoint : Σ (n : ℕ), Fin (n + 1) :=
  ⟨5, ⟨0, by omega⟩⟩

def doubleFst (p : Σ (n : ℕ), Fin (n + 1)) : ℕ :=
  2 * p.1

def sigmaShift (p : Σ (n : ℕ), Fin (n + 1)) :
    Σ (n : ℕ), Fin (n + 1) :=
  ⟨p.1 + 1, p.2.castSucc⟩

/- ## Part 2: Dependent functions (Pi types) -/

def zeroVec (n : ℕ) : Fin n → ℕ :=
  fun _ => 0

def idPerm (n : ℕ) : Fin n → Fin n :=
  fun i => i

def boolToType : Bool → Type
  | true  => ℕ
  | false => String

def boolToVal : (b : Bool) → boolToType b
  | true  => (0 : ℕ)
  | false => ""

/- ## Part 3: Subtypes -/

def evenNumber : {n : ℕ // n % 2 = 0} :=
  ⟨4, by norm_num⟩

def nextEven (n : {n : ℕ // n % 2 = 0}) : {m : ℕ // m % 2 = 0} :=
  ⟨n.1 + 2, by have := n.2; omega⟩

example : (⟨4, by norm_num⟩ : {n : ℕ // n % 2 = 0}) =
          (⟨4, by norm_num⟩ : {n : ℕ // n % 2 = 0}) := by
  rfl

/- ## Part 4: Universe levels -/

example : Type 0 := ℕ
example : Type 1 := Type 0
example : Type 0 := Prop

universe u
def myPolyId (α : Type u) (a : α) : α := a

#check myPolyId ℕ 42
#check myPolyId (Type 0) ℕ

/- ## Part 5: Subtype vs Exists -/

def squareRootOf25 : {n : ℕ // n * n = 25} :=
  ⟨5, by norm_num⟩

#eval squareRootOf25.1   -- 5

example : ∃ (n : ℕ), n * n = 25 :=
  ⟨5, by norm_num⟩

theorem subtypeToExists {α : Type} {P : α → Prop}
    (s : {x : α // P x}) : ∃ (x : α), P x :=
  ⟨s.1, s.2⟩

/- ## Part 6: Challenge problems -/

def safeHead {α : Type} (l : {l : List α // l ≠ []}) : α :=
  l.1.head l.2

example : safeHead ⟨[1, 2, 3], by simp⟩ = 1 := by
  rfl
