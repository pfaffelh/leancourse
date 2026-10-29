import Mathlib

/-!
# 1.4-a -- Dependent types

*Notes chapters 1.2 and 1.4, week 5.*

A type may depend on a value. `Σ (x : α), β x` pairs a value with
data whose type depends on it, `(x : α) → β x` is the function
version, and `{x : α // P x}` is the special case where the second
component is a proof.

Universes appear here too; they were introduced in chapter 1.2.
The axioms `propext` and `Classical.choice` are listed in chapter
1.5 and treated in chapter 2.2, with their own sheet `2.2-a` in
week 9; `funext` is a theorem. One exercise below needs choice; it is marked.

## Notation introduced here

| notation         | means                                         |
|------------------|-----------------------------------------------|
| `Σ (x : α), β x` | dependent pair, second component in `Type`    |
| `(x : α) → β x`  | dependent function (Pi type)                  |
| `{x : α // P x}` | subtype: a value together with a proof        |
| `p.1`, `p.2`     | the two components of a pair or subtype       |
| `Subtype.ext`    | two subtype elements agree if their values do |
| `universe u`     | declare a universe variable                   |
-/

/-
## Part 1: Sigma types

Recall: `Σ (x : α), β x` is the type of dependent pairs ⟨a, b⟩
where `a : α` and `b : β a`. The second component `β x` must itself
live in `Type`, not in `Prop`.  Sigma represents computationally
relevant data: you can extract the witness with `.1` and the
associated data with `.2`.

If the second component is a *proposition*, use the subtype
`{x : α // P x}` (covered in Part 3) or the universe-polymorphic
`PSigma`.  Genuine `Σ` requires `β x : Type`.
-/

-- Exercise 1: Construct an element of a Sigma type.
-- A length `n` together with a vector of that length
-- (here represented as `Fin n → ℕ`, a list of `n` natural numbers).
def lengthAndVec : Σ (n : ℕ), Fin n → ℕ :=
  sorry

-- Exercise 2: Construct another Sigma element.
-- A natural number n together with a term of Fin (n + 1)
-- (which is nonempty for every n, since `⟨0, _⟩ : Fin (n+1)`).
def withPoint : Σ (n : ℕ), Fin (n + 1) :=
  sorry

-- Exercise 3: A function on Sigma types.
-- Given a Sigma pair, extract and double the first component.
def doubleFst (p : Σ (n : ℕ), Fin (n + 1)) : ℕ :=
  sorry

-- Exercise 4: Map over the second component of a Sigma type.
-- Given ⟨n, k : Fin (n+1)⟩, produce ⟨n+1, k.castSucc : Fin (n+2)⟩.
-- Hint: `Fin.castSucc` includes `Fin (n+1)` into `Fin (n+2)`.
def sigmaShift (p : Σ (n : ℕ), Fin (n + 1)) :
    Σ (n : ℕ), Fin (n + 1) :=
  sorry

/-
## Part 2: Dependent functions (Pi types)

The type `(x : α) → β x` is a Pi type: a function whose return type
depends on the input value.
-/

-- Exercise 5: A simple dependent function
-- Given n, return the zero vector of length n (as a function from Fin n)
def zeroVec (n : ℕ) : Fin n → ℕ :=
  sorry

-- Exercise 6: Another dependent function
-- Given n, return the identity permutation on Fin n
def idPerm (n : ℕ) : Fin n → Fin n :=
  sorry

-- Exercise 7: A function that returns different types depending on input
def boolToType : Bool → Type
  | true  => ℕ
  | false => String

-- Now define a function that returns a value of the appropriate type
def boolToVal : (b : Bool) → boolToType b :=
  sorry

/-
## Part 3: Subtypes

The subtype `{x : α // P x}` consists of pairs ⟨x, h⟩ where x : α
and h : P x. Two subtypes are equal iff their first components agree.
-/

-- Exercise 8: Construct an element of a subtype
def evenNumber : {n : ℕ // n % 2 = 0} :=
  sorry

-- Exercise 9: Define a function on subtypes
-- Given an even number, produce the next even number
def nextEven (n : {n : ℕ // n % 2 = 0}) : {m : ℕ // m % 2 = 0} :=
  sorry

-- Exercise 10: Prove two subtype elements are equal
-- Hint: use Subtype.ext
example : (⟨4, by norm_num⟩ : {n : ℕ // n % 2 = 0}) =
          (⟨4, by norm_num⟩ : {n : ℕ // n % 2 = 0}) := by
  sorry

/-
## Part 4: Universe levels

Chapter 1.2 gave the hierarchy: `Prop = Sort 0`, `Type u = Sort (u+1)`,
and `Sort u : Sort (u+1)`.  Here you read it off in the editor.
-/

-- These three are given.  Check each with `#check` and convince
-- yourself the annotation is the only one that type-checks.

-- #check ℕ
example : Type 0 := ℕ

-- #check Type 0
example : Type 1 := Type 0

-- #check Prop
example : Type 0 := Prop

-- Exercise 11: Universe-polymorphic identity
-- Define a universe-polymorphic identity function
universe u
def myPolyId (α : Type u) (a : α) : α :=
  sorry

-- Once Exercise 11 is solved, these two work at different levels:
#check myPolyId ℕ 42
#check myPolyId (Type 0) ℕ

/-
## Part 5: Subtype vs Exists (and a note on PSigma)

Understand the difference between *computational* and *propositional*
existence.  Because `Σ` demands a `Type`-valued second component,
the right analogue of `∃ x : α, P x` (with `P : α → Prop`) is the
subtype `{x : α // P x}`.  It carries the witness as data.

(There is also `PSigma`, which is universe-polymorphic and accepts
a `Prop`-valued second component; `Subtype` is the more common
choice in Mathlib for this pattern.)
-/

-- Exercise 12: Subtypes give you data.
-- Construct a subtype element; you will be able to extract the
-- witness with `.1`.
def squareRootOf25 : {n : ℕ // n * n = 25} :=
  sorry

-- Now the witness is computable: squareRootOf25.1 evaluates to 5.
-- #eval squareRootOf25.1  -- uncomment after solving

-- Exercise 13: Exists gives only a proof.
-- You can prove existence but cannot extract the witness without
-- classical choice -- that direction is on sheet `2.2-a`.
example : ∃ (n : ℕ), n * n = 25 :=
  sorry

-- Exercise 14: Converting Subtype to Exists.
-- This direction always works (forgetting data) and needs no axiom.
theorem subtypeToExists {α : Type} {P : α → Prop}
    (s : {x : α // P x}) : ∃ (x : α), P x :=
  sorry

/-
## Part 6: Challenge problems
-/

-- Exercise 15: Define a "safe head" function using subtypes
-- The input is guaranteed to be a nonempty list
def safeHead {α : Type} (l : {l : List α // l ≠ []}) : α :=
  sorry

-- Exercise 16: Use the safe head function
-- Hint: you need to provide a list together with a proof it is nonempty
example : safeHead ⟨[1, 2, 3], by simp⟩ = 1 := by
  sorry
