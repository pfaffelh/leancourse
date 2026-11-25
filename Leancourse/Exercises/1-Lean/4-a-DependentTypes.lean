import Mathlib

/-!
# 1.4-a -- Dependent types

*Notes chapters 1.2 and 1.4, week 7.*

A type may depend on a value. A Σ-type pairs a value with data whose
type depends on it, a dependent function returns a value whose type
depends on the input, and a subtype pairs a value with a proof. An
indexed family is a type family declared with `inductive`.

Most exercises ask you to define something. Each definition is
followed by an `example` that pins down what it should compute. On
this sheet those examples are `sorry`; once your definition is done,
replace the `sorry` by the tactic named in the comment. If it fails,
the definition is wrong.

## Introduced here

| notation                    | means                                          |
|-----------------------------|------------------------------------------------|
| `(x : α) × β x`             | Σ-type: pairs `⟨a, b⟩` with `b : β a`          |
| `p.1`, `p.2`                | the two components of a pair                   |
| `Fintype.card α`            | the number of elements of a finite type        |
| `{x : α // P x}`            | subtype: pairs `⟨a, h⟩` with `h : P a`         |
| `s.val`, `s.property`       | the element and the proof                      |
| `Subtype.ext`               | two elements agree if their values do          |
| `inductive T : ℕ → Type`    | an indexed family: constructors fix the index  |

## Tactics from earlier sheets

| sheet   | tactics                          |
|---------|----------------------------------|
| `L-a`   | `apply`                          |
| `L-d`   | `absurd`                         |
| `L-f`   | `have`                           |
| `1.1-a` | `rfl`, `show`                    |
| `1.1-b` | `decide`                         |
| `1.1-c` | `simp`, `omega`                  |
| `1.3-a` | `induction t with`, `simp [f]`   |
-/

/-! ## Part 1: Σ-types

The second component of `⟨n, k⟩ : (n : ℕ) × Fin (n + 1)` has type
`Fin (n + 1)`, which depends on the first component `n`. -/

def aPair : (n : ℕ) × Fin (n + 1) := ⟨3, 2⟩

#eval aPair.1   -- 3
#eval aPair.2   -- 2, as an element of `Fin 4`

-- Exercise 1) Send `⟨n, k⟩` to `⟨n + 1, k⟩`: the same value `k`, now
-- as an element of `Fin (n + 2)`. Hint: match on `⟨n, k⟩` and build
-- the second component as `⟨k.val, _⟩`; `omega` knows `k.val < n + 1`.
def sigmaShift : (n : ℕ) × Fin (n + 1) → (n : ℕ) × Fin (n + 1) :=
  sorry

example : sigmaShift ⟨2, 1⟩ = ⟨3, 1⟩ := by
  sorry -- rfl, once solved

example : sigmaShift ⟨0, 0⟩ = ⟨1, 0⟩ := by
  sorry -- rfl, once solved

/- The pairs `⟨n, k⟩` with a fixed `n` form one piece, and the Σ-type
is the disjoint union of the pieces. So it has `∑ₙ |β n|` elements,
while the Π-type `(n : α) → β n` has `∏ₙ |β n|`. -/

example : Fintype.card ((n : Fin 4) × Fin (n + 1)) = 10 := by decide
example : Fintype.card ((n : Fin 4) → Fin (n + 1)) = 24 := by decide

-- Exercise 2) Compute both numbers by hand. Then replace each `sorry`
-- on the right-hand side by your number and the proof by `decide`.
example : Fintype.card ((n : Fin 5) × Fin n) = sorry := by
  sorry

example : Fintype.card ((n : Fin 5) → Fin n) = sorry := by
  sorry

/-! ## Part 2: Type families and dependent functions

A type family is a function whose values are types. A dependent
function `(b : Bool) → BoolFamily b` returns a value in `ℕ` or in
`String`, depending on `b`. -/

def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

def boolFamilyExample : (b : Bool) → BoolFamily b
  | true  => (42 : ℕ)
  | false => ("hello" : String)

-- Exercise 3) A pair `⟨b, x⟩` with `x : BoolFamily b` is a number or
-- a string. Return the number itself, or the length `s.length` of the
-- string. Hint: match on `⟨true, n⟩` and `⟨false, s⟩`.
def size : (b : Bool) × BoolFamily b → ℕ :=
  sorry

example : size ⟨true, (7 : ℕ)⟩ = 7 := by
  sorry -- rfl, once solved

example : size ⟨false, ("abc" : String)⟩ = 3 := by
  sorry -- decide, once solved

/- A type family can be defined by recursion. `NTuple n` is the type
of `n`-tuples of natural numbers, ending in `()`: -/

def NTuple : ℕ → Type
  | 0     => Unit
  | n + 1 => ℕ × NTuple n

example : NTuple 2 := (5, 7, ())

-- Exercise 4) Define the dependent function that sends `n` to the
-- tuple `(n - 1, ..., 1, 0, ())`. Each branch returns a value of a
-- different type: `NTuple 0` in the first, `NTuple (n + 1)` in the
-- second.
def countDown : (n : ℕ) → NTuple n :=
  sorry

example : countDown 3 = ((2, 1, 0, ()) : NTuple 3) := by
  sorry -- rfl, once solved

/-! ## Part 3: Subtypes

An element of `{n : ℕ // n % 2 = 0}` is a pair `⟨n, h⟩` of a number
and a proof that it is even. A function into a subtype has to supply
the proof. -/

def four : {n : ℕ // n % 2 = 0} := ⟨4, by decide⟩

-- Exercise 5) The next even number, `n + 2`. Hint: `n.property` is
-- the proof for `n`; make it a hypothesis with `have` for `omega`.
def nextEven (n : {n : ℕ // n % 2 = 0}) : {m : ℕ // m % 2 = 0} :=
  sorry

example : (nextEven four).val = 6 := by
  sorry -- rfl, once solved

-- Exercise 6) `rfl` fails: `n + n` and `2 * n` are different terms.
-- `apply Subtype.ext` reduces the goal to the values; `show n + n = 2 * n`
-- makes that visible to `omega`.
example (n : ℕ) (h₁ : (n + n) % 2 = 0) (h₂ : (2 * n) % 2 = 0) :
    (⟨n + n, h₁⟩ : {m : ℕ // m % 2 = 0}) = ⟨2 * n, h₂⟩ := by
  sorry

-- Exercise 7) From a subtype to `∃`. This direction forgets data and
-- needs no axiom. The converse, from `∃` to a subtype, needs choice;
-- it is on sheet `2.3-a`.
theorem subtypeToExists {α : Type} {P : α → Prop}
    (s : {x : α // P x}) : ∃ (x : α), P x :=
  sorry

-- Exercise 8) The first element of a list that is known to be
-- nonempty. Hint: match on `⟨a :: _, _⟩` and `⟨[], h⟩`. In the second
-- case `h : [] ≠ []`, which contradicts `rfl`.
def safeHead {α : Type} : {l : List α // l ≠ []} → α :=
  sorry

example : safeHead ⟨[1, 2, 3], by simp⟩ = 1 := by
  sorry -- rfl, once solved

/-! ## Part 4: An indexed family

`Vec α n` is the type of lists of length `n`. The index `n` is fixed
by the constructors: `nil` has length `0`, `cons` adds one. A match on
`v : Vec α (n + 1)` needs no case for `nil`, because `nil` has index
`0`, which is not of the form `n + 1`. -/

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n → Vec α (n + 1)

namespace Vec

def head {α : Type} {n : ℕ} : Vec α (n + 1) → α
  | .cons a _ => a

#eval (cons 1 (cons 2 nil)).head   -- 1

-- Exercise 9) Pair up two vectors of the same length. Two cases are
-- enough. Why are `nil` with `cons` and `cons` with `nil` not needed?
def zip {α β : Type} {n : ℕ} : Vec α n → Vec β n → Vec (α × β) n :=
  sorry

example : zip (cons 1 (cons 2 nil)) (cons true (cons false nil)) =
    cons (1, true) (cons (2, false) nil) := by
  sorry -- rfl, once solved

-- Exercise 10) Forget the length: turn a vector into a list.
def toList {α : Type} {n : ℕ} : Vec α n → List α :=
  sorry

example : (cons 1 (cons 2 (cons 3 nil))).toList = [1, 2, 3] := by
  sorry -- rfl, once solved

-- Exercise 11) The list has the length that the index promised.
-- Hint: induction on `v`, as for the trees on sheet `1.3-a`.
theorem length_toList {α : Type} {n : ℕ} (v : Vec α n) :
    v.toList.length = n := by
  sorry

end Vec
