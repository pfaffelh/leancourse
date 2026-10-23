import Mathlib

/-
# (witness) 2.9-a -- Monads

*Notes chapter 2.9, week 15.*

These exercises cover the Option type, do-notation, typeclass instances,
and monadic programming. One worked implementation for each exercise.
-/

/- ## Part 1: Option and safe computations -/

-- Exercise 1) Define a safe head function that returns none for an empty list.
def safeHead {α : Type} (xs : List α) : Option α :=
  xs.head?

-- Exercise 2) Define a safe function that returns the element at index n,
-- or none if the index is out of bounds.
def safeGet {α : Type} (xs : List α) (n : ℕ) : Option α :=
  xs[n]?

-- Exercise 3) Define safe division that returns none when dividing by zero.
def safeDiv (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)

-- Exercise 4) Using do-notation, define a function that takes a list of
-- natural numbers and an index, gets the element at that index,
-- and then safely divides 100 by that element.
-- Return none if the index is out of bounds or the element is zero.
def divByElement (xs : List ℕ) (i : ℕ) : Option ℕ := do
  let x ← safeGet xs i
  safeDiv 100 x

-- Exercise 5) Define a function that takes two lists and an index,
-- gets the element at that index from each list, and returns their sum.
-- Use do-notation.
def addAtIndex (xs ys : List ℕ) (i : ℕ) : Option ℕ := do
  let x ← safeGet xs i
  let y ← safeGet ys i
  return x + y

-- Exercise 6) Define a function that finds the first element in a list
-- satisfying a predicate. Return none if no element satisfies it.
def findFirst {α : Type} (p : α → Bool) : List α → Option α :=
  fun xs => xs.find? p

-- Exercise 7) Chain three Option computations using do-notation:
-- Given a list of lists, get the i-th list, then get the j-th element of that list,
-- then safely divide 1000 by that element.
def nestedLookupAndDivide (xss : List (List ℕ)) (i j : ℕ) : Option ℕ := do
  let xs ← safeGet xss i
  let x ← safeGet xs j
  safeDiv 1000 x

/- ## Part 2: Typeclass instances -/

-- Here is a type representing days of the week.
inductive Day where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
  deriving Repr, BEq

-- Exercise 8) Define a ToString instance for Day.
instance : ToString Day where
  toString
    | .monday => "Monday"
    | .tuesday => "Tuesday"
    | .wednesday => "Wednesday"
    | .thursday => "Thursday"
    | .friday => "Friday"
    | .saturday => "Saturday"
    | .sunday => "Sunday"

-- Exercise 9) Define a function that returns the next day.
def Day.next : Day → Day
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday
  | .sunday => .monday

-- Here is a structure for 2D vectors with integer coordinates.
structure IntVec where
  x : ℤ
  y : ℤ
  deriving Repr, BEq

-- Exercise 10) Define an Add instance for IntVec.
instance : Add IntVec where
  add u v := ⟨u.x + v.x, u.y + v.y⟩

-- Exercise 11) Define a Neg instance for IntVec (negating both components).
instance : Neg IntVec where
  neg v := ⟨-v.x, -v.y⟩

-- Exercise 12) Define a ToString instance for IntVec.
-- Format: "(x, y)"
instance : ToString IntVec where
  toString v := s!"({v.x}, {v.y})"

-- Exercise 13) Define an HMul instance so that an integer can scale a vector:
-- (n : ℤ) * (v : IntVec) = IntVec (n * v.x) (n * v.y)
instance : HMul ℤ IntVec IntVec where
  hMul n v := ⟨n * v.x, n * v.y⟩

-- Exercise 14) Prove that vector addition is commutative.
theorem intVec_add_comm (u v : IntVec) : u + v = v + u := by
  show IntVec.mk _ _ = IntVec.mk _ _
  rw [add_comm u.x, add_comm u.y]

-- Exercise 15) Define a Zero instance for IntVec.
instance : Zero IntVec where
  zero := ⟨0, 0⟩

-- Exercise 16) Prove that adding zero on the right gives back the same vector.
theorem intVec_add_zero (v : IntVec) : v + 0 = v := by
  show IntVec.mk (v.x + 0) (v.y + 0) = v
  rw [add_zero, add_zero]

/- ## Part 3: Defining and using a custom typeclass -/

-- Exercise 17) Define a typeclass `Describable` that provides a `describe` method
-- returning a String description of a value.
class Describable (α : Type) where
  describe : α → String

-- Exercise 18) Create a Describable instance for ℕ.
instance : Describable ℕ where
  describe n := s!"the natural number {n}"

-- Exercise 19) Create a Describable instance for Bool.
instance : Describable Bool where
  describe b := if b then "true" else "false"

-- Exercise 20) Create a Describable instance for Option α
-- (when α is itself Describable).
instance [Describable α] : Describable (Option α) where
  describe
    | none => "nothing"
    | some a => s!"just {Describable.describe a}"

/- ## Part 4: Monadic computations with lists and state -/

-- Exercise 21) Using the list monad (do-notation with lists), generate all
-- pairs (x, y) where x ∈ [1,2,3] and y ∈ [1,2,3] and x + y = 4.
def sumToFour : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [1, 2, 3]
  guard (x + y = 4)
  return (x, y)

-- Exercise 22) Using the list monad, generate all Pythagorean triples
-- (a, b, c) with 1 ≤ a ≤ b ≤ c ≤ 20 and a*a + b*b = c*c.
def pythagoreanTriples : List (ℕ × ℕ × ℕ) := do
  let a ← List.range' 1 20
  let b ← List.range' a (21 - a)
  let c ← List.range' b (21 - b)
  guard (a * a + b * b = c * c)
  return (a, b, c)

-- Exercise 23) Define a stateful computation that takes a list of natural numbers
-- and adds each one to an accumulator state, returning the final sum.
-- Use StateM ℕ.
def statefulSum (xs : List ℕ) : StateM ℕ ℕ := do
  for x in xs do
    modify (· + x)
  get

-- Exercise 24) Define a stateful computation that processes a list of integers
-- and keeps track of both the running sum and the count of elements.
-- Use StateM (ℤ × ℕ).
def statefulSumAndCount (xs : List ℤ) : StateM (ℤ × ℕ) Unit := do
  for x in xs do
    modify fun (s, n) => (s + x, n + 1)

-- Exercise 25) Use Except to define a function that parses a simple
-- expression. Given a list like ["3", "+", "5"], return 8.
-- Given a list like ["7", "-", "2"], return 5.
-- Return an error message for anything else.
def simpleCalc (tokens : List String) : Except String ℤ :=
  match tokens with
  | [a, op, b] =>
    match a.toInt?, b.toInt? with
    | some x, some y =>
      match op with
      | "+" => .ok (x + y)
      | "-" => .ok (x - y)
      | _   => .error s!"unknown operator {op}"
    | _, _ => .error "not a number"
  | _ => .error "expected three tokens"
