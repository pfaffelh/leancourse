import Mathlib

/-
# Exercises on Monads and Typeclasses

These exercises cover the Option type, do-notation, typeclass instances,
and monadic programming. Replace each `sorry` with a correct implementation.
-/

/- ## Part 1: Option and safe computations -/

-- Exercise 1) Define a safe head function that returns none for an empty list.
def safeHead {α : Type} (xs : List α) : Option α :=
  sorry

-- Exercise 2) Define a safe function that returns the element at index n,
-- or none if the index is out of bounds.
def safeGet {α : Type} (xs : List α) (n : ℕ) : Option α :=
  sorry

-- Exercise 3) Define safe division that returns none when dividing by zero.
def safeDiv (a b : ℕ) : Option ℕ :=
  sorry

-- Exercise 4) Using do-notation, define a function that takes a list of
-- natural numbers and an index, gets the element at that index,
-- and then safely divides 100 by that element.
-- Return none if the index is out of bounds or the element is zero.
def divByElement (xs : List ℕ) (i : ℕ) : Option ℕ := do
  sorry

-- Exercise 5) Define a function that takes two lists and an index,
-- gets the element at that index from each list, and returns their sum.
-- Use do-notation.
def addAtIndex (xs ys : List ℕ) (i : ℕ) : Option ℕ := do
  sorry

-- Exercise 6) Define a function that finds the first element in a list
-- satisfying a predicate. Return none if no element satisfies it.
def findFirst {α : Type} (p : α → Bool) : List α → Option α :=
  sorry

-- Exercise 7) Chain three Option computations using do-notation:
-- Given a list of lists, get the i-th list, then get the j-th element of that list,
-- then safely divide 1000 by that element.
def nestedLookupAndDivide (xss : List (List ℕ)) (i j : ℕ) : Option ℕ := do
  sorry

/- ## Part 2: Typeclass instances -/

-- Here is a type representing days of the week.
inductive Day where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
  deriving Repr, BEq

-- Exercise 8) Define a ToString instance for Day.
instance : ToString Day where
  toString := sorry

-- Exercise 9) Define a function that returns the next day.
def Day.next : Day → Day :=
  sorry

-- Here is a structure for 2D vectors with integer coordinates.
structure IntVec where
  x : ℤ
  y : ℤ
  deriving Repr, BEq

-- Exercise 10) Define an Add instance for IntVec.
instance : Add IntVec where
  add := sorry

-- Exercise 11) Define a Neg instance for IntVec (negating both components).
instance : Neg IntVec where
  neg := sorry

-- Exercise 12) Define a ToString instance for IntVec.
-- Format: "(x, y)"
instance : ToString IntVec where
  toString := sorry

-- Exercise 13) Define an HMul instance so that an integer can scale a vector:
-- (n : ℤ) * (v : IntVec) = IntVec (n * v.x) (n * v.y)
instance : HMul ℤ IntVec IntVec where
  hMul := sorry

-- Exercise 14) Prove that vector addition is commutative.
theorem intVec_add_comm (u v : IntVec) : u + v = v + u := by
  sorry

-- Exercise 15) Define a Zero instance for IntVec.
instance : Zero IntVec where
  zero := sorry

-- Exercise 16) Prove that adding zero on the right gives back the same vector.
theorem intVec_add_zero (v : IntVec) : v + 0 = v := by
  sorry

/- ## Part 3: Defining and using a custom typeclass -/

-- Exercise 17) Define a typeclass `Describable` that provides a `describe` method
-- returning a String description of a value.
class Describable (α : Type) where
  describe : α → String

-- Exercise 18) Create a Describable instance for ℕ.
instance : Describable ℕ where
  describe := sorry

-- Exercise 19) Create a Describable instance for Bool.
instance : Describable Bool where
  describe := sorry

-- Exercise 20) Create a Describable instance for Option α
-- (when α is itself Describable).
instance [Describable α] : Describable (Option α) where
  describe := sorry

/- ## Part 4: Monadic computations with lists and state -/

-- Exercise 21) Using the list monad (do-notation with lists), generate all
-- pairs (x, y) where x ∈ [1,2,3] and y ∈ [1,2,3] and x + y = 4.
def sumToFour : List (ℕ × ℕ) := do
  sorry

-- Exercise 22) Using the list monad, generate all Pythagorean triples
-- (a, b, c) with 1 ≤ a ≤ b ≤ c ≤ 20 and a*a + b*b = c*c.
def pythagoreanTriples : List (ℕ × ℕ × ℕ) := do
  sorry

-- Exercise 23) Define a stateful computation that takes a list of natural numbers
-- and adds each one to an accumulator state, returning the final sum.
-- Use StateM ℕ.
def statefulSum (xs : List ℕ) : StateM ℕ ℕ := do
  sorry

-- Exercise 24) Define a stateful computation that processes a list of integers
-- and keeps track of both the running sum and the count of elements.
-- Use StateM (ℤ × ℕ).
def statefulSumAndCount (xs : List ℤ) : StateM (ℤ × ℕ) Unit := do
  sorry

-- Exercise 25) Use Except to define a function that parses a simple
-- expression. Given a list like ["3", "+", "5"], return 8.
-- Given a list like ["7", "-", "2"], return 5.
-- Return an error message for anything else.
def simpleCalc (tokens : List String) : Except String ℤ :=
  sorry
