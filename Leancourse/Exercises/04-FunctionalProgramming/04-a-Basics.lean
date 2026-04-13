import Mathlib

/-
# Exercises on Functional Programming Basics

These exercises cover recursive functions, pattern matching on inductive types,
and higher-order functions. Replace each `sorry` with a correct implementation.
-/

/- ## Part 1: Recursive functions on natural numbers -/

-- Exercise 1) Define a function that computes the sum 0 + 1 + 2 + ... + n.
def sumUpTo : ℕ → ℕ :=
  sorry

-- Test: sumUpTo 5 should be 15
-- #eval sumUpTo 5

-- Exercise 2) Define a function that computes n! (factorial).
def myFactorial : ℕ → ℕ :=
  sorry

-- Exercise 3) Define a function that computes the n-th Fibonacci number.
-- fib 0 = 0, fib 1 = 1, fib (n+2) = fib n + fib (n+1)
def myFib : ℕ → ℕ :=
  sorry

-- Exercise 4) Define exponentiation: myPow b n = b^n.
def myPow (b : ℕ) : ℕ → ℕ :=
  sorry

-- Exercise 5) Prove that your sumUpTo function satisfies 2 * sumUpTo n = n * (n + 1).
-- Hint: Use induction on n.
theorem sumUpTo_formula (n : ℕ) : 2 * sumUpTo n = n * (n + 1) := by
  sorry

/- ## Part 2: Inductive types and pattern matching -/

-- Here is a type representing a simple arithmetic expression.
inductive Expr where
  | lit : ℕ → Expr                     -- a literal number
  | add : Expr → Expr → Expr           -- addition
  | mul : Expr → Expr → Expr           -- multiplication

-- Exercise 6) Write a function that evaluates an expression to a natural number.
def Expr.eval : Expr → ℕ :=
  sorry

-- Exercise 7) Write a function that counts the number of literal values in an expression.
def Expr.countLits : Expr → ℕ :=
  sorry

-- Exercise 8) Write a function that computes the depth (height) of an expression tree.
-- A literal has depth 0. An add or mul node has depth 1 + max of children depths.
def Expr.depth : Expr → ℕ :=
  sorry

-- Here is a binary tree type.
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node : BinTree α → α → BinTree α → BinTree α

-- Exercise 9) Count the number of nodes in a binary tree (leaves do not count).
def BinTree.size {α : Type} : BinTree α → ℕ :=
  sorry

-- Exercise 10) Compute the height of a binary tree (a leaf has height 0).
def BinTree.height {α : Type} : BinTree α → ℕ :=
  sorry

-- Exercise 11) Collect all values in a binary tree into a list (in-order traversal).
def BinTree.toList {α : Type} : BinTree α → List α :=
  sorry

/- ## Part 3: Higher-order functions on lists -/

-- Exercise 12) Without using List.map, define your own map function.
def myMap {α β : Type} (f : α → β) : List α → List β :=
  sorry

-- Exercise 13) Without using List.filter, define your own filter function.
def myFilter {α : Type} (p : α → Bool) : List α → List α :=
  sorry

-- Exercise 14) Define foldl (fold from the left) without using List.foldl.
-- foldl f init [a, b, c] = f (f (f init a) b) c
def myFoldl {α β : Type} (f : β → α → β) (init : β) : List α → β :=
  sorry

-- Exercise 15) Use List.map and List.foldl to compute the sum of squares
-- of a list of natural numbers.
def sumOfSquares (xs : List ℕ) : ℕ :=
  sorry

-- Exercise 16) Define a function that checks whether all elements of a list
-- satisfy a predicate. Use List.foldl or recursion.
def myAll {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  sorry

-- Exercise 17) Define function composition for three functions.
-- compose3 h g f should be the function x ↦ h(g(f(x))).
def compose3 {α β γ δ : Type} (h : γ → δ) (g : β → γ) (f : α → β) : α → δ :=
  sorry

-- Exercise 18) Define a function `applyTwice` that applies a function twice.
def applyTwice {α : Type} (f : α → α) (x : α) : α :=
  sorry

-- Exercise 19) Use applyTwice with (· + 1) applied to 0 to get 2.
-- Then prove the result equals 2.
example : applyTwice (· + 1) 0 = 2 := by
  sorry

-- Exercise 20) Define a function that reverses a list using foldl.
-- Hint: foldl with an accumulator that builds the reversed list.
def myReverse {α : Type} (xs : List α) : List α :=
  sorry
