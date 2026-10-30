import Mathlib

/-!
# 1.6-c -- Functors and monads

*Notes chapter 1.6, week 8.*

`Option` and `List` are type constructors, and the classes `Functor`
and `Monad` are classes over them. Read the section *Classes over type
constructors* of chapter 1.6 first.

## Introduced here

| notation         | what it does                                     |
|------------------|--------------------------------------------------|
| `g <$> x`        | `map`: apply `g` inside `x`                      |
| `pure a`         | the computation that returns `a`                 |
| `x >>= f`        | `bind`: run `x`, pass its result to `f`          |
| `do`             | a sequence of steps, translated into `>>=`       |
| `let a ← x`      | a step of a `do` block: run `x`, call it `a`     |
| `return a`       | `pure a`, as the last step of a `do` block       |
| `guard c`        | in the list monad: keep this branch only if `c`  |
| `id_map`         | the law `id <$> x = x`                           |
| `comp_map`       | the law `(g ∘ f) <$> x = g <$> f <$> x`          |

The definitions below come with `#eval` lines. Uncomment them once your
definition is in place and compare with the expected output.
-/

/-! ## Part 1: `map`

`map` applies a function inside, without changing the shape: `none`
stays `none`, and a list keeps its length. -/

example : (· + 10) <$> (some 5 : Option ℕ) = some 15 := rfl

-- Exercise 1) Replace `sorry` by the list, then `rfl`.
example : (· * 3) <$> [1, 2, 3] = sorry := by
  sorry

-- Exercise 2) Replace `sorry` by the value, then `rfl`.
example : (· + 1) <$> (none : Option ℕ) = sorry := by
  sorry

-- Exercise 3) The first functor law. One term does it.
example (xs : List ℕ) : id <$> xs = xs := by
  sorry

-- Exercise 4) The second functor law.
example (f g : ℕ → ℕ) (x : Option ℕ) :
    (g ∘ f) <$> x = g <$> f <$> x := by
  sorry

/-! ## Part 2: `Option` as a monad

A function that may fail returns an `Option`. With `do`, several of
them run one after the other, and the first `none` ends the chain. -/

def safeDivide (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)

def divideTwice (a b c : ℕ) : Option ℕ := do
  let r ← safeDivide a b
  safeDivide r c

example : divideTwice 100 5 4 = some 5 := rfl
example : divideTwice 100 0 4 = none := rfl

-- Exercise 5) The first element of a list, `none` for `[]`. Use
-- pattern matching.
def safeHead {α : Type} (xs : List α) : Option α :=
  sorry

-- #eval safeHead [3, 4]     -- some 3
-- #eval safeHead ([] : List ℕ)  -- none

-- Exercise 6) The element at index `n`, counting from `0`, and `none`
-- if the list is too short. Use pattern matching on `xs` and `n`
-- together and recursion.
def safeGet {α : Type} (xs : List α) (n : ℕ) : Option α :=
  sorry

-- #eval safeGet [5, 7] 1    -- some 7
-- #eval safeGet [5, 7] 2    -- none

-- Exercise 7) `a / b`, and `none` for `b = 0`.
def safeDiv (a b : ℕ) : Option ℕ :=
  sorry

-- Exercise 8) Take the element at index `i` and divide `100` by it.
-- `none` if the index is out of range or the element is `0`. Use `do`.
def divByElement (xs : List ℕ) (i : ℕ) : Option ℕ :=
  sorry

-- #eval divByElement [5, 0] 0   -- some 20
-- #eval divByElement [5, 0] 1   -- none

-- Exercise 9) The sum of the elements at index `i` of both lists.
def addAtIndex (xs ys : List ℕ) (i : ℕ) : Option ℕ :=
  sorry

-- #eval addAtIndex [1, 2] [10, 20] 1   -- some 22

-- Exercise 10) Take the `i`-th list, its `j`-th element, and divide
-- `1000` by it. Three steps.
def nestedDivide (xss : List (List ℕ)) (i j : ℕ) :
    Option ℕ :=
  sorry

-- #eval nestedDivide [[1], [3, 4]] 1 1   -- some 250

/-! ## Part 3: The laws for `Option`

For `Option`, every law is a computation. `cases x` gives the two
cases `none` and `some a`, and in each `rfl` finishes. -/

-- Exercise 11) Left identity.
example (a : ℕ) (f : ℕ → Option ℕ) :
    (pure a >>= f) = f a := by
  sorry

-- Exercise 12) Right identity.
example (x : Option ℕ) : (x >>= pure) = x := by
  sorry

-- Exercise 13) Associativity.
example (x : Option ℕ) (f g : ℕ → Option ℕ) :
    (x >>= f >>= g) = (x >>= fun a => f a >>= g) := by
  sorry

-- Exercise 14) `map` is `bind` followed by `pure`.
example (f : ℕ → ℕ) (x : Option ℕ) :
    f <$> x = (x >>= fun a => pure (f a)) := by
  sorry

/-! ## Part 4: Lists as a monad

In the list monad, `let x ← xs` means "for each `x` in `xs`".
`guard c` drops the current branch when `c` is false. -/

def pairs : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [10, 20]
  return (x, y)

example : pairs.length = 6 := rfl

-- Exercise 15) Replace `sorry` by the list, then `rfl`.
example : ([1, 2] >>= fun x => [x, x + 1]) = sorry := by
  sorry

-- Exercise 16) All pairs `(x, y)` with `x` and `y` in `[1, 2, 3]` and
-- `x + y = 4`, in this order: `[(1, 3), (2, 2), (3, 1)]`.
def sumToFour : List (ℕ × ℕ) :=
  sorry

-- #eval sumToFour

-- Exercise 17) All Pythagorean triples `(a, b, c)` with
-- `1 ≤ a ≤ b ≤ c ≤ 20`. `List.range' k n` is `[k, k + 1, …, k + n - 1]`.
def pythagoreanTriples : List (ℕ × ℕ × ℕ) :=
  sorry

-- #eval pythagoreanTriples
