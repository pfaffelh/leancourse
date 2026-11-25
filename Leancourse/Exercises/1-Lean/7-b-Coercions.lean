import Mathlib

/-!
# 1.7-b -- Coercions and casts

*Notes chapter 1.7, week 9.*

In mathematics a natural number *is* an integer. In Lean `ℕ` and `ℤ`
are different types, and moving between them is a *coercion*, written
`↑`. Coercions are instances, so instance resolution inserts them --
this is the same machinery as on sheet `1.6-a`, applied to the thing
you will trip over most often.

Three classes do three different jobs, and the chapter calls them
`Coe`, `CoeSort` and `CoeFun`. Numerals, which are also resolved
through a class, are on sheet `1.8-a`.

## What is introduced here

| notation / tactic | use it when                                  |
|-------------------|----------------------------------------------|
| `↑x`, `(x : β)`   | write a coercion explicitly                  |
| `Coe`             | a value becomes a value of another type      |
| `CoeSort`         | a value becomes a *type*                     |
| `CoeFun`          | a bundled object is applied like a function  |
| `norm_cast`       | normalise casts, often closing the goal      |
| `exact_mod_cast`  | `exact`, up to casts                         |
| `instance : Coe`  | a coercion for your own structure            |
| `extends`         | a class that contains other classes          |

## Tactics from earlier sheets

| sheet   | tactics                                        |
|---------|------------------------------------------------|
| `L-a`   | `exact`                                        |
| `1.1-a` | `rw`, `show`                                   |
| `L-f`   | `have`                                         |
| `1.1-c` | `ring`, `omega`, `push_cast`, `calc`, `exact?` |
-/

/-
## Part 1: The silent arrow

Lean inserts the coercion `ℕ → ℤ` without being asked. All three
lines below are the same term; only the second and third say so.
-/

example (n : ℕ) : ℤ := n        -- inserted silently
example (n : ℕ) : ℤ := ↑n       -- the same, written out
example (n : ℕ) : ℤ := (n : ℤ)  -- and again, as an ascription

/-
## Part 2: `Coe` -- a value becomes another value

The ordinary case. A subtype `{n : ℕ // n > 0}` is the type of
natural numbers carrying a proof that they are positive; it coerces
to `ℕ` by forgetting that proof. Subtypes in their own right are
chapter 1.4 and sheet `1.4-a` -- here they are only the most
convenient example of a coercion.
-/

-- Exercise 1: No tactic needed -- just hand Lean the subtype element
-- and let the coercion do the work.
example (s : {n : ℕ // n > 0}) : ℕ :=
  sorry

-- Exercise 2: The coerced value still satisfies the property.
-- Hint: the proof is the second component.
example (s : {n : ℕ // n > 0}) : (s : ℕ) > 0 :=
  sorry

/-
## Part 3: `CoeSort` -- a value becomes a type

`CoeSort` turns a term into something that may stand where a type is
expected. Two cases you will meet constantly: a `Bool` used as a
proposition (it means `b = true`), and a `Set α` used as a type (it
means the subtype of its members).
-/

-- Exercise 3: `(b : Prop)` unfolds to `b = true`, so the hypothesis
-- *is* the proof.
example (b : Bool) (h : b = true) : (b : Prop) :=
  sorry

-- Exercise 4: *Extra: uses `Set`, chapter 2.2.* A set, used where a
-- type is expected.
example (s : Set ℕ) : Type :=
  sorry

-- Exercise 5: *Extra: uses `Set`, chapter 2.2.* An element of that
-- type is a natural number again.
example (s : Set ℕ) (x : s) : ℕ :=
  sorry

/-
## Part 4: `CoeFun` -- a value becomes a function

`ℕ →+ ℕ` is the type of additive monoid homomorphisms. A term of it
is a *structure*, carrying a function together with proofs -- and yet
it may be applied like a plain function.
-/

-- Exercise 6: Apply the bundled morphism.
example (f : ℕ →+ ℕ) (n : ℕ) : ℕ :=
  sorry

-- Exercise 7: Being a homomorphism, it sends `0` to `0`.
-- Hint: `map_zero`.
example (f : ℕ →+ ℕ) : f 0 = 0 :=
  sorry

/-
## Part 5: The numeric chain

The chain is `ℕ → ℤ → ℚ → ℝ → ℂ`. A goal can fill up with `↑`s and
then `ring` or `linarith` will not fire, because the two sides are
not even the same type. Three tactics tidy this up:

* `push_cast` moves `↑` *inwards*, towards the leaves;
* `norm_cast` normalises and often closes the goal outright;
* `exact_mod_cast h` is `exact h`, up to casts.
-/

-- Exercise 8: The hypothesis is already cast-free inside; push the
-- cast in the goal inwards and finish.
example (n m : ℕ) (h : (n : ℤ) + m = 10) : (↑(n + m) : ℤ) = 10 := by
  sorry

-- Exercise 9: `ring` alone fails here -- the left side is a cast of
-- a sum, the right side a sum of casts. Fix that first.
example (n m : ℕ) : ((n + m : ℕ) : ℤ) ^ 2
    = (n : ℤ) ^ 2 + 2 * n * m + (m : ℤ) ^ 2 := by
  sorry

-- Exercise 10: An inequality that survives the cast.
example (n : ℕ) (h : n < 5) : (n : ℤ) < 5 := by
  sorry

-- Exercise 11: One tactic closes this.
example (n : ℕ) : ((n : ℤ) = 0) ↔ n = 0 := by
  sorry

-- Exercise 12: Two steps up the chain at once.
example (a b : ℕ) (h : (a : ℚ) = b) : a = b := by
  sorry

-- Exercise 13: Subtraction is the dangerous one, because `ℕ` cuts
-- off at zero. With `1 ≤ n` the statement is true; `omega` knows
-- both `ℕ` and `ℤ` and handles the casts itself.
example (n : ℕ) (h : 1 ≤ n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  sorry

-- Without the hypothesis the statement is false: for `n = 0` the
-- left side is `0` and the right side `-1`. Uncomment and watch
-- `omega` refuse:
-- example (n : ℕ) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega

/-
## Part 6: Your own coercions

A `Coe` instance for your own structure is one line: it names the
function Lean inserts. A `CoeFun` instance says how a value is applied
to an argument.
-/

structure Pos where
  val : ℕ
  pos : 0 < val

-- Exercise 14: Let `Pos` coerce to `ℕ` by forgetting the proof.
instance : Coe Pos ℕ :=
  sorry

-- Exercise 15: `p.pos` is the proof that was forgotten. `have` it,
-- then `omega`.
example (p q : Pos) : 0 < (p : ℕ) + q := by
  sorry

/-- The map `x ↦ a * x + b`, stored as its two coefficients. -/
structure Affine where
  a : ℤ
  b : ℤ

-- Exercise 16: Let an `Affine` be applied to `x : ℤ`, with value
-- `f.a * x + f.b`.
instance : CoeFun Affine (fun _ => ℤ → ℤ) :=
  sorry

def Affine.comp (f g : Affine) : Affine :=
  ⟨f.a * g.a, f.a * g.b + f.b⟩

-- Exercise 17: Composition is what its name says. `show` makes the
-- coercion explicit: write out both sides with `.a` and `.b`, then
-- `ring`.
example (f g : Affine) (x : ℤ) : f.comp g x = f (g x) := by
  sorry

/-
## Part 7: Hierarchies with `extends`

`extends Mul α, One α` makes `MyMonoid α` contain a `*` and a `1`;
the class adds two laws. An instance of `MyMonoid` also provides
`Mul` and `One`, so `*` and `1` work for every monoid.
-/

class MyMonoid (α : Type) extends Mul α, One α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a

-- Exercise 18: `ℕ` is a monoid. `*` and `1` are already there; give
-- the two laws. `exact?` finds them.
instance : MyMonoid ℕ :=
  sorry

-- Exercise 19: The unit is unique: an `e` with `e * a = a` for all
-- `a` is `1`. Apply `h` to `1`.
theorem MyMonoid.one_unique {α : Type} [MyMonoid α] (e : α)
    (h : ∀ a : α, e * a = a) : e = 1 := by
  sorry
