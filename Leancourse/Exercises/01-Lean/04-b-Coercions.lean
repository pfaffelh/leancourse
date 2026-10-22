import Mathlib

/-!
# 1.4-b -- Coercions and casts

*Notes chapter 1.4, week 5.*

In mathematics a natural number *is* an integer. In Lean `ℕ` and `ℤ`
are different types, and moving between them is a *coercion*, written
`↑`. Coercions are instances, so instance resolution inserts them --
this is the same machinery as on sheet `1.4-a`, applied to the thing
you will trip over most often.

Three classes do three different jobs, and the chapter calls them
`Coe`, `CoeSort` and `CoeFun`. The last part of the sheet is about
numerals, which are also resolved through a class.

## What is introduced here

| notation / tactic | use it when                                     |
|-------------------|-------------------------------------------------|
| `↑x`, `(x : β)`   | write a coercion explicitly                     |
| `Coe`             | a value becomes a value of another type         |
| `CoeSort`         | a value becomes a *type*                        |
| `CoeFun`          | a bundled object is applied like a function     |
| `push_cast`       | push `↑` inwards: `↑(a+b)` becomes `↑a + ↑b`    |
| `norm_cast`       | normalise casts, often closing the goal         |
| `exact_mod_cast`  | `exact`, up to casts                            |
| `OfNat`           | the class behind the numeral `2`                |
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
chapter 1.6 and sheet `1.6-a` -- here they are only the most
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

-- Exercise 4: A set, used where a type is expected.
example (s : Set ℕ) : Type :=
  sorry

-- Exercise 5: An element of that type is a natural number again.
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
## Part 6: `OfNat` -- where numerals come from

Even `2` is resolved through a class: writing `2` means
`OfNat.ofNat 2`, and which `2` you get depends on the instance.
-/

#check @OfNat.ofNat
-- {α : Type u_1} → (x : ℕ) → [self : OfNat α x] → α

-- Exercise 14: The numeral and the explicit form are the same term.
example : (2 : ℤ) = OfNat.ofNat 2 := by
  sorry

structure Pt where
  x : ℤ
  y : ℤ
deriving Repr, DecidableEq

-- Exercise 15: Give `Pt` a zero, so that the numeral `0` may be
-- written for the origin.
instance : OfNat Pt 0 :=
  sorry

-- Exercise 16: Once the instance is there, this holds by `rfl`.
example : (0 : Pt) = ⟨0, 0⟩ := by
  sorry

-- #eval (0 : Pt)   -- uncomment after Exercise 15
