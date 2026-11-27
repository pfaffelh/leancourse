import Mathlib

/-!
# 1.7-b -- Coercions

*Notes chapter 1.7, week 9.*

In mathematics a natural number *is* an integer. In Lean `ℕ` and `ℤ`
are different types, and moving between them is a *coercion*, written
`↑`. Coercions are instances, so instance resolution inserts them --
this is the same machinery as on sheet `1.6-a`, applied to the thing
you will trip over most often.

Three classes do three different jobs, and the chapter calls them
`Coe`, `CoeSort` and `CoeFun`. Numerals, which are also resolved
through a class, are on sheet `1.8-a`. Casts between number types,
`ℕ → ℤ → ℚ → ℝ`, are coercions too; they are practised on sheet
`2.1-a`, together with chapter 2.1.

## What is introduced here

| notation / tactic | use it when                                  |
|-------------------|----------------------------------------------|
| `↑x`, `(x : β)`   | write a coercion explicitly                  |
| `Coe`             | a value becomes a value of another type      |
| `CoeSort`         | a value becomes a *type*                     |
| `CoeFun`          | a bundled object is applied like a function  |
| `CoeDep`          | a coercion that exists only for some terms   |
| `instance : Coe`  | a coercion for your own structure            |
| `extends`         | a class that contains other classes          |

## Tactics from earlier sheets

| sheet   | tactics                                        |
|---------|------------------------------------------------|
| `L-a`   | `exact`                                        |
| `1.1-a` | `rfl`, `rw`, `show`                            |
| `1.1-b` | `decide`                                       |
| `L-f`   | `have`                                         |
| `1.1-c` | `ring`, `omega`, `calc`, `exact?`              |
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
## Part 5: Your own coercions

A `Coe` instance for your own structure is one line: it names the
function Lean inserts. A `CoeFun` instance says how a value is applied
to an argument.
-/

structure Pos where
  val : ℕ
  pos : 0 < val

-- Exercise 8: Let `Pos` coerce to `ℕ` by forgetting the proof.
instance : Coe Pos ℕ :=
  sorry

-- Exercise 9: `p.pos` is the proof that was forgotten. `have` it,
-- then `omega`.
example (p q : Pos) : 0 < (p : ℕ) + q := by
  sorry

/-- The map `x ↦ a * x + b`, stored as its two coefficients. -/
structure Affine where
  a : ℤ
  b : ℤ

-- Exercise 10: Let an `Affine` be applied to `x : ℤ`, with value
-- `f.a * x + f.b`.
instance : CoeFun Affine (fun _ => ℤ → ℤ) :=
  sorry

def Affine.comp (f g : Affine) : Affine :=
  ⟨f.a * g.a, f.a * g.b + f.b⟩

-- Exercise 11: Composition is what its name says. `show` makes the
-- coercion explicit: write out both sides with `.a` and `.b`, then
-- `ring`.
example (f g : Affine) (x : ℤ) : f.comp g x = f (g x) := by
  sorry

/-
## Part 6: Hierarchies with `extends`

`extends Mul α, One α` makes `MyMonoid α` contain a `*` and a `1`;
the class adds two laws. An instance of `MyMonoid` also provides
`Mul` and `One`, so `*` and `1` work for every monoid.
-/

class MyMonoid (α : Type) extends Mul α, One α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a

-- Exercise 12: `ℕ` is a monoid. `*` and `1` are already there; give
-- the two laws. `exact?` finds them.
instance : MyMonoid ℕ :=
  sorry

-- Exercise 13: The unit is unique: an `e` with `e * a = a` for all
-- `a` is `1`. Apply `h` to `1`.
theorem MyMonoid.one_unique {α : Type} [MyMonoid α] (e : α)
    (h : ∀ a : α, e * a = a) : e = 1 := by
  sorry

/-
## Part 7: Chains of coercions

Lean may insert several coercions in a row. Your instance from
Exercise 8 gives `Pos → ℕ`, and Lean has `ℕ → ℤ`; together they give
`Pos → ℤ`. The term Lean builds contains the functions inside the
instances, not `Coe.coe`: for `ℕ → ℤ` this is `Nat.cast`, for a
subtype it is `.val`.
-/

-- Exercise 14: Return `p` itself. Then `#print posToInt` and find the
-- two arrows.
def posToInt (p : Pos) : ℤ :=
  sorry

-- Exercise 15: Positive after both coercions. `have` the proof
-- `p.pos`, then `omega`.
example (p : Pos) : (0 : ℤ) < p := by
  sorry

-- Exercise 16: What the arrows unfold to. Both hold by definition.
example (n : ℕ) : (n : ℤ) = Nat.cast n := by
  sorry

example (s : {n : ℕ // n > 0}) : (s : ℕ) = s.val := by
  sorry

/-
## Part 8: `CoeDep` -- a coercion for some terms only

A `Prop` may stand where a `Bool` is expected, but only if it is
decidable: the coercion is `decide p`, and it needs an instance
`Decidable p`. Whether the coercion exists depends on the term `p`,
not only on its type `Prop`. This is the class `CoeDep`.
-/

-- Exercise 17: Write `n < 5` on the right. Lean inserts `decide`.
def isSmall (n : ℕ) : Bool :=
  sorry

example : isSmall 3 = true := by
  sorry

example : isSmall 7 = false := by
  sorry

-- Exercise 18: What Lean inserted.
example (n : ℕ) : isSmall n = decide (n < 5) := by
  sorry

-- Exercise 19: Writing `p` on the right fails for an arbitrary
-- `p : Prop`. Add one hypothesis in square brackets to the statement,
-- then write `p`.
example (p : Prop) : Bool :=
  sorry

/-
## Part 9: Where the arrow goes

Lean elaborates from the outside in. In `(a - b : ℤ)` with
`a b : ℕ`, the subtraction is already in `ℤ` and both arguments get
an arrow: `↑a - ↑b`. In `((a - b : ℕ) : ℤ)` the subtraction happens
in `ℕ`, and only the result is cast: `↑(a - b)`.
-/

-- Exercise 20: Replace each `sorry` on the right by an integer, then
-- prove the equation with `decide`.
example : ((5 - 7 : ℕ) : ℤ) = sorry := by
  sorry

example : ((5 : ℕ) - 7 : ℤ) = sorry := by
  sorry

-- Exercise 21: The same for division. Replace each `sorry` on the
-- right by a rational number, then `rfl`. (`decide` gets stuck on
-- the division in `ℚ`.)
example : ((7 / 2 : ℕ) : ℚ) = sorry := by
  sorry

example : ((7 : ℕ) / 2 : ℚ) = sorry := by
  sorry

-- Exercise 22: With `h`, the two positions of the arrow agree. Prove
-- it with `omega`. Then delete `h`: for which `n` is the statement
-- false?
example (n : ℕ) (h : 1 ≤ n) :
    ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  sorry
