import Mathlib

/-
# 1.8-a -- Defining your own notation

*Notes chapter 1.8, week 10.*

These exercises accompany chapter 1.8, *Notation and
abbreviations*. You will practice `notation`, `infixl`, `infixr`,
`prefix`, `postfix`, and `scoped` notation. Part 6 turns the order
of operations upside down. Part 7 reads Mathlib's notation (`∑`,
`∫`, `{x | p x}`, `∀ᶠ`) and the derivative, which has none. The
eighth part is about numerals, which are not declared notation but
are resolved through the class `OfNat`. The last part is about
`abbrev`, `▸` and `<|`.

Each exercise is stated as a comment.  Write the requested notation
declaration, then uncomment the `example` check lines below it to
verify that your declaration has the intended effect.

Because notation declarations are *commands* (not tactics), you
cannot leave them as `sorry`; instead, replace the template with a
real declaration.

## What is introduced here

| notation                        | use it when                               |
|---------------------------------|-------------------------------------------|
| `∑ i ∈ s, f i`                  | a finite sum, `Finset.sum s (fun i => f i)` |
| `deriv f x`                     | the derivative of `f : ℝ → ℝ` at `x`      |
| `set_option pp.notation false in` | to see what notation stands for         |
| `OfNat`                         | the class behind the numeral `2`          |
| `abbrev T := τ`                 | a shorthand instance search unfolds       |
| `inferInstanceAs (C τ)`         | reuse the instance of `τ` for a `def`     |
| `h ▸ e`                         | rewrite the type of `e` with `h : a = b`  |
| `f <| x`                        | `f x`, without parentheses around `x`     |

## Tactics from earlier sheets

| sheet   | tactics               |
|---------|-----------------------|
| `1.1-a` | `rfl`                 |
| `1.1-c` | `ring`, `norm_num`    |
-/

/- ## Part 1: Simple `notation` -/

-- Exercise 1.
-- Introduce a 0-ary symbol `π₂` that stands for `(2 : ℕ)`.
-- Template:
--   notation "π₂" => (2 : ℕ)
-- Then uncomment to check:
--   example : π₂ = 2 := rfl

-- Exercise 2.
-- Introduce a unary notation `sq x` meaning `x * x` on ℕ.
-- Template (fill in the right-hand side):
--   notation "sq " x => ?_
-- Then uncomment to check:
--   example : (sq 5 : ℕ) = 25 := rfl
-- The ascription is not decoration. Without it, `sq 5 = 25` parses
-- as `sq (5 = 25)`: a `notation` with a trailing placeholder takes
-- the longest term it can, so it swallows the equation. Giving the
-- precedence, `notation:max "sq " x:max => x * x`, is the other way
-- out.

-- Exercise 3.
-- Introduce a binary notation `avg(a, b)` meaning `(a + b) / 2`.
-- Note that every atom between the placeholders must be a real
-- token -- a bare `" "` is rejected with *invalid atom*, which is
-- why the comma and the brackets are there.
-- Template:
--   notation "avg(" a ", " b ")" => ?_
-- Then uncomment:
--   example : (avg(4, 6) : ℕ) = 5 := rfl

/- ## Part 2: Infix operators -/

-- Exercise 4.
-- Introduce a left-associative infix `⊙` at precedence 65 meaning
-- `fun (a b : ℕ) => a + 2 * b`.
-- Template:
--   infixl:65 " ⊙ " => fun (a b : ℕ) => ?_
-- Then uncomment:
--   example : (1 ⊙ 2 : ℕ) = 5 := rfl
--   -- Left-associativity: (1 ⊙ 2) ⊙ 3 = 5 + 2 * 3 = 11
--   example : (1 ⊙ 2 ⊙ 3 : ℕ) = 11 := rfl

-- Exercise 5.
-- Introduce a right-associative infix `▷` at precedence 65 with the
-- same underlying operation as in Exercise 4.
-- Template:
--   infixr:65 " ▷ " => fun (a b : ℕ) => a + 2 * b
-- Right-associativity: 1 ▷ 2 ▷ 3 = 1 ▷ (2 + 2*3) = 1 + 2*(2 + 6) = 17
--   example : (1 ▷ 2 ▷ 3 : ℕ) = 17 := rfl

/- ## Part 3: `prefix` and `postfix` -/

-- Exercise 6.
-- Introduce a prefix operator `⋄` (type `\diamond`) at precedence 80
-- that doubles a natural number.
-- Template:
--   prefix:80 "⋄" => fun n : ℕ => ?_
-- Then uncomment:
--   example : ⋄7 = 14 := rfl

-- Exercise 7.
-- Introduce a postfix operator `⁺⁺` at precedence 90 that adds 1 to
-- a natural number.  (Think of C's `++`.)
-- Template:
--   postfix:90 "⁺⁺" => fun n : ℕ => ?_
-- Then uncomment:
--   example : (3 : ℕ)⁺⁺ = 4 := rfl

/- ## Part 4: `scoped` notation -/

-- Exercise 8.
-- Inside the namespace below, declare a *scoped* notation `↯` for
-- `(100 : ℕ)`.  After your declaration and `open scoped MyArith`,
-- uncomment the `example` line.

namespace MyArith
  -- Your scoped notation goes here.
  -- scoped notation "↯" => (100 : ℕ)
end MyArith

-- open scoped MyArith
-- example : ↯ = 100 := rfl

/- ## Part 5: Mixing notation -/

-- Exercise 9.
-- Introduce a prefix-like notation `‖x‖₁` for `Int.natAbs x`, valid
-- on integers.  Then uncomment:
-- Template:
--   notation "‖" x "‖₁" => Int.natAbs x
--   example : ‖(-3 : ℤ)‖₁ = 3 := rfl
--   example (n : ℤ) : 0 ≤ (‖n‖₁ : ℤ) := by omega

-- Exercise 10.
-- Introduce a ternary notation `if! c then! a else! b` (with
-- `c : Bool`) meaning `bif c then a else b`.
-- Template:
--   notation "if! " c " then! " a " else! " b => bif c then a else b
-- Then uncomment:
--   example : (if! true  then! 1 else! 2 : ℕ) = 1 := rfl
--   example : (if! false then! 1 else! 2 : ℕ) = 2 := rfl

/-
## Part 6: Addition before multiplication

`+` and `-` have precedence `65`, `*` and `/` have `70`, `=` has `50`.
A higher number binds tighter, which is why `2 + 3 * 4` is `14`. With
two new symbols you can turn this around. Type `∗` as `\ast` and `÷`
as `\div`. The notation is `local` to the section, so the rest of the
file keeps the usual rules.
-/

section AdditionFirst

-- Exercise 11.
-- Declare `∗` for multiplication and `÷` for division, both
-- left-associative, with a precedence that makes `+` and `-` bind
-- tighter than `∗` and `÷`.
-- Template:
--   local infixl:?? " ∗ " => HMul.hMul
--   local infixl:?? " ÷ " => HDiv.hDiv
-- Then uncomment:
--   example : (2 : ℕ) + 3 ∗ 4 = 20 := rfl
--   example : (3 : ℕ) ∗ 4 + 2 = 18 := rfl
--   example : (8 : ℕ) - 2 ÷ 3 = 2 := rfl
--   example : (12 : ℕ) ÷ 2 ∗ 3 = 18 := rfl

-- Exercise 12.
-- Which precedences pass all four checks? Try `65` and `50` as well,
-- and explain in a comment why they fail.

-- Exercise 13.
-- The distributive law, in the new notation. Uncomment, read the
-- error, and add the brackets that make it the distributive law
-- again. Then prove it with `ring`.
--   example (a b c : ℚ) : a ∗ (b + c) = a ∗ b + a ∗ c := by ring

end AdditionFirst

/-
## Part 7: Notation in Mathlib

Mathlib's notation binds a variable, and the bound variable becomes a
`fun`: `∑ i ∈ s, f i` is `Finset.sum s (fun i => f i)`. To see what a
piece of notation stands for, print it without notation:
-/

set_option pp.notation false in
#check ∑ i ∈ Finset.range 3, i ^ 2

-- Exercise 14.
-- Predict both values before you compute anything. Then replace `?`
-- by your numbers and uncomment; `rfl` checks them. Explain the
-- difference in a comment.
--   example : ∑ i ∈ Finset.range 4, i + 1 = ? := rfl
--   example : ∑ i ∈ Finset.range 4, (i + 1) = ? := rfl

-- Exercise 15.
-- Find out with `set_option pp.notation false in #check` what the
-- left-hand sides stand for. Write that on the right, without the
-- notation, and uncomment.
--   example (f : ℕ → ℕ) : ∑ i ∈ Finset.range 5, f i = ? := rfl
--   example : {x : ℕ | x < 3} = ? := rfl
--   example (p : ℕ → Prop) : (∀ᶠ n in Filter.atTop, p n) = ? := rfl
--   example : ∫ x in (0 : ℝ)..1, x + 1 = ? := rfl
-- In the last one: is `+ 1` inside the integral or outside?
-- You need not know what `Filter.Eventually` or the integral mean;
-- only what the notation stands for.

-- Exercise 16.
-- The derivative has no notation: `deriv f x` takes the function as
-- an argument, written with `fun`. `norm_num` knows derivatives of
-- polynomials (`deriv_pow` etc.).
example : deriv (fun x : ℝ => x ^ 3) 2 = 12 := by
  sorry

/-
## Part 8: `OfNat` -- where numerals come from

Even `2` is resolved through a class: writing `2` means
`OfNat.ofNat 2`, and which `2` you get depends on the instance.
-/

#check @OfNat.ofNat
-- {α : Type u_1} → (x : ℕ) → [self : OfNat α x] → α

-- Exercise 17.
-- The numeral and the explicit form are the same term.
example : (2 : ℤ) = OfNat.ofNat 2 := by
  sorry

structure Pt where
  x : ℤ
  y : ℤ
deriving Repr, DecidableEq

-- Exercise 18.
-- Give `Pt` a zero, so that the numeral `0` may be written for the
-- origin.
instance : OfNat Pt 0 :=
  sorry

-- Exercise 19.
-- Once the instance is there, this holds by `rfl`.
example : (0 : Pt) = ⟨0, 0⟩ := by
  sorry

-- #eval (0 : Pt)   -- uncomment after Exercise 18

/-
## Part 9: Shorthands and `abbrev`

`def Meters := ℕ` makes a new name that instance search treats as a
new type. `abbrev Seconds := ℕ` is a shorthand that instance search
unfolds.
-/

def Meters := ℕ
abbrev Seconds := ℕ

example (a b : Seconds) : Seconds := a + b   -- works

-- Exercise 20.
-- Uncomment the line below and read the error. Explain in a comment
-- why it fails. Why does instance search see through `abbrev` but not
-- through `def`?
--   example (a b : Meters) : Meters := a + b

-- Exercise 21.
-- Give `Meters` an addition. `inferInstanceAs (Add ℕ)` hands over the
-- instance of `ℕ`. Then the example below works.
instance : Add Meters :=
  sorry

example (a b : Meters) : Meters := a + b

-- Exercise 22.
-- `h ▸ e` rewrites the type of `e` with `h : a = b`. Prove it in one
-- term.
example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) (ha : f a = 0) :
    f b = 0 :=
  sorry

-- Exercise 23.
-- `f <| x` is `f x`; it saves the parentheses around a long `x`.
-- Prove it with `absurd` and `<|`.
example (P Q : Prop) (hP : P) (hnP : ¬P) : Q :=
  sorry
