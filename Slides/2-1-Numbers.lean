import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Numbers" of part 2 (Mathematics). It follows the
chapter section by section: how the number types are built, the real
numbers as a quotient, arithmetic in ℕ and ℤ, junk values, the three
powers, nonnegative and extended reals, casts.
-/

namespace SlidesNumbers
open scoped NNReal ENNReal

#doc (Slides) "Numbers" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .small table, .reveal section table.small { font-size: 0.5em; }
.reveal section .small table code, .reveal section table.small code { font-size: 0.95em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.6em; }
```

# Numbers

Mathematics — chapter 1

:::class "key"
Each number type is built with a type former of part 1. How it is built explains what is surprising about it.
:::

# How the number types are built

:::table +colHeaders +rowSeps
*
  * type
  * built as
  * chapter
*
  * `ℕ`
  * inductive: `zero`, `succ`
  * 1.1
*
  * `ℤ`
  * inductive: `ofNat`, `negSucc`
  * 1.2
*
  * `ℚ`
  * structure with proof fields
  * 1.2
*
  * `ℝ`
  * structure around a quotient
  * 1.4
*
  * `ℂ`
  * structure: `re`, `im`
  * 1.2
*
  * `ℝ≥0`
  * subtype of `ℝ`
  * 1.4
*
  * `ℝ≥0∞`
  * `Option ℝ≥0`
  * 1.2
:::

# ℤ and ℚ

```
inductive Int where
  | ofNat : ℕ → ℤ
  | negSucc : ℕ → ℤ          -- negSucc n = -(n + 1)

structure Rat where
  num : ℤ
  den : ℕ
  den_nz : den ≠ 0
  reduced : num.natAbs.Coprime den
```

```lean -panel -stretch
example : Int.negSucc 2 = -3 := rfl
#eval (6 / 4 : ℚ)   -- 3 / 2
```

:::class "key"
One representation per number: `negSucc n` is `-(n + 1)`, and fractions are reduced.
:::

# The real numbers as a quotient

A real number: a Cauchy sequence of rationals; sequences whose difference tends to `0` give the same number.

::::class "small"
:::table +colHeaders +rowSeps
*
  * step
  * in Mathlib
  * type former
*
  * Cauchy sequences
  * `CauSeq ℚ abs` = `{f : ℕ → ℚ // IsCauSeq abs f}`
  * subtype
*
  * their classes
  * `CauSeq.Completion.Cauchy abs`, by `f ≈ g ↔ f - g → 0`
  * quotient
*
  * `ℝ`
  * `structure Real` with one field `cauchy`
  * structure
:::
::::

```lean -panel -stretch
example (f g : CauSeq ℚ abs) :
    f ≈ g ↔ (f - g).LimZero := Iff.rfl
```

# Adding real numbers

```lean -panel -stretch
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

Add representatives termwise. Well defined: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`; then `Quot.lift` gives `+` on the classes.

:::class "key"
This equation is the computation rule `Quot.lift f h (Quot.mk r a) ⟶ f a`.
:::

# Computing with real numbers

```lean -panel -stretch
#eval (1 : ℝ) + 1   -- the first terms of a Cauchy sequence
example : (1 : ℝ) + 1 = 2 := by norm_num
```

`decide` and `rfl` fail: equality of real numbers is not decidable.

```lean +error -panel -stretch
def recip (x : ℝ) : ℝ := 1 / x
```

```lean -panel -stretch
noncomputable def reciprocal (x : ℝ) : ℝ := 1 / x
```

:::class "key"
Division, inverse and square root use `Classical.choice`: `noncomputable`.
:::

# Complex, nonnegative, extended

```
structure Complex where
  re : ℝ
  im : ℝ

def NNReal := { r : ℝ // 0 ≤ r }      -- ℝ≥0
def ENNReal := WithTop ℝ≥0            -- ℝ≥0∞
```

```lean -panel -stretch
example : Complex.I ^ 2 = -1 := Complex.I_sq
example (x : ℝ≥0) : 0 ≤ (x : ℝ) := x.2
```

`ℝ≥0∞` is `Option ℝ≥0`, with `none` read as `∞`, as `ℕ∞` in 1.2.

# Arithmetic in ℕ and ℤ

```lean -panel -stretch
example : (5 : ℕ) - 7 = 0 := rfl
example : (7 : ℕ) / 2 = 3 := rfl
example : (7 : ℕ) / 0 = 0 := rfl
#check @Nat.sub_add_cancel  -- m ≤ n → n - m + m = n

example : (-7 : ℤ) / 2 = -4 := by decide
example : (-7 : ℤ) % 2 = 1 := by decide
```

:::class "key"
Subtraction on `ℕ` is truncated; in `ℤ` the remainder is never negative.
:::

# Junk values

```lean -panel -stretch
example : (1 : ℝ) / 0 = 0 := div_zero 1
example : Real.sqrt (-1) = 0 :=
  Real.sqrt_eq_zero_of_nonpos (by norm_num)
example : Real.log 0 = 0 := Real.log_zero
#check @div_mul_cancel₀   -- b ≠ 0 → a / b * b = a
```

Every function is total. The condition sits in the theorems: a statement that is false for `b = 0` has the hypothesis `b ≠ 0`.

:::class "key"
No false statement follows from a junk value. If a theorem does not apply, look for the missing hypothesis.
:::

# Junk values in analysis

:::table +colHeaders +rowSeps
*
  * value
  * if undefined
  * predicate
*
  * `deriv f x`
  * `0`
  * `DifferentiableAt ℝ f x`
*
  * `∑' n, f n`
  * `0`
  * `Summable f`
*
  * `∫ x, f x ∂μ`
  * `0`
  * `Integrable f μ`
*
  * `sSup s` in `ℝ`
  * `0`
  * `s.Nonempty`, `BddAbove s`
*
  * `Nat.card α`
  * `0`
  * `Finite α`
:::

The theorems about the value assume the predicate.

# Three kinds of power

:::table +colHeaders +rowSeps
*
  * exponent
  * function
  * defined for
*
  * `n : ℕ`
  * `Monoid.npow`, repeated multiplication
  * every monoid
*
  * `n : ℤ`
  * `zpow`, `x ^ (-n) = (x ^ n)⁻¹`
  * groups, fields
*
  * `y : ℝ`
  * `Real.rpow`, via `exp` and `log`
  * `ℝ`, `ℝ≥0`, `ℂ`
:::

```lean -panel -stretch
example (x : ℝ) : x ^ (1 / 2) = 1 := by norm_num
example (x : ℝ) : x ^ ((1 : ℝ) / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
```

:::class "key"
A numeral in the exponent is a natural number: `1 / 2 = 0`.
:::

# The extended reals

```lean -panel -stretch
example : (∞ : ℝ≥0∞) + 1 = ∞ := by simp
example : (0 : ℝ≥0∞) * ∞ = 0 := by simp
example : (∞ : ℝ≥0∞) - ∞ = 0 := by simp
example : (1 : ℝ≥0∞) / 0 = ∞ := by simp
example : (∞ : ℝ≥0∞).toReal = 0 := by simp
```

:::class "key"
`ℝ≥0∞` is the value type of measures: every set has a measure, every nonnegative series a sum.
:::

# Casts

Coercions run along `ℕ → ℤ → ℚ → ℝ → ℂ`, and `ℝ≥0 → ℝ`, `ℝ≥0 → ℝ≥0∞`.

```lean -panel -stretch
example (n : ℕ) : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
  push_cast; ring
example : ((7 / 2 : ℕ) : ℝ) = 3 := by norm_num
#check @Nat.cast_sub   -- m ≤ n → ((n - m : ℕ) : R) = n - m
```

:::class "key"
A cast commutes with `+` and `*`, not with truncated `-` or with `/` on `ℕ`.
:::

# Summary

- `ℤ` and `ℚ` have one representation per number; `ℝ` is a structure around a quotient of Cauchy sequences.
- Real numbers do not compute: `norm_num` instead of `decide`; division is `noncomputable`.
- Functions are total; junk values are harmless because theorems carry the hypotheses.
- `x ^ n` means three functions, chosen by the type of the exponent.
- Casts move with `push_cast`, `norm_cast`, `exact_mod_cast`.
