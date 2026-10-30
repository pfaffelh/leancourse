import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef
open scoped NNReal ENNReal

set_option pp.rawOnError true

#doc (Manual) "Numbers" =>
%%%
htmlSplit := .never
tag := "numbers"
%%%

Mathlib has a type for each number system. Each of them is built with one of the type formers of the {ref "lean"}[Lean part], and how it is built explains most of what is surprising about it: why `5 - 7 = 0` in `ℕ`, why `1 / 0 = 0` in `ℝ`, and why a natural number in a real computation carries an arrow `↑`.

# Notation
%%%
tag := "numbers-notation"
%%%

:::table +header
* + Symbol
  + Lean name
  + Typed as
* + `ℕ`
  + `Nat`
  + `\N`
* + `ℤ`
  + `Int`
  + `\Z`
* + `ℚ`
  + `Rat`
  + `\Q`
* + `ℝ`
  + `Real`
  + `\R`
* + `ℂ`
  + `Complex`
  + `\C`
* + `ℝ≥0`
  + `NNReal`
  + `\R\ge0`
* + `ℝ≥0∞`
  + `ENNReal`
  + `\R\ge0\infty`
* + `↑x`
  + `Nat.cast`, `Int.cast`, ...
  + `\u`
:::

`ℝ≥0` and `ℝ≥0∞` are available after `open scoped NNReal ENNReal`.

# How the number types are built
%%%
tag := "number-types"
%%%

`ℕ` is the inductive type with constructors `zero` and `succ` of {ref "nat"}[chapter 1.1]. `ℤ` is an inductive type with two constructors as well: `ofNat n` is the integer `n`, and `negSucc n` is `-(n + 1)`. The shift by one makes every integer have exactly one representation; there is no second zero.

```lean
#print Int
-- constructors:
-- Int.ofNat : ℕ → ℤ
-- Int.negSucc : ℕ → ℤ
example : Int.negSucc 2 = -3 := rfl
```

`ℚ` is a {ref "structures"}[structure] with two data fields and two proof fields: the numerator, the denominator, a proof that the denominator is not `0`, and a proof that the fraction is reduced. A rational number has only one representation, so equality of rationals is equality of the fields.

```lean
#print Rat
-- fields:
--   Rat.num : ℤ
--   Rat.den : ℕ
--   Rat.den_nz : self.den ≠ 0
--   Rat.reduced : self.num.natAbs.Coprime self.den
#eval (6 / 4 : ℚ)       -- 3 / 2
#eval (6 / 4 : ℚ).den   -- 2
```

`ℝ` is a structure with one field, an element of the quotient of the Cauchy sequences of rationals, as described in {ref "reals-quotient"}[Example: the real numbers]. A real number is not a finite object. `#eval` shows the first terms of a Cauchy sequence that represents it, and equality of real numbers is not decidable, so `decide` and `rfl` fail even on `1 + 1 = 2`. Concrete computations with real numbers are proved with `norm_num`.

```lean
#eval (1 : ℝ) + 1
-- Real.ofCauchy (sorry /- 2, 2, 2, 2, 2, 2, ... -/)
```

```lean +error
example : (1 : ℝ) + 1 = 2 := by decide
```

```lean
example : (1 : ℝ) + 1 = 2 := by norm_num
example : (1 : ℝ) < 2 := by norm_num
```

`ℂ` is a structure with fields `re` and `im`. Two complex numbers are equal when real and imaginary parts are equal, `Complex.ext_iff`.

```lean
#print Complex
-- fields:
--   Complex.re : ℝ
--   Complex.im : ℝ
example : Complex.I ^ 2 = -1 := Complex.I_sq
```

The nonnegative reals `ℝ≥0` are a {ref "subtypes"}[subtype] of `ℝ`, and `ℝ≥0∞` adds a largest element `∞` to them. It is `WithTop ℝ≥0`, which is `Option ℝ≥0` with `none` read as `∞`, as for `ℕ∞` in {ref "inductive"}[chapter 1.2].

```lean
#print NNReal    -- { r // 0 ≤ r }
#print ENNReal   -- WithTop ℝ≥0
#print WithTop   -- fun α => Option α
example (x : ℝ≥0) : 0 ≤ (x : ℝ) := x.2
```

:::table (align := left) +header
* + type
  + built as
  + see
* + `ℕ`
  + inductive: `zero`, `succ`
  + {ref "nat"}[1.1]
* + `ℤ`
  + inductive: `ofNat`, `negSucc`
  + {ref "inductive"}[1.2]
* + `ℚ`
  + structure with proof fields
  + {ref "structures"}[1.2]
* + `ℝ`
  + structure around a quotient
  + {ref "reals-quotient"}[1.4]
* + `ℂ`
  + structure: `re`, `im`
  + {ref "structures"}[1.2]
* + `ℝ≥0`
  + subtype of `ℝ`
  + {ref "subtypes"}[1.4]
* + `ℝ≥0∞`
  + `Option ℝ≥0`
  + {ref "inductive"}[1.2]
:::

# Arithmetic in ℕ and ℤ
%%%
tag := "nat-int-arithmetic"
%%%

Subtraction on `ℕ` is *truncated*: a difference that would be negative is `0`. Division is division with remainder, rounded down, and division by `0` gives `0`.

```lean
example : (5 : ℕ) - 7 = 0 := rfl
example : (7 : ℕ) / 2 = 3 := rfl
example : (7 : ℕ) % 2 = 1 := rfl
example : (7 : ℕ) / 0 = 0 := rfl
```

So `n - m + m = n` holds only if `m ≤ n`, and the theorem says so:

```lean
#check @Nat.sub_add_cancel
-- ∀ {n m : ℕ}, m ≤ n → n - m + m = n
```

`omega` knows these rules and proves linear statements with `-`, `/` and `%` by a constant.

In `ℤ`, division by a positive number rounds down, so that the remainder `%` is never negative:

```lean
example : (-7 : ℤ) / 2 = -4 := by decide
example : (-7 : ℤ) % 2 = 1 := by decide
```

# Total functions and junk values
%%%
tag := "junk-values"
%%%

Every function in Lean is defined on its whole domain. Where the mathematical function is undefined, Mathlib chooses a value, usually `0`:

```lean
example : (1 : ℝ) / 0 = 0 := div_zero 1
example : (0 : ℝ)⁻¹ = 0 := inv_zero
example : Real.sqrt (-1) = 0 :=
  Real.sqrt_eq_zero_of_nonpos (by norm_num)
example : Real.log 0 = 0 := Real.log_zero
example : sSup (∅ : Set ℝ) = 0 := Real.sSup_empty
```

The alternative would be a division that takes a proof of `b ≠ 0` as an argument. Then every term `a / b` would carry a proof, and every rewrite of `b` would have to transport it. Mathlib puts the condition into the theorems instead: a statement that is false for `b = 0` has the hypothesis `b ≠ 0`.

```lean
#check @div_mul_cancel₀
-- b ≠ 0 → a / b * b = a
#check @Real.sq_sqrt
-- 0 ≤ x → √x ^ 2 = x
```

So no false statement can be proved from a junk value; it only appears in statements that hold for it as well, such as `(a + b) / c = a / c + b / c`, which holds for `c = 0` too and therefore has no hypothesis. When a theorem does not apply, the first thing to check is which of its hypotheses is missing.

Functions of analysis follow the same pattern. Each has a predicate that says whether the value means what it should, and the theorems about the value assume the predicate:

:::table (align := left) +header
* + value
  + if undefined
  + predicate
* + `deriv f x`
  + `0`
  + `DifferentiableAt ℝ f x`, `HasDerivAt f f' x`
* + `∑' n, f n`
  + `0`
  + `Summable f`, `HasSum f s`
* + `∫ x, f x ∂μ`
  + `0`
  + `Integrable f μ`
* + `sSup s` in `ℝ`
  + `0`
  + `s.Nonempty`, `BddAbove s`
* + `Nat.card α`
  + `0`
  + `Finite α`
:::

```lean
#check @deriv_zero_of_not_differentiableAt
#check @tsum_eq_zero_of_not_summable
#check @MeasureTheory.integral_undef
#check @Nat.card_eq_zero_of_infinite
```

# Three kinds of power
%%%
tag := "powers"
%%%

`x ^ n` stands for three different functions, chosen by the type of the exponent:

:::table (align := left) +header
* + exponent
  + function
  + defined for
* + `n : ℕ`
  + `Monoid.npow`, repeated multiplication
  + every monoid
* + `n : ℤ`
  + `zpow`, with `x ^ (-n) = (x ^ n)⁻¹`
  + groups, fields
* + `y : ℝ`
  + `Real.rpow`, via `exp` and `log`
  + `ℝ`, `ℝ≥0`, `ℂ`
:::

Each has its own theorems (`pow_succ`, `zpow_neg`, `Real.rpow_add`), and they are related by casts, such as `Real.rpow_natCast : x ^ (n : ℝ) = x ^ n`. A numeral in the exponent is read as a natural number, so `x ^ 2` is `x * x`. The same holds for `1 / 2`, and that is a trap: `1 / 2` is then division in `ℕ`, which is `0`, and `x ^ (1 / 2)` is `1`.

```lean
example (x : ℝ) : x ^ (1 / 2) = 1 := by norm_num
example (x : ℝ) : x ^ ((1 : ℝ) / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
```

For a negative base, `x ^ y` with real `y` is defined as `exp (log x * y) * cos (y * π)`, the real part of the complex power. So `(-8) ^ (1 / 3 : ℝ)` is `2 * cos (π / 3) = 1`, not `-2`.

```lean
#check @Real.rpow_def_of_neg
```

# Nonnegative and extended reals
%%%
tag := "nnreal-ennreal"
%%%

`ℝ≥0` is used where a quantity cannot be negative: norms in `ℝ≥0` are written `‖x‖₊`, and a finite measure takes values in it. Subtraction on `ℝ≥0` is truncated, as on `ℕ`.

`ℝ≥0∞` is the value type of measures (chapter on {ref "measure-theory"}[measure theory]). Every set gets a measure, also an unbounded one, and every series of nonnegative terms has a sum, possibly `∞`. The arithmetic of `∞` has conventions of its own:

```lean
example : (∞ : ℝ≥0∞) + 1 = ∞ := by simp
example : (0 : ℝ≥0∞) * ∞ = 0 := by simp
example : (∞ : ℝ≥0∞) - ∞ = 0 := by simp
example : (1 : ℝ≥0∞) / 0 = ∞ := by simp
example : MeasureTheory.volume (Set.univ : Set ℝ) = ∞ := by
  simp
#check @ENNReal.summable   -- every f : α → ℝ≥0∞ is summable
```

The way back to `ℝ` has junk values again: `ENNReal.toReal ∞ = 0`, and `ENNReal.ofReal x = 0` for `x < 0`.

```lean
example : (∞ : ℝ≥0∞).toReal = 0 := by simp
example : ENNReal.ofReal (-1) = 0 := by simp
```

# Casts
%%%
tag := "number-casts"
%%%

A natural number in a real formula is converted by the {ref "coercions"}[coercion] `↑`, here `Nat.cast : ℕ → ℝ`. The coercions run along the chain `ℕ → ℤ → ℚ → ℝ → ℂ`, and also `ℝ≥0 → ℝ` and `ℝ≥0 → ℝ≥0∞`. The tactics `push_cast`, `norm_cast` and `exact_mod_cast` move casts; they were practised on sheet `1.6-b`.

A cast commutes with addition and multiplication, but not with the operations whose meaning changes between the types: truncated subtraction and division with remainder.

```lean
example (n : ℕ) : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
  push_cast; ring
example : ((7 / 2 : ℕ) : ℝ) = 3 := by norm_num
example : ¬ ∀ n : ℕ, ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  intro h
  have := h 0
  simp at this
#check @Nat.cast_sub
-- m ≤ n → ((n - m : ℕ) : R) = n - m
```

Where a cast appears depends on where Lean sees the type. In `(n - 1 : ℤ)` the subtraction is in `ℤ`, and `n` is cast first; in `((n - 1 : ℕ) : ℤ)` the subtraction is in `ℕ`, and the result is cast. The two agree only for `n ≥ 1`.
