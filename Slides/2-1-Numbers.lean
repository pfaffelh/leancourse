import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Numbers" of part 2 (Mathematics). It follows the
chapter section by section: how the number types are built, the real
numbers as a quotient, arithmetic in ℕ and ℤ, junk values, the three
powers, nonnegative and extended reals, casts. Chapter 2.2 has its own
deck, `2-2-SetsAndTypes`.
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
Each number type is built with a type former of part 1, and the construction explains its arithmetic.
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

`f ≈ g`: the relation of the `Setoid` (1.4), typed `\approx`; `(f - g).LimZero`: `f - g` tends to `0`.

# Adding real numbers

```lean -panel -stretch
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

Add representatives termwise. Well defined: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`; then `Quot.lift` gives `+` on the classes.

:::class "key"
This equation is the computation rule `Quot.lift φ h (Quot.mk r a) ⟶ φ a`.
:::

`+` on `ℝ` unwraps the structure and uses this.

# Computing with real numbers

```lean -panel -stretch
#eval (1 : ℝ) + 1   -- the first terms of a Cauchy sequence
example : (1 : ℝ) + 1 = 2 := by norm_num
```

`decide` fails: `DecidableEq ℝ` comes from `Classical.choice` and does not compute. `rfl` fails: `+` on `ℝ` does not reduce. Division, inverse and square root use choice too:

```lean +error -panel -stretch
def recip (x : ℝ) : ℝ := 1 / x
```

```lean -panel -stretch
noncomputable def reciprocal (x : ℝ) : ℝ := 1 / x
```

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
example : (-7 : ℤ) / 2 = -4 := by decide
example : (-7 : ℤ) % 2 = 1 := by decide
```

```
Nat.sub_add_cancel : m ≤ n → n - m + m = n
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
```

```
div_mul_cancel₀ : b ≠ 0 → a / b * b = a
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
:::

The theorems about the value assume the predicate. `∑' n, f n`: the sum of the series (`tsum`). `sSup s`: supremum of `s : Set ℝ`.

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
  * `Real.rpow` via `exp` and `log` (`NNReal.rpow`, `ENNReal.rpow` likewise)
  * `ℝ`, `ℝ≥0`, `ℝ≥0∞`
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
`ℝ≥0∞`: every nonnegative series has a sum, possibly `∞`. Mathlib also uses it for measures.
:::

# Casts go up

:::table +colHeaders
*
  * from
  * to
  * function behind `↑`
*
  * `ℕ`
  * `ℤ`, `ℚ`, `ℝ`, `ℂ`, any semiring
  * `Nat.cast`
*
  * `ℤ`
  * `ℚ`, `ℝ`, `ℂ`, any ring
  * `Int.cast`
*
  * `ℚ`
  * `ℝ`, `ℂ`
  * `Rat.cast`
*
  * `ℝ`
  * `ℂ`
  * `Complex.ofReal`
*
  * `ℝ≥0`
  * `ℝ`
  * `NNReal.toReal`
*
  * `ℝ≥0`
  * `ℝ≥0∞`
  * `ENNReal.ofNNReal`
:::

`set_option pp.coercions false` prints these names instead of `↑`.

:::class "key"
`(3 : ℕ)` and `(3 : ℝ)` are different terms. The way down is a function with a junk value.
:::

# Where the arrow goes

```lean -panel -stretch
variable (n : ℕ) in
#check (n + 1 : ℝ)
variable (n : ℕ) in
#check ((n + 1 : ℕ) : ℝ)
example : ((7 : ℕ) : ℝ) / 2 = 3.5 := by norm_num
example : (((7 : ℕ) / 2 : ℕ) : ℝ) = 3 := by norm_num
```

- for arithmetic, Lean finds the largest type among the operands and casts each operand into it: `(n + 1 : ℝ)` is `↑n + 1`
- a type ascription `(… : ℕ)` fixes where the cast sits
- for `+` both agree, for `-` and `/` not

# Casts and operations

:::table +colHeaders
*
  * operation
  * lemma
  * hypothesis
*
  * `+`, `*`, `^`
  * `Nat.cast_add`, `Nat.cast_mul`, `Nat.cast_pow`
  * none
*
  * numerals
  * `Nat.cast_zero`, `Nat.cast_one`, `Nat.cast_ofNat`
  * none
*
  * `=`
  * `Nat.cast_inj`
  * characteristic zero
*
  * `≤`, `<`
  * `Nat.cast_le`, `Nat.cast_lt`
  * target ordered
*
  * `-`
  * `Nat.cast_sub`
  * `m ≤ n`
*
  * `/`
  * `Nat.cast_div`
  * `n ∣ m`, `(n : K) ≠ 0`
:::

Same names for `Int.cast_*`, `Rat.cast_*`, `NNReal.coe_*`, `ENNReal.coe_*`. `Int.cast_sub` needs no hypothesis.

# The cast tactics

```lean -panel -stretch
example (m n : ℕ) (h : m ≤ n) :
    ((n - m : ℕ) : ℝ) = n - m := by
  push_cast [h]
  ring
example (m n : ℕ) (h : (m : ℝ) < n) : m < n := by
  exact_mod_cast h
```

- `push_cast`: casts towards the leaves; `push_cast [h]` also uses `h : m ≤ n` for `Nat.cast_sub`
- `norm_cast`: casts towards the root, then removes them
- `exact_mod_cast h`: `h` and goal differ only in casts
- they use the lemmas marked `@[norm_cast]`

# `zify`: from ℕ to ℤ

```lean -panel -stretch
example (m n : ℕ) (h : m ≤ n) :
    (n - m) * (n + m) = n ^ 2 - m ^ 2 := by
  have h2 : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
  zify [h, h2]
  ring
```

- `omega` fails: not linear; `ring` fails in `ℕ`: `-` is truncated
- `zify [h]` moves the goal to `ℤ` and uses `h : m ≤ n` for `↑(n - m)`
- likewise `qify` (to `ℚ`) and `rify` (to `ℝ`)

# Between ℝ, ℝ≥0 and ℝ≥0∞

:::table +colHeaders
*
  * from
  * to
  * function
  * junk value
*
  * `ℝ≥0`
  * `ℝ`, `ℝ≥0∞`
  * coercion `↑`
  * none
*
  * `ℝ`
  * `ℝ≥0`
  * `x.toNNReal`
  * `0` for `x < 0`
*
  * `ℝ`
  * `ℝ≥0∞`
  * `ENNReal.ofReal x`
  * `0` for `x < 0`
*
  * `ℝ≥0∞`
  * `ℝ≥0`
  * `a.toNNReal`
  * `0` for `a = ∞`
*
  * `ℝ≥0∞`
  * `ℝ`
  * `a.toReal`
  * `0` for `a = ∞`
:::

```
ENNReal.toReal_ofReal : 0 ≤ x → (ofReal x).toReal = x
ENNReal.toReal_add : a ≠ ∞ → b ≠ ∞ →
  (a + b).toReal = a.toReal + b.toReal
```

:::class "key"
`norm_cast` knows the coercions, not the four functions: their lemmas need hypotheses.
:::

# `lift`: move to ℝ≥0 first

```lean -panel -stretch
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : a ≤ b) : a.toReal ≤ b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast at h ⊢
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (x * y)
      = ENNReal.ofReal x * ENNReal.ofReal y := by
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  simp
```

- `lift a to ℝ≥0 using ha` replaces `a : ℝ≥0∞` by `↑a` with `a : ℝ≥0`
- then only coercions are left, and `norm_cast` or `simp` works
- the same for `x : ℝ` with `hx : 0 ≤ x`; without the `lift`s, `simp` fails

# The way down

:::table +colHeaders
*
  * function
  * notation
  * at a negative argument
*
  * `Int.toNat k`
  * —
  * `0`
*
  * `Int.natAbs k`
  * —
  * the absolute value
*
  * `Int.floor x`, `Int.ceil x`
  * `⌊x⌋`, `⌈x⌉`
  * rounded down, up
*
  * `Nat.floor x`, `Nat.ceil x`
  * `⌊x⌋₊`, `⌈x⌉₊`
  * `0`
:::

```lean -panel -stretch
example : (-3 : ℤ).toNat = 0 := by decide
example : ⌊(-2.7 : ℝ)⌋₊ = 0 := by norm_num
```

# Summary

- `ℤ` and `ℚ` have one representation per number; `ℝ` is a structure around a quotient of Cauchy sequences and does not compute.
- Functions are total; theorems carry the hypotheses. `x ^ n` is three functions.
- Casts go up; the way down is a function with a junk value.
- `push_cast`, `norm_cast`, `exact_mod_cast`, `zify` and `lift` move casts.
