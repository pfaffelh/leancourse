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

The [slides](slides/2-1-numbers/) for this chapter follow it section by section.

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

Each number type is built with a type former of the {ref "lean"}[Lean part]:

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
  + {ref "reals-quotient"}[below]
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

## The integers and the rationals
%%%
number := false
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

## The real numbers
%%%
tag := "reals-quotient"
number := false
%%%

In analysis, `ℝ` is the completion of `ℚ`: a real number is given by a Cauchy sequence of rationals, and two Cauchy sequences give the same real number if their difference tends to `0`. Mathlib builds `ℝ` in exactly this way, in three steps: a {ref "subtypes"}[subtype], a {ref "quotient-types"}[quotient] and a {ref "structures"}[structure].

*Cauchy sequences: a subtype.* `CauSeq ℚ abs` is `{f : ℕ → ℚ // IsCauSeq abs f}`, a sequence of rationals together with a proof that it is Cauchy for the absolute value `abs`.

```lean
#check (CauSeq ℚ abs)
example (f : CauSeq ℚ abs) : ℕ → ℚ := f.1
```

*Classes of sequences: a quotient.* Two Cauchy sequences are related, `f ≈ g`, if `f - g` tends to `0`. The quotient by this relation is `CauSeq.Completion.Cauchy abs`, and `CauSeq.Completion.mk` is its `Quot.mk`. Related sequences give the same class by `Quotient.sound`, the form of `Quot.sound` for an equivalence relation:

```lean
example (f g : CauSeq ℚ abs) :
    f ≈ g ↔ (f - g).LimZero := Iff.rfl

example : CauSeq.Completion.Cauchy (abs : ℚ → ℚ) =
    Quotient (CauSeq.equiv (abv := (abs : ℚ → ℚ))) := rfl

example (f g : CauSeq ℚ abs) (h : f ≈ g) :
    CauSeq.Completion.mk f = CauSeq.Completion.mk g :=
  Quotient.sound h
```

*The real numbers: a structure.* `ℝ` is a {ref "structures"}[structure] with one field, an element of this quotient. The wrapper makes Lean treat `ℝ` as a type of its own instead of unfolding it to the quotient.

```lean
#print Real
-- structure Real : Type
--   Real.cauchy : CauSeq.Completion.Cauchy abs
```

*Operations: well-definedness.* Two real numbers are added by adding representative sequences termwise. This is well defined because addition respects the relation: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`. With that proved, `Quot.lift` gives addition on the classes, and its computation rule says that `mk` turns the sum of sequences into the sum of reals:

```lean
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

This equation is the computation step `Quot.lift f h (Quot.mk r a) ⟶ f a`, for an operation with two arguments. Multiplication, the order and the limits of `ℝ` are defined in the same way: on representatives, with a proof that the result does not depend on the choice.

A real number is not a finite object. `#eval` shows the first terms of a Cauchy sequence that represents it, and equality of real numbers is not decidable, so `decide` and `rfl` fail even on `1 + 1 = 2`. Concrete computations with real numbers are proved with `norm_num`.

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

Division, the inverse and the square root on `ℝ` are not given by an algorithm: their definitions use `Classical.choice`. They are `noncomputable` (the appendix section {ref "noncomputable"}[Computable and noncomputable definitions] says what the keyword means). A definition that uses them must be marked as well. Lean says so:

```lean +error
def recip (x : ℝ) : ℝ := 1 / x
```

The error is `failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Real.instDivInvMonoid'`. With the keyword the definition is accepted, and proofs about it work as usual:

```lean
noncomputable def reciprocal (x : ℝ) : ℝ := 1 / x

example : reciprocal 2 = 1 / 2 := rfl
```

A file with many such definitions starts with `noncomputable section` and ends the section with `end`; inside, Lean marks every definition that needs it. Addition and multiplication are computable, so `def addOne (x : ℝ) : ℝ := x + 1` needs no keyword.

## Complex, nonnegative and extended numbers
%%%
number := false
%%%

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

`ℝ≥0∞` is the value type of measures. Every set gets a measure, also an unbounded one, and every series of nonnegative terms has a sum, possibly `∞`. The arithmetic of `∞` has conventions of its own:

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

On paper, `3` is one number, and `ℕ ⊆ ℤ ⊆ ℝ`. In Lean, `(3 : ℕ)` and `(3 : ℝ)` are terms of different types, and every expression has exactly one type. A natural number in a real formula is therefore converted by a function, the {ref "coercions"}[coercion] `↑`, which Lean inserts by itself. Proofs then have to move these arrows, and that is unfamiliar: the arrow is invisible on paper.

Casts go *up*, from a smaller number system into a larger one. The way down is an ordinary function with a junk value ({ref "junk-values"}[Total functions and junk values]).

## Which casts there are
%%%
number := false
%%%

:::table (align := left) +header
* + From
  + To
  + Function behind `↑`
* + `ℕ`
  + `ℤ`, `ℚ`, `ℝ`, `ℂ`, any semiring
  + `Nat.cast`
* + `ℤ`
  + `ℚ`, `ℝ`, `ℂ`, any ring
  + `Int.cast`
* + `ℚ`
  + `ℝ`, `ℂ`, any field of characteristic zero
  + `Rat.cast`
* + `ℝ`
  + `ℂ`
  + `Complex.ofReal`
* + `ℝ≥0`
  + `ℝ`
  + `NNReal.toReal`, the value of the subtype
* + `ℝ≥0`
  + `ℝ≥0∞`
  + `ENNReal.ofNNReal`, that is `some`
:::

`set_option pp.coercions false` prints the names instead of `↑`:

```lean
section
variable (n : ℕ) (k : ℤ) (r : ℝ≥0)
set_option pp.coercions false in
#check ((n : ℝ), (k : ℚ), (r : ℝ), (r : ℝ≥0∞))
end
```

## Where the arrow goes
%%%
number := false
%%%

Lean elaborates from the outside in: the expected type decides where a cast is needed. In `(n : ℝ) + 1` the addition happens in `ℝ`, and `n` is cast first. In `((n + 1 : ℕ) : ℝ)` the addition happens in `ℕ`, and the sum is cast:

```lean
section
variable (n : ℕ)
#check (n : ℝ) + 1          -- ↑n + 1 : ℝ
#check ((n + 1 : ℕ) : ℝ)    -- ↑(n + 1) : ℝ
end
```

For `+` the two agree. For `-` and `/` they do not, because these operations mean different things in `ℕ` and in `ℝ`:

```lean
example : ((7 : ℕ) : ℝ) / 2 = 3.5 := by norm_num
example : (((7 : ℕ) / 2 : ℕ) : ℝ) = 3 := by norm_num
example : ¬ ∀ n : ℕ, ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  intro h
  have := h 0
  simp at this
```

## Casts and operations
%%%
number := false
%%%

A cast commutes with an operation if the operation means the same on both sides. Each case is a lemma; the names follow one pattern:

:::table (align := left) +header
* + Operation
  + Lemma
  + Hypothesis
* + `+`, `*`, `^`
  + `Nat.cast_add`, `Nat.cast_mul`, `Nat.cast_pow`
  + none
* + `0`, `1`, numerals
  + `Nat.cast_zero`, `Nat.cast_one`, `Nat.cast_ofNat`
  + none
* + `=`
  + `Nat.cast_inj`
  + target of characteristic zero
* + `≤`, `<`
  + `Nat.cast_le`, `Nat.cast_lt`
  + target ordered
* + `-`
  + `Nat.cast_sub`
  + `m ≤ n`
* + `/`
  + `Nat.cast_div`
  + `n ∣ m` and `(n : K) ≠ 0`
:::

The same names exist for the other casts: `Int.cast_add`, `Rat.cast_mul`, `NNReal.coe_add`, `ENNReal.coe_mul`. `Int.cast_sub` has no hypothesis, because subtraction in `ℤ` is not truncated.

```lean
#check @Nat.cast_sub
-- m ≤ n → ((n - m : ℕ) : R) = ↑n - ↑m
#check @Nat.cast_div
-- n ∣ m → (n : K) ≠ 0 → ((m / n : ℕ) : K) = ↑m / ↑n
example (n : ℕ) (h : 2 ∣ n) :
    ((n / 2 : ℕ) : ℝ) = n / 2 := by
  rw [Nat.cast_div h (by norm_num)]
  norm_num
```

## The cast tactics
%%%
number := false
%%%

The lemmas above carry the attribute `@[norm_cast]`. The tactics use them in both directions:

- {ref "push-cast"}[`push_cast`] moves casts towards the leaves: `↑(n + 1)` becomes `↑n + 1`. With `push_cast [h]` it uses `h : m ≤ n` for `Nat.cast_sub`.
- {ref "norm-cast"}[`norm_cast`] moves casts towards the root and removes them where it can: the goal `(n : ℝ) + m = 10` becomes `n + m = 10`, and a matching hypothesis closes it.
- `exact_mod_cast h` proves the goal from `h` when the two differ only in casts.
- `zify`, `qify` and `rify` move a goal about natural numbers into `ℤ`, `ℚ` or `ℝ`, where subtraction and division are not truncated. `zify [h]` uses `h : m ≤ n` to turn `↑(n - m)` into `↑n - ↑m`.
- `omega` handles linear goals in `ℕ` and `ℤ` with the cast between them.

```lean
example (m n : ℕ) (h : m ≤ n) :
    ((n - m : ℕ) : ℝ) = n - m := by
  push_cast [h]
  ring
example (m n : ℕ) (h : (m : ℝ) < n) : m < n := by
  exact_mod_cast h
example (m n : ℕ) (h : m + n = 10) :
    (m : ℝ) + n = 10 := by
  norm_cast
example (m n : ℕ) (h : m ≤ n) :
    (n - m) * (n + m) = n ^ 2 - m ^ 2 := by
  have h2 : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
  zify [h, h2]
  ring
```

In the last example `omega` fails, because the goal is not linear, and `ring` fails in `ℕ`, because `-` is truncated. `zify` moves the goal to `ℤ`, where `ring` works.

## Between ℝ, ℝ≥0 and ℝ≥0∞
%%%
number := false
tag := "real-nnreal-ennreal-casts"
%%%

Only two of the six directions are coercions: `ℝ≥0 → ℝ` and `ℝ≥0 → ℝ≥0∞`. The other four are functions with a junk value:

:::table (align := left) +header
* + From
  + To
  + Function
  + Junk value
* + `ℝ`
  + `ℝ≥0`
  + `Real.toNNReal x`, written `x.toNNReal`
  + `0` for `x < 0`
* + `ℝ`
  + `ℝ≥0∞`
  + `ENNReal.ofReal x`
  + `0` for `x < 0`
* + `ℝ≥0∞`
  + `ℝ≥0`
  + `ENNReal.toNNReal a`, written `a.toNNReal`
  + `0` for `a = ∞`
* + `ℝ≥0∞`
  + `ℝ`
  + `ENNReal.toReal a`, written `a.toReal`
  + `0` for `a = ∞`
:::

The lemmas about these functions carry the hypothesis that excludes the junk value:

```lean
section
variable (x y : ℝ) (a b : ℝ≥0∞)
example (hx : 0 ≤ x) : (x.toNNReal : ℝ) = x :=
  Real.coe_toNNReal x hx
example (hx : 0 ≤ x) : (ENNReal.ofReal x).toReal = x :=
  ENNReal.toReal_ofReal hx
example (ha : a ≠ ∞) : ENNReal.ofReal a.toReal = a :=
  ENNReal.ofReal_toReal ha
example (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (a + b).toReal = a.toReal + b.toReal :=
  ENNReal.toReal_add ha hb
example (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (x + y)
      = ENNReal.ofReal x + ENNReal.ofReal y :=
  ENNReal.ofReal_add hx hy
-- `ofReal` goes through `ℝ≥0`
example : ENNReal.ofReal x = ((x.toNNReal : ℝ≥0) : ℝ≥0∞) :=
  rfl
end
```

`norm_cast` knows the two coercions (`NNReal.coe_add`, `ENNReal.coe_add`, …) but not the four functions, because their lemmas need hypotheses. Most often one therefore moves to `ℝ≥0` first. The tactic `lift` does this: given `ha : a ≠ ∞`, `lift a to ℝ≥0 using ha` replaces `a : ℝ≥0∞` by `↑a` with `a : ℝ≥0`. In the same way `lift x to ℝ≥0 using hx` works for `x : ℝ` with `hx : 0 ≤ x`.

```lean
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞)
    (h : a ≤ b) : a.toReal ≤ b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast at h ⊢
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x ^ 3 := by
  lift x to ℝ≥0 using hx
  positivity
```

## The way down
%%%
number := false
%%%

From `ℤ` to `ℕ` and from `ℝ` to `ℤ` there is no cast either, only functions:

:::table (align := left) +header
* + Function
  + Notation
  + Value at a negative argument
* + `Int.toNat k`
  + —
  + `0`
* + `Int.natAbs k`
  + —
  + the absolute value
* + `Int.floor x`, `Int.ceil x`
  + `⌊x⌋`, `⌈x⌉`
  + rounded down, up
* + `Nat.floor x`, `Nat.ceil x`
  + `⌊x⌋₊`, `⌈x⌉₊`
  + `0`
:::

```lean
example : (-3 : ℤ).toNat = 0 := by decide
example : (-3 : ℤ).natAbs = 3 := by decide
example : ⌊(-2.7 : ℝ)⌋ = -3 := by norm_num
example : ⌊(-2.7 : ℝ)⌋₊ = 0 := by norm_num
example (k : ℤ) (h : 0 ≤ k) : ((k.toNat : ℕ) : ℤ) = k :=
  Int.toNat_of_nonneg h
```

