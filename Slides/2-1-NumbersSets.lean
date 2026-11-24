import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapters "Numbers" and "Sets and types" of part 2
(Mathematics), read in one lecture. It follows the two chapters section
by section. Numbers: how the number types are built, the real numbers
as a quotient, arithmetic in ℕ and ℤ, junk values, the three powers,
nonnegative and extended reals, casts. Sets and types: sets versus
types, sets as predicates and their operations, indexed unions, set
equality, image and preimage, injective and surjective maps, finite
sets and sums, and the subtype of a set.
-/

namespace SlidesNumbers
open scoped NNReal ENNReal

#doc (Slides) "Numbers; sets and types" =>

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

# Numbers; sets and types

Mathematics — chapters 1 and 2

:::class "key"
Each number type is built with a type former of part 1, and the construction explains its arithmetic. A set is not a new type: it is a predicate on a type.
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
```

```
Nat.cast_sub : m ≤ n → ((n - m : ℕ) : R) = n - m
```

:::class "key"
A cast commutes with `+` and `*`, not with truncated `-` or with `/` on `ℕ`.
:::

# Sets versus types

In set theory `∈` is the primitive, and an object lies in many sets. In type theory every term `a : α` has exactly one type.

:::table +colHeaders +rowSeps
*
  * notion
  * written
  * its terms
*
  * type
  * `α`
  * `a : α`, with exactly one type
*
  * set
  * `s : Set α`
  * terms of `α` that satisfy a predicate
*
  * subtype
  * `{ x : α // p x }`
  * a new type: pairs of a value and a proof of `p`
:::

:::class "key"
A set is not a new type. `s : Set α` selects terms of `α`, and its elements keep their type `α`.
:::

# Sets are predicates

```lean -panel -stretch
example : Set ℕ = (ℕ → Prop) := rfl

def Evens : Set ℕ := { n | n % 2 = 0 }

example : (4 ∈ Evens) ↔ (4 % 2 = 0) := Iff.rfl
example : 4 ∈ Evens := by
  show 4 % 2 = 0
  decide
example : 3 ∉ Evens := by
  show ¬ (3 % 2 = 0)
  decide
```

:::class "key"
`Set α` is `α → Prop`, and `a ∈ s` is `s a`.
:::

# Operations are connectives

:::table +colHeaders +rowSeps
*
  * statement
  * unfolds to
  * typed as
*
  * `s ⊆ t`
  * `∀ a, a ∈ s → a ∈ t`
  * `\subseteq`
*
  * `a ∈ s ∩ t`
  * `a ∈ s ∧ a ∈ t`
  * `\cap`
*
  * `a ∈ s ∪ t`
  * `a ∈ s ∨ a ∈ t`
  * `\cup`
*
  * `a ∈ sᶜ`
  * `¬ a ∈ s`
  * `\compl`
*
  * `a ∈ ∅`
  * `False`
  * `\empty`
*
  * `a ∈ Set.univ`
  * `True`
  * `Set.univ`
*
  * `a ∈ { x | p x }`
  * `p a`
  * literal braces
:::

:::class "key"
The operations are defined pointwise on the predicates. Each line is `Iff.rfl`.
:::

# Indexed unions and intersections

For a family `s : ι → Set α`:

```lean -panel -stretch
example (s : ℕ → Set ℕ) (a : ℕ) :
    (a ∈ ⋃ i, s i) ↔ ∃ i, a ∈ s i := Set.mem_iUnion
example (s : ℕ → Set ℕ) (a : ℕ) :
    (a ∈ ⋂ i, s i) ↔ ∀ i, a ∈ s i := Set.mem_iInter
example (S : Set (Set ℕ)) (a : ℕ) :
    (a ∈ ⋃₀ S) ↔ ∃ t ∈ S, a ∈ t := Set.mem_sUnion
```

`⋃ i ∈ a, s i` ranges over a set `a : Set ι`. `⋃ i, s i` is `iSup s`, and `⋃₀ S` is `sSup S`.

:::class "key"
Membership in an indexed union is an `∃`, in an indexed intersection a `∀`.
:::

# Set equality

```lean -panel -stretch
example (s t : Set ℕ) :
    s = t ↔ ∀ a, a ∈ s ↔ a ∈ t :=
  ⟨fun h a => by rw [h], fun h => Set.ext h⟩

example : { n : ℕ | n % 2 = 0 } = { n | 2 ∣ n } := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> omega

example : (⋃ n : ℕ, {n}) = Set.univ := by
  ext a; simp
```

`Set.ext` uses `funext` (a theorem, from `Quot.sound`) and `propext`.

:::class "key"
Two sets are equal when they have the same members. `ext` turns `s = t` into `a ∈ s ↔ a ∈ t`.
:::

# Image and preimage

```lean -panel -stretch
example (f : ℕ → ℕ) (s : Set ℕ) (y : ℕ) :
    y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := Iff.rfl
example (f : ℕ → ℕ) (t : Set ℕ) (x : ℕ) :
    x ∈ f ⁻¹' t ↔ f x ∈ t := Iff.rfl
```

A hypothesis `h : y ∈ f '' s` is a triple: `obtain ⟨x, hx, rfl⟩ := h` gives `x`, a proof of `x ∈ s`, and replaces `y` by `f x`. To prove `y ∈ f '' s`, name the point: `⟨x, hx, rfl⟩` or `use x`.

A hypothesis `x ∈ f ⁻¹' t` needs no unpacking. The image of the whole type is `Set.range f`.

:::class "key"
Membership in the image is an `∃`; membership in the preimage is `f x ∈ t`.
:::

# Image, preimage, inclusion

```lean -panel -stretch
example (f : ℕ → ℕ) (s t : Set ℕ) :
    f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h hx
example (f : ℕ → ℕ) (t₁ t₂ : Set ℕ) :
    f ⁻¹' (t₁ ∩ t₂) = f ⁻¹' t₁ ∩ f ⁻¹' t₂ := rfl
example (f : ℕ → ℕ) (s₁ s₂ : Set ℕ) :
    f '' (s₁ ∩ s₂) ⊆ f '' s₁ ∩ f '' s₂ :=
  Set.image_inter_subset f s₁ s₂
```

:::class "key"
The preimage commutes with all set operations, by `rfl`. The image commutes with `∪`, and with `∩` only up to `⊆`.
:::

# Injective and surjective

```lean -panel -stretch
example (f : ℕ → ℕ) : Function.Injective f ↔
    ∀ a b, f a = f b → a = b := Iff.rfl
example (f : ℕ → ℕ) : Function.Surjective f ↔
    ∀ b, ∃ a, f a = b := Iff.rfl
example : Function.Injective (fun n : ℕ => n + 1) := by
  intro a b h
  simpa using h
example : ¬ Function.Surjective (fun n : ℕ => n + 1) := by
  intro h
  obtain ⟨a, ha⟩ := h 0
  simp at ha
```

The two points in `Injective` are implicit: `hf h : a = b` for `h : f a = f b`. So `g ∘ f` is injective by `fun _ _ h => hf (hg h)`.

:::class "key"
Both are definitions with quantifiers; `intro` unfolds them.
:::

# Bijections and equivalences

```lean -panel -stretch
example (f : ℕ → ℕ) : Function.Bijective f ↔
    Function.Injective f ∧ Function.Surjective f := Iff.rfl
example (f : ℕ → ℕ) :
    Function.Surjective f ↔ Set.range f = Set.univ :=
  Set.range_eq_univ.symm
```

`α ≃ β` is a map together with its inverse. `Equiv.ofBijective` chooses the inverse with `Classical.choice`:

```lean +error -panel -stretch
def idEquiv : ℕ ≃ ℕ :=
  Equiv.ofBijective id Function.bijective_id
```

```lean -panel -stretch
noncomputable def idEquiv' : ℕ ≃ ℕ :=
  Equiv.ofBijective id Function.bijective_id
```

:::class "key"
Bijectivity is a property of `f`; the inverse is data.
:::

# Finite sets

A `Set α` may be infinite. `Finset α` is a finite set given as data:

```
structure Finset (α : Type*) where
  val : Multiset α        -- a list up to permutation
  nodup : val.Nodup
```

```lean -panel -stretch
example : Finset.range 4 = {0, 1, 2, 3} := by decide
example : ({1, 2, 3} : Finset ℕ).card = 3 := by decide
example : ∑ i ∈ Finset.range 4, i = 6 := by decide
example : ∏ i ∈ Finset.Icc 1 4, i = 24 := by decide
```

`s.image f` removes duplicates among the values, so it needs `DecidableEq β`.

:::class "key"
A `Finset` is data, so `decide` computes with it.
:::

# Sums by induction

`∑ i ∈ s, f i` is typed `\sum`, `∏` is `\prod`. The sum over `Finset.range n` runs over `0, …, n - 1`.

```lean -panel -stretch
example (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
```

:::class "key"
Induction on `n`; `Finset.sum_range_succ` splits off the last term.
:::

# Counting

A type with `[Fintype α]` has `Finset.univ`, the finset of all its elements.

:::table +colHeaders +rowSeps
*
  * count
  * of
  * infinite case
*
  * `s.card`, also `#s`
  * `s : Finset α`
  * does not occur
*
  * `Fintype.card α`
  * `α` with `[Fintype α]`
  * does not occur
*
  * `Nat.card α`
  * any type `α`
  * `0`
*
  * `s.ncard`
  * `s : Set α`
  * `0`
*
  * `s.encard`
  * `s : Set α`, value in `ℕ∞`
  * `⊤`
:::

:::class "key"
The `0` for an infinite set is a junk value; theorems about `ncard` assume `s.Finite`.
:::

# From a set back to a type

A function defined only on `s`, or a sum over its elements, needs a type. The coercion `↥s` is the subtype `{ x // x ∈ s }`.

```lean -panel -stretch
example : ↥Evens = { x : ℕ // x ∈ Evens } := rfl
example : ↥Evens := ⟨4, by show 4 % 2 = 0; decide⟩
example (x : ↥Evens) : (x : ℕ) % 2 = 0 := x.2
```

:::class "key"
A term of `↥s` pairs a value in `α` with a proof that it lies in `s`.
:::

# Summary

- `ℤ` and `ℚ` have one representation per number; `ℝ` is a structure around a quotient of Cauchy sequences and does not compute.
- Functions are total; theorems carry the hypotheses. `x ^ n` is three functions; casts move with `push_cast`.
- `Set α` is `α → Prop`: the operations are connectives, membership is `Iff.rfl`, equality is `ext`.
- `y ∈ f '' s` is an `∃`, `x ∈ f ⁻¹' t` is `f x ∈ t`, and `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`.
- `Injective` and `Surjective` are formulas; the inverse `α ≃ β` is data, chosen noncomputably.
- `Finset α` is data: `decide`, sums, induction with `Finset.sum_range_succ`. `↥s` turns a set into a type.
