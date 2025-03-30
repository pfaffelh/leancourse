import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "ℕ and ℝ" =>
%%%
htmlSplit := .never
tag := "numbers"
%%%

# Natural numbers
To get a little more mathematical, we now introduce the natural numbers. This type (abbreviated `ℕ`, type `\N`) is defined (see 02-a.lean) so that `0 : ℕ` and `succ (n : ℕ) : ℕ`, i.e. with `n` is also `succ n` a natural number. `succ n` stands for the successor of `n`. Furthermore, we will get to know the types `set ℕ` and `Finset ℕ` here. These are the subsets of `ℕ` and the finite subsets of `ℕ`.
-  Sheet 02-a: Natural numbers and the `calc` mode:
    After an introduction to how natural numbers are implemented in `Lean`, we introduce the `calc` mode. This allows us to perform calculations step by step, using previously proven statements. This way, we can, for example, prove binomial formulas. We also get to know the very powerful tactics `ring`, `norm_num`, `linarith` and `simp` can simplify a lot of work. Here we also learn the `fun` notation for defining functions.
-  Page 02-b: divisibility:
    For `m n : ℕ` (or `m n : ℤ`) `h : m | n` (type `\|`), means that `n` is divided by `m`. In other words, there is `a : ℕ` with `n = a * m`. With this definition, the goal of this sheet is to show the long known statement that a number is exactly divisible by 3 (or 9) if and only if its cross sum is divisible by 3 (or 9). Here we will only do this for numbers up to `10000`.
**Bonus task:** An especially simple method of proving the divisibility rule by 3 in Lean is with the following Lean file (here, `\%` is the modulo sign and `digits 10` is the finite list of decimal representations of the
  number `n`):
  ```
    open Nat
    example (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum := by
      refine dvd_iff_dvd_digits_sum 3 10 _ n
      norm_num
  ```
This proof is based on the following statement:
```
lemma dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
b ∣ n ↔ b ∣ (digits b' n).sum
```
Give a script proof of this statement.
-  Page 02-c: `\sqrt 2`:
     This is about the proof `√2 ∉ ℚ`. Here is the proof as you would find it in a script (or school book): Assuming that there are `m` and `n` such that `√2 = m/n`, then  `2n² = m²`. Let `m` and `n` be relatively prime. Then `2 ∣ m²`. Since `m²` is even, `m` must also be even, so `m = 2a` for some `a`. Thus `2*n² = 4 * a²` or `n² = 2 a²`. This means that `n²` is even, and as just argued, `n` would then be even. However, this contradicts the complementary division of `m` and `n`. This proof is formalized here. (Note that the proof given here only works for `√2`, but not for `√3`. The reason is that we use that for every `m ∈ ℕ` either `m` or `m+1` is even (i.e. divisible by 2). This is obviously false for `3`.)
-  Page 02-d: induction
    induction has been known since the first semester: If one shows for a statement `P : ℕ → Prop` both `P 0` and also `∀ d : ℕ, P d → P (d + 1)`, then one has `∀ n : ℕ, P n` shown. This is the so-called *weak*    induction that we will use here for a few statements. We will also show the well-ordering principle of `ℕ`, which states that every non-empty subset of ℕ contains a smallest element
-  Sheet 02-e: Pigeonhole principle
   If you distribute `m` balls among `n<m` drawers, at least two balls end up in the same drawer. In more mathematical terms, there is no injective mapping of an `m`-element set into an `n<m`-element one. To prove this, we first introduce introduce injective mappings and use an induction principle for `Finset`s.

# Real Numbers

We now come to real numbers without looking at their definition (which
uses Cauchy sequences).
-   Sheet 03-a: Lower Bounds on a Set\
   We introduce the set of lower bounds on a set `A \subsets \mathbb R` is introduced. The largest lower bound is then known to be the `\inf A`. To formulate the main result, we also introduce the limit of a sequence. Finally, we prove that `x = \inf A` holds if and only if there is a sequence in `A` that converges to `x`.
-  Page 03-b: The derivative of `x\mapsto x^{n+1}`\
    As is well known, the derivative of `x\mapsto x^{n+1}` is given by     `x\mapsto (n+1)x^n`. To show this, we need the concept of the derivative (here as a sequence limit), as well as the product rule. We will reduce everything to the calculation rules for limits, such as the fact that the limit of the product of two convergent sequences is given by the product of the limits. After this preliminary work, we prove the formula by induction.
