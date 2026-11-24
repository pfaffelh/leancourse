import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Notation and abbreviations" (part 1 of the
notes). It follows the chapter section by section: `notation`, infix,
prefix and postfix operators, notation in Mathlib (`∑`, `∫`, `deriv`),
scoped notation, numerals, `▸` and `<|`, `abbrev`.
New notation here is `local` or `scoped`, so it does not leak into the
other decks when all of them are compiled together.
-/

namespace SlidesNotation
#doc (Slides) "Notation and abbreviations" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Notation and abbreviations

Lean and its type theory — notation, shorthands, `abbrev`.

# Defining new notation

```
notation "symbol" arg1 arg2 ... => expression
```

Left: the syntax pattern. Right: what it expands to.

```lean -panel -stretch
local notation "δ" => (2 : ℕ)
#check (δ : ℕ)
```

# Notation is syntax

```lean -panel -stretch
local notation "double" x => x + x
#eval double 5 -- 10
```

:::class "key"
Lean replaces the notation by the right-hand side _before_ type checking.
:::

# Infix operators

```lean -panel -stretch
local infixl:65 " ⊕⊕ " =>
  fun (a b : ℕ) => a + b + 1
#eval 3 ⊕⊕ 4 -- 8
```

- `infixl`: left-associative, `infixr`: right-associative
- `65`: binding power, the same as `+`
- the spaces around `⊕⊕` are part of the syntax

# Prefix and postfix

Unary notation on a single argument:

```lean -panel -stretch
-- precedence 80, higher than `+`
local prefix:80 "¡" => fun n : ℕ => n * n
#eval ¡5    -- 25

local postfix:90 "!!" => fun n : ℕ => 2 * n + 1
#eval 4!!   -- 9
```

# Multi-argument notation

Custom tokens mixed with several arguments:

```lean -panel -stretch
-- the half-open interval from a to b
local notation "between " a " and " b =>
  Set.Ico a b
#check between (1 : ℕ) and 10    -- Set ℕ
```

# Notation in Mathlib

:::table +colHeaders
*
  * you write
  * Lean reads
*
  * `∑ i ∈ s, f i`
  * `Finset.sum s (fun i => f i)`
*
  * `∫ x in a..b, f x`
  * `intervalIntegral (fun x => f x) a b volume`
*
  * `∫ x, f x ∂μ`
  * `MeasureTheory.integral μ (fun x => f x)`
*
  * `{x | p x}`
  * `Set.ofPred (fun x => p x)`
*
  * `∀ᶠ x in F, p x`
  * `Filter.Eventually (fun x => p x) F`
*
  * `|x|`, `‖x‖`, `⌊x⌋`
  * `abs x`, `norm x`, `Int.floor x`
:::

Built with `notation3`, or `syntax` plus `macro_rules`.

:::class "key"
A variable bound after the symbol becomes a `fun`: the notation is a function applied to a lambda.
:::

# The derivative has no notation

```lean -panel -stretch
#check deriv (fun x : ℝ => x ^ 2)
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  norm_num
```

- `deriv f x`: the function is an argument, written with `fun`
- `deriv f : ℝ → ℝ`, the second derivative is `deriv (deriv f)`
- defined through the Fréchet derivative: `deriv f x = fderiv ℝ f x 1`

# Looking behind notation

```lean -panel -stretch
set_option pp.notation false in
#check ∑ i ∈ Finset.range 3, i + 1
#eval ∑ i ∈ Finset.range 3, i + 1    -- 4, not 6
```

- `pp.notation false` prints the term without notation
- the body of `∑` stops before `+`: this is `(∑ i ∈ range 3, i) + 1`
- the body of `∫` does not: `∫ x in 0..1, x + 1` integrates `x + 1`

:::class "key"
When in doubt, bracket: `∑ i ∈ s, (f i + 1)`.
:::

# Scoped notation

```lean -panel -stretch
namespace MyDemo
scoped notation "✦" => (42 : ℕ)
end MyDemo

open scoped MyDemo
#eval ✦    -- 42
```

Active only after `open MyDemo` or `open scoped MyDemo`. Mathlib does
this for `𝓝` (`open Topology`), `𝓟` (`open Filter`) and `n !` (`open Nat`);
`∑`, `∫` and `∀ᶠ` are always available.

# Where numerals come from

Not declared notation: the parser knows literals, an instance gives the meaning.
`2` becomes `OfNat.ofNat 2`; it works for every `α` with an `OfNat α 2` instance.

```lean -panel -stretch
structure Countdown where
  val : Nat

instance (n : Nat) : OfNat Countdown n where
  ofNat := ⟨n⟩

#eval (5 : Countdown).val    -- 5
```

A bare `2` is a natural number: a _default instance_.

# Rewriting a hypothesis with `▸`

From `h : x = y` and `hx : P x`, the term `h ▸ hx` proves `P y`.
Type `▸` as `\t`.

```lean -panel -stretch
example (P : ℕ → Prop) (x y : ℕ)
    (h : x = y) (hx : P x) : P y := by
  exact h ▸ hx
```

# Brackets with `<|`

`first (second very long statement)` becomes
`first <| second very long statement` — no closing bracket.

```lean -panel -stretch
example (P Q : Prop) (hP : P) (hnP : ¬P) :
    Q := by
  apply False.elim <| hnP hP
```

# The `abbrev` command

```lean -panel -stretch
abbrev NatAlias := ℕ
def NatAlias' := ℕ
```

:::table +colHeaders +rowHeaders +rowSeps
*
  * property
  * `abbrev`
  * `def`
*
  * unfolded
  * automatically (reducible)
  * not automatically (semireducible)
*
  * instances of `ℕ`
  * available
  * must be derived or registered
:::

:::class "key"
`abbrev`: a short name, no new abstraction barrier. `def`: hide the definition.
:::

# Summary

- `notation` is syntax, expanded before type checking
- `infixl`, `infixr`, `prefix`, `postfix` with a binding power
- Mathlib's `∑`, `∫`, `{x | p x}` turn a bound variable into a `fun`
- `pp.notation false` shows what notation stands for
- `scoped` keeps notation inside a namespace
- numerals are literals, read through `OfNat`
- `h ▸ hx` rewrites, `f <| x` saves brackets
- `abbrev` unfolds automatically, `def` does not
