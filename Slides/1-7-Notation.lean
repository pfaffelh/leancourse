import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Notation and abbreviations" (part 1 of the
notes). It follows the chapter section by section: `notation`, infix,
prefix and postfix operators, scoped notation, `syntax` and `macro_rules`,
the tables of common Mathlib notation, `deriv`,
numerals, `▸` and `<|`, `abbrev`.
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

local postfix:90 "°" => fun n : ℕ => 2 * n + 1
#eval 4°   -- 9
```

# Multi-argument notation

Custom tokens mixed with several arguments:

```lean -panel -stretch
-- the half-open interval from a to b
local notation "between " a " and " b =>
  Set.Ico a b
#check between (1 : ℕ) and 10    -- Set ℕ
```

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

# `syntax` and `macro_rules`

```lean -panel -stretch
local syntax "twice " term:max : term
local macro_rules
  | `(twice $x) => `($x + $x)
#eval twice 5   -- 10
```

- `syntax`: what may be written, a new rule for the parser
- `macro_rules`: what it is replaced by; `` `(…) `` is syntax with holes `$x`
- `notation` does both at once; several rules: the list literal `[1, 2, 3]` (1.3)
- `notation3`: Mathlib's `notation` for symbols that bind a variable

# Are `∀` and `∃` notation?

```lean -panel -stretch
set_option pp.notation false in
#check ∀ n : ℕ, n = n
set_option pp.notation false in
#check ∃ n : ℕ, n = n
```

- `∃ x, p x` is notation for `Exists (fun x => p x)`
- `∀ x, p x` and `P → Q` are not: they are function types, part of the kernel's language

:::class "key"
A variable bound after the symbol becomes a `fun`.
:::

# Notation: logic

:::table +colHeaders
*
  * you write
  * Lean reads
  * input
*
  * `¬P`
  * `Not P`
  * `\not`
*
  * `P ∧ Q`, `P ∨ Q`
  * `And P Q`, `Or P Q`
  * `\and`, `\or`
*
  * `P ↔ Q`
  * `Iff P Q`
  * `\iff`
*
  * `∃ x, p x`
  * `Exists (fun x => p x)`
  * `\ex`
*
  * `a = b`, `a ≠ b`
  * `Eq a b`, `Ne a b`
  * `\ne`
*
  * `P → Q`, `∀ x, p x`
  * not notation
  * `\to`, `\all`
:::

# Notation: numbers

:::table +colHeaders
*
  * you write
  * Lean reads
  * input
*
  * `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`
  * `Nat`, `Int`, `Rat`, `Real`, `Complex`
  * `\N`, `\Z`, `\Q`, `\R`, `\C`
*
  * `ℝ≥0`, `ℝ≥0∞`
  * `NNReal`, `ENNReal`
  * `open NNReal`, `open ENNReal`
*
  * `a ∣ b`
  * `Dvd.dvd a b`
  * `\dvd`
*
  * `a / b`, `a % b`
  * `HDiv.hDiv a b`, `HMod.hMod a b`
  * —
*
  * `x⁻¹`, `x ^ n`
  * `Inv.inv x`, `HPow.hPow x n`
  * `\inv`
*
  * `|x|`, `‖x‖`
  * `abs x`, `norm x`
  * `\||` for `‖`
*
  * `⌊x⌋`, `⌈x⌉`
  * `Int.floor x`, `Int.ceil x`
  * `\lfloor`, `\lceil`
*
  * `n !`, `n‼`
  * `Nat.factorial n`, `Nat.doubleFactorial n`
  * `\!!`, `open Nat`
:::

# Notation: order and sets

:::table +colHeaders
*
  * you write
  * Lean reads
  * input
*
  * `a ≤ b`, `a < b`
  * `LE.le a b`, `LT.lt a b`
  * `\le`
*
  * `a ≥ b`
  * `GE.ge a b`, that is `LE.le b a`
  * `\ge`
*
  * `a ⊔ b`, `a ⊓ b`
  * `max a b`, `min a b`
  * `\sup`, `\inf`
*
  * `a ∈ s`, `a ∉ s`
  * `Membership.mem s a`, `¬(a ∈ s)`
  * `\in`, `\notin`
*
  * `s ⊆ t`
  * `LE.le s t` (`Set`, `Finset`)
  * `\sub`
*
  * `s ∩ t`, `s ∪ t`
  * `Inter.inter s t`, `Union.union s t`
  * `\cap`, `\cup`
*
  * `sᶜ`, `s \ t`, `∅`
  * `compl s`, `sdiff s t`, `EmptyCollection.emptyCollection`
  * `\^c`, `\empty`
:::

# Notation: sets and types

:::table +colHeaders
*
  * you write
  * Lean reads
  * input
*
  * `{x | p x}`
  * `Set.ofPred (fun x => p x)`
  * —
*
  * `{a, b}`
  * `insert a (singleton b)`
  * —
*
  * `f '' s`, `f ⁻¹' t`
  * `Set.image f s`, `Set.preimage f t`
  * `\inv`, then `'`
*
  * `#s`
  * `Finset.card s`
  * `open Finset`
*
  * `f ∘ g`
  * `Function.comp f g`
  * `\o`
*
  * `α × β`, `α ⊕ β`
  * `Prod α β`, `Sum α β`
  * `\x`, `\oplus`
*
  * `{x // p x}`
  * `Subtype (fun x => p x)`
  * —
*
  * `Σ x, β x`
  * `Sigma (fun x => β x)`
  * `\Sigma`
*
  * `α ≃ β`
  * `Equiv α β`
  * `\equiv`
:::

# Notation: sums, integrals, limits

:::table +colHeaders
*
  * you write
  * Lean reads
  * input
*
  * `∑ i ∈ s, f i`
  * `Finset.sum s (fun i => f i)`
  * `\sum`
*
  * `∏ i ∈ s, f i`
  * `Finset.prod s (fun i => f i)`
  * `\prod`
*
  * `∑ i, f i`
  * `Finset.sum Finset.univ (fun i => f i)`
  * —
*
  * `∫ x in a..b, f x`
  * `intervalIntegral (fun x => f x) a b volume`
  * `\integral`
*
  * `∫ x, f x ∂μ`
  * `MeasureTheory.integral μ (fun x => f x)`
  * `\partial`
*
  * `∀ᶠ x in F, p x`
  * `Filter.Eventually (fun x => p x) F`
  * `\all\^f`
*
  * `𝓝 x`, `𝓟 s`
  * `nhds x`, `Filter.principal s`
  * `\nhds`, `\MCP`
:::

`\int` gives `ℤ`, not `∫`. `𝓝` needs `open Topology`, `𝓟` needs `open Filter`.

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

# Why `def`: other instances

```lean -panel -stretch
example : ¬((1, 5) ≤ ((2, 0) : ℕ × ℕ)) := by decide
example : toLex (1, 5) ≤ toLex ((2, 0) : ℕ × ℕ) := by
  decide
abbrev LexA (α : Type) := α
example : ¬((1, 5) ≤ ((2, 0) : LexA (ℕ × ℕ))) := by
  decide
```

- Mathlib: `def Lex (α : Type*) := α`, with the lexicographic order
- with `abbrev`, instance search sees through `LexA` and finds the componentwise order
- also: with `def`, goals show the concept's name, and `simp` does not unfold it

# Summary

- `notation` is syntax, expanded before type checking
- `infixl`, `infixr`, `prefix`, `postfix` with a binding power
- `syntax` declares a form, `macro_rules` says what it becomes
- almost every Mathlib symbol is a named constant; `∑`, `∫`, `∃` turn a bound variable into a `fun`
- `∀` and `→` are not notation
- `pp.notation false` shows what notation stands for
- `scoped` keeps notation inside a namespace
- numerals are literals, read through `OfNat`
- `h ▸ hx` rewrites, `f <| x` saves brackets
- `abbrev` unfolds automatically, `def` does not; `def` can carry its own instances (`Lex`)
