import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Notation and abbreviations" (part 1 of the
notes). It follows the chapter section by section: `notation`, infix,
prefix and postfix operators, scoped notation, `▸` and `<|`, `abbrev`.
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

# Notation with binders

Mathlib writes `∑ k ∈ range n, f k` and `∀ᶠ x in F, p x`.

- these bind a variable after the comma
- built with `notation3`, or `syntax` plus `macro_rules`
- writing them from scratch takes macro plumbing

:::class "key"
For day-to-day notation, `notation`, `infixl`, `infixr`, `prefix` and `postfix` are almost always enough.
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
this for `𝓝`, `𝓟`, `∫`, `∀ᶠ`.

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
- `scoped` keeps notation inside a namespace
- `h ▸ hx` rewrites, `f <| x` saves brackets
- `abbrev` unfolds automatically, `def` does not
