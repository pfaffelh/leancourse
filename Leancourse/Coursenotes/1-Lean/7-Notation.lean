import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Notation and abbreviations" =>
%%%
htmlSplit := .never
tag := "notation"
%%%

The [slides](slides/1-7-notation/) for this chapter follow it section by section.

# Defining new notation
%%%
tag := "notation-defining"
%%%

Lean allows you to define custom notation using the `notation` command. This is useful when you want a concise mathematical symbol for a frequently used expression. The general syntax is
```
notation "symbol" arg1 arg2 ... => expression
```
where the left-hand side describes the syntax pattern (with arguments) and the right-hand side is the Lean expression it expands to. Here is a simple example:

```lean
section NotationDemo

notation "δ" => (2 : ℕ)
#check (δ : ℕ)

```

After this definition, `δ` is replaced by `2` everywhere. The notation is purely syntactic: Lean replaces every occurrence of the new notation by the right-hand side before type checking. Here is a more interesting example with an argument:

```lean
notation "double" x => x + x
#eval double 5 -- 10

end NotationDemo
```

You can also define infix notation with a priority (determining how tightly the operator binds):

```lean
section InfixDemo

infixl:65 " ⊕⊕ " => fun (a b : ℕ) => a + b + 1
#eval 3 ⊕⊕ 4 -- 8

end InfixDemo
```

Here, `infixl` means left-associative infix, `65` is the binding power (the same as `+`), and the spaces around `⊕⊕` are part of the syntax. Similarly, `infixr` gives right-associative infix, and `prefix` / `postfix` are available for unary operators.

## Prefix and postfix operators
%%%
number := false
%%%

`prefix` and `postfix` define unary notation on a single argument:

```lean
section UnaryDemo

-- A prefix "bang" operator, 80 precedence (higher than `+`)
prefix:80 "¡" => fun n : ℕ => n * n
#eval ¡5    -- 25

-- A postfix factorial-style operator
postfix:90 "!!" => fun n : ℕ => 2 * n + 1
#eval 4!!   -- 9

end UnaryDemo
```

## Multi-argument `notation`
%%%
number := false
%%%

`notation` can take more than one argument and mix custom tokens with them:

```lean
section TernaryDemo

-- "between a and b" means the half-open interval [a, b)
notation "between " a " and " b => Set.Ico a b
#check between (1 : ℕ) and 10    -- Set ℕ

end TernaryDemo
```

## Scoped notation
%%%
number := false
%%%

If a notation should only be active inside a namespace (so it does
not pollute the global symbol space), mark it `scoped`:

```lean
namespace MyDemo
scoped notation "✦" => (42 : ℕ)
end MyDemo

-- Outside the namespace, `✦` is not in scope by default;
-- enable it with `open MyDemo` or `open scoped MyDemo`.
open scoped MyDemo
#eval ✦    -- 42
```

Mathlib does this for `𝓝` (`open Topology`), `𝓟` (`open Filter`)
and the factorial `n !` (`open Nat`). Other notation, such as `∑`,
`∫` and `∀ᶠ`, is always available.

For more complex notation involving multiple tokens or bespoke
parsing rules, you can use the `syntax` and `macro_rules` commands,
but `notation`, the infix variants, `prefix`/`postfix`, and
`notation3` cover most common use cases.

# Notation in Mathlib
%%%
tag := "mathlib-notation"
%%%

Most notation met in Mathlib binds a variable: the `i` in `∑ i ∈ s, f i` exists only after the comma. Such notation is declared with `notation3` (or `syntax` plus `macro_rules`), and Lean turns the bound variable into a `fun`. The notation is a function applied to a lambda:

:::table (align := left) +header
* + You write
  + Lean reads
* + `∑ i ∈ s, f i`
  + `Finset.sum s (fun i => f i)`
* + `∏ i ∈ s, f i`
  + `Finset.prod s (fun i => f i)`
* + `∑ i, f i`
  + `Finset.sum Finset.univ (fun i => f i)`
* + `∫ x in a..b, f x`
  + `intervalIntegral (fun x => f x) a b volume`
* + `∫ x, f x ∂μ`
  + `MeasureTheory.integral μ (fun x => f x)`
* + `{x | p x}`
  + `Set.ofPred (fun x => p x)`
* + `∃ x, p x`
  + `Exists (fun x => p x)`
* + `∀ᶠ x in F, p x`
  + `Filter.Eventually (fun x => p x) F`
* + `|x|`, `‖x‖`, `⌊x⌋`
  + `abs x`, `norm x`, `Int.floor x`
:::

Both sides are the same term, so `rfl` proves the equation:

```lean
example (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i
      = Finset.sum (Finset.range n) f := rfl

example (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, f x
      = intervalIntegral f 0 1
          MeasureTheory.volume := rfl
```

The derivative has no notation. `deriv f x` is the derivative of `f` at `x`, and the function is passed as an argument, written with `fun`. `deriv f` is again a function `ℝ → ℝ`, so the second derivative is `deriv (deriv f)`. Mathlib defines `deriv` through the Fréchet derivative: `deriv f x = fderiv ℝ f x 1`.

```lean
#check deriv (fun x : ℝ => x ^ 2)
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  norm_num
example (f : ℝ → ℝ) :
    deriv f = fun x => fderiv ℝ f x 1 := rfl
```

## Looking behind notation
%%%
number := false
%%%

`set_option pp.notation false` prints a term without notation. This also answers questions of precedence. The body of `∑` is parsed with precedence 67, above that of `+` (65), so it stops before a `+`:

```lean
set_option pp.notation false in
#check ∑ i ∈ Finset.range 3, i + 1
#eval ∑ i ∈ Finset.range 3, i + 1     -- 4
#eval ∑ i ∈ Finset.range 3, (i + 1)   -- 6
```

The body of `∫` is parsed with precedence 60, so `∫ x in 0..1, x + 1` integrates `x + 1`. When in doubt, use brackets.

# Where numerals come from (`OfNat`)
%%%
tag := "ofnat"
%%%

Numerals look like notation but are not declared with `notation`. The parser knows numeric literals, and a typeclass decides what they mean. `a + b` is declared notation and becomes `HAdd.hAdd a b`; the literal `2` becomes `OfNat.ofNat 2`:

```lean
#check @OfNat.ofNat
-- {α : Type} → (n : ℕ) → [OfNat α n] → α
```

So `(2 : α)` means "the element of `α` denoted by the numeral `2`", available for any `α` that has an `OfNat α 2` instance. That is why the same `2` works across types,

```lean
#check (2 : ℤ)
#check (2 : ℝ)
```

and why you can give a numeral to your own type simply by providing the instance:

```lean
structure Countdown where
  val : Nat

instance (n : Nat) : OfNat Countdown n where
  ofNat := ⟨n⟩

#eval (5 : Countdown).val    -- 5
```

The instance decides what a numeral means. In {ref "pi-types"}[Dependent functions], `#eval` printed `2` for `(7 : ZMod 5)`. `#synth` names the instance Lean finds:

```lean
#synth OfNat (ZMod 5) 7   -- instOfNatAtLeastTwo
```

This instance exists for every type with a cast from ℕ and turns the numeral `7` into `Nat.cast 7`. Mathlib defines the cast into `ZMod (n + 1)` as the cast into `Fin (n + 1)`, and that takes the remainder: `Fin.ofNat n i` is `⟨i % n, _⟩`. So `(7 : ZMod 5)` is `⟨7 % 5, _⟩`, and `rfl` sees it:

```lean
example : (7 : ZMod 5) = 2 := rfl
```

Without any other information Lean reads a bare numeral as a natural number. This is a *default instance*: `@[default_instance]` marks an instance to use when synthesis would otherwise be ambiguous.

```lean
#check 2         -- 2 : ℕ
#check (2 : ℝ)   -- 2 : ℝ
```

# Two useful shorthands
%%%
tag := "abreviation"
%%%

There are at least two abbreviations used in `Mathlib` which you will encounter frequently.

If you have `h : x = y` and `hx : P x` (with `P x : Prop`), you can prove `P y` by replacing `h` in `hx`. The shorthand notation for this is `h ▸ hx`. (Write `\t` for `▸`).

```lean
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (hx : P x) :
    P y := by
  exact h ▸ hx
```

Sometimes, bracketing is critical, and it appears frequently that it has the form
`apply first (second very long statement)`, and you might get lost since the closing brackets are far away from their opening counterparts. In this case, we write `apply first <| second very long statement`, which does not need a closing symbol.

```lean
example (P Q : Prop) (hP : P) (hnP : ¬P) : Q := by
    apply False.elim <| hnP hP
```

# The `abbrev` command
%%%
tag := "abbrev"
%%%

The `abbrev` command introduces a definition that is *reducibly transparent*, meaning Lean's {ref "kernel-elaborator"}[elaborator] will unfold it automatically whenever needed. In contrast, a definition introduced with `def` is *semireducible* and will not be unfolded automatically.

```lean
abbrev NatAlias := ℕ
```

After this, `NatAlias` and `ℕ` are interchangeable everywhere — Lean treats them as definitionally equal without needing any extra work. In particular, all type class instances that apply to `ℕ` are automatically available for `NatAlias`. Compare this with

```lean
def NatAlias' := ℕ
```

where `NatAlias'` is a genuinely new type: Lean will *not* automatically apply `ℕ` instances to `NatAlias'`, and you would have to derive or register them yourself.

Use `abbrev` when you want a short name for a type or expression but do not want to create a new abstraction barrier. Use `def` when you intentionally want to hide the definition (e.g. to prevent the simplifier from unfolding it).
