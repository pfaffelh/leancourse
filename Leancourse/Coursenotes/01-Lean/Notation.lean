import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
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

`notation` can take more than one argument and mix custom tokens with them:

```lean
section TernaryDemo

-- "between a and b" means the half-open interval [a, b)
notation "between " a " and " b => Set.Ico a b
#check between (1 : ℕ) and 10    -- Set ℕ

end TernaryDemo
```

## Notation with binders

Mathlib uses `notation3` (and its underlying machinery `syntax` +
`macro_rules`) to introduce binder-style notation like
`∑ k ∈ range n, f k` and `∀ᶠ x in F, p x`.  These let you bind a
variable inside the expression that follows the comma.  Writing such
notation from scratch involves a fair amount of macro plumbing and
is beyond the scope of this section -- the standard reference is the
[Lean 4 documentation on macros](https://leanprover.github.io/theorem_proving_in_lean4/macros.html).
For ordinary day-to-day notation, plain `notation`, `infixl`,
`infixr`, `prefix`, and `postfix` are almost always enough.

## Scoped notation

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

This is the pattern used throughout Mathlib for notation like `𝓝`,
`𝓟`, `∫`, `∀ᶠ`, etc.: they are scoped to the relevant namespace and
enabled with `open scoped`.

For more complex notation involving multiple tokens or bespoke
parsing rules, you can use the `syntax` and `macro_rules` commands,
but `notation`, the infix variants, `prefix`/`postfix`, and
`notation3` cover most common use cases.

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

The `abbrev` command introduces a definition that is *reducibly transparent*, meaning Lean's elaborator will unfold it automatically whenever needed. In contrast, a definition introduced with `def` is *semireducible* and will not be unfolded automatically.

```lean
abbrev MyNat := ℕ
```

After this, `MyNat` and `ℕ` are interchangeable everywhere — Lean treats them as definitionally equal without needing any extra work. In particular, all type class instances that apply to `ℕ` are automatically available for `MyNat`. Compare this with

```lean
def MyNat' := ℕ
```

where `MyNat'` is a genuinely new type: Lean will *not* automatically apply `ℕ` instances to `MyNat'`, and you would have to derive or register them yourself.

Use `abbrev` when you want a short name for a type or expression but do not want to create a new abstraction barrier. Use `def` when you intentionally want to hide the definition (e.g. to prevent the simplifier from unfolding it).
