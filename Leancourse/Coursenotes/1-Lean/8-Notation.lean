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

The [slides](slides/1-8-notation/) for this chapter follow it section by section.

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

You can also define infix notation with a precedence:

```lean
section InfixDemo

infixl:65 " ⊕⊕ " => fun (a b : ℕ) => a + b + 1
#eval 3 ⊕⊕ 4       -- 8
#eval 3 ⊕⊕ 4 * 2   -- 12
#eval 1 ⊕⊕ 2 ⊕⊕ 3  -- 8

end InfixDemo
```

Here, `65` is the precedence, the same as that of `+`. A higher number binds tighter: `*` has precedence 70, so `3 ⊕⊕ 4 * 2` is `3 ⊕⊕ 8 = 12`. `infixl` means left-associative: `a ⊕⊕ b ⊕⊕ c` is `(a ⊕⊕ b) ⊕⊕ c`, so `1 ⊕⊕ 2 ⊕⊕ 3` is `4 ⊕⊕ 3 = 8`. The spaces around `⊕⊕` are part of the syntax. Similarly, `infixr` gives right-associative infix, and `prefix` / `postfix` are available for unary operators.

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

-- A postfix operator: the n-th odd number
postfix:90 "°" => fun n : ℕ => 2 * n + 1
#eval 4°   -- 9

end UnaryDemo
```

## Multi-argument `notation`
%%%
number := false
%%%

`notation` can take more than one argument and mix custom tokens with them:

```lean
section TernaryDemo

-- "avg a and b" is the mean of a and b
notation "avg " a " and " b => (a + b) / 2
#eval avg 4 and 10    -- 7

end TernaryDemo
```

## Scoped notation
%%%
number := false
%%%

A notation marked `local` is valid until the end of the current
section or file, as a `local instance`
({ref "managing-instances"}[chapter 1.7]). If a notation should only
be active inside a namespace (so it does not pollute the global symbol
space), mark it `scoped`:

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

## `syntax`, `macro_rules` and `notation3`
%%%
number := false
tag := "syntax-macro-rules"
%%%

`notation` does two things at once, and Lean has a command for each.
`syntax` declares what may be written: a new rule for the parser.
`macro_rules` says what it is replaced by. The pieces in
`` `(…) `` are quotations, pieces of Lean syntax with holes `$x`:

```lean
section MacroDemo
local syntax "twice " term:max : term
local macro_rules
  | `(twice $x) => `($x + $x)
#eval twice 5   -- 10
end MacroDemo
```

`term:max` says that the argument is a term of maximal precedence:
a name, a numeral, or something in brackets. The final `: term` makes
the whole expression a term again. The `local` in front works as for
`notation`.

This is the same as `notation "twice " x:max => x + x`. `notation`
describes one fixed shape with one replacement. The two separate
commands solve three problems that `notation` cannot:

1. *Any number of arguments.* `term,*` in a `syntax` line accepts a
   comma-separated list of terms of any length, including none.
2. *Cases on the input.* `macro_rules` may have several rules, like a
   `match` on syntax; the first that fits is used. A rule may use the
   new syntax again, so the replacement can be recursive.
3. *Extension later.* Another `macro_rules` for the same syntax may
   follow, also in another file. For a tactic, Lean tries all rules,
   the most recent first, until one succeeds.

An example for 1 and 2, a sum of any length:

```lean
section SumDemo
local syntax "sum⟪" term,* "⟫" : term
local macro_rules
  | `(sum⟪⟫) => `(0)
  | `(sum⟪$x⟫) => `($x)
  | `(sum⟪$x, $xs,*⟫) => `($x + sum⟪$xs,*⟫)
#eval sum⟪1, 2, 3⟫   -- 6
end SumDemo
```

`$xs,*` is the rest of the list. The list literal `[1, 2, 3]` in
{ref "pattern-matching"}[Pattern matching] is built the same way:
one `syntax` line, one rule for `[]`, one for a single element, and
one that peels off the first element.

An example for 3: the tactic `trivial` is declared in Lean's core as
`syntax "trivial" : tactic`, followed by one `macro_rules` each for
`rfl`, `assumption`, `contradiction`, `decide` and others. Its
documentation invites you to add more. The same in small:

```lean
section TacticDemo
local syntax "easy" : tactic
local macro_rules
  | `(tactic| easy) => `(tactic| rfl)
local macro_rules
  | `(tactic| easy) => `(tactic| assumption)

example : 2 + 2 = 4 := by easy
example (p : Prop) (h : p) : p := by easy
end TacticDemo
```

In the first example the newer rule (`assumption`) fails, and Lean
falls back to `rfl`.

`notation3` is Mathlib's extension of `notation` for notation that
binds a variable. Mathlib declares `∀ᶠ` with it:

```
notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r
```

`(...)` stands for the bound variables, and `scoped p => …` turns
the body after the comma into a function `p`. The next section lists
what such declarations produce. Writing them is not part of this
course.

# Notation in Mathlib
%%%
tag := "mathlib-notation"
%%%

Almost every symbol in Mathlib is notation for a named constant, and `set_option pp.notation false` shows the name ({ref "looking-behind-notation"}[Looking behind notation]). The tables below list the common ones, with the key sequence for the editor. Notation that binds a variable, such as `∃ x, p x` or `∑ i ∈ s, f i`, turns the variable into a `fun` ({ref "syntax-macro-rules"}[`syntax`, `macro_rules` and `notation3`]).

Two symbols are not notation. `P → Q` and `∀ x, p x` are function types, `∀` the dependent one ({ref "pi-types"}[Dependent functions]); they belong to the language of the kernel, and `pp.notation false` leaves them as they are. `∃` is notation for the inductive type `Exists`:

```lean
set_option pp.notation false in
#check ∀ n : ℕ, n = n   -- ∀ (n : Nat), Eq n n
set_option pp.notation false in
#check ∃ n : ℕ, n = n   -- Exists fun n => Eq n n
```

*Logic.*

:::table (align := left) +header
* + You write
  + Lean reads
  + Input
* + `¬P`
  + `Not P`
  + `\not`
* + `P ∧ Q`, `P ∨ Q`
  + `And P Q`, `Or P Q`
  + `\and`, `\or`
* + `P ↔ Q`
  + `Iff P Q`
  + `\iff`
* + `∃ x, p x`
  + `Exists (fun x => p x)`
  + `\ex`
* + `a = b`, `a ≠ b`
  + `Eq a b`, `Ne a b`
  + `\ne`
* + `P → Q`, `∀ x, p x`
  + not notation: function types
  + `\to`, `\all`
:::

*Numbers and order.*

:::table (align := left) +header
* + You write
  + Lean reads
  + Input
* + `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`
  + `Nat`, `Int`, `Rat`, `Real`, `Complex`
  + `\N`, `\Z`, `\Q`, `\R`, `\C`
* + `ℝ≥0`, `ℝ≥0∞`
  + `NNReal`, `ENNReal`
  + after `open NNReal`, `open ENNReal`
* + `a ≤ b`, `a < b`
  + `LE.le a b`, `LT.lt a b`
  + `\le`
* + `a ≥ b`
  + `GE.ge a b`, by definition `LE.le b a`
  + `\ge`
* + `a ∣ b`
  + `Dvd.dvd a b`
  + `\dvd`
* + `a / b`, `a % b`
  + `HDiv.hDiv a b`, `HMod.hMod a b`
  + —
* + `x⁻¹`, `x ^ n`
  + `Inv.inv x`, `HPow.hPow x n`
  + `\inv`
* + `|x|`, `‖x‖`
  + `abs x`, `norm x`
  + `\||` for `‖`
* + `⌊x⌋`, `⌈x⌉`
  + `Int.floor x`, `Int.ceil x`
  + `\lfloor`, `\lceil`
* + `n !`, `n‼`
  + `Nat.factorial n`, `Nat.doubleFactorial n`
  + `\!!`; after `open Nat`
* + `a ⊔ b`, `a ⊓ b`
  + `max a b`, `min a b`
  + `\sup`, `\inf`
:::

*Sets.*

:::table (align := left) +header
* + You write
  + Lean reads
  + Input
* + `a ∈ s`, `a ∉ s`
  + `Membership.mem s a`, `¬(a ∈ s)`
  + `\in`, `\notin`
* + `s ⊆ t`
  + `LE.le s t` (for `Set` and `Finset`)
  + `\sub`
* + `s ∩ t`, `s ∪ t`
  + `Inter.inter s t`, `Union.union s t`
  + `\cap`, `\cup`
* + `sᶜ`, `s \ t`
  + `compl s`, `sdiff s t`
  + `\^c`
* + `∅`
  + `EmptyCollection.emptyCollection`
  + `\empty`
* + `{x | p x}`
  + `Set.ofPred (fun x => p x)`
  + —
* + `{a, b}`
  + `insert a (singleton b)`
  + —
* + `f '' s`, `f ⁻¹' t`
  + `Set.image f s`, `Set.preimage f t`
  + `\inv` then `'`
* + `#s`
  + `Finset.card s`
  + after `open Finset`
:::

In `a ∈ s` the set comes first in `Membership.mem s a`. And `⊆` on `Set` and `Finset` is the order `≤`; the symbol is only printed differently.

*Functions and types.*

:::table (align := left) +header
* + You write
  + Lean reads
  + Input
* + `f ∘ g`
  + `Function.comp f g`
  + `\o`
* + `fun x ↦ e`
  + `fun x => e`
  + `\mapsto`
* + `α × β`, `α ⊕ β`
  + `Prod α β`, `Sum α β`
  + `\x`, `\oplus`
* + `{x // p x}`
  + `Subtype (fun x => p x)`
  + —
* + `Σ x, β x`, `(x : α) × β x`
  + `Sigma (fun x => β x)`
  + `\Sigma`
* + `α ≃ β`
  + `Equiv α β`
  + `\equiv`
:::

*Sums, integrals, limits.*

:::table (align := left) +header
* + You write
  + Lean reads
  + Input
* + `∑ i ∈ s, f i`, `∏ i ∈ s, f i`
  + `Finset.sum s (fun i => f i)`, `Finset.prod s (fun i => f i)`
  + `\sum`, `\prod`
* + `∑ i, f i`
  + `Finset.sum Finset.univ (fun i => f i)`
  + —
* + `∑' n, f n`
  + `tsum (fun n => f n)`
  + `\sum` then `'`
* + `∫ x in a..b, f x`
  + `intervalIntegral (fun x => f x) a b volume`
  + `\integral` (`\int` gives `ℤ`)
* + `∫ x, f x ∂μ`
  + `MeasureTheory.integral μ (fun x => f x)`
  + `\partial`
* + `∀ᶠ x in F, p x`
  + `Filter.Eventually (fun x => p x) F`
  + `\all\^f`
* + `𝓝 x`, `𝓟 s`
  + `nhds x`, `Filter.principal s`
  + `\nhds`, `\MCP`; after `open Topology`, `open Filter`
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

The derivative has no notation. `deriv f x` is the derivative of `f` at `x`, and the function is passed as an argument, written with `fun`. `deriv f` is again a function `ℝ → ℝ`, so the second derivative is `deriv (deriv f)`. Mathlib defines `deriv` through the Fréchet derivative: `fderiv ℝ f x` is the derivative as a linear map `ℝ → ℝ`, and its value at `1` is the number `deriv f x`.

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
tag := "looking-behind-notation"
%%%

`set_option pp.notation false` prints a term without notation. This also answers questions of precedence. The body of `∑` is parsed with precedence 67, above that of `+` (65), so it stops before a `+`:

```lean
set_option pp.notation false in
#check ∑ i ∈ Finset.range 3, i + 1
#eval ∑ i ∈ Finset.range 3, i + 1     -- 4
#eval ∑ i ∈ Finset.range 3, (i + 1)   -- 6
```

The body of `∫` is parsed with precedence 60, so `∫ x in 0..1, x + 1` integrates `x + 1`. When in doubt, use brackets.

# How `(n : ℤ)` calls the coercion
%%%
tag := "coercion-elaboration"
%%%

`(e : T)` is not a function but syntax, a *type ascription*. Its elaborator in Lean's source (`elabTypeAscription`) does three things, simplified:

```
let type ← elabType T       -- ℤ
let e ← elabTerm e type     -- n, with expected type ℤ
ensureHasType type e        -- ℕ is not ℤ: coercion
```

`ensureHasType` checks whether the type of `e` is `T`, up to definitional unfolding. If not, it searches an instance of `CoeT ℕ n ℤ` ({ref "coercion-chains"}[chapter 1.7]). Without one, the result is the error `Type mismatch`. For `(n : ℤ)` with `n : ℕ` the steps are:

1. Elaborate `n` against `ℤ`. Its type is `ℕ`, a mismatch.
2. Search `CoeT ℕ n ℤ`. It is found via `CoeTail ℕ ℤ`, which comes from `NatCast ℤ`. Lean inserts `CoeT.coe ℕ n ℤ inst`.
3. Unfold every coercion function in this term until `Nat.cast n` is left.
4. Display: `Nat.cast` has the attribute `@[coe]`, so Lean prints `↑n`.

```lean
def natToInt (n : ℕ) : ℤ := (n : ℤ)
example (n : ℕ) : (n : ℤ) = @CoeT.coe ℕ n ℤ _ := rfl
set_option pp.coercions false in
set_option pp.fieldNotation false in
#print natToInt
-- fun n => Nat.cast n
```

The arrows are notation too. `↑e` elaborates `e` and then calls `ensureHasType` with the expected type; if there is none, `↑` does nothing. `⇑f` searches a `CoeFun` instance, `↥s` a `CoeSort` instance. `set_option pp.coercions false` shows the functions behind the arrows:

```lean
example (n : ℕ) : ℤ := ↑n
example (f : ℕ →+ ℕ) : ℕ → ℕ := ⇑f
example (s : Set ℕ) : Type := ↥s
set_option pp.coercions false in
#check fun (f : ℕ →+ ℕ) (s : Set ℕ) (x : s) => (f x : ℤ)
-- fun f s x => (DFunLike.coe f x.val).cast
```

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

This instance exists for every type with a cast from ℕ and every numeral `n ≥ 2`; `0` and `1` come from the classes `Zero` and `One`. It turns the numeral `7` into `Nat.cast 7`. Mathlib defines the cast into `ZMod (n + 1)` as the cast into `Fin (n + 1)`, and that takes the remainder: `Fin.ofNat n i` is `⟨i % n, _⟩`. So `(7 : ZMod 5)` is `⟨7 % 5, _⟩`, and `rfl` sees it:

```lean
example : (7 : ZMod 5) = 2 := rfl
```

Without any other information Lean reads a bare numeral as a natural number: the instance `instOfNatNat : OfNat ℕ n` is marked `@[default_instance]`, which means it is used when nothing else fixes the type.

```lean
#check 2         -- 2 : ℕ
#check (2 : ℝ)   -- 2 : ℝ
```

# Two useful shorthands
%%%
tag := "abreviation"
%%%

There are at least two abbreviations used in `Mathlib` which you will encounter frequently.

If you have `h : x = y` and `hx : P x` (with `P x : Prop`), you can prove `P y` by rewriting `hx` with `h`. The shorthand notation for this is `h ▸ hx`. (Write `\t` for `▸`).

```lean
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (hx : P x) :
    P y := by
  exact h ▸ hx
```

`h ▸ hx` is similar to the tactic `subst h`. If `y` is a variable,
`subst h` replaces `y` by `x` everywhere, in the goal and in all
hypotheses, and removes `y` and `h`. Then `hx` proves the goal:

```lean
example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (hx : P x) :
    P y := by
  subst h
  exact hx
```

There are two differences. `subst` needs one side of the equation to
be a variable; `▸` does not, it works for `h : f x = 3` as well. And
`▸` changes only the one term `hx` and the goal, `subst` the whole
context.

```lean
example (P : ℕ → Prop) (f : ℕ → ℕ) (x : ℕ)
    (h : f x = 3) (hx : P (f x)) : P 3 :=
  h ▸ hx
```

Long terms often have the form `f (g (h x))`, and the closing brackets end up far from their opening counterparts. `f <| g <| h x` means the same and needs no closing symbol: everything to the right of `<|` is the argument.

```lean
example (P Q : Prop) (hP : P) (hnP : ¬P) : Q := by
    apply False.elim <| hnP hP
```

# The `abbrev` command
%%%
tag := "abbrev"
%%%

`abbrev` makes a definition *reducible* (see the reducibility levels in {ref "reduction-rules"}[chapter 1.1]): instance search, unification and `simp` see through it, `rw` does not. A `def` is *semireducible*: `rfl` and `exact` unfold it, instance search and `simp` do not.

```lean
abbrev NatAlias := ℕ
```

After this, all type class instances that apply to `ℕ` are available for `NatAlias`. Compare this with

```lean
def NatAlias' := ℕ
example : NatAlias' := (2 : ℕ)
```

where `NatAlias'` is a new name that instance search does not see through: Lean does *not* apply `ℕ` instances to `NatAlias'`, and you would have to derive or register them yourself. Definitional unfolding still works, so the `example` is accepted.

Use `abbrev` when you want a short name for a type or expression but do not want to create a new abstraction barrier. Use `def` when the new name should be a concept of its own:

- *Other instances.* Mathlib defines `def Lex (α : Type*) := α`. Because `Lex` is a `def`, `Lex (ℕ × ℕ)` can carry the lexicographic order while `ℕ × ℕ` keeps the componentwise one ({ref "typeclasses"}[chapter 1.6]). With `abbrev`, instance search would see through the name and find the componentwise order again. `OrderDual` (the reversed order) and `Multiplicative` (an additive structure written multiplicatively) are built the same way.
- *Lemmas.* `simp` and instance search see through an `abbrev` when they match a lemma: for `abbrev F (n : ℕ) := n + 1` and `h : x + 1 = 5`, `simp [h]` proves `F x = 5`. For a `def` it does not, so a `def` needs lemmas of its own. In both cases the goal shows the name `F x`.
- *Speed.* Reducible definitions are unfolded again and again during unification, which costs time for large definitions.

```lean
example : ¬((1, 5) ≤ ((2, 0) : ℕ × ℕ)) := by decide
example : toLex (1, 5) ≤ toLex ((2, 0) : ℕ × ℕ) := by
  decide

abbrev LexA (α : Type) := α
-- with `abbrev`, the componentwise order comes back
example : ¬((1, 5) ≤ ((2, 0) : LexA (ℕ × ℕ))) := by
  decide
```

`toLex` sends a pair to the same pair, seen as an element of `Lex (ℕ × ℕ)`.

For the point on lemmas:

```lean
abbrev F (n : ℕ) := n + 1
example (x : ℕ) (h : x + 1 = 5) : F x = 5 := by
  simp [h]
```
