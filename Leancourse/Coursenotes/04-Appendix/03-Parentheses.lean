import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Different parentheses in `Lean`" =>
%%%
htmlSplit := .never
tag := "parenthesis"
%%%

There are (essentially) three different types of parentheses in `Lean` statements. The simplest is `(...)`, which, as in normal use, indicates parentheses in the sense of what belongs together. However, you have to learn how `Lean` brackets internally when no '()' are given. Operators like *and* (`∧`), *or* (`∨`), are right-associative, so e.g. `P ∧ Q ∧ R := P ∧ (Q ∧ R)`. The application of functions in sequence, such as `f : ℕ → ℝ` and `g : ℝ → ℝ `, applied to `n : ℕ` is `g (f n)`, because `g` expects an input of type `ℝ`, and this is what `f n` provides. You cannot omit (...), i.e. in this case the parenthesis is left-associative.

Beyond grouping, `Lean` uses four kinds of *binder* brackets in a declaration's signature; they differ in *who supplies the argument, and how*:

:::table (align := left) +header
* + Bracket
  + Kind
  + Who fills it in
* + `(x : α)`
  + explicit
  + you, at every call
* + `{x : α}`
  + implicit
  + Lean, by *unification* (from the other arguments), eagerly
* + `⦃x : α⦄` (or `{{x : α}}`)
  + strict implicit
  + Lean, by unification -- but only once a following *explicit* argument is supplied
* + `[C α]`
  + instance-implicit
  + Lean, by *typeclass search* ({ref "typeclasses"}[the typeclass mechanism])
:::

Here is one definition using three of them; `#check @` makes every argument visible:

```lean
def foo {α : Type} [Add α] (x : α) : α := x + x

#check @foo
-- @foo : {α : Type} → [Add α] → α → α
```

`α` sits in `{}` because Lean infers it from the type of the explicit `x`; `Add α` sits in `[]` because it is found by instance search; only `x` must be given at the call. Real Mathlib lemmas read the same way:

```lean
#check @gt_iff_lt
-- @gt_iff_lt : ∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
```

Here `{α}`, `[inst : LT α]` and `{x y}` are all supplied automatically, so you write just `gt_iff_lt` (or apply it to concrete `x`, `y`).

# `{}` versus `⦃⦄`: eager vs. strict implicit
%%%
tag := "strict-implicit"
%%%

Both `{}` and `⦃⦄` are *implicit* -- Lean fills them in -- but they differ in *when*. A regular implicit `{x}` is solved *eagerly*, the moment the function is mentioned. A strict implicit `⦃x⦄` (also written `{{x}}`) is solved *only when a following explicit argument is actually supplied*; until then the binder stays put.

```lean
def idImp    {α : Type} (x : α) : α := x
def idStrict {{α : Type}} (x : α) : α := x
```

In ordinary use the difference is invisible (`idImp 5` and `idStrict 5` both give `5`). It matters when a function is used *without* its explicit argument -- exactly the situation for `⊆`. Mathlib defines `s ⊆ t` as `∀ ⦃a⦄, a ∈ s → a ∈ t` with a *strict* implicit `a`, so that from `h : s ⊆ t` you may apply `h` directly to a membership proof:

```lean
example (s t : Set ℕ) (h : s ⊆ t) (a : ℕ) (ha : a ∈ s) : a ∈ t := h ha
```

Had `a` been an ordinary implicit, mentioning `h` alone would have eagerly forced a metavariable for `a`, making `h ha` more awkward. Strict implicits keep such "apply me later" arguments out of the way until a real argument pins them down.
