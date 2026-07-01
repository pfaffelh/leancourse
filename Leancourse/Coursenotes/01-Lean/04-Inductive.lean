import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Inductive types" =>
%%%
htmlSplit := .never
tag := "inductive"
%%%

Many everyday types in Lean -- `Nat`, `List`, `Option`, `Bool`, even
`Empty` -- are *inductive* types. You declare one by giving a name,
the type's universe, and a list of *constructors*: each constructor
says how to build a new element of the type out of existing pieces.

The classical example is the natural numbers:

```lean
namespace Demo
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
end Demo
```

This declaration introduces three things at once:

- a new type `Demo.MyNat`;
- two constructors `Demo.MyNat.zero` and `Demo.MyNat.succ`, so every
  element of `MyNat` is either `zero` or `succ n` for some `n`;
- a *recursor* `Demo.MyNat.rec` which lets you define functions on
  `MyNat` by specifying what happens in each constructor case.

Definitions on an inductive type are typically written with the
pattern-matching syntax from the chapter on function definitions:

```lean
namespace Demo
def double : MyNat → MyNat
  | .zero    => .zero
  | .succ n => .succ (.succ (double n))
end Demo
```

Proofs about an inductive type use the `induction` tactic, which
applies the recursor for you: one subgoal per constructor, with an
induction hypothesis for each recursive argument.

Inductive types also cover non-recursive data:

```lean
inductive Colour where
  | red | green | blue
```

and parameterized types:

```lean
-- `Option α` is either `none` or `some a` for some `a : α`.
namespace Demo
inductive MyOption (α : Type) where
  | none : MyOption α
  | some (a : α) : MyOption α
end Demo
```

Inductive types are the main mechanism by which new data types enter
Lean; `Mathlib` uses them extensively, and understanding them is
essential for reading the library.
