import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 6: Mutual inductive types" =>
%%%
tag := "project-mutual"
%%%

*What it is.*  The course did not cover *mutual inductive types*:
several types, declared together in a `mutual … end` block, whose
constructors refer to each other. The first task is to find out what
they are, using the
[Lean Language Reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#Lean___Parser___Command___mutual)
and experiments. The second is to come up with examples of your own.
Here are two to start from:

```
mutual
  inductive IsEven : ℕ → Prop
    | zero : IsEven 0
    | succ {n : ℕ} : IsOdd n → IsEven (n + 1)
  inductive IsOdd : ℕ → Prop
    | succ {n : ℕ} : IsEven n → IsOdd (n + 1)
end

mutual
  inductive MTree (α : Type) where
    | node : α → MForest α → MTree α
  inductive MForest (α : Type) where
    | nil : MForest α
    | cons : MTree α → MForest α → MForest α
end
```

A tree is a label and a forest of children; a forest is a list of
trees.

*Implementation idea.*

* *Even and odd.* Prove `IsEven n ∨ IsOdd n`, that no number is both,
  and that `IsEven` and `IsOdd` agree with Mathlib's `Even` and `Odd`.
* *Trees and forests.* Define `size`, `mirror` and the list of labels
  by mutual recursion (a `mutual` block of `def`s), and prove
  statements such as `t.mirror.size = t.size`. The tactic `induction`
  refuses mutual types. The proofs are therefore again mutual
  recursions, as `theorem`s in a `mutual` block.
* *The recursor.* `#check @MTree.rec` shows two motives, one for each
  type. Explain how it is built, following the recipe of
  {ref "recursor"}[chapter 1.3].
* *Your own examples.* Two suggestions:
  - A small language with arithmetic and Boolean expressions: `AExp`
    has an `if b then a₁ else a₂` with `b : BExp`, and `BExp` has a
    comparison `a₁ ≤ a₂` with `aᵢ : AExp`. Write the evaluators
    `AExp.eval` and `BExp.eval`, a simplifier (constant folding), and
    prove that the simplifier does not change the value.
  - Games: given `move : P → P → Prop`, define winning and losing
    positions mutually. A position is winning if some move leads to a
    losing position, and losing if every move leads to a winning one.
    For the game "take 1 or 2 from a pile of `n`", prove that `n` is
    losing if and only if `3 ∣ n`.

*Comments and extensions.*
* *Nested types.* `inductive Rose (α : Type) | node : α → List (Rose
  α) → Rose α` is not declared as mutual, but `#check @Rose.rec` also
  shows two motives, the second one for `List (Rose α)`. Lean treats
  nested types as mutual ones. Construct `MTree α ≃ Rose α`.
* *One type instead of two.* Encode `MTree` and `MForest` as a single
  family `TF : Bool → Type` indexed by "tree or forest", and prove
  that it is equivalent to the mutual version.
* *Games.* The inductive `Win`/`Lose` only see games in which every
  play ends. What happens for a game with a cycle? Discuss
  coinductive definitions in the write-up.

*References.*  The Lean Language Reference (link above) for `mutual`;
{citet theoremProvingInLean4}[], chapter on inductive types, for
mutual and nested inductive types.
