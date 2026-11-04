import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 1: The natural numbers, Lean against Peano" =>
%%%
tag := "project-naturals"
%%%

*What it is.*  In Lean, `Nat` is an inductive type with two
constructors, `zero` and `succ` ({ref "nat"}[chapter 1.1]). Peano's
axiomatization of 1889 has five axioms:

1. `0` is a natural number.
2. Every natural number `n` has a successor `succ n`.
3. `0` is not the successor of any natural number.
4. `succ` is injective.
5. Induction: a property that holds for `0`, and for `succ n` whenever
   it holds for `n`, holds for every natural number.

The project shows how the two sides come together. In one direction,
the two constructors and the recursor `Nat.rec` give all five axioms.
In the other, any type satisfying the five axioms is equivalent to
`Nat`.

*Implementation idea.*

* *From `Nat` to Peano.* Axioms 1 and 2 are the constructors. Prove 3
  and 4 by hand, without `Nat.succ_ne_zero` and `Nat.succ_injective`.
  This needs the fact that constructors are distinct and injective,
  which Lean derives from the recursor (`Nat.noConfusion`, or the
  tactics `cases` and `injection`). Axiom 5 is `Nat.rec` with a
  motive in `Prop`.
* *From Peano to `Nat`.* Package the axioms as a structure:

  ```
  structure Peano where
    N : Type
    zero : N
    succ : N → N
    succ_ne_zero : ∀ n, succ n ≠ zero
    succ_inj : ∀ m n, succ m = succ n → m = n
    ind : ∀ P : N → Prop, P zero →
      (∀ n, P n → P (succ n)) → ∀ n, P n
  ```

  The map `Nat → N` is defined by recursion on `Nat`. The map back is
  the main work: `ind` only proves *propositions*, it does not define
  functions. You need Dedekind's *recursion theorem* (1888): for every
  `a : X` and `f : X → X` there is exactly one `g : N → X` with
  `g zero = a` and `g (succ n) = f (g n)`. Prove it from `ind`, for
  example by building `g` as a relation and showing by induction that
  it is the graph of a function. Then construct `N ≃ ℕ`.
* *Which axiom is used where?* Drop axiom 3, 4 or 5 and give a model
  of the remaining axioms that is not equivalent to `Nat`: `Fin 1`
  with `succ 0 = 0`; `Fin 2` with `succ` constantly `1`; `ℕ ⊕ ℤ` with
  `succ` on both summands.

*Comments and extensions.*
* Lean's `Nat.rec` has a motive `ℕ → Sort u`, so it defines functions
  as well as proving statements. Peano's axiom 5 is the weaker,
  `Prop`-valued half. The recursion theorem is exactly the gap
  between the two.
* Uniqueness: show that the equivalence commutes with `zero` and
  `succ` and that there is only one such map. In the language of
  category theory: `Nat` is an initial algebra.
* Transport addition and multiplication to `N` with the recursion
  theorem and prove that the equivalence respects them.
* `ind` quantifies over *all* predicates, so it is a second-order
  axiom; that is why any two models are equivalent. First-order
  Peano arithmetic has non-standard models. Explain the difference
  in the write-up.

*References.* Dedekind, *Was sind und was sollen die Zahlen?* (1888),
§ 126 for the recursion theorem; Peano, *Arithmetices principia*
(1889). {citet theoremProvingInLean4}[] describes how Lean generates
`Nat.rec` and `Nat.noConfusion`.
