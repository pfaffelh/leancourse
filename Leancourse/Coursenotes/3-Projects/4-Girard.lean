import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 1: Girard's paradox, or why `Type : Type` is fatal" =>
%%%
tag := "project-girard"
%%%

*What it is.*  Russell's paradox shows that a "set of all sets that
do not contain themselves" is contradictory.  *Girard's paradox* is
its type-theoretic incarnation: in a type theory where the universe
contains itself — where `Type : Type` holds — one can construct a
closed term of type `False`, so the whole system collapses.  This is
precisely why Lean arranges its universes in a hierarchy
({ref "type-universes"}[the universe hierarchy]): `Type u` lives
in `Type (u+1)`, never in itself.  The project is to make this story
precise in Lean: build the paradoxical machinery, watch *exactly*
where the type-checker stops it, and prove that any universe evading
the hierarchy is contradictory.

*Implementation idea.*  A possible route, in four steps of increasing
depth:

* Build Girard's universe and locate the failure.  The only type
  former needed is the power set `Set X` (definitionally `X → Prop`).
  Girard's universe is engineered so that its own double power set
  embeds back into it:

  ```
  def U : Type 1 :=
    (X : Type) → (Set (Set X) → X) → Set (Set X)

  -- encoding: a "set of sets of U" as an element of U
  def τ (t : Set (Set U)) : U :=
    fun X f p => t (fun x => p (f (x X f)))

  -- decoding -- but `s U` instantiates `s : U` at `U`
  -- itself, and `U : Type 1`, not `Type`: rejected!
  def σ (s : U) : Set (Set U) := s U τ
  ```

  `U` and `τ` type-check; `σ` does not, and `#check_failure` lets you
  document the failure inside a compiling file.  Convince yourself
  (and your readers) that the level mismatch persists at *every*
  universe level — predicativity makes the self-instantiation
  untypeable, full stop.

* Smuggle the paradox in as a *hypothesis*.  What `Type : Type` would
  buy you is an injection of `Set (Set U)` into `U`.  Assume it and
  derive `False` — with no extra axioms — by composing with the
  singleton map `Set U → Set (Set U)` and applying Cantor's theorem,
  which Mathlib provides as `Function.cantor_injective`.  Check with
  `#print axioms` that your proof only uses Lean's standard axioms.

* Formalize Coquand's abstract version.  Package a "paradoxical
  universe" as a structure: a type `U` with maps `σ : U → Set U` and
  `τ : Set U → U` satisfying `σ (τ X) = (fun x => τ (σ x)) '' X`.
  Prove that *every* such universe is contradictory.  The proof is a
  Burali-Forti-style argument via the accessibility predicate `Acc`
  and can be carried out *without any axioms at all* — `#print
  axioms` reports none, making the refutation fully constructive.

* Stretch goals: formalize Hurkens' famous simplification of the
  paradox, and explain — in prose and with `#check_failure`
  experiments — why Lean's *impredicative* `Prop` does not fall to
  the same argument.

*References.*  The paradox is from the thesis of
{citet girard1972}[]; {citet coquand1986}[] gives the analysis on
which the abstract version above is based, and {citet hurkens1995}[]
the short self-contained term.  A formalization of Hurkens' term is
in the file `Logic/Hurkens.v` of the Rocq (formerly Coq) standard
library, which can serve as a blueprint.
