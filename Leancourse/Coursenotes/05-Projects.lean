import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Projects" =>
%%%
htmlSplit := .never
tag := "projects"
%%%

While the exercise sheets accompany the first half of the semester,
the second half is devoted to *individual projects*: you pick a topic,
formalize it in Lean, and present the result.  This chapter collects
five suggestions.  Each comes with a description of what the project
is about, a sketch of one possible implementation, and references.
The suggestions are calibrated so that a first working version fits
into a few hundred lines of Lean, and every one of them has natural
stretch goals if you want to go further.

You are equally welcome to propose a topic of your own -- for
example, formalizing an exercise from your first year of studies, or
exploring a corner of Mathlib that interests you -- as long as you
discuss the scope with us first.

# Project 1: Girard's paradox, or why `Type : Type` is fatal
%%%
tag := "project-girard"
%%%

*What it is.*  Russell's paradox shows that a "set of all sets that
do not contain themselves" is contradictory.  *Girard's paradox* is
its type-theoretic incarnation: in a type theory where the universe
contains itself -- where `Type : Type` holds -- one can construct a
closed term of type `False`, so the whole system collapses.  This is
precisely why Lean stratifies its universes
({ref "universe-hierarchy"}[the universe hierarchy]): `Type u` lives
in `Type (u+1)`, never in itself.  The project is to make this story
precise in Lean: build the paradoxical machinery, watch *exactly*
where the type-checker stops it, and prove that any universe evading
the stratification is contradictory.

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
  universe level -- predicativity makes the self-instantiation
  untypeable, full stop.

* Smuggle the paradox in as a *hypothesis*.  What `Type : Type` would
  buy you is an injection of `Set (Set U)` into `U`.  Assume it and
  derive `False` -- with no extra axioms -- by composing with the
  singleton map `Set U → Set (Set U)` and applying Cantor's theorem,
  which Mathlib provides as `Function.cantor_injective`.  Check with
  `#print axioms` that your proof only uses Lean's standard axioms.

* Formalize Coquand's abstract version.  Package a "paradoxical
  universe" as a structure: a type `U` with maps `σ : U → Set U` and
  `τ : Set U → U` satisfying `σ (τ X) = (fun x => τ (σ x)) '' X`.
  Prove that *every* such universe is contradictory.  The proof is a
  Burali-Forti-style argument via the accessibility predicate `Acc`
  and can be carried out *without any axioms at all* -- `#print
  axioms` reports none, making the refutation fully constructive.

* Stretch goals: formalize Hurkens' famous simplification of the
  paradox, and explain -- in prose and with `#check_failure`
  experiments -- why Lean's *impredicative* `Prop` does not fall to
  the same argument.

*References.*  The paradox is from the thesis of
{citet girard1972}[]; {citet coquand1986}[] gives the analysis on
which the abstract version above is based, and {citet hurkens1995}[]
the short self-contained term.  A formalization of Hurkens' term is
in the file `Logic/Hurkens.v` of the Rocq (formerly Coq) standard
library, which can serve as a blueprint.

# Project 2: Cantor-Schröder-Bernstein via Knaster-Tarski
%%%
tag := "project-csb"
%%%

*What it is.*  The Cantor-Schröder-Bernstein theorem states that if
there are injections `f : α → β` and `g : β → α`, then there is a
bijection between `α` and `β`.  It is the "antisymmetry of
cardinality" and a genuinely non-obvious theorem -- the bijection has
to be assembled from pieces of `f` and the inverse of `g`.  The
slickest proof runs through the Knaster-Tarski fixed-point theorem
from the {ref "fixed-points"}[chapter on orders and lattices].

*Implementation idea.*  Consider the map on subsets of `α` sending
`A` to the complement of `g '' (f '' A)ᶜ` (image of the complement of
the image).  Show it is monotone, so Knaster-Tarski -- in Mathlib:
`OrderHom.lfp` -- produces a fixed point `A`.  On `A` define the
bijection by `f`; outside `A`, the fixed-point equation shows every
element lies in the image of `g`, so it has a unique `g`-preimage.
Prove that the resulting function is bijective.  Mathlib's own proof
(`Function.Embedding.schroederBernstein`) follows exactly this route,
so you can compare notes when you are done -- but try it yourself
first.  Stretch goals: derive the statement in its embedding form
`α ↪ β → β ↪ α → Nonempty (α ≃ β)`, and investigate which axioms
your proof uses (`#print axioms` -- where does choice sneak in?).

*References.*  {citet buzzardMehta}[] discuss the theorem as a
showcase formalization; the Mathlib source and
{citet mathlibDocs}[] document the library version.

# Project 3: Limits of sequences, with and without filters
%%%
tag := "project-limits"
%%%

*What it is.*  In the {ref "filters"}[filters chapter] we saw that
Mathlib phrases convergence via `Filter.Tendsto`.  This project
builds the classical theory first -- the epsilon-N definition from
Analysis 1 -- and then proves that the two formulations agree.  It is
the ideal project if you want to formalize material you know very
well and see the filter language pay off.

*Implementation idea.*  Define
`TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop` by the usual quantifier chain
(for every positive epsilon there is an N beyond which the distance
is below epsilon).  Then build the toolbox: limits are unique; a
constant sequence converges; limits respect sums, scalar multiples,
and products; the squeeze theorem.  Expect to practice `intro`,
`obtain`, `specialize`, and the art of choosing the right `N` (a
`max` of two thresholds) -- plus `linarith` and `abs` lemmas.
Finally, prove the bridge:
`TendsTo a t ↔ Filter.Tendsto a Filter.atTop (nhds t)`, using
Mathlib's `Metric.tendsto_atTop` as the stepping stone, and reprove
one of your toolbox lemmas in one line with
{ref "filter-tendsto"}[the filter API].  Stretch goal: monotone
bounded sequences converge (this needs the completeness of `ℝ` via
suprema).

*References.*  {citet mathematicsInLean}[] develops exactly this
programme in its convergence chapter, and {citet buzzardMehta}[]
cover limits of sequences as a running example; consult them when
stuck, not before.

# Project 4: The integers from scratch
%%%
tag := "project-integers"
%%%

*What it is.*  In Lean, `ℤ` could be *defined* as the quotient of
`ℕ × ℕ` by the relation identifying `(a, b)` and `(c, d)` whenever
`a + d = b + c` -- the pair `(a, b)` standing for the difference of
`a` and `b`.  This project carries that construction out: it is the
canonical way to experience {ref "quotient-types"}[quotient types]
and the axiom {ref "axiom-quot"}[`Quot.sound`] doing real work.

*Implementation idea.*  Define the relation on `ℕ × ℕ`, prove it is
an equivalence, and set `MyInt := Quotient` of the corresponding
setoid.  Lift `0`, `1`, addition, negation, and multiplication with
`Quotient.map` and `Quotient.lift`, proving each time that the
operation respects the relation (multiplication is the interesting
case).  Then assemble a `CommRing MyInt` instance -- `ring` is not
available inside your own ring, so the laws are proved by `omega` or
`nlinarith` on representatives.  Add the linear order and the
embedding of `ℕ`.  Stretch goals: construct `ℚ` as a quotient of
`ℤ × ℕ` the same way, or build a ring isomorphism between `MyInt`
and Mathlib's `ℤ` (which, for efficiency, is *not* defined as a
quotient -- find out how it is defined instead).

*References.*  {citet theoremProvingInLean4}[] explains the quotient
machinery in detail; {citet mathlibDocs}[] documents
`Quotient.lift`, `Quotient.map`, and friends.

# Project 5: The Monty Hall problem with the PMF monad
%%%
tag := "project-monty-hall"
%%%

*What it is.*  A car is hidden uniformly behind one of three doors;
you pick a door; the host opens another door, revealing a goat; you
may stay or switch.  Famously, switching wins with probability 2/3.
This project models the game in the
{ref "probability-pmf"}[probability monad `PMF`] and *proves* that
number -- a complete formalization of a statement most people refuse
to believe when they first hear it.

*Implementation idea.*  Work over `Fin 3`.  The car position is
`PMF.uniformOfFintype (Fin 3)`; fix the contestant's initial pick as
door `0` (argue by symmetry in prose, or model the pick uniformly as
a stretch goal).  The host's choice is the subtle part: if the car is
behind door `0` the host opens one of the two goat doors uniformly,
otherwise his hand is forced.  Chain these with `PMF.bind` and
`PMF.pure` -- or `do`-notation -- into a distribution over outcomes,
and define the two strategies as functions from the observed
information to the final door.  The theorem is that the switch
strategy wins with probability 2/3 and staying wins with 1/3.  The
computation unfolds via `PMF.bind_apply` and `PMF.pure_apply` into a
finite sum over `Fin 3` (`Fin.sum_univ_three` helps); note that PMF
probabilities live in `ENNReal`, so keep the extended-real
simp lemmas nearby.  Stretch goals: `n` doors of which the host
opens `k`, or a host with a known bias -- does switching still help?

*References.*  {citet mathlibDocs}[] documents the `PMF` API; the
{ref "probability-pmf"}[probability chapter] of these notes develops
`pure`, `bind`, and the monad laws that the model is built from.
