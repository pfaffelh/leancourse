import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 2: Cantor-Schröder-Bernstein via Knaster-Tarski" =>
%%%
tag := "project-csb"
%%%

*What it is.*  The Cantor-Schröder-Bernstein theorem states that if
there are injections `f : α → β` and `g : β → α`, then there is a
bijection between `α` and `β`.  It is the "antisymmetry of
cardinality" and a genuinely non-obvious theorem — the bijection has
to be assembled from pieces of `f` and the inverse of `g`.  The
slickest proof runs through the Knaster-Tarski fixed-point theorem
from the {ref "fixed-points"}[chapter on orders and lattices].

*Implementation idea.*  Consider the map on subsets of `α` sending
`A` to the complement of `g '' (f '' A)ᶜ` (image of the complement of
the image).  Show it is monotone, so Knaster-Tarski — in Mathlib:
`OrderHom.lfp` — produces a fixed point `A`.  On `A` define the
bijection by `f`; outside `A`, the fixed-point equation shows every
element lies in the image of `g`, so it has a unique `g`-preimage.
Prove that the resulting function is bijective.  Mathlib's own proof
(`Function.Embedding.schroederBernstein`) follows exactly this route,
so you can compare notes when you are done — but try it yourself
first.  Stretch goals: derive the statement in its embedding form
`α ↪ β → β ↪ α → Nonempty (α ≃ β)`, and investigate which axioms
your proof uses (`#print axioms` — where does choice sneak in?).

*References.*  {citet buzzardMehta}[] discuss the theorem as a
showcase formalization; the Mathlib source and
{citet mathlibDocs}[] document the library version.
