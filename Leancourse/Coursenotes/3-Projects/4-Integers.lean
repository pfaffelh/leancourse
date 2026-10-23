import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 4: The integers from scratch" =>
%%%
tag := "project-integers"
%%%

*What it is.*  In Lean, `ℤ` could be *defined* as the quotient of
`ℕ × ℕ` by the relation identifying `(a, b)` and `(c, d)` whenever
`a + d = b + c` — the pair `(a, b)` standing for the difference of
`a` and `b`.  This project carries that construction out: it is the
canonical way to experience {ref "quotient-types"}[quotient types]
and the axiom {ref "axiom-quot"}[`Quot.sound`] doing real work.

*Implementation idea.*  Define the relation on `ℕ × ℕ`, prove it is
an equivalence, and set `MyInt := Quotient` of the corresponding
setoid.  Lift `0`, `1`, addition, negation, and multiplication with
`Quotient.map` and `Quotient.lift`, proving each time that the
operation respects the relation (multiplication is the interesting
case).  Then assemble a `CommRing MyInt` instance — `ring` is not
available inside your own ring, so the laws are proved by `omega` or
`nlinarith` on representatives.  Add the linear order and the
embedding of `ℕ`.  Stretch goals: construct `ℚ` as a quotient of
`ℤ × ℕ` the same way, or build a ring isomorphism between `MyInt`
and Mathlib's `ℤ` (which, for efficiency, is *not* defined as a
quotient — find out how it is defined instead).

*References.*  {citet theoremProvingInLean4}[] explains the quotient
machinery in detail; {citet mathlibDocs}[] documents
`Quotient.lift`, `Quotient.map`, and friends.
