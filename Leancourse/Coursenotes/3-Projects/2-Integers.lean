import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 2: The integers, defined in several ways" =>
%%%
tag := "project-integers"
%%%

*What it is.*  There are several reasonable definitions of `ℤ`, and
each makes different things easy. The project builds at least three
of them, proves that they are isomorphic rings, and compares them.

1. *Quotient.* `ℕ × ℕ` modulo `(a, b) ∼ (c, d) ↔ a + d = b + c`; the
   pair `(a, b)` stands for `a - b`. This is the standard construction
   from a first-year course, and it uses
   {ref "quotient-types"}[quotient types] and the axiom
   {ref "axiom-quot"}[`Quot.sound`].
2. *Inductive, as in Lean.* Two constructors `ofNat n` (for `n`) and
   `negSucc n` (for `-(n + 1)`). Every integer has exactly one
   representation, so equality is decidable and `#eval` works.
3. *Normal forms.* The subtype of pairs `(a, b) : ℕ × ℕ` with
   `a = 0 ∨ b = 0`, i.e. one chosen representative from each class
   of 1.

Optional fourth: an inductive type `zero | pos (n : ℕ+) | neg (n : ℕ+)`
(sign and absolute value).

*Implementation idea.*  For the quotient: prove that the relation is
an equivalence, set `MyInt := Quotient` of the setoid, and lift `0`,
`1`, addition, negation and multiplication with `Quotient.map₂` and
`Quotient.lift`, each time proving that the operation respects the
relation (multiplication is the interesting case). Then build a
`CommRing` instance; the ring laws reduce to `ring` or `omega` on
representatives. For the inductive version, addition needs a case
split on the constructors, and the ring laws need more cases. Then
construct maps between the versions, prove that they are mutually
inverse and respect `+` and `·`, and finish with a `RingEquiv` to
Mathlib's `ℤ`. Add the order `≤` and the embedding of `ℕ`.

*Comments and extensions.*
* The write-up should say which version made which proof short:
  ring laws (easy for the quotient, case-heavy for the inductive
  type), decidable equality and computation (free for the inductive
  type, needs work for the quotient), and the normal form (where
  is the work hidden?).
* `#print axioms` for each version: where does `Quot.sound` appear?
* Stretch: `ℚ` as a quotient of `ℤ × ℕ+`, compared with Mathlib's
  `Rat` (a structure with a reduced numerator and denominator, see
  {ref "numbers"}[chapter 2.1]).

*References.*  {citet theoremProvingInLean4}[] explains the quotient
machinery; {citet mathlibDocs}[] documents `Quotient.lift`,
`Quotient.map₂` and `Int`.
