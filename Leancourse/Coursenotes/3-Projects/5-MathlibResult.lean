import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 5: Reading a theorem in Mathlib" =>
%%%
tag := "project-mathlib"
%%%

*What it is.*  Take an important result in Mathlib and understand its
proof, or the construction behind it, through the formalization. The
result is a written account of how Mathlib does it, together with a
Lean file in which you redo the central step yourself.

Candidates (with their Mathlib names):

* the fundamental theorem of algebra, `Complex.isAlgClosed`;
* the completeness of `ℝ`, `Real.exists_isLUB`;
* Banach's fixed-point theorem, `ContractingWith.fixedPoint_isFixedPt`;
* Sylow's first theorem, `Sylow.exists_subgroup_card_pow_prime`;
* quadratic reciprocity, `legendreSym.quadratic_reciprocity`;
* Lagrange's four-square theorem, `Nat.sum_four_squares`.

Other choices are welcome; agree on the result with us first.

*Implementation idea.*

1. *Statement.* Read the statement until every symbol is clear:
   which typeclasses appear, what each hypothesis says, and why it is
   phrased this way (for example with `Nat.card` or `Fact p.Prime`).
   Compare with the textbook statement.
2. *Dependencies.* Follow the proof with "go to definition" and
   `#check`. Draw the tree of definitions and lemmas it rests on,
   down to the point where everything is familiar.
3. *Comparison.* Put the Mathlib proof next to a textbook proof.
   Where do they agree? Where did Mathlib generalize (filters,
   typeclasses, a more abstract setting), and which other results
   use the general version?
4. *Own proof.* In your own file, prove the central step, or a
   special case of the theorem, without the Mathlib lemma that does
   it. Use `#print axioms` to compare your proof with Mathlib's.

*Comments.*  This project trains the skill used most in practice:
reading and using a large library. The difficulty depends on the
theorem; agree on the depth of step 4 when choosing.

*References.*  {citet mathlibDocs}[]; each declaration there links to
its source.
