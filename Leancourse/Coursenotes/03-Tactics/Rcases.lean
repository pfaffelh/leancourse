import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`rcases`" =>

+-------------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==============================+:=============+:======================+
| `h : P ∧ Q ∨ P ∧ R`\ | | |
| `⊢ P` | | |
| | | |
| & | | |
| | | |
| `rcases h with`\ | | |
| `(⟨hP1,hQ⟩|⟨hP2,hR⟩),` | | |
| | | |
| & | | |
| | | |
| `hP1 : P`\ | | |
| `hQ : Q`\ | | |
| `⊢ P`\ | | |
| `hP2 : P `\ | | |
| `hR : R`\ | | |
| `⊢ P` | | |
+-------------------------------+--------------+-----------------------+

**Summary:** `rcases` is a more flexible version of `cases`. Here, it is allowed to use `⟨ hP, hQ ⟩` (or `(hP | hQ)`) to to split the hypotheses `hP` and `hQ` into their cases.  As can be seen in the example above, it is also possible to nest `⟨.,.⟩` and `(.|.)`.

**Examples:**

+----------------------------+--------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:===========================+:=============+:======================+
| `h : P ∧ Q`\ | | |
| `⊢ R` | | |
| | | |
| & | | |
| | | |
| `rcases h with`\ | | |
| ` ⟨ hP, hQ ⟩` | | |
| | | |
| & | | |
| | | |
| `hP : P`\ | | |
| `hQ : Q`\ | | |
| `⊢ R` | | |
+----------------------------+--------------+-----------------------+

**Notes:**

The last example shows how to use `rcases` to directly resolve a `∃` quantifier in a hypothesis that has more than one constraint (here: `0 ≤ m)` and `m < n` can be resolved directly.
