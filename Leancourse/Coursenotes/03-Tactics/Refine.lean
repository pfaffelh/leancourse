import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`refine`" =>

**Summary:** The `refine` tactic is like `exact` with holes. More precisely: if the goal is to apply a combination of hypotheses, you can do that with 'refine' and write an open term '_' for each. You then get each '_' back as a new goal (where those with definitional equality are solved immediately).

**Examples:**

+----------------------+----------------------+----------------------+
| **Proof state** | **Command** | **New proof |
| | | state** |
+:=====================+:=====================+:=====================+
| `hQ : Q` | `refin | `hQ : Q` |
| | e ⟨ _, hQ ⟩,` | |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q` | | `⊢ P` |
+----------------------+----------------------+----------------------+
| `⊢ ∃ (n : ℕ) (h | | |
| : n > 0), `\ | | |
| ` | | |
| n ^ 2 = 9` | | |
| | | |
| & | | |
| | | |
| `refine `\ | | |
| `⟨3, ?_, b | | |
| y norm_num⟩,` | | |
| | | |
| & | | |
| | | |
| `⊢ 3 > 0` | | |
+----------------------+----------------------+----------------------+
