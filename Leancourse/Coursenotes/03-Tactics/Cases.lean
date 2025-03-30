import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`cases'`" =>

**Summary:** If a hypothesis is composed, i.e. can be expanded into two or more cases, `cases'` delivers exactly that. This can be used not only used with hypotheses `h : P ∨ Q` or `h : P ∧ Q`, but also with structures that consist of several cases, such as `∃...` (here there is a variable and a statement) and `x : bool` or `n : ℕ`.

**Examples:**


**Notes:**

* The application `cases' n` for `n : ℕ` is strictly weaker than complete induction (see `induction`). After all, `cases` only converts `n : ℕ` into the two cases `0` and `succ n`, but you cannot use the statement for `n-1` to prove the statement for `n`.
* A more flexible version of `cases'` is `rcases`.
