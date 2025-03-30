import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`by_cases`" =>

**Summary:**
If you have a term `P : Prop` as a hypothesis, `by_cases hP : P` returns two goals. The first one has `hP : P`, and the second one `hP : ¬P`. This tactic is thus identical to `have hP : P ∨ ¬ P, exact em P, cases hP,`. (The second expression is `em : ∀ (p : Prop), p ∨ ¬p`.)

**Examples**


In the second example, we use a variable of type `bool` This is defined as follows:

```
inductive bool : Type
| ff : bool
| tt : bool
```

A Boolean variable can only have the values `tt` (for `true`) and `ff` (for `false`).

**Notes**

* Apparently, the `by_cases` tactic (just like `by_contradiction`) assumes that a statement is either true or false. This is also known as the law of excluded middle. In mathematics, proofs that do not use this rule are called constructive.
* For terms of type `Prop`, the tactic `tauto` (or `tauto!`) can
draw
