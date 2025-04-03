import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`by_cases`" =>
%%%
tag := "by_cases"
%%%

**Summary:**
If you have a term `P : Prop` as a hypothesis, `by_cases hP : P` returns two goals. The first one has `hP : P`, and the second one `hP : ¬P`. This tactic is thus identical to `have hP : P ∨ ¬ P, exact em P, cases hP,`. (The second expression is `em : ∀ (p : Prop), p ∨ ¬p`.)

**Examples**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P`
  + `by_cases h : Q`
  + `h : Q` {br}[] `⊢ P` {br}[] `h : ¬Q` `⊢ P`
* + `x : Bool` {br}[] `⊢ x = True ∨ x = False`
  + `by_cases x = True`
  + `x: bool` {br}[] `h: x = True` {br}[] `⊢ x = True ∨ x = False` {br}[]  `x: bool` {br}[] `h: ¬x = True` {br}[] `⊢ x = True ∨ x = False`
:::

In the second example, we use a variable of type `bool` This is defined as follows:

{Docstring Bool}

```lean
inductive myBool : Type
| falsch : myBool
| wahr : myBool
```
A Boolean variable can only have the values `True` and `False`.

```lean
example (P Q : Prop) (hP: P → Q) ( hP' : ¬P → Q) : Q := by
  by_cases h : P
  · exact hP h
  · exact hP' h
```

**Notes**

* Apparently, the `by_cases` tactic (just like `by_contradiction`) assumes that a statement is either true or false. This is also known as the law of excluded middle. In mathematics, proofs that do not use this rule are called constructive.
* For terms of type `Prop`, the tactic `tauto` (or `tauto!`) can draw various conclusions from a truth table.
