import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Equality" =>
%%%
htmlSplit := .never
tag := "equality"
%%%

Due to the multitude of types in Lean, we have to be careful about equality. In Lean, there are three types of equality:

* Syntactic equality: If two terms are letter-for-letter equal, then they are syntactically equal. However, there are a few more situations in which two terms are syntactically equal. Namely, if one term is just an abbreviation for the other (for example, `x = y` is an abbreviation for ` Eq x y`, where `Eq` is a function which takes two terms of the same type, and assigns `True` if they are the same and `False` otherwise), then these both terms are syntactically equal. Also equal are terms in which globally quantified variables have different letters. For example, `∀ x, ∃ y, f x y` and `∀ y, ∃ x, f y x` are syntactically equal.

* Definitional equality: Some terms are equal *by computation* -- Lean reduces both to a common form. For example, for `x : ℕ`, `x + 0` reduces to `x`, whereas `0 + x` does not (an asymmetry that comes from how `Nat` addition is defined). This notion, the *reduction rules* that generate it, and the cases where `rfl` gets *stuck*, are developed in full in {ref "reduction-rules"}[the reduction-rules section] of the chapter on the natural numbers.

* Propositional equality: If there is a proof of `x = y`, then `x` and `y` are said to be *propositionally equal*; likewise `P` and `Q` are propositionally equal when you can prove `P ↔ Q`. This is the equality you state and rewrite with in everyday mathematics.

The distinction matters because *tactics differ in which equality they respect* -- some see through it, some do not. `rfl`, `exact`, and `apply` accept a term whenever it is merely *definitionally* equal to what is expected (they run the reductions for you), whereas `rw` matches *syntactically* and will not fire unless the subterm literally appears. Many otherwise-puzzling tactic failures come down to exactly this.

There is a special kind of equality to be observed with sets and functions. For example, two functions are exactly the same if they return the same value for all values in the domain. This behavior is called *extensionality* in the theory of programming languages. (If extensionality applies, then, for example, two sorting algorithms are the same if they always produce the same result).
