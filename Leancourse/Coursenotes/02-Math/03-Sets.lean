import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Dealing with Sets" =>
%%%
htmlSplit := .never
tag := "Sets"
%%%

# Dealing with Sets

Regarding the notation: for sets, we are used to writing `n ∈ ℕ` if `n` is a natural number. In type theory, we write `n : ℕ` and say that `n` is a term (or expression) of type `ℕ`. More generally, when typing an expression, Lean checks its type and tells us if it can make sense of our statement. (Incidentally, this can be quite confusing: for example, the statement `(x : ℕ) → (x : ℤ)`, i.e. (every natural number is also an integer) is not at all comprehensible for `lean`. Because `x` is a term of type `ℕ` (and thus of no other type), so that `x : ℤ` makes no sense at all for Lean. In this case, the solution is an 'invisible mapping' (or coercion) `coe : ℕ → ℤ`.)
