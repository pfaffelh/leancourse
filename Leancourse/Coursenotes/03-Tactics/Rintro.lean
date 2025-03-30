import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`rintro`" =>

**Summary:** The `rintro` tactic is used to process several `intro` and `cases` tactics on one line.

**Examples**

**Proof state** **Command** **New proof state**
---------------------- ------------------------------ -----------------------
`⊢ P ∨ Q → R` `rintro ( hP | hQ ),` `hP : P`
$=$ `⊢ P`
`intro h,` `hQ : Q`
`cases h with hP hQ,` `⊢ Q`
`⊢ P ∧ Q → R` `rintro ⟨ hP , hQ ⟩,` `hP : P`
$=$ `hQ : Q`
`intro h,` `⊢ Q`
`cases h with h1 h2,`

**Notes:**

Here, more than two `∨` can also be split into cases in one step: With `A ∨ B ∨ C`, `rintro (A | B | C)` introduces three goals.
