import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Manual.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`congr`" =>
%%%
tag := "congr"
%%%

**Summary:** If you have to show an equality `f x = f y`, then `congr` uses the statement that the equality is particularly true if `x = y`.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P x = P y`
  + `congr`
  + `⊢ x = y`
:::


**Notes:**

The related tactic `congr'` uses another parameter that determines how many recursive layers are eliminated in the goal. This is helpful in the following examples:

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + ⊢ f (x + y) = f (y + x)
  + congr
  + ⊢ x = y {br}[] ⊢ y = x
* + ⊢ f (x + y) = f (y + x)
  + congr' 2
  + ⊢ y = x
* + ⊢ f (x + y) = f (y + x)
  + congr' 1
  + ⊢ x + y = y + x
:::
