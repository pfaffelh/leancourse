import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`obtain`" =>

**Summary:** The `obtain` tactic can be used to merge `have` and `cases` into one command.

**Examples:**

**Proof state** **Command** **New proof state**
------------------------------------------ --------------------------- -------------------------------------
`f : ℕ → ℕ → Prop` `obtain ⟨ m, hm ⟩` `f: ℕ → ℕ → Prop`
`h : ∀ (n : ℕ), ∃ (m : ℕ), f n m` ` := h 27,` `h : ∀ (n : ℕ), ∃ (m : ℕ), `
` f n m`
`m : ℕ`
`hm : f 27 m`
