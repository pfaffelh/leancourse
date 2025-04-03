import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`obtain`" =>
%%%
tag := "obtain"
%%%

**Summary:** The `obtain` tactic can be used to merge `have` and `cases` into one command.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + f : ℕ → ℕ → Prop {br}[] h : ∀ (n : ℕ), ∃ (m : ℕ), f n m
  + obtain ⟨ m, hm ⟩ := h 27
  + f: ℕ → ℕ → Prop {br}[] h : ∀ (n : ℕ), ∃ (m : ℕ), f n m {br}[] m : ℕ {br}[] hm : f 27 m
:::
