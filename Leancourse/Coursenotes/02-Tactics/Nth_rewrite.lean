import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`nth_rewrite`" =>
%%%
tag := "nth_rewrite"
%%%

**Summary:**

This tactic is related to `rw`. The difference is that you can specify the occurrence number of the term to be replaced on which `rw` is to be applied. The exact syntax is `nth_rewrite k h`, where `k` is the number (starting with $0$) of the term to be replaced and `h` is the hypothesis to be replaced. As with `rw`, this must be in the form `h : x=y` or `h : A↔B`.

**Examples:**

:::table (align := left) (header := true)
* + Proof state
  + Tactic
  + New proof state
* + `n : ℕ` {br}[] ⊢ 0 + n = 0 + 0 + n
  + `nth_rewrite 0 zero_add`
  + `n : ℕ` {br}[] ⊢ n = 0 + 0 + n
* + `n : ℕ` {br}[] ⊢ 0 + n = 0 + 0 + n
  + `nth_rewrite 1 zero_add`
  + `n : ℕ` {br}[] ⊢ 0 + n = 0 + n
* + `n : ℕ` {br}[] ⊢ 0 + n = 0 + 0 + n
  + `nth_rewrite 2 zero_add`
  + `n : ℕ` {br}[] ⊢ 0 + n = 0 + n
:::

In the above example, Lean sees three terms of the form `0 + ?_`: Number 0 is on the left-hand side, for numbers 1 and 2, on the right side (because of the parenthesis `0 + 0 + n = (0 + 0) + n`),  the second = is checked first. To the left of it is `0 + 0`, which is by definition identical to `0`. applying `rw zero_add` here, the term is converted to `n`. For number 2, you see `0 + 0`, determine that it is of the desired form and convert it to `0`.
