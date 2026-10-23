import VersoManual
import Manual.Meta
import Leancourse.Markup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`nth_rewrite`, `nth_rw`" =>
%%%
tag := "nth_rewrite"
%%%

*Summary:*

Like `rw`, but you say *which* occurrence of the pattern to rewrite.
The syntax is `nth_rewrite k [h]`, where `k` counts the occurrences of
the left-hand side of `h` in the goal, **starting at 1**. As with `rw`,
`h` must be of the form `h : x = y` or `h : A ↔ B`. `nth_rw` is the
same tactic under a shorter name.

*Examples:*

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `n : ℕ` {br}[] ⊢ 0 + n = 0 + 0 + n
  + `nth_rewrite 1 [zero_add]`
  + `n : ℕ` {br}[] ⊢ n = 0 + 0 + n
* + `n : ℕ` {br}[] ⊢ 0 + n = 0 + 0 + n
  + `nth_rewrite 2 [zero_add]`
  + `n : ℕ` {br}[] ⊢ 0 + n = 0 + n
:::

*Notes:*

Counting is syntactic. In the goal above Lean sees two subterms of the
form `0 + ?a`: the `0 + n` on the left, and, since `0 + 0 + n` is
`(0 + 0) + n`, the `0 + 0` on the right. The outer `(0 + 0) + n` is not
one of them: its left argument is `0 + 0`, not `0`. So `nth_rewrite 3`
fails, and so does `nth_rewrite 0`.
