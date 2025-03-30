import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`intro`" =>
%%%
tag := "intro"
%%%

**Summary**

If the goal is of the form `⊢ P → Q` or `∀ (n : ℕ), P n`, you can proceed with `intro P` or `intro n`. You can use several `intro` commands at the same time to summarize a single one. A little more precisely, `intro h1 h2 h3,` is identical to `intro h1; intro h2; intro h3`.


**Examples**

**Proof state** **Command** **New proof state**
--------------------------- ------------------- -----------------------
`⊢ P → Q` `intro hP` `hP : P`
`⊢ Q`
`f : α → Prop` `intro x,` `f: α → Prop`
`⊢ ∀ (x : α), f x` `x : α`
`⊢ f x`

+-------------------------------+------------------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:==============================+:=======================+:======================+
| `⊢ P → Q → R` | `intros hP hQ,` | `hP : P` |
+-------------------------------+------------------------+-----------------------+
| | | `hQ : Q` |
+-------------------------------+------------------------+-----------------------+
| | | `⊢ R` |
+-------------------------------+------------------------+-----------------------+
| `P: ℕ → Prop`\ | | |
| `⊢ ∀ (n : ℕ), P n → Q` | | |
| | | |
| & | | |
| | | |
| `intros n hP` | | |
| | | |
| & | | |
| | | |
| `P: ℕ → Prop`\ | | |
| `n: ℕ`\ | | |
| `hP: P n` `⊢ Q` | | |
+-------------------------------+------------------------+-----------------------+


**Notes**

* Several `intro` commands in a row are best combined. Furthermore,  `rintro` is a more flexible variant.
* A reversal of `intro` is `revert`.
