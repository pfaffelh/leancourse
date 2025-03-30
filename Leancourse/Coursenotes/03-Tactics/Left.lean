import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "`left`" =>

**Summary:**

The application of `left,` is identical to `apply h` for `h : P → P ∨ Q`. So if you have a goal of the form `⊢ P ∨ Q`, `left,` causes you to have only the goal `⊢ P`. After all, it is sufficient to show `P` to close the goal.

**Examples:**

+-------------------------+----------------+-----------------------+
| **Proof state** | **Command** | **New proof state** |
+:========================+:===============+:======================+
| `⊢ P ∨ Q` | `left,` | `⊢ P` |
+-------------------------+----------------+-----------------------+
| `⊢ ℕ` | | |
| | | |
| & | | |
| | | |
| `left,` | | |
| | | |
| & | | |
| | | |
| **goals accomplished** | | |
+-------------------------+----------------+-----------------------+


The second example requires a little explanation. First of all, you have to understand that the goal `⊢ ℕ` is to show that there is a term of type `ℕ`, i.e. that there is a natural number. Now you have to know how `ℕ` is implemented in Lean. This is

```
inductive nat
| zero : nat
| succ (n : nat) : nat
```

together with

```
notation `ℕ` := nat
```
This means: The type `ℕ` is defined by the fact that `zero` is a term of this type, and that there is a function `succ : ℕ → ℕ`. Thus, in the second example, the input `left,` is closed because by definition `zero : ℕ` holds, so in particular there is a term of type `ℕ`.

**Notes:**

* See also `right,` for the equivalent tactic, which is `apply h` for `h : Q → P ∨ Q`.
* As in the second example, `left,` can always be applied when dealing with an inductive type with two constructors (such like `ℕ`).
