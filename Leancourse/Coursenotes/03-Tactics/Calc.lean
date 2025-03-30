import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table
import Leancourse.Misc.Defs

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

#doc (Manual) "`calc`" =>

**Summary:** As the word suggests, `calc` is about concrete calculations. This is not a tactic, but a `lean` mode. This means that you can enter this mode (with the word `calc`) and enter calculation steps and proofs that each individual calculation step is correct.

**Examples**

Here is a proof of the first binomial formula that only comes about by rewriting of calculating properties from the `mathlib`.

```
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
have h : n + n = 2*n,
{
nth_rewrite 0 ← one_mul n,
nth_rewrite 1 ← one_mul n,
rw ← add_mul,
},
calc (n+1)^2 = (n+1) * (n+1) : by { rw pow_two, }...
 = (n+1)*n + (n+1) * 1: by {rw mul_add, }
... = n*n + 1*n + (n+1) : by {rw add_mul, rw mul_one (n+1),}...
 = n^2 + n + (n+1) : by {rw one_mul, rw ← pow_two,}
... = n^2 + (n + n+1) : by {rw add_assoc, rw ← add_assoc n n 1,}...
 = n^2 + 2*n + 1 : by { rw ← add_assoc, rw ← h, },
```

The same can be achieved without the `calc` mode, like this:

```
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  have h : n + n = 2*n, by { nth_rewrite 0 ← one_mul n,
  nth_rewrite 1 ← one_mul n, rw ← add_mul, },
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul,
  ← pow_two, add_assoc, ← add_assoc n n 1,
  ← add_assoc, ← h],
```

However, this is much less readable.

**Notes**
