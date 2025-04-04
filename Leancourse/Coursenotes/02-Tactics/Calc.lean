import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "`calc`" =>
%%%
tag := "calc"
%%%

**Summary:** As the word suggests, `calc` is about concrete calculations. This is not a tactic, but a `lean` mode. This means that you can enter this mode (with the word `calc`) and enter calculation steps and proofs that each individual calculation step is correct.

**Examples**

Here is a proof of the first binomial formula that only comes about by rewriting of calculating properties from the `mathlib`.

```lean
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 := by
  have h : n + n = 2 * n := by
    nth_rewrite 1 [← one_mul n]
    nth_rewrite 2 [← one_mul n]
    rw [← add_mul]
    rfl
  calc (n+1)^2 = (n+1) * (n+1) := by rw [pow_two]
  _ = (n + 1) * n + (n + 1) * 1 := by rw [mul_add]
  _ = n * n + 1 * n + (n + 1) := by
    rw [add_mul, mul_one (n + 1)]
  _ = n^2 + n + (n + 1) := by rw [one_mul, ← pow_two]
  _ = n^2 + (n + n + 1) := by
    rw [add_assoc, ← add_assoc n n 1]
  _ = n^2 + 2*n + 1 := by rw [← add_assoc, ← h]
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


**Remarks**

* The exact notation is important in `calc` mode.
* The `calc` mode not only works for equalities, but also for inequalities, subset-relations etc.
* The example above can be solved easily using `linarith` or `ring`.
* In order to generate a proof in `calc` mode, one can do it as follows (see the example below):
  + give the exact calculation steps without proof (using `by sorry`)
  + fill in the proofs which are left over.

::::keepEnv
:::example " "
Here is how to start the proof of the binomial formula. First, leave out all proofs:
```lean
example (n : ℕ) : n + n = 2*n := by
  calc n + n = 1 * n + 1 * n := by sorry
  _ = (1 + 1) * n := by sorry
  _ = 2 * n := by sorry
```
Then, fill in the details
```lean
example (n : ℕ) : n + n = 2*n := by
  calc n + n = 1 * n + 1 * n := by rw [one_mul]
  _ = (1 + 1) * n := by rw [add_mul]
  _ = 2 * n := by rfl
```

:::
::::
