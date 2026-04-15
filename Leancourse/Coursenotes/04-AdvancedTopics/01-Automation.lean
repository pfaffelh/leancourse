import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Proof Automation" =>
%%%
htmlSplit := .never
tag := "proof-automation"
%%%

In this chapter, we discuss the many automation tactics available in Lean and Mathlib. Choosing the right tactic for the right situation is one of the most important skills in proof engineering. When used well, automation can turn a 20-line manual proof into a single line. When used poorly, it can cause slow compilation and obscure proof scripts.

# The `simp` tactic
%%%
tag := "simp-tactic"
%%%

The `simp` tactic is the workhorse of Lean automation. It applies a set of rewriting rules (called _simp lemmas_) repeatedly until no more rules apply. A lemma is marked as a simp lemma by adding the `@[simp]` attribute to it. Mathlib contains thousands of such lemmas.

Basic usage:
```lean
example (n : ℕ) : n + 0 = n := by simp
example (s : Set ℝ) : s ∩ Set.univ = s := by simp
example (n : ℕ) : n ∈ ({n} : Set ℕ) := by simp
```

The variant `simp only [...]` restricts simp to use only the listed lemmas. This is preferred in Mathlib contributions because it makes proofs more robust against changes in the simp set.
```lean
example (n : ℕ) : 0 + n + 0 = n := by simp only [Nat.add_zero, Nat.zero_add]
```

The variant `simp_all` applies `simp` to all hypotheses and the goal simultaneously. This is more powerful than calling `simp at *` because simplifications in one hypothesis can unlock simplifications elsewhere.
```lean
example (n m : ℕ) (h : n + 0 = m) : m = n := by simp_all
```

**Performance warning:** The global `simp` call (without `only`) searches through all simp lemmas, which can be slow. In library code, prefer `simp only`. In interactive exploration, plain `simp` is fine. You can use `simp?` to find out which lemmas simp uses, and then replace `simp` by `simp only [...]`.

# The `aesop` tactic
%%%
tag := "aesop-tactic"
%%%

The `aesop` tactic (Automated Extensible Search for Obvious Proofs) performs a best-first tree search using a configurable set of rules. It can apply lemmas, split goals, use `simp`, and more. It is particularly good for goals involving set membership, basic logic, and algebraic structures.

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by aesop
example (x : ℕ) (s t : Set ℕ) (hs : x ∈ s) : x ∈ s ∪ t := by aesop
```

You can register your own lemmas as aesop rules using the `@[aesop]` attribute:
```
@[aesop safe apply]   -- always try applying this lemma
@[aesop unsafe 50% apply]  -- try with 50% priority
```

# The `omega` tactic
%%%
tag := "omega-tactic"
%%%

The `omega` tactic decides linear arithmetic over `ℕ` and `ℤ`. It handles equalities, inequalities, divisibility, and modular arithmetic involving linear expressions. It cannot handle multiplication of variables (that is nonlinear).

```lean
example (n : ℕ) (h : n ≥ 3) : n ≥ 1 := by omega
example (a b : ℤ) (h1 : a + b ≤ 10) (h2 : a ≥ 3) : b ≤ 7 := by omega
example (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega
```

Note that `omega` works on `ℕ` and `ℤ` but not on `ℚ` or `ℝ`. For those, use `linarith`.

# The `decide` tactic
%%%
tag := "decide-tactic"
%%%

The `decide` tactic works on _decidable_ propositions -- propositions for which there is a computable decision procedure. This includes Boolean expressions, finite quantifiers, and computations on finite types.

```lean
example : 2 + 3 = 5 := by decide
example : ¬ (3 ∣ 7) := by decide
example : Nat.Prime 17 := by decide
```

**Warning:** `decide` runs a computation at kernel level. For large numbers, it can be extremely slow or time out. For example, `Nat.Prime 104729` will take very long. In such cases, use `norm_num` instead.

# The `norm_num` tactic
%%%
tag := "norm-num-tactic"
%%%

The `norm_num` tactic normalizes numerical expressions. It can prove equalities and inequalities involving concrete numbers, and it has extensions for primality, divisibility, and more.

```lean
example : (3 : ℝ) * 7 = 21 := by norm_num
example : (2 : ℚ) / 3 + 1 / 6 = 5 / 6 := by norm_num
example : Nat.Prime 104729 := by norm_num
example : ¬ Nat.Prime 4 := by norm_num
```

Unlike `decide`, `norm_num` uses verified computation and is much more efficient for numerical goals. It also works in types like `ℝ` and `ℚ` where `decide` does not apply.

# The `ring` tactic
%%%
tag := "ring-tactic"
%%%

The `ring` tactic proves equalities in commutative (semi)rings. It works with `ℕ`, `ℤ`, `ℚ`, `ℝ`, polynomial rings, and any type that has a `CommRing` or `CommSemiring` instance. It does not use hypotheses -- it only uses the ring axioms.

```lean
example (x y : ℝ) : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring
example (a b c : ℤ) : (a - b) * (a + b) = a^2 - b^2 := by ring
```

# `polyrith` and `linear_combination`
%%%
tag := "polyrith-linear-combination"
%%%

The `linear_combination` tactic proves an equality goal by providing a linear (or polynomial) combination of hypotheses. You supply the combination, and the tactic verifies it (usually via `ring`).

```lean
example (x y : ℝ) (h1 : x + y = 3) (h2 : x - y = 1) : x = 2 := by
  linear_combination (h1 + h2) / 2
```

The `polyrith` tactic tries to find such a combination automatically by calling an external oracle. It then suggests a `linear_combination` call. This requires network access and may not always succeed.

# The `linarith` tactic
%%%
tag := "linarith-tactic"
%%%

The `linarith` tactic proves linear arithmetic goals over ordered fields and rings. Unlike `omega`, it works over `ℝ` and `ℚ`, but it only handles linear expressions (no multiplication of variables).

```lean
example (x y : ℝ) (h1 : x ≤ 3) (h2 : y ≤ 5) : x + y ≤ 8 := by linarith
example (ε : ℝ) (hε : ε > 0) : ε / 2 > 0 := by linarith
```

For nonlinear goals, you can sometimes help `linarith` by providing auxiliary facts:
```lean
example (x : ℝ) (hx : x ≥ 0) : x^2 + x ≥ 0 := by
  nlinarith [sq_nonneg x]
```

The variant `nlinarith` can sometimes handle nonlinear goals by trying to multiply hypotheses together.

# The `positivity` tactic
%%%
tag := "positivity-tactic"
%%%

The `positivity` tactic proves goals of the form `0 ≤ e` or `0 < e`. It understands sums, products, powers, absolute values, norms, and more.

```lean
example (x : ℝ) : 0 ≤ x^2 + 1 := by positivity
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x * y + x := by positivity
```

# The `gcongr` tactic
%%%
tag := "gcongr-tactic"
%%%

The `gcongr` (generalized congruence) tactic proves inequalities by matching the structure of both sides and reducing to component-wise inequalities. It is very useful for goals like "if `a ≤ b` and `c ≤ d`, then `a + c ≤ b + d`".

```lean
example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  gcongr
```

# The `field_simp` tactic
%%%
tag := "field-simp-tactic"
%%%

The `field_simp` tactic clears denominators and simplifies expressions involving division in a field. It is typically followed by `ring` to finish the proof.

```lean
example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by field_simp
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp
  ring
```

Note that `field_simp` needs hypotheses that denominators are nonzero. It will look for these in the context.

# Choosing the right tactic
%%%
tag := "choosing-tactics"
%%%

Here is a rough guide for choosing the right automation tactic:

:::table +header
* + Goal type
  + Tactic
* + Numerical computation (`2 + 3 = 5`)
  + `norm_num` or `decide`
* + Linear arithmetic over `ℕ`, `ℤ`
  + `omega`
* + Linear arithmetic over `ℝ`, `ℚ`
  + `linarith`
* + Ring equality (`(x+y)^2 = ...`)
  + `ring`
* + Nonlinear inequality
  + `nlinarith` or `positivity`
* + Clearing denominators
  + `field_simp` then `ring`
* + Simplification with known lemmas
  + `simp` or `simp only [...]`
* + Set membership, basic logic
  + `aesop`
* + Monotonicity / congruence
  + `gcongr`
* + Decidable finite computation
  + `decide`
* + Using hypotheses as linear combination
  + `linear_combination`
:::

When in doubt, try `simp`, then `aesop`, then more specialized tactics. Use `simp?` to discover which simp lemmas apply, and then switch to `simp only` for a more maintainable proof.
