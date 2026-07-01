import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Common Pitfalls" =>
%%%
htmlSplit := .never
tag := "common-pitfalls"
%%%

Even experienced Lean users regularly run into frustrating situations where a proof that "should" work simply does not. This section catalogs the most common pitfalls and gives practical advice for diagnosing and fixing them.

# Universe issues
%%%
tag := "universe-issues"
%%%

Every type in Lean lives in a universe. The hierarchy is:

- `Prop` (also called `Sort 0`) — the universe of propositions
- `Type 0` (also called `Type`) — the universe of "ordinary" types like `ℕ`, `ℝ`
- `Type 1`, `Type 2`, ... — higher universes

Most of the time, you do not need to think about universes. Problems arise when you write definitions that are universe-polymorphic and Lean cannot unify the universe levels.

**Symptom:** An error message mentioning `universe level` or `Sort u_1`.

**Fix:** Add explicit universe annotations. For example:
```
universe u v
variable {α : Type u} {β : Type v}
```

In practice, if you are working with concrete types (`ℕ`, `ℝ`, etc.) and Mathlib structures, universe issues are rare. They mostly appear when defining very general abstractions.

# Coercion headaches
%%%
tag := "coercion-headaches"
%%%

In mathematics, we freely treat a natural number as an integer, a rational as a real, and so on. In Lean, these are different types, and moving between them requires _coercions_, written `↑` (or `Nat.cast`, `Int.cast`, etc.).

Lean inserts coercions automatically in many cases, but sometimes the coercion chain gets confused, especially when mixing several numeric types.

**The standard coercion chain:**
```
ℕ → ℤ → ℚ → ℝ → ℂ
```

**Common problem:** Your goal looks right, but it involves a mismatch between, say, `(n : ℕ)` and `(↑n : ℤ)`, and tactics like `ring` or `linarith` fail because the types do not match.

**Tactics for coercion issues:**

- `push_cast` pushes coercions inward: it rewrites `↑(a + b)` to `↑a + ↑b`, `↑(a * b)` to `↑a * ↑b`, etc.
- `pull_cast` pulls coercions outward (the reverse direction).
- `norm_cast` normalizes cast expressions and can close goals involving casts.
- `exact_mod_cast` and `apply_mod_cast` are versions of `exact` and `apply` that handle casts automatically.

```lean
example (n m : ℕ) (h : (n : ℤ) + m = 10) : (↑(n + m) : ℤ) = 10 := by push_cast; exact h
example (n : ℕ) (h : n < 5) : (n : ℤ) < 5 := by exact_mod_cast h
```

**Tip:** When working with mixed types, try to state everything in the "largest" type from the start. For example, if you are working with both `ℕ` and `ℝ`, cast to `ℝ` as early as possible and use `push_cast` and `norm_cast` to manage the casts.

# Definitional equality surprises
%%%
tag := "definitional-equality"
%%%

In Lean, some equalities hold _by definition_ (definitional equality), while others require a proof (propositional equality). The distinction can be surprising.

**When `rfl` works:** `rfl` closes a goal `a = b` when `a` and `b` are definitionally equal. For example:
```lean
example : 2 + 3 = 5 := by rfl        -- Lean computes this
example (n : ℕ) : n + 0 = n := by rfl -- by definition of Nat.add
```

**When `rfl` fails:**
```
-- This does NOT work:
-- example (n : ℕ) : 0 + n = n := by rfl
-- Because Nat.add is defined by recursion on the first argument,
-- 0 + n is not definitionally equal to n.
```

The `change` tactic lets you replace the goal with a definitionally equal one:
```lean
example (n : ℕ) : Nat.succ n = n + 1 := by
  change n + 1 = n + 1
  rfl
```

The `show` tactic does the same thing but is more readable when used at the start of a proof:
```lean
example (n : ℕ) : Nat.succ n = n + 1 := by
  show n + 1 = n + 1
  rfl
```

**Tip:** If a tactic unexpectedly fails, try using `change` to rewrite the goal into an equivalent form. Sometimes the goal looks right in the Infoview but contains hidden definitional mismatches.

# Typeclass diamonds
%%%
tag := "typeclass-diamonds"
%%%

A _typeclass diamond_ occurs when there are two different paths to derive the same typeclass instance for a type, and these paths produce instances that are not definitionally equal.

For example, suppose `ℤ` gets a `Monoid` instance both directly and through `CommRing → Ring → Monoid`. If these produce different `Monoid` structures, Lean may complain about type mismatches.

**Symptom:** An error like "type mismatch" where the types look identical in the Infoview, or `rfl` fails on something that "obviously" should work.

**How Mathlib avoids diamonds:** Mathlib carefully designs its typeclass hierarchy so that diamonds are definitionally equal. This is one reason why the hierarchy is so carefully structured with `extends` and `forgetful inheritance`. When defining your own instances, follow the same patterns.

**Practical advice:** If you encounter a diamond, check whether you have defined a typeclass instance that conflicts with one from Mathlib. The fix is usually to ensure your instance agrees definitionally with the existing one, or to remove it and use the one from Mathlib.

# Simp loop issues
%%%
tag := "simp-loops"
%%%

A _simp loop_ occurs when two simp lemmas rewrite back and forth indefinitely. For example, if both `a = b` and `b = a` were simp lemmas, `simp` would loop forever.

**Symptom:** `simp` takes very long or times out.

**How to diagnose:** Use `set_option trace.Meta.Tactic.simp true in` before your tactic call to see which lemmas simp is applying. If you see the same lemma applied repeatedly, you have a loop.

```
-- Diagnose simp behavior:
-- set_option trace.Meta.Tactic.simp true in
-- example : ... := by simp
```

**Prevention:** When marking a lemma `@[simp]`, ensure it rewrites toward a "simpler" or "canonical" form. The left-hand side should be more complex than the right-hand side. Never add both `a = b` and `b = a` as simp lemmas.

# Dependent type complications
%%%
tag := "dependent-type-hell"
%%%

Lean's type system is very expressive, but dependent types can cause headaches when types that "should" be equal are not definitionally equal.

**The classic problem:** You have `h : a = b` and want to rewrite in a type that depends on `a`. But after rewriting, the type of some term changes, and Lean complains about a type mismatch.

**Tools for dealing with this:**

- `subst h` : if `h : a = b` and `a` is a variable, this substitutes `b` for `a` everywhere.
- `congr` / `congr 1` : tries to reduce an equality goal to equalities of the components.
- `convert e` : like `exact e` but allows the types to differ, generating subgoals for the mismatches.
- `Eq.mpr` and `cast` : explicitly transport a term along an equality of types (rarely needed in tactic mode).

**`HEq` (Heterogeneous equality):** Sometimes two terms have different types but you want to say they are "equal." This is what `HEq` provides. It should be avoided when possible, as it is harder to work with than `Eq`.

**Practical advice:** If you get stuck with dependent type issues, try:
1. Rewrite earlier so that types match before you build dependent terms.
2. Use `convert` instead of `exact` when the goal is almost right.
3. Use `simp` or `congr` to reduce the problem.

# Timeout issues
%%%
tag := "timeout-issues"
%%%

Lean has a computational budget measured in _heartbeats_. When a tactic or elaboration exceeds this budget, you get a timeout error.

**Common causes:**
- `simp` with too many lemmas or a simp loop
- `decide` on a large computation
- Typeclass search going through too many instances
- Deeply nested term elaboration

**How to increase the budget (for debugging only):**
```
set_option maxHeartbeats 400000 in
example : ... := by sorry
```

The default is 200000. Increasing it is a band-aid, not a solution. Find the root cause.

**How to diagnose:**
```
-- See what simp is doing:
set_option trace.Meta.Tactic.simp true in

-- See typeclass search:
set_option trace.Meta.synthInstance true in

-- Profile a tactic:
set_option profiler true in
```

# Practical debugging tips
%%%
tag := "debugging-tips"
%%%

Here is a collection of debugging techniques that every Lean user should know.

**1. Use the Infoview.** Always keep the Lean Infoview panel open in VS Code. Place your cursor after each tactic to see the current goal state. This is the single most important debugging tool.

**2. Type annotations.** When Lean gives a confusing error, add explicit type annotations to help it (and yourself) understand what is going on:
```
-- Instead of:
-- let x := f a
-- Write:
-- let x : ℝ := f a
```

**3. `#check` everything.** If you are not sure what type a lemma expects, `#check` it:
```lean
#check mul_le_mul_of_nonneg_left
-- ∀ {α : Type u_1} [inst : OrderedSemiring α] {a b c : α},
--   a ≤ b → 0 ≤ c → c * a ≤ c * b
```

**4. Binary search for errors.** If a long proof breaks, comment out the bottom half and see if the top half is OK. Then narrow down. You can also replace a tactic with `sorry` to skip it temporarily.

**5. `trace` options.** Lean has many `trace` options for understanding what is happening:
```lean
set_option trace.Meta.Tactic.simp true       -- trace simp
set_option trace.Meta.synthInstance true      -- trace typeclass search
set_option trace.Elab.definition true         -- trace definition elaboration
```

**6. Minimize the example.** If you are stuck, try to create a minimal example that reproduces the issue. Remove all unnecessary hypotheses, imports, and context. This often reveals the problem.

**7. Check Zulip.** The [Lean Zulip chat](https://leanprover.zulipchat.com/) is an active community where you can ask questions. Search the archive first -- your question has likely been asked before.

**8. Use `conv` for surgical rewriting.** When `rw` rewrites in the wrong place, use `conv` to target a specific subexpression:
```lean
example (a b : ℝ) : a + b + a = a + a + b := by
  conv_lhs => rw [add_comm a b]
  ring
```

**9. The `?` suffix.** Many tactics have a `?` variant that suggests a more explicit call:
- `simp?` suggests `simp only [...]`
- `exact?` suggests the exact term to use
- `apply?` suggests which lemma to apply
- `rw?` suggests which lemma to rewrite with

Use the `?` variant during exploration, then copy the suggestion into your final proof for robustness and speed.
