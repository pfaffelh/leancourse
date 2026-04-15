import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Navigating Mathlib" =>
%%%
htmlSplit := .never
tag := "navigating-mathlib"
%%%

Mathlib is the community-maintained mathematical library for Lean 4. It contains hundreds of thousands of lines of formalized mathematics, covering algebra, analysis, topology, measure theory, number theory, combinatorics, and more. Learning to navigate Mathlib effectively is essential for writing proofs that build on existing results rather than reinventing the wheel.

# How Mathlib is organized
%%%
tag := "mathlib-organization"
%%%

The Mathlib source code lives in the `Mathlib/` directory and is organized by mathematical area. Here are some of the main subdirectories:

- `Mathlib.Algebra`: groups, rings, fields, modules, linear algebra
- `Mathlib.Analysis`: real analysis, normed spaces, calculus, measure theory
- `Mathlib.Topology`: topological spaces, continuous maps, filters
- `Mathlib.Order`: partial orders, lattices, well-founded relations
- `Mathlib.Data`: concrete data types (`Nat`, `Int`, `Rat`, `Real`, `Fin`, `List`, `Set`, ...)
- `Mathlib.Logic`: basic logic, classical reasoning, choice
- `Mathlib.SetTheory`: ordinals, cardinals
- `Mathlib.NumberTheory`: primes, arithmetic functions, quadratic reciprocity
- `Mathlib.MeasureTheory`: measures, integration, probability
- `Mathlib.CategoryTheory`: categories, functors, natural transformations
- `Mathlib.Combinatorics`: graph theory, combinatorial identities
- `Mathlib.Tactic`: custom tactics (`ring`, `norm_num`, `positivity`, ...)

Within each directory, files are further organized by specificity. For example, `Mathlib.Topology.Basic` contains the definition of topological spaces, while `Mathlib.Topology.MetricSpace.Basic` specializes to metric spaces.

# Searching for results: `exact?`, `apply?`, `rw?`
%%%
tag := "search-tactics"
%%%

Lean provides several tactics that search Mathlib for applicable lemmas. These are invaluable when you know what you need but do not know its name.

**`exact?`** searches for a single lemma (possibly with arguments) that closes the current goal. It will print a suggestion that you can copy into your proof.

```lean
-- Suppose your goal is `0 < 1`. Try:
example : (0 : ℝ) < 1 := by exact?
-- This might suggest: exact zero_lt_one
```

**`apply?`** searches for a lemma whose conclusion matches the goal, possibly leaving subgoals.

```lean
example : Continuous (fun x : ℝ ↦ x ^ 2 + 1) := by
  fun_prop
```

**`rw?`** searches for a lemma that can rewrite part of the goal.

These tactics can be slow because they search through a large library. Use them during exploration, but replace them with the concrete result they find for your final proof.

# Using `#check`, `#print`, and `#search`
%%%
tag := "check-print-search"
%%%

The commands `#check` and `#print` are fundamental for exploring the library interactively.

**`#check`** shows the type of a term or lemma:
```lean
#check Nat.add_comm     -- Nat.add_comm : ∀ (n m : ℕ), n + m = m + n
#check Set.mem_union     -- shows the type of the union membership lemma
```

**`#print`** shows the full definition of a term, including its proof:
```lean
#print Nat.add_comm      -- shows the actual proof term
#print Set               -- shows the definition of Set
```

If you are in VS Code, you can also use `F12` (Go to Definition) to jump to the source code of any definition or lemma. This is one of the fastest ways to understand how something is defined.

# External search tools: Moogle and Loogle
%%%
tag := "moogle-loogle"
%%%

When you cannot guess the name of a lemma, external search tools can help.

**Loogle** ([loogle.lean-lang.org](https://loogle.lean-lang.org)) lets you search Mathlib by type signature. For example:
- Searching for `List.map` shows all lemmas involving `List.map`
- Searching for `_ + _ = _ + _` finds commutativity and related lemmas
- Searching for `Continuous, Real.exp` finds lemmas about continuity of `exp`

**Moogle** ([moogle.ai](https://www.moogle.ai)) uses natural language search powered by AI. You can type queries like:
- "continuous function on compact set is bounded"
- "sum of convergent series"
- "every finite group is a quotient of a free group"

Both tools link directly to the Mathlib documentation and source code.

# The Mathlib documentation website
%%%
tag := "mathlib-docs"
%%%

The official Mathlib documentation is available at [the Mathlib docs site](https://leanprover-community.github.io/mathlib4_docs/). It provides:

- A searchable index of all declarations
- Rendered source code with clickable cross-references
- Type signatures and docstrings

When browsing the docs, pay attention to the namespace. For example, `Set.union_comm` lives in the `Set` namespace, so you can use it as `Set.union_comm` or open `Set` and use `union_comm`.

# Naming conventions in Mathlib
%%%
tag := "naming-conventions"
%%%

Mathlib follows systematic naming conventions that make lemma names predictable once you know the pattern. The general rule is:

**The conclusion is described first, then hypotheses are listed after `_of_`.**

For example:
- `continuous_add` : continuity of addition (goal: `Continuous ...`)
- `isOpen_of_isOpen_inter` : a set is open given that some intersection is open
- `le_of_lt` : `a ≤ b` follows from `a < b`

**Common abbreviations:**

:::table +header
* + Full name
  + Abbreviation
* + addition
  + `add`
* + multiplication
  + `mul`
* + subtraction
  + `sub`
* + division
  + `div`
* + negation
  + `neg`
* + inverse
  + `inv`
* + commutativity
  + `comm`
* + associativity
  + `assoc`
* + left
  + `left`
* + right
  + `right`
* + if and only if
  + `iff`
* + less than
  + `lt`
* + less or equal
  + `le`
* + greater than
  + `gt`
:::

**Common patterns:**
- `X_comm` : commutativity (`a * b = b * a`)
- `X_assoc` : associativity (`(a * b) * c = a * (b * c)`)
- `X_zero` / `zero_X` : interaction with zero (`a * 0 = 0`)
- `X_one` / `one_X` : interaction with one (`a * 1 = a`)
- `X_self` : applied to itself (`a - a = 0`)
- `X_left` / `X_right` : left/right variants

**Examples:**
```lean
#check mul_comm        -- a * b = b * a
#check add_assoc       -- (a + b) + c = a + (b + c)
#check mul_zero        -- a * 0 = 0
#check sub_self        -- a - a = 0
#check le_of_lt        -- a < b → a ≤ b
#check lt_of_le_of_lt  -- a ≤ b → b < c → a < c
```

Knowing these conventions lets you guess lemma names. For instance, if you need `a + b - b = a`, try `add_sub_cancel`. If you need the reverse direction of some `iff`, try appending `.mpr` or `.mp`.

# Reading Mathlib source code
%%%
tag := "reading-source"
%%%

When using a Mathlib lemma, it is often helpful to look at its source code to understand exactly what it says. Here are some tips:

1. **Use `F12` in VS Code** to jump to the definition.
2. **Read the type signature carefully.** Implicit arguments (in `{...}`) are inferred by Lean. Instance arguments (in `[...]`) are resolved by typeclass search.
3. **Look at the namespace.** If a lemma is in `namespace Foo`, it can be used on terms of type `Foo` with dot notation: `h.foo` instead of `Foo.foo h`.
4. **Check the imports.** The file header tells you what dependencies the file has.

For example, consider:
```lean
#check Set.Finite.union
-- Set.Finite.union : Set.Finite s → Set.Finite t → Set.Finite (s ∪ t)
```
This tells you: if `s` and `t` are finite sets, then `s ∪ t` is finite. Because it is in the `Set.Finite` namespace, you can also write `hs.union ht` if `hs : Set.Finite s` and `ht : Set.Finite t`.

# Understanding implicit arguments and typeclass resolution
%%%
tag := "implicit-typeclass"
%%%

Lean uses several kinds of argument brackets:

- `(x : α)` — explicit: you must provide this argument
- `{x : α}` — implicit: Lean infers this from context
- `[inst : SomeClass α]` — instance: resolved by typeclass search
- `⦃x : α⦄` — strict implicit: like `{}` but slightly different unification behavior

When applying a lemma, you usually only provide explicit arguments. If Lean cannot infer an implicit argument, you can provide it with `@`:
```lean
#check @add_comm ℕ _ 3 5  -- explicitly providing the type and the arguments
```

Typeclass resolution is the mechanism by which Lean automatically finds, for example, that `ℝ` is a `CommRing` or that `ℕ` has a `LinearOrder`. This works through a chain of instances registered with the `instance` command.

# Managing dependencies with `lake`
%%%
tag := "lake-dependencies"
%%%

Lean projects use `lake` (Lean's build system and package manager) to manage dependencies. If you need Mathlib in your project, your `lakefile.lean` will contain something like:

```
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "main"
```

Useful `lake` commands:
- `lake build` — build the project
- `lake update` — update dependencies
- `lake exe cache get` — download precompiled Mathlib `.olean` files (saves hours of compilation)

Always run `lake exe cache get` after updating Mathlib to avoid recompiling the entire library.

# Common patterns in Mathlib proofs
%%%
tag := "common-patterns"
%%%

Here are some patterns you will see frequently in Mathlib and should adopt:

**Pattern 1: Dot notation for structure projections and namespace lemmas.**
```lean
-- Instead of: And.left h
-- Write: h.left or h.1
example (h : P ∧ Q) : P := h.1
```

**Pattern 2: Anonymous constructor notation.**
```lean
-- Instead of: And.intro hP hQ
-- Write: ⟨hP, hQ⟩
example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
```

**Pattern 3: `calc` blocks for chains of equalities or inequalities.**
```lean
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  calc a ≤ b := h1
    _ ≤ c := h2
```

**Pattern 4: `suffices` to restructure a proof by stating an intermediate goal.**
```lean
example (n : ℕ) (h : n > 0) : n * n > 0 := by
  suffices n ≥ 1 by positivity
  omega
```

**Pattern 5: `have` for local forward reasoning, `obtain` for destructuring.**
```lean
example (h : ∃ n : ℕ, n > 5 ∧ n < 10) : ∃ n : ℕ, n > 3 := by
  obtain ⟨n, hn, _⟩ := h
  exact ⟨n, by omega⟩
```
