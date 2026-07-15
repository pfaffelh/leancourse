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

# Searching by type shape or in natural language
%%%
tag := "moogle-loogle"
%%%

When you cannot guess a lemma's name, several search *services* help.  (For the `#check`/`#print`/`inferInstance` commands that inspect a known definition, see {ref "checkprint"}[Exploring definitions] earlier in this appendix.)  All of the services below are available both as web pages and, more conveniently, as commands inside Lean via the `LeanSearchClient` package (a Mathlib dependency).

- *Loogle* ([loogle.lean-lang.org](https://loogle.lean-lang.org/)) searches by *type shape*.  You write a pattern (using `_` for holes) and Loogle returns every lemma whose statement unifies with it.  Inside Lean:
  ```
  #loogle (?a + ?b) * ?c = _
  ```
  It also accepts a comma-separated list of constants that must appear, e.g. `#loogle Real.exp, Real.log`, or a target conclusion `#loogle |- tsum _ = _`.
- *LeanSearch* ([leansearch.net](https://leansearch.net/)) searches by *natural language*.  From inside Lean:
  ```
  #leansearch "the derivative of a product of functions"
  ```
- *Moogle* ([moogle.ai](https://www.moogle.ai/)) is another natural-language search with a different ranking model:
  ```
  #moogle "bolzano-weierstrass"
  ```
  The two often surface different lemmas, so it is worth trying both.

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

# Getting more help: Zulip and AI assistants
%%%
tag := "help-services"
%%%

Beyond automated search, two more resources are worth knowing.

- *Zulip* (`leanprover.zulipchat.com`, the `#new members` and `#Mathlib4` streams) is the community chat.  For questions that no search answers, posting a minimal `example` together with the goal you are stuck on almost always gets a helpful reply within hours.
- *AI assistants* (ChatGPT, Claude, Gemini, Copilot, and the Lean-focused tools built on them) have become surprisingly effective at suggesting lemma names, explaining why a tactic fails, and translating informal arguments into Lean.  They are fallible -- they will cheerfully invent lemmas that do not exist or quote outdated Mathlib 3 syntax -- so use them critically: paste your goal state and the surrounding `example`, ask for a couple of candidate approaches, and *verify each suggestion in Lean* (via `exact?`, `#loogle`, or by compiling it).  Treat AI output like a confident but occasionally wrong colleague.

As a rule of thumb: try `exact?` / `apply?` first (they know your exact proof state), then `#loogle` (precise, fast), then `#leansearch` / `#moogle` or an AI assistant (when you do not know the vocabulary Mathlib uses), and finally the docs or Zulip for open-ended questions.
