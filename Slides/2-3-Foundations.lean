import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Foundations: universes, axioms, well-foundedness"
of part 2 (Mathematics). It follows the chapter section by section:
`propext` and Diaconescu, what the kernel bakes in, `partial def`,
well-foundedness and paradoxes, constructive vs classical logic, ZFC,
other type theories. Material lectured in part 1 (chapters 1.3 and
1.5) is only recalled.
-/

namespace SlidesFoundations

#doc (Slides) "Foundations: universes, axioms, well-foundedness" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .small table, .reveal section table.small { font-size: 0.5em; }
.reveal section .small table code, .reveal section table.small code { font-size: 0.95em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.6em; }
```

# Foundations: universes, axioms, well-foundedness

Mathematics — chapter 3

:::class "key"
Lean's mathematics rests on a kernel with a few rules, three axioms, and two mechanisms against vicious circles.
:::

# Recall from chapter 1.5

- Lean's rules form a variant of the _Calculus of Inductive Constructions_ (CIC): dependent functions (Coquand, Huet 1988), inductive types (Coquand, Paulin-Mohring 1990), universes.
- `Prop` is proof irrelevant and impredicative; it eliminates into `Type` only for subsingletons (`False`, `Eq`, `And`, `Acc`), never for `∨`, `∃`.
- Three axioms: `propext`, `Quot.sound`, `Classical.choice`. `funext` is a theorem from `Quot.sound` (chapter 1.4).

```lean -panel -stretch
#print axioms Classical.em
-- [propext, Classical.choice, Quot.sound]
```

:::class "key"
This chapter: what the axioms give, what the kernel adds silently, and what rules out vicious circles.
:::

# `propext`

```lean -panel -stretch
#check @propext  -- (a ↔ b) → a = b

example (P : Prop) : (P ∧ True) = P := by
  ext
  simp
```

- A set `s : Set α` is a predicate `α → Prop`.
- Same members: `propext` makes the predicates equal at every point, `funext` makes them equal.

:::class "key"
`propext` and `funext` together make set equality extensional.
:::

# Diaconescu's theorem

Fix `p : Prop`. Define two predicates on `Prop`:

- `U x := (x = True) ∨ p` and `V x := (x = False) ∨ p`.
- `True` satisfies `U`, `False` satisfies `V`. Choice gives `u`, `v` with `u = True ∨ p` and `v = False ∨ p`.
- If one of them is the right branch: `p`.
- Otherwise `u = True`, `v = False`, so `u ≠ v`. If `p` held, `U = V` (`propext`, `funext`). `u` and `v` are `Classical.choose` applied to equal arguments, so `u = v`. Hence `¬p`.

Concluding `¬p` from a contradiction under `p` is the definition of `¬`, not `by_contra`.

:::class "key"
The only non-constructive step is choice: it turns the proposition `p` into data, `True` or `False`, that can be compared.
:::

# Built in, not declared

::::class "small"
:::table +colHeaders +rowSeps
*
  * principle
  * what it gives
  * where
*
  * proof irrelevance
  * any two proofs of `P : Prop` are equal
  * 1.5
*
  * η for functions and structures
  * `fun x => f x ≡ f`, `⟨s.1, s.2⟩ ≡ s`
  * 1.5
*
  * reduction (β, δ, ζ, ι)
  * `2 + 2 = 4` by `rfl`
  * 1.1
*
  * quotient computation
  * `Quot.lift f h (Quot.mk r a) ≡ f a`
  * 1.4
*
  * impredicative `Prop`, universes
  * `∀ p : Prop, p → p` is a `Prop`; no `Type : Type`
  * 1.5, 1.2
*
  * strict positivity
  * no type `Bad`
  * 1.3
*
  * restricted elimination
  * no data from `∨`, `∃`; exception: subsingletons (`False`, `Eq`, `And`, `Acc`)
  * 1.5
:::
::::

```lean -panel -stretch
theorem pf_irrel (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
#print axioms pf_irrel   -- does not depend on any axioms
```

:::class "key"
`#print axioms` reports only the declared `axiom` constants. None of these can be switched off.
:::

# Literal arithmetic

- The kernel stores `Nat` literals in binary and computes `+`, `*`, `-`, `/`, `%`, `^`, `gcd`, `Nat.beq`, `Nat.ble` with bignum operations, not as towers of `succ`.
- This is why `decide` handles large numbers.
- `String` literals are kernel primitives too. `Int` has no such support; it reduces through its `Nat` components.

:::class "key"
An implementation choice, not a rule of the type theory, and part of what one trusts.
:::

# What `#print axioms` does not see

- The trusted base of a Lean proof is the whole kernel: the CIC with proof irrelevance, η, quotient reduction, native computation and the universe rules.
- Proof irrelevance makes all proofs of `a = b` equal. This is _uniqueness of identity proofs_ (axiom K).
- Univalence (equivalent types are equal, see "Other type theories") needs distinct proofs of equality, so it contradicts this.

:::class "key"
Believing a Lean theorem means believing the kernel, not only three axioms.
:::

# `partial def`

A non-terminating recursion would prove `False` (chapter 1.3). But Lean is also a programming language, and programs may loop:

```lean -panel -stretch
partial def spin (_ : Unit) : Nat := spin ()
```

A `partial` definition is opaque to the logic: it has no defining equation, so no proof can unfold it. One more requirement:

```lean +error -panel -stretch
partial def spinFalse (_ : Unit) : False := spinFalse ()
```

`could not prove that the type ∀ (x : Unit), False is nonempty`.

:::class "key"
`partial` is accepted only if the result type is already known to be inhabited.
:::

# The first inhabitant

:::table +colHeaders +rowSeps
*
  * way to a term of `False`
  * blocked by
*
  * `def c : False := c`
  * recursion only through recursors or `WellFounded.fix`
*
  * `Bad.mk : (Bad → False) → Bad`
  * strict positivity
*
  * `partial def c : False`
  * the result type must be nonempty
:::

:::class "key"
Loops are not forbidden. A loop may only return a value of a type that is already known to be inhabited.
:::

# Well-founded relations

`r : α → α → Prop` is _well-founded_ if there is no infinite descending chain `… r a₂ r a₁ r a₀`. Then one may recurse and induct along `r`: to prove `P x`, assume `P y` for all `y` with `r y x`.

:::table +colHeaders +rowSeps
*
  * relation
  * well-founded
  * reason
*
  * `<` on `ℕ`
  * yes
  * every chain stops at `0`
*
  * `>` on `ℕ`
  * no
  * `0 < 1 < 2 < …`
*
  * `<` on `ℤ`
  * no
  * `0 > -1 > -2 > …`
*
  * `<` on `ℚ`, `ℝ`
  * no
  * `1 > 1/2 > 1/4 > …`
:::

:::class "key"
Well-founded means: recursion and induction along `r` are valid.
:::

# Accessibility

```
inductive Acc (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → Acc r y) : Acc r x
-- WellFounded r: every element is accessible
```

`x` is accessible once all its predecessors are. `Acc` is inductive: a proof of `Acc r x` is a finite tree, and an infinite descending chain would need an infinitely deep one.

:::class "key"
`termination_by` and `decreasing_by` work through `WellFounded.fix`.
:::

# Why `Nat` is well-founded

```lean -panel -stretch
#check (Nat.lt_wfRel.wf : WellFounded Nat.lt)
```

`Acc (· < ·) n`, by induction on `n`:

- `0`: vacuously, there is no `m < 0`.
- `n + 1`: a predecessor `m < n + 1` is `n` (induction hypothesis) or `m < n`, and then `Acc n` gives `Acc m` (`Acc.inv`).

Every inductive type has `sizeOf` (number of constructors used); `sizeOfWFRel` compares by it. With `termination_by` (1.3) you only show that the measure decreases.

:::class "key"
A natural number is a finite tower of `succ`: nothing infinite to descend through.
:::

# Why `s ∈ s` is impossible

```lean -panel -stretch
#check @Set.instMembership   -- Membership α (Set α)

def mySet : Set ℕ := {0}
-- #check_failure succeeds only if the term
-- fails to elaborate
#check_failure (mySet ∈ mySet)
```

`x ∈ s` needs `x : α` and `s : Set α`. For `s ∈ s`, the same `s` would need both types: `α = Set α = (α → Prop)`. No type satisfies this. In ZFC, `s ∈ s` is a formula, excluded by the axiom of foundation.

:::class "key"
In Lean, `s ∈ s` is not false but ill-formed. Russell's `{x | x ∉ x}` cannot be written.
:::

# Cantor and Russell

```lean -panel -stretch
#check @Function.cantor_surjective
-- (f : α → Set α) : ¬Function.Surjective f
```

- No type `α` equals `α → Prop`: there is no surjection `α → Set α`.
- Diagonal: `{x | x ∉ f x}` is no `f a`, else `a ∈ f a ↔ a ∉ f a`.
- This set is Russell's `{x | x ∉ x}`. Cantor concludes that no surjection exists where naive set theory finds a contradiction. The same diagonal makes a negative occurrence fatal (chapter 1.3).
- One level up, `Type : Type` gives Girard's paradox; the universe hierarchy rules it out (Project 4).

# Two mechanisms against vicious circles

:::table +colHeaders +rowSeps
*
  * ruled out
  * mechanism
*
  * infinite descent, non-terminating recursion
  * `Acc`, `WellFounded`: an inductive predicate within a type
*
  * `s ∈ s`, `{x | x ∉ x}`, `Type : Type`
  * typing and the universe hierarchy
:::

:::class "key"
The first is a theorem-level tool used for recursion. The second is part of the rules for well-formed terms.
:::

# Classical reasoning in use

```lean -panel -stretch
example (P : Prop) : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  exact hnnP hnP
```

- Constructive: a proof of `∃ x, P x` contains a witness, a proof of `P ∨ Q` names a side.
- Needs choice: `by_cases`, `by_contra` on any proposition; an element of a nonempty type without a witness; a `Decidable` instance without an algorithm (`classical`, chapter 1.6).
- Does not: decidable propositions, defining functions by an algorithm, direct proofs and induction.

:::class "key"
Mathlib uses classical logic freely: its subject is mathematical truth, not computation.
:::

# Lean and ZFC

::::class "small"
:::table +colHeaders +rowSeps
*
  * feature
  * ZFC
  * Lean
*
  * basic notion
  * sets and membership `∈`
  * types and terms `:`
*
  * `3 ∈ 7`
  * well-formed; true for von Neumann numerals (`7 = {0,…,6}`)
  * type error
*
  * functions
  * sets of ordered pairs
  * primitive
*
  * equality
  * between any two sets
  * only within a type
*
  * proofs
  * not objects of the theory
  * terms
*
  * computation
  * not built in
  * terms reduce
*
  * type checking
  * does not apply
  * decidable in practice
:::
::::

Werner 1997: ZFC embeds into the CIC, and a dialect of the CIC embeds into ZFC with a hierarchy of inaccessible cardinals. This is not a statement about the type theory Lean implements.

# The ZFC axioms in Lean

::::class "small"
:::table +colHeaders +rowSeps
*
  * ZFC
  * in Lean
  * status
*
  * extensionality
  * `funext`, `propext`, `Set.ext`
  * theorem, axiom, theorem
*
  * empty set
  * `Empty`, `(∅ : Set α)`
  * inductive type, definition
*
  * pairing
  * `{a, b}`
  * definition
*
  * union
  * `⋃₀`, `α ⊕ β`, `Σ`
  * definition, inductive types
*
  * power set
  * `Set α := α → Prop`
  * function type
*
  * infinity
  * `ℕ`
  * inductive type
*
  * separation
  * `{x : α // p x}`, `{x | p x}`
  * definitions
*
  * replacement
  * the image `f '' s`
  * definition (the strength of replacement comes from the universes)
*
  * foundation
  * none: `x ∈ x` is not well-typed
  * not needed
*
  * choice
  * `Classical.choice`
  * axiom
:::
::::

:::class "key"
Of the ten ZFC axioms, two remain axioms. The rest become rules, inductive types or definitions.
:::

# Other type theories

:::table +colHeaders +rowSeps
*
  * system
  * since
  * in short
*
  * simply typed λ-calculus
  * Church 1940
  * no dependent types
*
  * System F
  * Girard, Reynolds, 1970s
  * polymorphism; basis of Haskell, OCaml
*
  * Martin-Löf type theory
  * 1971
  * dependent types; Agda
*
  * CIC
  * 1988, 1990
  * Lean, Rocq
*
  * homotopy type theory
  * 2013
  * univalence: equivalent types are equal
*
  * cubical type theory
  * 2015
  * univalence that computes
:::

:::class "key"
Lean works in the CIC with proof irrelevance, quotients and choice. Univalence contradicts its proof irrelevance.
:::

# Summary

- `propext` and `funext` make set equality extensional.
- Diaconescu: choice gives excluded middle, so `Classical.em` is a theorem.
- The kernel also bakes in proof irrelevance, η, quotient computation and positivity; `#print axioms` does not show them.
- Recursors, strict positivity, `partial` only into nonempty types: a loop may only return a value of a type already known to be inhabited.
- `Acc` rules out infinite descent; typing rules out `s ∈ s`.
- The core is constructive, choice makes it classical. ZFC axioms become rules, types and definitions.
