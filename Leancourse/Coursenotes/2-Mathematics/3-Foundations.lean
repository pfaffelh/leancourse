import VersoManual
import Manual.Meta
import Leancourse.Markup
import Leancourse.Coursenotes.References
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Leancourse.Refs
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Foundations: universes, axioms, well-foundedness" =>
%%%
htmlSplit := .never
tag := "universes-axioms"
%%%

This chapter is about what Lean's mathematics rests on beyond the rules of chapter {ref "rules"}[1.5]: what `propext` is used for and how the excluded middle follows from the three axioms, what the kernel builds in without declaring it, `partial def`, well-founded relations and the two mechanisms that rule out vicious circles, and classical against constructive logic. The last sections compare Lean with ZFC and with other type theories. The rules themselves, the three axioms and proof irrelevance are in chapter {ref "rules"}[1.5]; recursion, the recursor and strict positivity in chapter {ref "pattern-matching-and-recursion"}[1.3]; `Quot.sound` and the proof of `funext` from it in chapter {ref "quotient-types"}[1.4].

The [slides](slides/2-3-foundations/) for this chapter follow it section by section.

# The axioms of Lean
%%%
tag := "lean-axioms"
%%%

Lean has three axioms, `propext`, `Quot.sound` and `Classical.choice` ({ref "rules-axioms"}[Axioms] in chapter 1.5). `propext` says that logically equivalent propositions are equal:

```lean
#check @propext
-- propext : ∀ {a b : Prop}, (a ↔ b) → a = b

-- Example: P ∧ True is the same proposition as P
example (P : Prop) : (P ∧ True) = P := by
  ext
  simp
```

Together with `funext` it makes {ref "foundations-set-eq"}[set equality] extensional. A set `s : Set α` is a predicate `α → Prop`. If two sets have the same members, `propext` makes the two predicates equal at every point, and `funext` makes them equal.

## Excluded middle is a theorem (Diaconescu)
%%%
number := false
tag := "em-derived"
%%%

The law of excluded middle `∀ p, p ∨ ¬p` is *not* an axiom. It follows from the three axioms by *Diaconescu's theorem*: the axiom of choice implies excluded middle. `#print axioms` shows the dependency:

```lean
#check @Classical.em
-- Classical.em : ∀ (p : Prop), p ∨ ¬p

#print axioms Classical.em
-- 'Classical.em' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

The argument is worth seeing, because it pinpoints exactly where non-constructivity enters. Fix a proposition `p` and form two predicates on `Prop`:

- `U x := (x = True) ∨ p`
- `V x := (x = False) ∨ p`

Both are nonempty — `True` satisfies `U` and `False` satisfies `V` — so `Classical.choice` hands us concrete witnesses `u v : Prop` together with proofs of `u = True ∨ p` and `v = False ∨ p`. Now case-split on those two disjunctions:

- If either disjunction takes its *right* branch, we have a proof of `p` outright — the left side of `p ∨ ¬p`.
- Otherwise `u = True` and `v = False`, so `u ≠ v`. But were `p` true, then `U x` and `V x` would both be equivalent to `True`, so `propext` makes them equal for every `x` and `funext` gives `U = V`; the chosen witnesses would then coincide, `u = v` — a contradiction. The argument thus uses all three axioms: `Classical.choice`, `propext`, and `Quot.sound` through `funext`. Hence `¬p`, the right side.

Either way we obtain `p ∨ ¬p`. The decisive step is that `Classical.choice` turns the *propositional* assumption `p` into *comparable data*, the booleans `True` and `False`, which is the move a constructive system refuses. Mathlib packages the result as `Classical.em`, used in practice through `by_contra` or `by_cases`.

The step "assume `p`, derive a contradiction, conclude `¬p`" does not itself use excluded middle, so the argument is not circular. Proving `¬p` by assuming `p` and reaching a contradiction is *negation introduction* — it is simply the definition of `¬p` as `p → False`, and it is constructively valid. The *classical* principle is the opposite direction: concluding a positive `p` from `¬¬p` (that is `by_contra`), which we never invoke here. Likewise, the case splits above *eliminate* disjunctions we already hold (from the choice specification); they do not conjure `p ∨ ¬p` out of nothing — that disjunction is our *conclusion*, assembled constructively from the cases. The one and only non-constructive ingredient is `Classical.choice`, and using it is not the same as assuming the `p ∨ ¬p` we are proving.

# Declared axioms vs. what the kernel bakes in
%%%
tag := "baked-in"
%%%

`#print axioms` reports exactly the *declared* axioms, the `axiom` constants. The rules of the kernel build in further principles that leave no trace there and cannot be switched off. All of them appeared in Part 1:

:::table +header
* + Built-in principle
  + What it gives you
  + Where
* + Proof irrelevance
  + any two proofs of the same proposition are equal
  + {ref "type-rules"}[1.5], conversion
* + η for functions and structures
  + `f ≡ fun x => f x`, `s ≡ ⟨s.1, s.2⟩`
  + {ref "type-rules"}[1.5], conversion
* + Computation (β, δ, ζ, ι)
  + `2 + 2 = 4` by `rfl`
  + {ref "reduction-rules"}[1.1]
* + Quotient computation
  + `Quot.lift f h (Quot.mk r a) ≡ f a`
  + {ref "quotient-types"}[1.4]
* + Impredicative `Prop`
  + `∀ p : Prop, p → p` is a `Prop`
  + {ref "prop-special"}[1.5]
* + Universe hierarchy
  + never `Type : Type`
  + {ref "type-universes"}[1.2]
* + Strict positivity
  + no `inductive Bad | mk : (Bad → False) → Bad`
  + {ref "positivity-rule"}[1.3]
* + Subsingleton elimination
  + no data from proofs of `∨` or `∃`
  + {ref "prop-special"}[1.5]
:::

None of them costs an axiom:

```lean
theorem pf_irrel (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

#print axioms pf_irrel
-- 'pf_irrel' does not depend on any axioms
```

One more is not a rule of the type theory but an implementation choice: the kernel represents `Nat` literals as binary numbers and computes `+`, `*`, `-`, `/`, `%`, `gcd`, `==` and `≤` on them with bignum operations rather than unary `succ` — the reason `decide` handles large numbers. `String` literals are kernel primitives as well. `Int` has no such support; it reduces through its `Nat` components.

Two consequences. First, the *trusted base* of a Lean proof is not "three axioms" but the whole kernel, with all of the above. Believing a Lean theorem means believing all of that. Second, proof irrelevance for `Prop` makes all proofs of `a = b` equal, which is *uniqueness of identity proofs* (axiom K). This makes Lean *incompatible* with the univalence axiom of {ref "other-type-theories"}[Homotopy Type Theory], where distinct equality proofs must be allowed to differ.

# `partial def`: loops outside the logic
%%%
tag := "partial-def"
%%%

Recursion that does not terminate would give a proof of `False`, which is why Lean demands termination ({ref "recursion"}[chapter 1.3]). Lean is also a programming language, though, and programs may loop. `partial def` permits it:

```lean
partial def spin (_ : Unit) : Nat := spin ()
```

A `partial` definition is opaque to the logic. It has no defining equation there, so no proof can unfold it. And it carries one more requirement:

```lean +error
partial def spinFalse (_ : Unit) : False := spinFalse ()
```

`could not prove that the type ∀ (x : Unit), False is nonempty`. A `partial` definition is only accepted when its result type is *already known to be inhabited*, so it can never be the first inhabitant of anything.

That is the rule underneath termination, strict positivity and `partial def`. Loops are not forbidden. What is forbidden is producing an inhabitant of a type that is not already known to have one.

# Well-foundedness and paradoxes
%%%
tag := "logic-wf"
%%%

A recurring worry in the foundations of mathematics is *vicious
circularity*: infinite descending chains that make recursion
meaningless, or self-referential sets like Russell's `{x | x ∉ x}`.
Lean rules these out, but — importantly — by *two different
mechanisms* that are worth keeping apart.  This section looks at
both.

## Accessibility and well-founded relations
%%%
number := false
tag := "wf-acc"
%%%

The first mechanism lives *inside* a type and governs recursion.  A
relation `r : α → α → Prop` is *well-founded* when there are no
infinite descending chains `… r a₂ r a₁ r a₀` — following
`r`-predecessors downward, you always hit bottom after finitely many
steps.

Why care?  Well-foundedness is *exactly* the condition that makes
recursion and induction legitimate.  If `f x` is defined in terms of
`f y` for `r`-smaller `y`, the computation terminates *only* because
you cannot descend forever; and the induction principle "to prove
`P x`, assume `P y` for every `y` with `r y x`" is valid *precisely*
when `r` is well-founded.  In one phrase: well-founded means "you may
recurse and induct along `r`".

Lean expresses this through the inductive predicate `Acc`
("accessible"):

```
inductive Acc (r : α → α → Prop) : α → Prop where
  | intro (x : α) (h : ∀ y, r y x → Acc r y) : Acc r x
```

Read the constructor as: `x` is *accessible* once *all* of its
`r`-predecessors `y` (those with `r y x`) are themselves accessible.
A relation is well-founded when every element is accessible:

```lean
#check @Acc
-- Acc : {α : Sort u} → (α → α → Prop) → α → Prop
#check @WellFounded
-- WellFounded : {α : Sort u} → (α → α → Prop) → Prop
#check @WellFounded.fix
```

`Acc` is an *inductive* type — the
*least* fixed point, so it is finitely generated.  The constructor
for `Acc r x` demands accessibility of *every* predecessor, so the
only way to build the proof is for every downward branch to bottom
out after finitely many steps: a proof of `Acc r x` is a *finite*
tree.  An infinite descending chain would force an infinitely deep
proof, which no inductive type admits — so, where every element is
accessible, no such chain exists.  (Were `Acc` instead *coinductive*,
the *greatest* fixed point, infinite proofs would be allowed and
every element would count as accessible; the definition would be
vacuous.  The induction is the whole point.)  This is exactly what
powers *well-founded recursion* (`WellFounded.fix`): you may recurse
along `r` because every descent terminates, and `termination_by` /
`decreasing_by` use precisely this.

It helps to see what *fails*.  These relations are *not*
well-founded:

- `<` on the integers `ℤ`: the chain `0 > -1 > -2 > …` descends
  forever, with no bottom.
- `<` on `ℚ` or `ℝ`: `1 > ½ > ¼ > …` never terminates.
- *greater-than* `>` on `ℕ`: the chain `0 < 1 < 2 < …` is an infinite
  `>`-descending chain.

For none of these can Lean offer well-founded recursion — there is no
terminating direction to recurse in.  The contrast between `<` and `>`
on `ℕ` is the lesson: less-than bottoms out at `0`, greater-than runs
off to infinity.

Concretely, this abstract picture is realized in Lean in two ways.
Each `inductive` type comes with an auto-generated *recursor*
(`Nat.rec`, `List.rec`, ...) that *is* its structural induction and
recursion principle — well-foundedness for that type, guaranteed by
the kernel.  And for a *uniform* supply of well-founded relations,
every inductive type carries a `SizeOf` instance, which `sizeOfWFRel`
turns into a `WellFoundedRelation` whose well-foundedness is pulled
back from `<` on `Nat` through `InvImage.wf`.  So "inductive, hence
finite trees, hence well-founded" becomes, in practice, the single
fact `Nat.lt_wfRel.wf` transported along `sizeOf`.

## Why `Nat` is well-founded
%%%
number := false
tag := "wf-nat"
%%%

The relation `<` on `Nat` is well-founded:

```lean
#check (Nat.lt_wfRel.wf : WellFounded Nat.lt)
```

One proves `Acc (· < ·) n` by induction on `n`:

- `0` is accessible *vacuously* — there is no `m < 0`.
- `n + 1` is accessible because every `m < n + 1` (that is, `m ≤ n`)
  is accessible by the induction hypothesis.

The deeper reason is that `Nat` is *itself* an inductive type
(`zero | succ`): every natural number is a *finite* tower of `succ`
over `zero`, so there is no infinite natural number to descend
through.  Structural recursion on `Nat` is the prototype of
well-founded recursion, and the well-foundedness of `<` is just a
restatement of it.

In practice you almost never prove well-foundedness yourself.  Mathlib
already supplies it — the `Nat.lt_wfRel.wf` above is one of many
`WellFoundedRelation` instances — and when you write a recursive
definition with `termination_by` ({ref "wf-recursion"}[Termination by a measure] in chapter
1.3), Lean finds the well-founded relation automatically
and asks you only, via `decreasing_by`, to show that your *measure*
decreases.  The induction
argument just given is the one-time justification the library
performs, not something you repeat; you would do it by hand only for a
genuinely new, exotic relation.

## Why `s ∈ s` is impossible
%%%
number := false
tag := "wf-membership"
%%%

The second mechanism is *typing*, and it is what blocks
self-membership and Russell's paradox.  Unlike ZFC, Lean has no global
membership relation: `∈` is *typed*.  The instance behind it,

```lean
#check @Set.instMembership
-- Membership α (Set α)
```

says that `x ∈ s` requires `x : α` and `s : Set α`.  For `s ∈ s` the
same `s` would need type `α` *and* type `Set α` at once — that is,
`α = Set α`, i.e. `α = (α → Prop)` (recall that a
{ref "foundations-sets"}[set is just a predicate]).  No such type
exists (there is no
matching `Membership` instance, and by *Cantor's theorem*
`α ≄ (α → Prop)`).  So `s ∈ s` is not a *false* statement; it is
*ill-formed*:

```lean
def mySet : Set ℕ := {0}

-- `#check_failure` succeeds exactly because the term
-- below fails to elaborate -- `mySet ∈ mySet` is a type
-- error, not a refutable proposition.
#check_failure (mySet ∈ mySet)
```

Consequently Russell's set `{x | x ∉ x}` cannot even be *written* in
Lean.  Compare ZFC (see {ref "comparison-zfc"}[the ZFC comparison] and, for the history, {ref "prehistory"}[the Introduction]),
where `s ∈ s` *is* a well-formed proposition and is excluded only by
the separate axiom of foundation.  Lean rules it out one step
earlier, by typing.

*Cantor's theorem* (`Function.cantor_surjective`), invoked above, says that there is no surjection `α → Set α`. Its diagonal set `{x | x ∉ f x}` is Russell's `{x | x ∉ x}`, and the same diagonal shows why a negative occurrence in an inductive type is fatal ({ref "positivity-sufficient"}[Why positivity is enough] in chapter 1.3). One level up, typing forbids `Type : Type` ({ref "type-universes"}[chapter 1.2]); building Girard's paradox in Lean is {ref "project-girard"}[one of the course projects].

## Two kinds of "no vicious circle"
%%%
number := false
tag := "wf-summary"
%%%

It is worth holding the two mechanisms apart — they forbid
circularity at different places:

:::table +header
* + Phenomenon ruled out
  + Mechanism
* + Infinite descent; non-terminating recursion
  + `Acc` / `WellFounded` — an inductive predicate *within* a type
* + `s ∈ s`, `{x | x ∉ x}`, `Type : Type`
  + Typing and the universe hierarchy — the *structure* of the system
:::

Both express the intuition "no self-swallowing circles", but the first
is a *theorem-level* tool you invoke for recursion, while the second
is baked into the *well-formedness* rules of the language.

# Constructive vs classical logic
%%%
tag := "constructive-classical"
%%%

Without `Classical.choice`, Lean's logic is *constructive*: a proof of `∃ x, P x` comes from a concrete witness, and a proof of `P ∨ Q` from one of the two sides. The axiom of choice adds *classical* reasoning.

## Excluded middle in use
%%%
number := false
tag := "excluded-middle"
%%%

The excluded middle is a theorem ({ref "em-derived"}[Diaconescu's theorem]). It licenses a case split on *any* proposition, and with it double-negation elimination, which is not provable constructively:

```lean
-- excluded middle powers `by_contra` and `by_cases`
example (P : Prop) : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  exact hnnP hnP
```

## When do you need Classical.choice?
%%%
number := false
tag := "when-classical"
%%%

You need classical axioms when:
- You want to do a case split on an arbitrary proposition (`by_cases`, `by_contra`)
- You want to choose an element from a nonempty type without a constructive witness
- You want to use the law of excluded middle
- A definition or statement needs a `Decidable` instance that has no algorithm; the {ref "classical-tactic"}[`classical` tactic] and `open Classical in` supply one ({ref "decidable-typeclass"}[chapter 1.6])

You do *not* need classical axioms when:
- Working with decidable propositions (natural number arithmetic, finite structures)
- Constructing specific terms (defining functions, data structures)
- Proving things by direct construction or induction

Mathlib uses classical logic freely, since its subject is mathematical truth rather than computation: `by_cases` and `by_contra` everywhere, and the `classical` tactic where a proof needs a `Decidable` instance.

# Comparison with ZFC set theory
%%%
tag := "comparison-zfc"
%%%

Most mathematicians are (at least implicitly) trained in ZFC set theory. Here are the key differences from Lean's type theory:

:::table +header
* + Feature
  + ZFC
  + Lean
* + Foundation
  + Sets and membership `∈`
  + Types and terms `:`
* + Everything is a...
  + Set
  + Term of some type
* + `3 ∈ 7`
  + Well-formed (and true!)
  + Type error
* + Functions
  + Sets of ordered pairs
  + Primitive notion
* + Equality
  + Between any two sets
  + Only within a type
* + Proof objects
  + Not part of the theory
  + First-class citizens
* + Computation
  + Not built in
  + Built in (terms reduce)
* + Type checking
  + Not applicable
  + Decidable (in practice)
:::

A key practical difference: in ZFC, you can ask nonsensical questions like "is 3 ∈ π?" and get an answer. In Lean, comparing objects of different types is a type error, which catches many mistakes early.


The axioms of ZFC are listed in the box below. Lean's type theory has rules instead, given in {ref "type-rules"}[The rules of Lean's type theory], and three axioms: `propext`, `Quot.sound` and `Classical.choice`.

::::example "The axioms of ZFC"
ZFC is a theory in first-order logic with a single binary relation $`\in`. The logic brings its own rules (modus ponens, generalization, the rules for equality); the theory adds the axioms below. Symbols such as $`\emptyset`, $`\subseteq`, $`\cup` and $`\{x\}` are abbreviations defined from $`\in`. Separation and replacement are schemas, one axiom for each formula $`\varphi`.

:::table (align := left) +header
* + Axiom
  + Statement
* + Extensionality
  + $`\forall A\, \forall B\, \big(\forall x\, (x \in A \leftrightarrow x \in B) \to A = B\big)`
* + Empty set
  + $`\exists A\, \forall x\, \neg (x \in A)`
* + Pairing
  + $`\forall a\, \forall b\, \exists A\, \forall x\, (x \in A \leftrightarrow x = a \lor x = b)`
* + Union
  + $`\forall \mathcal F\, \exists A\, \forall x\, \big(x \in A \leftrightarrow \exists B\, (x \in B \land B \in \mathcal F)\big)`
* + Power set
  + $`\forall A\, \exists P\, \forall B\, (B \in P \leftrightarrow B \subseteq A)`
* + Infinity
  + $`\exists A\, \big(\emptyset \in A \land \forall x\, (x \in A \to x \cup \{x\} \in A)\big)`
* + Separation
  + $`\forall A\, \exists B\, \forall x\, \big(x \in B \leftrightarrow x \in A \land \varphi(x)\big)`
* + Replacement
  + $`\forall A\, \big(\forall x \in A\, \exists! y\, \varphi(x, y) \to \exists B\, \forall x \in A\, \exists y \in B\, \varphi(x, y)\big)`
* + Foundation
  + $`\forall A\, \big(A \neq \emptyset \to \exists x \in A\, (x \cap A = \emptyset)\big)`
* + Choice
  + $`\forall \mathcal F\, \big(\emptyset \notin \mathcal F \to \exists f \colon \mathcal F \to \textstyle\bigcup \mathcal F\ \forall A \in \mathcal F\, f(A) \in A\big)`
:::

Zermelo's list of 1908 contains all of these except replacement and foundation. Replacement was added by Abraham Fraenkel and Thoralf Skolem in 1922. Separation is the axiom that answers Russell.
::::

Each ZFC axiom has a counterpart in Lean:

:::table (align := left) +header
* + ZFC
  + in Lean
  + status
* + Extensionality
  + `funext`, `propext`, `Set.ext`
  + theorem, axiom, theorem
* + Empty set
  + `Empty`, `(∅ : Set α)`
  + inductive type, definition
* + Pairing, union
  + `α × β`, `α ⊕ β`, `Σ`; for sets `{a, b}`, `⋃`
  + inductive types, definitions
* + Power set
  + `Set α := α → Prop`
  + function type
* + Infinity
  + `ℕ`
  + inductive type
* + Separation
  + `{x : α // p x}`, `{x | p x}`
  + definitions
* + Replacement
  + the image `f '' s`
  + definition
* + Foundation
  + no counterpart: `x ∈ x` is not well-typed
  + not needed
* + Choice
  + `Classical.choice`
  + axiom
:::

Of the ten ZFC axioms, two survive as axioms; the rest become rules, inductive types or definitions.

Nearly everything that can be formalized in ZFC can also be formalized in Lean's type theory, and the other way round. {citet werner1997}[] makes one half of this precise: ZFC embeds into the CIC, and a dialect of the CIC embeds back into ZFC with a hierarchy of inaccessible cardinals. It is not a statement about Lean. The type theory Lean actually implements has no complete public relative-consistency proof{citep hales2026}[]; see {ref "prop-special"}[the chapter on types].

# Brief mention of other type theories
%%%
tag := "other-type-theories"
%%%

Lean's type theory is one of several:

- **Simply typed lambda calculus** (Church, 1940): No dependent types. Foundation for Haskell, OCaml.
- **System F** (Girard, Reynolds, 1970s): Adds polymorphism but not full dependent types.{citep girard1972}[]
- **Martin-Löf Type Theory** (MLTT, 1971+): The origin of dependent types in proof assistants. Used in Agda.{citep martinLof1975}[]
- **Calculus of Inductive Constructions** (CIC): the system Lean's kernel implements ({ref "type-rules"}[chapter 1.5]); also used, in a closely related form, by Coq/Rocq.
- **Homotopy Type Theory** (HoTT, 2013): Interprets types as topological spaces and equality as paths. Adds the univalence axiom (due to Voevodsky): equivalent types are equal. This is incompatible with Lean's proof irrelevance for `Prop`, so HoTT uses different proof assistants (Agda, cubical Agda, or specialized Lean forks).
- **Cubical Type Theory** (2015+): Makes HoTT computational by using a cube category to model paths.{citep cohenEtAl2018}[]

For this course, Lean's type theory (CIC + proof irrelevance + quotients + choice) is the framework we work in. It is expressive enough to formalize virtually all of modern mathematics, as the Mathlib library demonstrates.
