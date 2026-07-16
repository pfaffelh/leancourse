import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Leancourse.Coursenotes.References
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Leancourse.Refs
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Universes, Axioms, and Foundations" =>
%%%
htmlSplit := .never
tag := "universes-axioms"
%%%

Lean's type theory rests on a carefully designed system of universes, a small number of axioms, and a powerful logic that can be used both constructively and classically. In this chapter, we examine these foundational aspects.

# The universe hierarchy
%%%
tag := "universe-hierarchy"
%%%

Part 1 introduced the {ref "type-universes"}[universe hierarchy] as a working tool: `Prop = Sort 0`, `Type = Type 0 = Sort 1`, `Type u = Sort (u+1)`, the single rule `Sort u : Sort (u + 1)`, and universe-polymorphism via `Type*`. Here we record *why* the absence of `Type : Type` is not optional. Were `Type : Type` to hold, one could reproduce Russell's paradox at the level of types -- *Girard's paradox* -- and thereby prove `False`. The stratification

```lean
#check (Type 0 : Type 1)    -- Type : Type 1
#check (Type 1 : Type 2)    -- Type 1 : Type 2
```

is exactly what blocks this, and it is what keeps the whole system consistent. Everything else in this chapter -- the axioms, proof irrelevance, the CIC -- rests on top of it.

## Girard's paradox
%%%
number := false
tag := "girard"
%%%

Why is `Type : Type` fatal? Because it lets you form a "type of all types" that contains *itself*, and self-membership at that scale is exactly the ingredient of Russell's paradox. Recall Russell: the collection `R = { x | x ∉ x }` of all sets that do not contain themselves satisfies `R ∈ R ↔ R ∉ R`, a contradiction. *Girard's paradox* is the type-theoretic version: given an impredicative universe that may contain itself -- which `Type : Type` would provide -- one can build a term playing the role of `R` and derive a *closed proof of `False`*. Historically it is a Burali-Forti-style argument (a well-ordering of all ordinals that is its own proper initial segment); A. Hurkens (1995) distilled it to a remarkably short term in the inconsistent system "λU".

Lean makes the collapse impossible by *stratifying*: `Type u` never has type `Type u`, only `Type (u+1)`, so the self-reference cannot even be written down. The ascription `Type : Type` is rejected outright:

```lean +error
-- `Type` has type `Type 1`, not `Type` -- the hierarchy forbids this
#check (Type : Type)
```

```lean
-- what is actually true: each universe sits one level up
#check (Type : Type 1)
example : Type = Type 0 := rfl
```

The paradox cannot be *run* here, but -- rather than wave at it -- we can build it in Lean and watch *exactly* where the type-checker stops it. The only type former it needs is the *power set*: for a type `X` this is `Set X`, definitionally `X → Prop` ({ref "sets-and-types"}[the previous chapter]; classical set theory writes it `℘ X`), and iterating gives the double power set `Set (Set X)`. Girard's universe `U` is engineered so that its *own* double power set `Set (Set U)` embeds back into `U`; that self-embedding is the forbidden fruit. Watch how far Lean plays along:

```lean
namespace Girard  -- self-contained; nothing leaks to later chapters

-- With predicative `Type`, the outer `∀ X : Type` pushes `U` one
-- level up: it lives in `Type 1`, not `Type`.  Lean accepts this.
def U : Type 1 := (X : Type) → (Set (Set X) → X) → Set (Set X)

-- τ *encodes* a "set of sets of U" as a single element of U (σ,
-- below, would *decode* it back).  Recall `Set X` is `X → Prop`,
-- so a set applied to a point, `s a`, is just `a ∈ s`.  τ
-- type-checks -- and here `x : U`:
def τ (t : Set (Set U)) : U :=
  fun (X : Type) (f : Set (Set X) → X) (p : Set X) =>
    t (fun (x : U) => p (f (x X f)))

-- The next step is where it breaks. Defining σ needs `s U` --
-- instantiating `s : U` at the type `U` itself -- but `U : Type 1`,
-- not `Type`. Lean rejects `s U`, so `#check_failure` *succeeds*:
#check_failure (fun (s : U) => s U)

end Girard
```

So the wheels come off already at `σ`, not at the final theorem -- and the universe level we chose makes no difference. `U` always sits one level above the `Type` its quantifier ranges over (the {ref "universe-hierarchy"}[`Type u` are predicative]), so `s U` is off by one *everywhere*: lift `U`'s domain to `Type 1` and `U` climbs to `Type 2`, and now `s U` wants a `Type 1`. The self-instantiation can never be typed. Grant `Type : Type` and the gap closes: `σ` goes through, and the rest -- well-typed *relative to* `σ`, `τ` and their reduction `σ (τ t) p = t (fun x => p (τ (σ x)))` -- runs all the way to `False`:

```
-- Under `Type : Type`, σ becomes definable (with the reduction
--   σ (τ t) p  =  t (fun x => p (τ (σ x)))  ), and the rest goes:
def σ (s : U) : Set (Set U) := s U τ

-- Δ is the Russell set `{x | x ∉ x}`; Ω is its diagonal fixpoint.
def Δ : Set U := fun y => ¬ ∀ p : Set U, σ y p → p (τ (σ y))
def Ω : U := τ (fun p => ∀ x : U, σ x p → p x)

-- Every property holding hereditarily along σ holds at Ω:
def lem : ∀ p : Set U, (∀ x : U, σ x p → p x) → p Ω :=
  fun p H => H Ω (fun x => H (τ (σ x)))

-- Feeding `lem` the bad set Δ yields both Δ Ω and ¬ Δ Ω:
theorem girard : False :=
  lem Δ
    (fun x l₂ l₃ => l₃ Δ l₂ (fun p => l₃ (fun y => p (τ (σ y)))))
    (fun p => lem (fun y => p (τ (σ y))))
```

`lem` proves that every hereditary property holds at the diagonal point `Ω`; instantiating it at `Δ` proves `Δ Ω`, while the last argument supplies *exactly* the statement that `Δ Ω = ¬ (…)` negates -- the two collide, and the term has type `False`. The whole edifice rests on the single step Lean refused, `s U`. That one act of stratification is what stops the paradox.

A natural objection: Lean's `Prop` is itself *impredicative* -- `(∀ p : Prop, p) : Prop` quantifies over all of `Prop` yet stays in `Prop` -- so why does the same argument not detonate there? Because impredicativity is only *half* of Girard's ingredient; the other half is a sort that quantifies over itself *and* whose elements can be used as data to eliminate on. `Prop` is walled off from both:

* `Prop : Type`, not `Prop : Prop`. So `U` cannot even be *stated* with `Prop` in the role of the self-containing universe: `∀ X : Prop, …` produces a term whose type mentions `Prop`, and that type does not itself live in `Prop`. The self-reference the paradox feeds on is absent -- exactly as it is for `Type`.
* Proofs cannot be eliminated into data ({ref "prop-vs-type"}[proof irrelevance], the next section): from `h : P` with `P : Prop` one may build another proof, never a `Type`-level element `X`. Hurkens' `σ`/`τ` machinery lives in `Type` and treats inhabitants of `U` as *data* to eliminate; the construction has no `Prop`-level twin, because the elimination it needs is forbidden.

So impredicative `Prop` sitting on top of the *predicative* `Type` hierarchy is consistent -- this is Coquand's Calculus of Constructions, and it has a set-theoretic model. What is inconsistent is Girard's System `U`, where an impredicative sort *also* contains itself as data. Lean deliberately keeps the safe half (impredicative `Prop`) and rejects the dangerous one (`Type : Type`).

This is the same consistency instinct as {ref "inductive"}[strict positivity] one level down: there, a constructor storing `Bad → False` was rejected to stop a self-applying `neg (Bad.mk neg) : False`; here, `Type : Type` is rejected to stop its universe-level twin.

# Prop vs Type: proof irrelevance
%%%
tag := "prop-vs-type"
%%%

The universe `Prop` has a special property that distinguishes it from all `Type n`: **proof irrelevance** (introduced in {ref "prop-special"}[why `Prop` is special]). Recall that if `P : Prop` and `h1 h2 : P`, then `h1 = h2`: all proofs of the same proposition are considered equal. Here we revisit it from the foundational side.

This is a deliberate design choice. It means:
- You cannot pattern-match on a proof to extract computational data.
- Proofs can be erased at compile time without affecting program behavior.
- Two mathematical proofs of the same theorem are interchangeable.

That any two proofs of the same `P : Prop` are *equal* is itself
provable by `rfl` and costs no axiom; this, and the reason an
existential therefore lives in `Prop` -- so that recovering its witness
needs {ref "axiom-choice"}[choice] -- are taken up in
{ref "baked-in"}[Declared axioms vs. what the kernel bakes in] below.

The distinction between `Prop` and `Type` corresponds to the mathematical distinction between "asserting that something exists" (Prop) and "constructing a specific example" (Type).

# The Calculus of Inductive Constructions
%%%
tag := "cic"
%%%

We have now met the ingredients of Lean's foundation one at a time: the universe hierarchy, `Prop` with its proof irrelevance, dependent functions, and inductive types. Assembled into a single formal system, they are exactly what Lean's kernel implements{citep lean4_2021}[] -- the *Calculus of Inductive Constructions*, or CIC. This is worth stating plainly, because the CIC is the *entire* trusted core of Lean: every definition, theorem, and tactic ultimately elaborates down to terms that the kernel re-checks against these rules, and nothing outside them is trusted.

The CIC is built from exactly three ideas:

1. *Dependent functions* -- the "Constructions". This is the *Calculus of Constructions* of {citet coquandHuet1988}[]: a typed lambda calculus in which the *type* of the output may depend on the *value* of the input, giving the Π-types written `(x : α) → β x`. In one stroke this subsumes ordinary functions, polymorphic functions (which take types as arguments), and type-level functions.

2. *Inductive types* -- the "Inductive", added by {citet coquandPaulin1990}[]. This is the rule that lets you introduce a genuinely new type by listing its constructors. Remarkably, *both* data and logic are built from this one mechanism: `Nat`, `List`, and `Prod` are inductive types, but so are the logical connectives `And`, `Or`, `False`, and even equality `Eq`.

```lean
-- Data: `Nat` is an inductive type with two constructors
#check @Nat.zero    -- Nat
#check @Nat.succ    -- Nat → Nat

-- Logic too: `And`, `Or`, `Eq` are *also* inductive types
#check @And.intro
#check @Or.inl
#check @Eq.refl

-- Every inductive type comes with a recursor, which the
-- kernel generates automatically; it is how induction
-- and recursion are justified in the first place:
#check @Nat.rec
```

Defining your own inductive type uses exactly the same mechanism the standard library does -- there is no special magic reserved for the built-in types:

```lean
inductive Traffic where
  | red | amber | green
```

3. *A universe hierarchy* (`Prop`, `Type 0`, `Type 1`, ...), exactly as in the first section, which keeps the system logically consistent by forbidding `Type : Type`.

On top of these three ingredients the kernel bakes in one thing that set theory has no notion of: *computation*. Terms reduce, so `(fun n => n + 1) 2` and `3` are not merely provably equal but *definitionally* equal, and the kernel checks this by evaluating. This is the same reduction that makes {keywordOf Lean.Parser.Command.eval}`#eval` and the `decide` tactic work, and it is what lets us speak of *computable* functions at all.

What is striking about the CIC is how little it is. A type checker for it is only a few thousand lines of code, and that small program is the whole of what you must trust in order to believe a Lean proof. Everything in Mathlib -- the integers, the real numbers, manifolds, schemes -- is in the end a tower of inductive types and dependent functions resting on this kernel.

# The axioms of Lean
%%%
tag := "lean-axioms"
%%%

Powerful as it is, the CIC by itself is deliberately *minimal and constructive*: a handful of principles that working mathematicians use without a second thought cannot be proved in it. Lean therefore adds a few axioms on top of the kernel -- and it is worth being precise about *how* few. Lean has exactly *three* axioms, and we can ask Lean itself to confirm it with the `#print axioms` command, which traces a constant back to the axioms it ultimately depends on:

```lean
#print axioms propext
-- 'propext' depends on axioms: [propext]
#print axioms Quot.sound
-- 'Quot.sound' depends on axioms: [Quot.sound]
#print axioms Classical.choice
-- 'Classical.choice' depends on axioms: [Classical.choice]
```

Each of the three depends only on itself -- the signature of a genuine axiom. Everything else that *looks* axiomatic -- function extensionality, the law of excluded middle, the set-theoretic axiom of choice -- is in fact a *theorem* derived from these three, as we verify below. We take the three axioms first.

## Propositional extensionality (`propext`)
%%%
number := false
tag := "axiom-propext"
%%%

Two propositions are equal if and only if they are logically equivalent:

```lean
#check @propext
-- propext : ∀ {a b : Prop}, (a ↔ b) → a = b

-- Example: P ∧ True is the same proposition as P
example (P : Prop) : (P ∧ True) = P := by
  ext
  simp
```

This axiom is exactly what makes {ref "foundations-set-eq"}[set equality] *extensional*: since `Set α` is `α → Prop`, `propext` is what lets predicates that are logically equivalent count as the *same* set.

## The axiom of quotients
%%%
number := false
tag := "axiom-quot"
%%%

Lean has built-in support for {ref "quotient-types"}[quotient types] (introduced in the Types chapter). Given a type `α` and an equivalence relation `r` on `α`, you can form the quotient type `Quot r`. The axiom `Quot.sound` says that if `r a b`, then `Quot.mk r a = Quot.mk r b`.

This is how many mathematical constructions are formalized: the integers as a quotient of `ℕ × ℕ`, the rationals as a quotient of `ℤ × ℤ`, the reals as a quotient of Cauchy sequences, and so on.

```lean
-- Quotient types are built into Lean
#check @Quot.mk
#check @Quot.sound
#check @Quot.lift
```

Quotient soundness carries more weight than it looks: function extensionality is *proved* from it, as we see below.

## The axiom of choice (`Classical.choice`)
%%%
number := false
tag := "axiom-choice"
%%%

The most powerful (and most controversial) axiom in Lean is the axiom of choice:

```lean
#check @Classical.choice
-- Classical.choice : ∀ {α : Sort u}, Nonempty α → α
```

Given a proof that a type is nonempty (i.e., inhabited), `Classical.choice` produces an actual element. This is a non-constructive axiom: it asserts existence without providing any recipe for the element. From it one also recovers the more familiar set-theoretic axiom of choice and Hilbert's `ε`-operator.

# What is *not* an axiom: `funext` and excluded middle
%%%
tag := "derived-not-axioms"
%%%

Two principles that mathematicians treat as bedrock are, perhaps surprisingly, *not* axioms in Lean but theorems derived from the three above.

## Function extensionality is a theorem
%%%
number := false
tag := "axiom-funext"
%%%

Two functions are equal if they agree on every input -- which, together with `propext`, is what makes {ref "foundations-set-eq"}[set equality] extensional (two sets with the same members are equal because they are equal *functions* into `Prop`). In practice one *uses* it through the `funext` lemma and tactic:

```lean
-- funext: if f x = g x for all x, then f = g
#check @funext
-- funext : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
--   (∀ (x : α), f x = g x) → f = g

example : (fun n : ℕ => n + 0) = (fun n : ℕ => n) := by
  funext n
  simp
```

Despite the name and its fundamental role, `funext` is *not* an axiom: it is provable from quotient soundness. Lean confirms that its only axiomatic dependency is `Quot.sound`:

```lean
#print axioms funext
-- 'funext' depends on axioms: [Quot.sound]
```

## Excluded middle is a theorem (Diaconescu)
%%%
number := false
tag := "em-derived"
%%%

Likewise the law of excluded middle `∀ p, p ∨ ¬p` is *not* an axiom. It follows from the three axioms by a classical argument known as *Diaconescu's theorem*: the axiom of choice implies excluded middle. Lean again makes the dependency explicit:

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

Both are nonempty -- `True` satisfies `U` and `False` satisfies `V` -- so `Classical.choice` hands us concrete witnesses `u v : Prop` together with proofs of `u = True ∨ p` and `v = False ∨ p`. Now case-split on those two disjunctions:

- If either disjunction takes its *right* branch, we have a proof of `p` outright -- the left side of `p ∨ ¬p`.
- Otherwise `u = True` and `v = False`, so `u ≠ v`. But were `p` true, then `propext` would collapse `U` and `V` into the same predicate, forcing the chosen witnesses to coincide, `u = v` -- a contradiction. Hence `¬p`, the right side.

Either way we obtain `p ∨ ¬p`. The decisive step is that `Classical.choice` turns the *propositional* assumption `p` into *comparable data* -- the booleans `True` and `False` -- which is precisely the move a constructive system refuses to make. Mathlib packages the result as `Classical.em`; in practice you simply use it (often via `by_contra` or `by_cases`).

You might object that the step "assume `p`, derive a contradiction, conclude `¬p`" already *uses* excluded middle, which would make the argument circular. It does not. Proving `¬p` by assuming `p` and reaching a contradiction is *negation introduction* -- it is simply the definition of `¬p` as `p → False`, and it is constructively valid. The *classical* principle is the opposite direction: concluding a positive `p` from `¬¬p` (that is `by_contra`), which we never invoke here. Likewise, the case splits above *eliminate* disjunctions we already hold (from the choice specification); they do not conjure `p ∨ ¬p` out of nothing -- that disjunction is our *conclusion*, assembled constructively from the cases. The one and only non-constructive ingredient is `Classical.choice`, and using it is not the same as assuming the `p ∨ ¬p` we are proving.

# Declared axioms vs. what the kernel bakes in
%%%
tag := "baked-in"
%%%

Saying Lean has "exactly three axioms" is precise about *declared* axioms -- the `axiom` constants, which are exactly what `#print axioms` reports. But the kernel's typing and definitional-equality rules quietly build in further logical principles that are *not* axioms and leave *no* trace in `#print axioms`. They come for free, and -- unlike the three axioms -- you cannot opt out of them.

The clearest are *definitional*: they hold by `rfl`, yet cost nothing.

```lean
-- Each holds by `rfl` -- it is *definitional* -- and none
-- of them costs an axiom.
theorem pf_irrel (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
theorem eta_fun (f : Nat → Nat) :
    (fun x => f x) = f := rfl
theorem quot_red (a : Nat) (f : Nat → Nat) (h) :
    Quot.lift f h (Quot.mk (fun _ _ => True) a) = f a :=
  rfl

#print axioms pf_irrel
-- 'pf_irrel' does not depend on any axioms
```

So the following are all *built into the kernel*, not assumed on top of it:

:::table +header
* + Baked-in principle
  + What it gives you
* + Proof irrelevance for `Prop`
  + any two proofs of the same proposition are *equal*
* + Eta for functions
  + `f` and `fun x => f x` are interchangeable
* + Eta for structures
  + `s` and `⟨s.1, s.2⟩` are interchangeable
* + Quotient computation
  + `Quot.lift f h (Quot.mk r a)` reduces to `f a`
:::

## More that the kernel bakes in
%%%
number := false
tag := "baked-in-more"
%%%

The list does not stop there:

- *Computation* (beta, iota, delta, zeta reduction): the kernel *evaluates* terms, so `2 + 2 = 4` holds by `rfl` (these {ref "reduction-rules"}[reduction rules] are detailed in the appendix).
- *Native literal arithmetic*: the kernel computes `Nat`, `Int`, and `String` literals with bignum-backed operations rather than unary `succ` -- a baked-in optimization you rely on every time you `decide` or `#eval`.
- *Impredicative `Prop`*: `∀ (α : Type), p α` is again a `Prop`, no matter how large `α` is.
- *Inductive types and their recursors*: every `inductive` declaration generates an eliminator together with its built-in computation (iota) rule (see {ref "cic"}[the CIC section]).
- *The universe hierarchy* ({ref "universe-hierarchy"}[the first section]): in particular, never `Type : Type`.
- *Subsingleton (large) elimination*: you may eliminate a `Prop` into `Type` only when it is a *subsingleton* -- `False`, `Eq`, `And`, `Acc` qualify, but `Or` and `Exists` do not, because they would let you extract genuine data (which side, which witness) from a mere proof.

That last rule is exactly why an existential lives in `Prop` and you need {ref "axiom-choice"}[choice] to get its witness:

```lean
-- `False` is a subsingleton: large elimination is fine
#check (False.elim : False → Nat)

-- `Exists` carries data (its witness), so it may NOT
-- be eliminated into `Type`: the witness can't escape.
#check_failure
  (fun (h : ∃ n : Nat, True) =>
    Exists.rec (motive := fun _ => Nat)
      (fun w _ => w) h)

-- `Or` has two constructors -- likewise no data elimination
#check_failure
  (fun (h : (0 = 0) ∨ (1 = 1)) =>
    Or.rec (motive := fun _ => Nat)
      (fun _ => 0) (fun _ => 1) h)
```

## What this means
%%%
number := false
tag := "baked-in-meaning"
%%%

Two consequences are worth drawing.

First, `#print axioms` sees *only* the declared axioms.  The baked-in principles are invisible to it and cannot be switched off, so the *trusted base* of a Lean proof is not "three axioms" but the whole kernel -- the CIC together with proof irrelevance, eta, the quotient reduction, native computation, and the universe rules.  Believing a Lean theorem means believing all of that.

Second, proof irrelevance for `Prop` is effectively *uniqueness of identity proofs* (axiom K): all proofs of `a = b` are equal.  This is a deliberate design choice -- but it is precisely what makes Lean *incompatible* with the univalence axiom of {ref "other-type-theories"}[Homotopy Type Theory], where distinct equality proofs must be allowed to differ.

# Constructive vs classical logic
%%%
tag := "constructive-classical"
%%%

By default, Lean's type theory is *constructive*: proofs must provide explicit witnesses and constructions. The axiom of choice introduces *classical* reasoning, which allows non-constructive arguments.

## Excluded middle in use
%%%
number := false
tag := "excluded-middle"
%%%

We saw above that excluded middle is a *theorem*, not an axiom (see {ref "em-derived"}[Diaconescu's theorem]). What makes it indispensable in everyday proofs is that it licenses a case split on *any* proposition, and with it classical staples such as double-negation elimination:

```lean
-- excluded middle powers `by_contra` and `by_cases`
example (P : Prop) : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  exact hnnP hnP
```

Without excluded middle, double negation elimination `¬¬P → P` is not provable -- one of the key differences between constructive and classical logic.

## Decidability, classically
%%%
number := false
tag := "decidable-classically"
%%%

Recall the {ref "decidable-typeclass"}[`Decidable` typeclass] from
Part 1: a proposition is `Decidable` when an algorithm can compute
whether it holds, which is what makes `if P then _ else _` and the
`decide` tactic run *without any axioms*. Classical logic extends this
reach at a price. When you `open Classical`, every `Prop` becomes
`Decidable` -- but *non-constructively*, via `Classical.choice`, so the
instance carries no algorithm. This is convenient in proofs (you may
`by_cases` on any proposition), but code that relies on it is no longer
executable. Decidability is thus the exact dividing line between the
constructive core and the classical extension.

## When do you need Classical.choice?
%%%
number := false
tag := "when-classical"
%%%

You need classical axioms when:
- You want to do a case split on an arbitrary proposition (`by_cases`, `by_contra`)
- You want to choose an element from a nonempty type without a constructive witness
- You want to use the law of excluded middle

You do *not* need classical axioms when:
- Working with decidable propositions (natural number arithmetic, finite structures)
- Constructing specific terms (defining functions, data structures)
- Proving things by direct construction or induction

In Mathlib, most proofs use classical logic freely (via `open Classical`), since the focus is on mathematical truth rather than computational content.

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

Both foundations are equiconsistent for most of mathematics. Nearly everything that can be formalized in ZFC can also be formalized in Lean's type theory (and vice versa).

# Brief mention of other type theories
%%%
tag := "other-type-theories"
%%%

Lean's type theory is one of several:

- **Simply typed lambda calculus** (Church, 1940): No dependent types. Foundation for Haskell, OCaml.
- **System F** (Girard, Reynolds, 1970s): Adds polymorphism but not full dependent types.{citep girard1972}[]
- **Martin-Löf Type Theory** (MLTT, 1971+): The origin of dependent types in proof assistants. Used in Agda.{citep martinLof1975}[]
- **Calculus of Inductive Constructions** (CIC): the system Lean's kernel implements, described earlier in this chapter; also used, in a closely related form, by Coq/Rocq.
- **Homotopy Type Theory** (HoTT, 2013): Interprets types as topological spaces and equality as paths. Adds the univalence axiom (due to Voevodsky): equivalent types are equal. This is incompatible with Lean's proof irrelevance for `Prop`, so HoTT uses different proof assistants (Agda, cubical Agda, or specialized Lean forks).
- **Cubical Type Theory** (2015+): Makes HoTT computational by using a cube category to model paths.{citep cohenEtAl2018}[]

For this course, Lean's type theory (CIC + proof irrelevance + quotients + choice) is the framework we work in. It is expressive enough to formalize virtually all of modern mathematics, as the Mathlib library demonstrates.
