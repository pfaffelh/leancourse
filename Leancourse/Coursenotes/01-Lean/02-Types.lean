import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Types" =>
%%%
htmlSplit := .never
tag := "types"
%%%

In all programming languages, you have data types such as `int`, `string` and `float`. In Lean, these exist as well, but you can (and will in this course) define own data types. In all cases, we write `x : α` for a term `x` of type `α`, so we write `False : Bool`, `42 : ℕ`, but also `f : ℕ → ℝ` (for a function from ℕ to ℝ, which is an own type) and `0 ≠ 1 : Prop` (the proposition that 0 and 1 are different natural numbers), which is a proposition. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` (the term `n < n + 1` depends on `n : ℕ`) and `f : (n : ℕ) → (Fin n → ℝ)` where `Fin n` is the type which carries `{0, ..., n-1}` (here, the type `Fin n → ℝ` depends on `n : ℕ`), which is a function `f` with domain `ℕ` such that `f n ∈ ℝ^n`.

Two words for terms recur throughout, depending on their type: a term `h : P` whose type `P` is a `Prop` is called a *proof* (of `P`), while a term `a : α` whose type `α` is a `Type u` is called *data*. So `42 : ℕ` and `true : Bool` are data, whereas any term of the proposition `0 ≠ 1` is a proof of it. (The two kinds of universe, `Prop` and `Type u`, are the subject of the next section.)

As we see, these new data types are more abstract: Lean understands `ℕ` (and `ℝ`) as genuinely infinite types, not limited by floating-point arithmetic. The `zero`/`succ` construction of `ℕ` was the subject of the {ref "nat"}[introduction]; the real numbers, by contrast, are built from an equivalence relation on Cauchy sequences, which is considerably more elaborate -- a {ref "quotient-types"}[quotient type], as we will see at the end of this chapter.

In Lean, all objects are terms, and every term needs a type. Interestingly, since a type is also some term in the language, it needs a type as well.

# The universe hierarchy
%%%
tag := "type-universes"
%%%

The answer is a hierarchy: these types-of-types (called *universes*) are organized into a countably infinite tower, which is exactly what keeps the system consistent.

At the bottom sit the two universes you meet first (Here, the `#check` command gives the type of a term):

```lean
#check (42 : ℕ)         -- a term ...
#check (ℕ : Type)       -- ... whose type ℕ lives in `Type`
#check ((2 = 2) : Prop) -- a proposition ...
#check (Prop : Type)    -- ... and `Prop` itself lives in `Type`
```

`Type` (which is the same as `Type 0`) is the universe of ordinary data types (`ℕ`, `ℝ`, `Bool`, `List α`, ...), and `Prop` (which is the universe of *propositions*, i.e. True/False-statements). But `Type` cannot contain itself -- that would be paradoxical -- so `Type` in turn lives in a larger universe `Type 1`, which lives in `Type 2`, and so on without end:

```lean
#check (Type : Type 1)      -- Type   : Type 1
#check (Type 1 : Type 2)    -- Type 1 : Type 2
```

:::example "The connection of `Type` to `Sort`"

The whole tower is captured by a single keyword `Sort`:

* `Sort 0` is `Prop`;
* `Sort 1` is `Type 0`, i.e. `Type`;
* `Sort (u+1)` is `Type u`.

```lean
example : Sort 0 = Prop := rfl
example : Sort 1 = Type := rfl
example : Type = Type 0 := rfl
```

So `Sort` is the umbrella that unifies `Prop` and all the `Type u`, and the one rule governing the hierarchy is `Sort u : Sort (u+1)`. There is deliberately no `Type : Type`; *why* this restriction is needed -- it blocks a type-theoretic version of Russell's paradox -- is taken up in the {ref "universe-hierarchy"}[Mathematics part].
:::

# How the universe of a type is determined
%%%
tag := "universe-determined"
%%%

You rarely write universe levels by hand -- Lean computes the universe of a compound type from the universes of its parts. A function type `α → β` lands in the *larger* of the two universes involved:

```lean
#check (ℕ → ℕ)        -- Type
#check (ℕ → Type)     -- Type 1  (because `Type : Type 1`)
```

The same holds for a `∀` (a *dependent* function type), whose universe is read off from the universe it ranges over together with that of its body. When the body is data -- something in a `Type` -- the whole `∀` is forced to grow with the domain:

```lean
-- Type-valued body: the universe grows with the domain.
#check (∀ α : Type, α → α)     -- Type 1
#check (∀ α : Type 5, α → α)   -- Type 6
```

This climbing is what it means for the `Type u` to be *predicative*. The word says it: a *predicative* definition may refer only to things already available *below* it -- whatever a type quantifies over must be strictly smaller, so the type it forms can never land back inside its own domain. That is exactly why `∀ α : Type 5, α → α` is pushed up to `Type 6`, safely *above* everything it ranges over, and it is what keeps the whole hierarchy well-founded. (The terminology goes back to Poincaré and Russell, who imposed predicativity to outlaw the self-referential definitions behind the set-theoretic paradoxes.)

This is not mere bookkeeping. Suppose `∀ α : Type, α → α` were allowed to have type `Type` rather than `Type 1` -- i.e. a `∀` over `Type` could land back inside `Type`. That is the first step toward a universe that contains itself, `Type : Type`, and *that* is fatal: from `Type : Type` one can encode Russell's paradox at the level of types -- *Girard's paradox* -- and derive an honest proof of `False`, so *every* proposition becomes provable and the system is worthless. Predicativity, by forcing the climb to `Type 1`, is exactly what rules this out. (The proof is not short, and Lean's kernel enforces the bump, so you cannot even state `∀ α : Type, α → α : Type` to try it; the construction of the paradox from `Type : Type` is spelled out in {ref "universe-hierarchy"}[the Mathematics part].)

(A definition can also be made to work at *any* universe level at once; that uses `def`, so we defer it to the {ref "polymorphic-functions"}[chapter on functions].)

There is exactly one universe that is allowed to break this rule -- `Prop` -- and that exception is the subject of the next section.

# Why `Prop` is special
%%%
tag := "prop-special"
%%%

Of particular interest is the type `Prop`, which consists of statements that can be `True` or `False`. It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. Synonomously, it means that `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the proofs of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`. (Note the similarity to function notation as in `f : ℝ → ℝ`.)

We note three specifics which only apply to `Prop`:

*Proof irrelevance*: Note that `Prop` only records *that* a statement holds, but not *which* proof we chose. This is *proof irrelevance*, which means the following goal closes by `rfl`:

```lean
example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl
```

For data living in a `Type` there is no such collapse, for obvious reasons.

```lean +error
example (a b : ℕ) : a = b := rfl
```
See also {ref "prop-vs-type"}[Prop vs Type].

*`Prop` is impredicative*: `Prop` is the one universe that escapes the predicativity of the {ref "universe-determined"}[previous section]. As long as the body of a `∀` statement is a proposition, the whole `∀` is a `Prop` -- even when we range over an arbitrarily large universe of types:

```lean
-- Prop-valued body: stays `Prop`, however big the domain.
#check (∀ α : Type, α = α)     -- Prop
#check (∀ α : Type 5, α = α)   -- Prop
```

Compare this with the `Type`-valued `∀ α : Type 5, α → α`, which had to climb to `Type 6`. The two statements are syntactically parallel and differ only in their body, yet land in wildly different places -- `Prop` versus `Type 6`. A `∀` into `Prop` stays small; a `∀` into `Type u` must climb. This is exactly what *impredicative* means: a proposition may be defined by quantifying over a totality *to which it itself belongs*. `∀ P : Prop, P` is again a `Prop`, so it ranges over a collection that already contains it -- the definition, so to speak, feeds on itself. `Prop` is allowed this self-reference because proof irrelevance keeps it harmless.

*Restricted (subsingleton) elimination*: First, a word on what *elimination* means. A type's constructors *introduce* its values -- they are the ways we build them (`Or.inl`, `isTrue`, `Nat.succ`, and so on). *Eliminating* a value is the opposite: we *use* it, by looking at which constructor produced it. This is what a `match` does -- the {ref "pattern-matching"}[pattern-matching] construct `match h with | … => …`, taken up properly in the chapter on terms -- and, as we saw in the {ref "nat-intro"}[introduction], it is ultimately the job of the type's {ref "inductive"}[recursor] (there, `Nat.rec`). To *eliminate into a type `T`* means that this case analysis returns a result of type `T`. The restriction on `Prop` is about exactly this. A proof carries no observable content, so Lean does not let us *read data off a proof* in this way: otherwise the result could depend on *which* proof we started from, and proof irrelevance says there is no such difference to observe. So eliminating a proposition may, in general, only produce further propositions, never data. For example, deciding as a {ref "bool"}[`Bool`] which side of a disjunction holds is rejected:

```lean +error
example (a b : Prop) (h : a ∨ b) : Bool :=
  match h with
  | Or.inl _ => true
  | Or.inr _ => false
```

The error message is telling: `recursor 'Or.casesOn' can only eliminate into 'Prop'`. There is one exception, called *subsingleton elimination*. If a proposition has *at most one constructor* and all of its fields are *themselves proofs*, then it has at most one inhabitant, so eliminating it can reveal nothing -- and Lean does allow it into *any* type. This covers `False` (no constructors at all, which is exactly why `False.elim` closes *any* goal), `Eq` (which is why we may `rw` even in goals that carry data), and `And` (both of its fields are proofs). It does *not* cover `Or` (the {ref "disjunction-sum"}[disjunction] `∨`, which has two constructors) or `∃` (its first field is a genuine witness, not a proof). None of this applies to `Type`: an inductive type in `Type` always eliminates into anything.

Why must it be this way? This is not red tape -- consistency forces it, and for `Or` the reason is worth spelling out. What cannot escape here is not a *witness* (as it would be for `∃`) but the *tag*: the information about *which* of the two branches holds. Take a true `a` and consider the proposition `a ∨ a`. Its two constructors give definitionally equal terms, by proof irrelevance:

```lean
example {a : Prop} (h : a) :
    (Or.inl h : a ∨ a) = Or.inr h := rfl
```

"Left or right?" is simply not a well-posed question about a proof of `a ∨ a`: the tag is not distinguishable content. So if the rejected `(a ∨ b) → Bool` above were allowed, then setting `b := a` would give `which (Or.inl h) = true` and `which (Or.inr h) = false`; but `Or.inl h ≡ Or.inr h` (they are {ref "defeq"}[definitionally equal], the `≡` from the previous chapter), so we would get `true ≡ false`, a contradiction. Because proofs are indistinguishable, the tag has to stay trapped -- just as a leaked `∃`-witness would have forced `3 ≡ 5`.

The way out mirrors the one for `∃`, one level up. The data-carrying counterpart of `a ∨ ¬a` is `Decidable a` (the {ref "decidable-typeclass"}[`Decidable` typeclass]), which -- crucially -- lives in `Type`, not `Prop`:

```
inductive Decidable (p : Prop) : Type where
  | isFalse (h : ¬p)
  | isTrue  (h :  p)
```

Because `Decidable p` is in `Type`, it *may* eliminate into `Type` -- which is exactly why `if h : p then _ else _` (a *dependent* `if`, whose `h : p` names the proof made available in the then-branch) and the {ref "decide"}[`decide`] tactic compute. The two stories line up exactly:

:::table (align := left) +header
* + Proposition (in `Prop`)
  + Data version (in `Type`)
  + what stays hidden
* + `∃ x, q x`
  + {ref "sigma-types"}[`Σ x, q x`]
  + the *witness*
* + `a ∨ ¬a`
  + `Decidable a`
  + the *tag* (which side)
:::

The classical route mirrors `Classical.choose` in the same way: `Classical.em : a ∨ ¬a` is always available (it is a `Prop`), but its data-carrying counterpart `Classical.propDecidable : Decidable a` goes through `Classical.choice` and is therefore `noncomputable`. So the two halves -- `∃`/`Σ`/`choose` for the *witness*, `∨`/`Decidable`/`em` for the *tag* -- are really the same story: computationally relevant information can leave the `Prop` world only if we put it in `Type` from the start, or pay for it noncomputably with the axiom of choice. (The `Nonempty`/`Classical.choice` form of this is taken up in the {ref "curry-howard"}[chapter on propositions and proofs].)

# Inductive types
%%%
tag := "inductive"
%%%

Many everyday types in Lean -- `Nat`, `List`, `Option`, `Bool`, even `Empty` -- are *inductive* types. We have already dissected one of them, `Nat`, in the {ref "nat-intro"}[previous chapter]: its two constructors `Nat.zero`/`Nat.succ`, and its recursor `Nat.rec`. This section is about the general mechanism -- how you *declare* such a type yourself, and which declarations Lean accepts.

You declare an inductive type by giving a name, the type's universe, and a list of *constructors*, each saying how to build a new element out of existing pieces. Declaring the natural numbers by hand reproduces exactly the structure of `Nat`:

```lean
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
```

As with `Nat`, this single declaration introduces three things at once: the type `MyNat`; its two constructors `MyNat.zero` and `MyNat.succ`, so every element is either `zero` or `succ n`; and a *recursor* `MyNat.rec` -- the type's *eliminator*, the counterpart of its constructors -- of the same shape as `Nat.rec`, into which pattern matching, `cases`, and `induction` all translate. Its {ref "reduction-rules"}[iota rule], `MyNat.rec z s (.succ n) ⟶ s n (MyNat.rec z s n)`, is the firing we watched for `Nat`. And a recursor is not special to `inductive`: since a `structure` is a single-constructor inductive, it too has one -- `Point.rec` (from the next section) takes a single case, a function of the fields, and the projections `Point.x`, `Point.y` are defined through it.

Now that we have {ref "type-universes"}[universes] in hand, we can state the recursor in full generality. The introduction used its *non-dependent* form, into a fixed result type; the true `MyNat.rec` lets that type *depend* on the value being consumed, a dependency recorded by a *motive* `MyNat → Sort u` (the leading `@` in `@MyNat.rec` makes Lean's normally-hidden implicit arguments -- here the `motive` -- explicit, so that `#check` prints them; see {ref "strict-implicit"}[the appendix on parentheses]):

```lean
#check @MyNat.rec
-- {motive : MyNat → Sort u} →
--   motive .zero →                      -- zero case
--   ((n : MyNat) → motive n →
--      motive n.succ) →                 -- succ case
--   (t : MyNat) → motive t
```

With a data-valued `motive` this is the *recursion* the introduction showed; with a `Prop`-valued one it is precisely the *induction principle*. Recursion and induction are thus two readings of the single primitive `MyNat.rec` -- which is why the `induction` tactic and recursive definitions feel so alike.

The declaration only *forms the type*. How to actually build its elements and *define functions* on it -- typically by pattern matching on the constructors -- is the subject of {ref "terms"}[the next chapter], on constructing terms.

Proofs about an inductive type use the `induction` tactic, which applies the recursor for you: one subgoal per constructor, with an induction hypothesis for each recursive argument.

Inductive types also cover non-recursive data:

```lean
inductive Colour where
  | red | green | blue
```

and parameterized types:

```lean
-- `MyOption α` is either `none` or `some a` for some `a : α`.
inductive MyOption (α : Type) where
  | none : MyOption α
  | some (a : α) : MyOption α
```

Inductive types are the main mechanism by which new data types enter Lean; `Mathlib` uses them extensively, and understanding them is essential for reading the library. This also answers the question of the previous section from the other side: the universe of an inductive type must be large enough to hold all of its constructor arguments.

Not every `inductive` declaration is accepted, though. A constructor may mention the type being defined, but only *positively* -- never to the *left* of an arrow inside one of its arguments. This *strict positivity* condition keeps inductive types built from well-founded data and free of paradox. A tree branching over `ℕ` is fine, because `MyTree` occurs only to the *right* of `→`:

```lean
inductive MyTree where
  | node : (ℕ → MyTree) → MyTree   -- accepted: `MyTree` is positive
```

But a constructor that stores a *function out of* the type is rejected:

```
inductive Bad where
  | mk : (Bad → False) → Bad
-- error: (kernel) arg #1 of 'Bad.mk' has a non positive
--        occurrence of the datatypes being declared
```

The rejection is not pedantry: were `Bad` allowed, one could prove `False`. Project the stored function out of a `b : Bad` and apply it to `b` itself,

```
def app : Bad → (Bad → False) | .mk f => f
def neg (b : Bad) : False := app b b
```

so `neg : Bad → False`. Then `Bad.mk neg : Bad`, and `neg (Bad.mk neg) : False` is a closed proof of `False` (it even loops, `neg (Bad.mk neg) ⟶ neg (Bad.mk neg)` -- the untyped Ω combinator smuggled into the theory). Strict positivity outlaws exactly the negative occurrence that ties this self-applying knot -- the same consistency concern that rules out `Type : Type`. (That positivity is also *sufficient* for consistency -- every strictly positive type is the least fixed point of a monotone functor, so the theory has a model -- is a deep metatheorem, not something Lean proves about itself.)

# Structures
%%%
tag := "structures"
%%%

While inductive types let us define types with multiple constructors, many mathematical objects are better described as a *collection of named fields*. For example, a point in the plane has an `x`-coordinate and a `y`-coordinate. In Lean, we use `structure` for this.

A `structure` is a special case of an inductive type with exactly one constructor and named fields. Here is a simple example:

```lean
structure Point where
  x : ℕ
  y : ℕ
```

This declares a new type `Point` whose elements are records with two `ℕ` fields. (Both must be given in order to define a `Point`, which is the only way we can make such a Point, i.e. it only has a single constructor.) Like every declaration, it produces more than the type alone: a constructor `Point.mk` and one projection per field. We can inspect their types without building any value yet:

```lean
#check (Point.mk : ℕ → ℕ → Point)
#check (Point.x : Point → ℕ)
#check (Point.y : Point → ℕ)
```

Fields may be given *default values* as part of the declaration:

```lean
structure MyConfig where
  width : ℕ := 80
  height : ℕ := 24
  title : String := "Untitled"
```

These defaults are used whenever a value is built without specifying every field.

One structure can *extend* another, inheriting all of its fields:

```lean
structure Point3D extends Point where
  z : ℕ
```

so a `Point3D` has fields `x`, `y` (from `Point`) and `z`. This is particularly important in Mathlib, where the algebraic hierarchy uses structure extension extensively: `CommRing` extends `Ring`, which extends `Semiring`, and so on.

Structures are natural for representing mathematical objects. A *Gaussian integer* (a complex number with integer parts) is a pair of `ℤ`s,

```lean
structure MyComplex where
  re : ℤ
  im : ℤ
```

and a structure may bundle *data together with a property* -- here a linear map, carrying both a function and a proof that it respects addition (the square brackets `[Add α]` are an *instance-implicit* argument, requiring `α` to carry an addition; see {ref "square-bracket-notation"}[the typeclasses chapter]):

```lean
structure MyLinearMap (α β : Type) [Add α] [Add β] where
  toFun : α → β
  map_add : ∀ x y : α, toFun (x + y) = toFun x + toFun y
```

This pattern of bundling data with properties is fundamental to how Mathlib organizes mathematics.

How to *construct* values of these types, read their fields, and define operations on them is the subject of {ref "terms"}[the next chapter].

# Inductive types vs structures
%%%
tag := "inductive-vs-structure"
%%%

When should you use `inductive` and when `structure`?

* Use `structure` when your type has a single constructor with named fields. Examples: points, complex numbers, algebraic structures.
* Use `inductive` when your type has multiple constructors. Examples: natural numbers, lists, trees, `Option`, `Bool`.

A `structure` is syntactic sugar for an inductive type with one constructor. The definition

```
structure Point where
  x : ℕ
  y : ℕ
```

is essentially equivalent to

```
inductive Point where
  | mk : ℕ → ℕ → Point
```

but the `structure` version gives us named fields, {ref "structure-values"}[dot notation], the possibility for default values, and the `extends` mechanism. (A `class` is in turn a `structure` marked for use by instance search; we return to it in the {ref "typeclasses"}[Typeclass] chapter.)

# Quotient types
%%%
tag := "quotient-types"
%%%

Alongside universes, function types, and inductive types, Lean has one more basic way to *form* a type: the *quotient*. Given a type `α` and a relation `r : α → α → Prop`, the type `Quot r` glues together elements that `r` relates -- it is `α` "seen up to `r`". This is how the chapter's opening remark, that `ℝ` is Cauchy sequences up to an equivalence, becomes an actual construction; `ℤ`, `ℚ`, `Multiset α` (lists up to reordering), and `ZMod n` are quotients too.

Its entire interface is four constants:

```lean
#check @Quot.mk     -- (r : α → α → Prop) → α → Quot r
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#check @Quot.lift   -- (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
#check @Quot.ind
```

- `Quot.mk r` sends each element to its class.
- `Quot.sound` is the crux: if `r a b`, then the two classes are *the same term*. It is one of Lean's few genuine axioms -- the `#print axioms name` command traces a constant back to the axioms it depends on, and here `#print axioms Quot.sound` reports `[Quot.sound]`.
- `Quot.lift` defines a function *out of* the quotient -- but only once you *prove* it respects `r` (the `∀ a b, r a b → f a = f b` argument), which is exactly the mathematician's "check that this is well-defined". And it computes: `Quot.lift f h (Quot.mk r a)` reduces to `f a`.
- `Quot.ind` proves a property of every quotient element by checking it on the classes `Quot.mk r a`.

In practice one usually goes through `Quotient`, a thin wrapper of `Quot` over a bundled equivalence relation (a `Setoid`). The status of `Quot.sound` as an axiom is taken up again in the {ref "axiom-quot"}[axioms chapter].

::::keepEnv
:::example "How `ℝ` is built as a quotient"
Mathlib's real numbers are a concrete instance of exactly this construction. First, a `CauSeq` is a {ref "subtypes"}[*subtype*]: the notation `{ f : ℕ → ℚ // IsCauSeq abs f }` means a rational sequence `f : ℕ → ℚ` bundled with a proof that it is Cauchy.

```lean
#check (CauSeq ℚ abs)
-- CauSeq ℚ abs = { f : ℕ → ℚ // IsCauSeq abs f }
example (f : CauSeq ℚ abs) : ℕ → ℚ := f.1
```

`ℝ` is then a one-field structure wrapping the *quotient* of these sequences by the relation "the difference tends to `0`". The class map `CauSeq.Completion.mk` is the `Quot.mk` of that quotient:

```lean
#check @Real.ofCauchy
-- CauSeq.Completion.Cauchy abs → ℝ

#check @CauSeq.Completion.mk
-- CauSeq ℚ abs → CauSeq.Completion.Cauchy abs

-- two sequences give the same real iff (f - g) → 0;
-- `≈` is the Setoid equivalence relation on `CauSeq`
example (f g : CauSeq ℚ abs) :
    f ≈ g ↔ (f - g).LimZero := Iff.rfl
```

Addition is the payoff of `Quot.lift`. To add two reals you add *representative* sequences termwise -- but this is only well-defined because `+` respects the relation (if `f ≈ f'` and `g ≈ g'` then `f + g ≈ f' + g'`). Having checked that, `Quot.lift` hands you exactly the computation rule that `mk` is an additive homomorphism:

```lean
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

This `mk (f) + mk (g) = mk (f + g)` equation *is* the `Quot.lift f h (Quot.mk r a) ⟶ f a` reduction from the {ref "reduction-rules"}[reduction rules], applied to a two-argument operation.
:::
::::
