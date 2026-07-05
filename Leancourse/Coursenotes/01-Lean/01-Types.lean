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

As we see, these new data types are more abstract in the sense that Lean understands `ℕ` (and `ℝ`) as infinite types, which are not limited by floating point arithmetic. E.g., `ℕ` actually represents an infinite set that is characterized by containing `0`, and if it contains `n`, then it also contains the successor of `n` (represented by `succ n`). (Frequently, this construction is attributed to Giuseppe Peano.) Accordingly, the real numbers are defined by an equivalence relation on Cauchy sequences, which is quite elaborate. (Although `ℝ` is implemented as such a quotient within `Lean`, we will not have to deal with these implementation details when working with real numbers, since we will rely on results in `Mathlib`, the mathematical library, taking care of these details.)

In Lean, all objects are terms, and every term needs a type. Interestingly, since a type is also some term in the language, it needs a type as well. This leads to a hierarchy of these types.

# The universe hierarchy
%%%
tag := "type-universes"
%%%

Every term has a type; but a type is itself a term of some type. To keep the system consistent, these type-of-a-type (also called universes) are organized into a countably infinite hierarchy.

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

*Why `Prop` is special.*
Of particular interest is the type `Prop`, which consists of statements that can be `True` or `False`. It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. Synonomously, it means that `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the proofs of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`. (Note the similarity to function notation as in `f : ℝ → ℝ`.)

We note three specifics which only apply to `Prop`:

*Proof irrelevance*: Note that `Prop` only records *that* a statement holds, but not *which* proof we chose. This is *proof irrelevance*, which means the following goal closes by `rfl`:

```lean
example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl
```

For data living in a `Type` there is no such collapse, for obvious reasons. (The red squiggly line indicates an error, i.e. a proof which does not work.)

```lean +error
example (a b : ℕ) : a = b := rfl
```
See also {ref "prop-vs-type"}[Prop vs Type].

*`Prop` is impredicative*: As long as the body of a `∀` statement is a proposition, the whole `∀` is a `Prop` -- even when we range over an arbitrarily large universe of types:

```lean
-- Prop-valued body: stays `Prop`, however big the domain.
#check (∀ α : Type, α = α)     -- Prop
#check (∀ α : Type 5, α = α)   -- Prop
```

No `Type u` behaves this way. Replace the proposition `α = α` by `α → α`, and the universe of the `∀` is forced to grow with the domain, exactly as predicativity demands:

```lean
-- Type-valued body: the universe grows with the domain.
#check (∀ α : Type, α → α)     -- Type 1
#check (∀ α : Type 5, α → α)   -- Type 6
```

So the two syntactically parallel statements `∀ α : Type 5, α = α` and `∀ α : Type 5, α → α` land in wildly different places -- `Prop` versus `Type 6` -- purely because the first has a `Prop` body and the second a `Type` body. This asymmetry (a `∀` into `Prop` stays small; a `∀` into `Type u` must climb) is exactly what it means to say *`Prop` is impredicative and the `Type u` are predicative*.

(A definition can be made to work at *any* universe level at once; that uses `def`, so we defer it to the {ref "polymorphic-functions"}[chapter on functions].)

*Restricted (subsingleton) elimination*: A proof carries no observable content, so Lean forbids *reading data off a proof* by case analysis -- otherwise a value could depend on *which* proof we had, which proof irrelevance declares meaningless. Eliminating a proposition may therefore, in general, only produce further propositions, not data. Deciding as a `Bool` which side of a disjunction holds is rejected:

```lean +error
example (a b : Prop) (h : a ∨ b) : Bool :=
  match h with
  | Or.inl _ => true
  | Or.inr _ => false
```

The error is telling: `recursor 'Or.casesOn' can only eliminate into 'Prop'`. The one exception is *subsingleton elimination*: a proposition with *at most one constructor*, all of whose fields are *themselves proofs*, provably has at most one inhabitant -- so eliminating it can reveal nothing, and Lean does allow it into *any* type. This covers `False` (no constructors, which is exactly why `False.elim` closes *any* goal), `Eq` (which is why we may `rw` even inside data-carrying goals), and `And` (both fields are proofs); but not `Or` (two constructors) nor `∃` (its first field is a genuine witness, not a proof). None of this restriction applies to `Type`: an inductive type in `Type` always eliminates into anything.

Why must it be this way? It is not bureaucracy -- consistency forces it, and for `Or` the argument is a little gem. What cannot escape here is not a *witness* (as it would be for `∃`) but the *tag*: the information *which* of the two branches holds. Take a true `a` and look at the proposition `a ∨ a`. Its two opposite injections are definitionally equal, by proof irrelevance:

```lean
example {a : Prop} (h : a) :
    (Or.inl h : a ∨ a) = Or.inr h := rfl
```

"Left or right?" is simply not a well-posed question about a proof of `a ∨ a` -- the tag does not exist as distinguishable content. So had the rejected `(a ∨ b) → Bool` above been allowed, then with `b := a` it would give `which (Or.inl h) = true` and `which (Or.inr h) = false`; but `Or.inl h ≡ Or.inr h`, so `true ≡ false` -- a contradiction. The indistinguishability of proofs forces the tag to stay trapped, exactly as it would have forced `3 ≡ 5` for a leaked `∃`-witness.

The escape mirrors the one for `∃`, one level up. The data-carrying counterpart of `a ∨ ¬a` is `Decidable a`, which -- crucially -- lives in `Type`, not `Prop`:

```
inductive Decidable (p : Prop) : Type where
  | isFalse (h : ¬p)
  | isTrue  (h :  p)
```

Because `Decidable p` is in `Type`, it *may* eliminate into `Type` -- which is exactly why `if h : p then _ else _` and `decide` compute. The two stories line up exactly:

:::table (align := left) +header
* + Proposition (in `Prop`)
  + Data version (in `Type`)
  + what stays hidden
* + `∃ x, q x`
  + `Σ x, q x`
  + the *witness*
* + `a ∨ ¬a`
  + `Decidable a`
  + the *tag* (which side)
:::

And the classical route mirrors `Classical.choose` precisely: `Classical.em : a ∨ ¬a` is always available (a `Prop`), but its data-carrying counterpart `Classical.propDecidable : Decidable a` goes through `Classical.choice` and is therefore `noncomputable`. The two halves -- `∃`/`Σ`/`choose` about the *witness*, `∨`/`Decidable`/`em` about the *tag* -- are one and the same story: computationally relevant information can leave the `Prop` world only if you place it in `Type` from the start, or pay for it noncomputably with the axiom of choice. (The `Nonempty`/`Classical.choice` version of this is taken up in the {ref "curry-howard"}[chapter on propositions and proofs].)

## How the universe of a type is determined
%%%
tag := "universe-determined"
%%%

You rarely write universe levels by hand -- Lean computes the universe of a compound type from the universes of its parts. A function type `α → β` lands in the *larger* of the two universes involved:

```lean
#check (ℕ → ℕ)        -- Type
#check (ℕ → Type)     -- Type 1  (because `Type : Type 1`)
```

# Inductive types
%%%
tag := "inductive"
%%%

Many everyday types in Lean -- `Nat`, `List`, `Option`, `Bool`, even `Empty` -- are *inductive* types. You declare one by giving a name, the type's universe, and a list of *constructors*: each constructor says how to build a new element of the type out of existing pieces.

The classical example is the natural numbers:

```lean
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
```

This declaration introduces three things at once:

- a new type `MyNat`;
- two constructors `MyNat.zero` and `MyNat.succ`, so every element of `MyNat` is either `zero` or `succ n` for some `n`;
- a *recursor* `MyNat.rec` which lets you define functions on `MyNat` by specifying what happens in each constructor case.

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

# Structures
%%%
tag := "structures"
%%%

While inductive types let us define types with multiple constructors, many mathematical objects are better described as a *collection of named fields*. For example, a point in the plane has an `x`-coordinate and a `y`-coordinate. In Lean, we use `structure` for this.

A `structure` is a special case of an inductive type with exactly one constructor and named fields. Here is a simple example:

```lean
structure Point where
  x : Float
  y : Float
```

This declares a new type `Point` whose elements are records with two `Float` fields. Like every declaration, it produces more than the type alone: a constructor `Point.mk` and one projection per field. We can inspect their types without building any value yet:

```lean
#check (Point.mk : Float → Float → Point)
#check (Point.x : Point → Float)
#check (Point.y : Point → Float)
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
  z : Float
```

so a `Point3D` has fields `x`, `y` (from `Point`) and `z`. This is particularly important in Mathlib, where the algebraic hierarchy uses structure extension extensively: `CommRing` extends `Ring`, which extends `Semiring`, and so on.

Structures are natural for representing mathematical objects. A complex number is a pair of `Float`s,

```lean
structure MyComplex where
  re : Float
  im : Float
```

and a structure may bundle *data together with a property* -- here a linear map, carrying both a function and a proof that it respects addition:

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
  x : Float
  y : Float
```

is essentially equivalent to

```
inductive Point where
  | mk : Float → Float → Point
```

but the `structure` version gives us named fields, dot notation, default values, and the `extends` mechanism. (A `class` is in turn a `structure` marked for use by instance search; we return to it in the {ref "typeclasses"}[Typeclass] chapter.)
