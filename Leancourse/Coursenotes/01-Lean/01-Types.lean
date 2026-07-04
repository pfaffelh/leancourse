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

:::collapsedDetails "The connection of `Type` to `Sort`"

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

Of particular interest is the type `Prop`, which consists of statements that can be `True` or `False`. It includes mathematical statements, so either the hypotheses, or the goal of what is to be proven. A hypothesis in Lean has the form `hP : P`, which means `P` is true, and this statement is called `hP`. Synonomously, it means that `P` is true and `hP` is a proof of `P`. The hypotheses here have names `P Q R S`, and the proofs of the hypotheses `hP hQ hR hS`. All names can be arbitrary. Furthermore, there are hypotheses of the form `P → Q`, which is the statement that `P` implies `Q`. (Note the similarity to function notation as in `f : ℝ → ℝ`.)

We can make one consequence of this concrete already. Because a `Prop` only records *that* a statement holds -- never *which* proof we chose -- the kernel treats any two proofs of the same proposition as equal. This is *proof irrelevance*, and it means the following goal closes by `rfl`:

```lean
example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := rfl
```

For data living in a `Type` there is no such collapse: two terms are equal only when they genuinely are. The syntactically identical statement about natural numbers therefore fails to typecheck, since `a` and `b` are not definitionally equal:

```lean +error
example (a b : ℕ) : a = b := rfl
```

*Why `Prop` is special.* `Prop` sits at the very bottom, `Sort 0`, and is set apart from every `Type u` by *proof irrelevance*: any two proofs of the same proposition are considered equal, because for a proposition we only care *that* it holds, not *which* proof we have (see {ref "prop-vs-type"}[Prop vs Type] in Part 2). It is also *impredicative*: a `∀`-statement quantifying over an arbitrarily large type is still just a `Prop`.

## How the universe of a type is determined
%%%
tag := "universe-determined"
%%%

You rarely write universe levels by hand -- Lean computes the universe of a compound type from the universes of its parts. A function type `α → β` lands in the *larger* of the two universes involved:

```lean
#check (ℕ → ℕ)        -- Type
#check (ℕ → Type)     -- Type 1  (because `Type : Type 1`)
```

The impredicativity of `Prop` shows up here: as soon as the *codomain* is a proposition, the whole function type collapses back into `Prop`, no matter how big the domain is:

```lean
#check (ℕ → Prop)              -- Type  (a family of propositions)
#check (∀ n : ℕ, n = n)        -- Prop  (a single proposition)
#check (∀ α : Type, α → α)     -- Prop  (still just a proposition!)
```

The last line is the striking case: `∀ α : Type, α → α` quantifies
over *every* type, yet the statement itself is an ordinary `Prop`.
(A definition can be made to work at *any* universe level at once; that
uses `def`, so we defer it to the {ref "polymorphic-functions"}[chapter
on functions].)

# Inductive types
%%%
tag := "inductive"
%%%

Many everyday types in Lean -- `Nat`, `List`, `Option`, `Bool`, even
`Empty` -- are *inductive* types. You declare one by giving a name,
the type's universe, and a list of *constructors*: each constructor
says how to build a new element of the type out of existing pieces.

The classical example is the natural numbers:

```lean
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
```

This declaration introduces three things at once:

- a new type `MyNat`;
- two constructors `MyNat.zero` and `MyNat.succ`, so every element of
  `MyNat` is either `zero` or `succ n` for some `n`;
- a *recursor* `MyNat.rec` which lets you define functions on `MyNat`
  by specifying what happens in each constructor case.

Definitions on an inductive type are typically written with the
pattern-matching syntax from the {ref "functions"}[chapter on
functions]:

```lean
def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))
```

The leading dot in `.zero` and `.succ` is *anonymous constructor
notation*: because Lean already knows from the type that the result
must be a `MyNat`, we may write `.zero` in place of the full
`MyNat.zero`. Writing plain `zero` would fail -- there is no `zero` in
scope, only `MyNat.zero`.

Proofs about an inductive type use the `induction` tactic, which
applies the recursor for you: one subgoal per constructor, with an
induction hypothesis for each recursive argument.

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

Inductive types are the main mechanism by which new data types enter
Lean; `Mathlib` uses them extensively, and understanding them is
essential for reading the library. This also answers the question of
the previous section from the other side: the universe of an inductive
type must be large enough to hold all of its constructor arguments.

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

This defines a type `Point` with two fields, `x` and `y`, both of type `Float`. We create values of type `Point` using anonymous constructor syntax or by naming the constructor explicitly:

```lean
def origin : Point := { x := 0.0, y := 0.0 }
def p1 : Point := ⟨1.0, 2.5⟩
def p2 : Point := Point.mk 3.0 4.0
```

All three syntaxes create a `Point`. The angle brackets `⟨...⟩` (typed `\<` and `\>`) are the anonymous constructor.

We access fields using dot notation:

```lean
#eval p1.x          -- outputs 1.0
#eval p1.y          -- outputs 2.5
```

We can also define functions in the `Point` namespace, and then call them with dot notation:

```lean
def Point.distToOrigin (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval p2.distToOrigin    -- outputs 5.0
```

This works because Lean sees that `p2` has type `Point`, so it looks for `Point.distToOrigin`.

We can create a new structure value based on an existing one, changing only some fields. This uses the `with` keyword:

```lean
def p3 : Point := { p1 with y := 10.0 }
-- p3.x = 1.0, p3.y = 10.0
```

Since structures are immutable (as everything in functional programming), this creates a new `Point` rather than modifying `p1`.

Fields can have default values:

```lean
structure MyConfig where
  width : ℕ := 80
  height : ℕ := 24
  title : String := "Untitled"

def myConfig : MyConfig := { title := "My Window" }
-- myConfig.width = 80, myConfig.height = 24
```

One structure can extend another, inheriting all of its fields:

```lean
structure Point3D extends Point where
  z : Float

def q : Point3D := { x := 1.0, y := 2.0, z := 3.0 }

#eval q.x    -- outputs 1.0 (inherited from Point)
#eval q.z    -- outputs 3.0
```

This is particularly important in Mathlib, where the algebraic hierarchy uses structure extension extensively. For example, `CommRing` extends `Ring`, which extends `Semiring`, and so on.

Structures are natural for representing mathematical objects. Here is a complex number type:

```lean
structure MyComplex where
  re : Float
  im : Float

def MyComplex.add (a b : MyComplex) : MyComplex :=
  { re := a.re + b.re, im := a.im + b.im }

def MyComplex.mul (a b : MyComplex) : MyComplex :=
  { re := a.re * b.re - a.im * b.im,
    im := a.re * b.im + a.im * b.re }

def MyComplex.norm (a : MyComplex) : Float :=
  Float.sqrt (a.re * a.re + a.im * a.im)

def i : MyComplex := { re := 0.0, im := 1.0 }
def oneComplex : MyComplex := { re := 1.0, im := 0.0 }

#eval (MyComplex.mul i i).re    -- outputs -1.0
```

Here is a structure representing a linear map between two types that have addition and scalar multiplication:

```lean
structure MyLinearMap (α β : Type) [Add α] [Add β] [HMul ℕ α α] [HMul ℕ β β] where
  toFun : α → β
  map_add : ∀ x y : α, toFun (x + y) = toFun x + toFun y
```

Notice that the structure contains both data (the function `toFun`) and a property (`map_add`). This pattern of bundling data with properties is fundamental to how Mathlib organizes mathematics.

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
