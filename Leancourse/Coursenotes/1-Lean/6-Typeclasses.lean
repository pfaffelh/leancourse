import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Typeclasses" =>
%%%
htmlSplit := .never
tag := "typeclasses"
%%%

A typeclass associates operations and properties with a type and lets Lean find the right implementation on its own. It is the mechanism by which Lean knows that the integers form a ring and the reals a field, and it is how Mathlib organizes mathematics.

The chapter is read in two lectures. The second begins at {ref "type-constructor-classes"}[Classes over type constructors]. Each lecture has its slides: [first lecture](slides/1-6-typeclasses/), [second lecture](slides/1-6b-functors-monads/).

# The problem typeclasses solve
%%%
tag := "typeclass-motivation"
%%%

Consider the `+` operator. It works on natural numbers, integers, real numbers, matrices, polynomials, and many other types. How does Lean know which `+` to use?

One approach would be to define different functions: `addNat`, `addInt`, `addReal`, etc. But that would be extremely tedious. Instead, Lean uses typeclasses: there is a single `Add` typeclass, and each type that supports addition provides an `instance` of `Add`.

When you write `a + b`, Lean looks at the types of `a` and `b`, finds the appropriate `Add` instance, and uses it. This process is called *instance resolution* and happens automatically.

# Defining typeclasses
%%%
tag := "defining-typeclasses"
%%%

A typeclass is defined using the `class` keyword. Here is a simplified version of how `Add` might be defined:

```lean
class MyAdd (α : Type) where
  myAdd : α → α → α
```

This says: for any type `α`, an instance of `MyAdd α` provides a function `myAdd : α → α → α`. The `class` keyword is *almost* the same as `structure` — in fact, every `class` is internally a `structure`. The difference is operational:

- A `structure` is constructed and passed *explicitly*: you write `⟨...⟩` or call its named projections.
- A `class` is also a structure, but Lean's *instance resolution* will synthesize one for you whenever a function expects an `[Add α]` argument. You never write the instance argument by hand.

Use `structure` when the value is data the user manipulates: a `Point`, a `Person`, a `RingHom`. Use `class` when it is a *canonical* piece of structure attached to a type — a `Group` on `ℤ`, an `Add` on `ℕ` — that Lean should find on its own.

# Data classes and Prop classes
%%%
tag := "class-universe"
%%%

Because a `class` is a `structure`, the applied class `C α` is an ordinary *type*, and an *instance* is simply a *term* of that type. Its universe follows the same rule as any {ref "structures"}[structure] — the largest universe among its fields — and this splits typeclasses into two kinds.

*Data classes* bundle operations, so they carry `Type`-valued fields and live in `Type`. Their instances are *data*: a record of operations and proofs, carried at runtime and projected like any structure.

```lean
#check (Add ℕ)                    -- Type
#check (inferInstance : Add ℕ)    -- a term of it: data
```

(`inferInstance` stands for the instance that Lean finds by itself.)

*Prop classes* have only propositional fields, so they live in `Prop`, and their instances are *proofs*. Mathlib's `Fact` is the standard example: it packages a proof of `p` as an instance that instance search can find ({ref "fact"}[Propositions as instances] below).

```lean
#check @Fact                          -- Prop → Prop
```

Being a proposition, a `Prop` class inherits {ref "prop-special"}[proof irrelevance]: any two instances are definitionally equal. That is a feature — such an instance can never *conflict* with another, and it is erased at runtime.

```lean
example (h₁ h₂ : Fact (2 = 2)) : h₁ = h₂ := rfl
```

Typeclasses inherit the *proof* / *data* split drawn for terms in general: an instance is data or a proof exactly according to whether its class lives in `Type` or `Prop`.

An instance is a term you construct: that is what `instance … where …` does, and its fields are values you can project and run. You then use it as a *property of the type* — declared once, synthesized wherever `[C α]` is required, rarely named or passed by hand. For a data class it stays data, carried at runtime; for a `Prop` class it is a proof and is erased. So "an instance is only a property, not a term" describes the usage, not the substance: the term is there, and its construction is delegated to instance resolution.

The parallel holds at the term level: `class` is a `structure` marked for instance search, and `instance` is a `def` marked for instance search, with `instance foo : C := …` sugar for `@[instance] def foo : C := …`. A plain `def` of a class type is a perfectly good term, only invisible to the search.

:::table (align := left) +header
* + Level
  + plain
  + registered for search
* + type (constructor)
  + `structure`
  + `class`
* + term (value)
  + `def`
  + `instance`
:::

*Typeclasses add nothing to the logic.* The {ref "kernel-elaborator"}[kernel] knows neither `class` nor `instance`: a class is a structure, an instance is a definition, and `[C α]` is an ordinary argument of a function type. Instance resolution runs in the elaborator, which writes the instance it finds into the term, and the kernel checks that term like any other. The option `pp.explicit` shows the filled-in term:

```lean
set_option pp.explicit true in
#check fun (n : ℕ) => n + 1
-- fun n => @HAdd.hAdd ℕ ℕ ℕ (@instHAdd ℕ instAddNat) n
--   (@OfNat.ofNat ℕ 1 (instOfNatNat 1))
```

So typeclasses cannot make Lean inconsistent, and they use no axiom. What an instance does decide is what a statement *means*: `≤` and `+` stand for whatever instance is found. On `ℕ × ℕ` the order found is the componentwise one, so `(1, 5) ≤ (2, 0)` is false. The lexicographic order lives on the type `Lex (ℕ × ℕ)`, which has the same elements and a different instance:

```lean
example : ¬ ((1, 5) ≤ ((2, 0) : ℕ × ℕ)) := by decide
example : toLex (1, 5) ≤ (toLex (2, 0) : Lex (ℕ × ℕ)) := by
  decide
```

Reading a formal statement therefore includes knowing which instance its notation refers to.

# Creating instances
%%%
tag := "creating-instances"
%%%

We create instances using the `instance` keyword:

```lean
instance : MyAdd ℕ where
  myAdd := Nat.add

instance : MyAdd ℤ where
  myAdd := Int.add
```

Now we can use `MyAdd.myAdd` on natural numbers and integers, and Lean will automatically find the right instance.

Let us define a custom type and give it an `Add` instance:

```lean
structure Vec2 where
  x : Float
  y : Float

instance : Add Vec2 where
  add a b := { x := a.x + b.x, y := a.y + b.y }

instance : ToString Vec2 where
  toString v := s!"({v.x}, {v.y})"

#eval (⟨1.0, 2.0⟩ : Vec2) + ⟨3.0, 4.0⟩    -- outputs (4.0, 6.0)
```

We defined two instances: `Add Vec2` so we can use `+`, and `ToString Vec2` so Lean can print `Vec2` values.

# Using `deriving`
%%%
tag := "deriving"
%%%

Writing instances by hand is not always necessary: for a range of
standard typeclasses Lean can generate the instance automatically, if
you append a `deriving` clause to the type definition.

```lean
structure Student where
  name : String
  age : ℕ
  deriving Repr

def alice : Student := { name := "Alice", age := 22 }
#eval alice    -- outputs { name := "Alice", age := 22 }
```

Without `deriving Repr`, the `#eval` command would not know how to print a `Student`. The `deriving` clause tells Lean to automatically create a `Repr` instance. Here is what the commonly derived classes provide:

:::table +header
* + Typeclass
  + What it provides
* + `Repr`
  + a way to *display* a value (needed by `#eval`)
* + `BEq`
  + Boolean equality `a == b`
* + `Hashable`
  + a hash function (for use in hash maps/sets)
* + `Inhabited`
  + a designated *default* value `default : α`
* + `DecidableEq`
  + a *decidable* equality test `a = b` (returns a proof either way)
:::

Several instances can be derived at once:

```lean
structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr, BEq, Hashable
```

`deriving` is not part of the type theory. For each class that supports it, Lean has a *deriving handler*: a program, written in Lean, that runs when the type is declared. It reads the declaration of the type from the environment, its constructors and their fields, and writes the source code of an `instance`. That code is then elaborated and checked like an instance written by hand. The option `trace.Elab.Deriving.repr` prints what the handler writes for `Student`; slightly simplified:

```
def instReprStudent.repr (x : Student) (prec : Nat) : Format :=
  Format.bracket "{ "
    ("name" ++ " := " ++ repr x.name ++ "," ++ Format.line ++
     "age" ++ " := " ++ repr x.age)
    " }"

instance instReprStudent : Repr Student :=
  ⟨instReprStudent.repr⟩
```

The handler for `Repr` writes one line per field. The handler for `DecidableEq` writes a function that compares the constructors of the two arguments and then their fields, with a proof of equality or of inequality in each branch. The result is an ordinary definition with an ordinary name:

```lean
#print instReprStudent
```

Nothing in a handler has to be trusted. If it wrote wrong code, the elaborator or the kernel would reject it, as they reject any wrong definition. The instance appears as a definition in the environment, and `#print axioms` shows which axioms it uses; for a derived `DecidableEq` there are none. Lean has handlers for the classes in the table above and a few more, and libraries can register their own. For a type that is already declared, `deriving instance Repr for Student` does the same afterwards.

# The square bracket notation
%%%
tag := "square-bracket-notation"
%%%

When a function needs a typeclass instance, we use square brackets `[...]` in its signature:

```lean
def doubleIt [Add α] (x : α) : α := x + x

#eval doubleIt 5        -- outputs 10
#eval doubleIt (3 : ℤ)  -- outputs 6
```

The `[Add α]` argument tells Lean: "find an `Add` instance for `α` automatically." We do not need to pass it explicitly; Lean's instance resolution handles it.

You can name the instance if you need to refer to it:

```lean
def tripleIt [inst : Add α] (x : α) : α := inst.add x (inst.add x x)
```

But usually the unnamed form `[Add α]` is preferred, since Lean resolves it behind the scenes.

So `[...]` is the *typeclass bracket*: it marks an instance argument, filled by instance search — as opposed to `(...)`, which you supply yourself, and `{...}`, which Lean infers by unification. The four kinds of binder brackets `()`, `{}`, `⦃⦄`, and `[]` are contrasted side by side in {ref "parenthesis"}[the appendix on parentheses].

# Inspecting typeclass arguments with `@`
%%%
tag := "inspecting-typeclasses"
%%%

When working with Mathlib, it is often useful to see all the implicit and typeclass arguments of a lemma. The `@` symbol makes all arguments explicit:

```
#check mul_comm
-- mul_comm : ∀ {M : Type u_1} [inst : CommMonoid M] (a b : M), a * b = b * a
```

```
#check @mul_comm
-- @mul_comm : ∀ {M : Type u_1} → CommMonoid M → M → M → M = M
```

The first form shows `[inst : CommMonoid M]` in brackets, meaning it is found automatically. The `@` version shows all arguments explicitly, which helps understand exactly what typeclass constraints are required.

# Defining multiple instances
%%%
tag := "multiple-instances"
%%%

Let us build a more complete example. We define a type `Mod3` representing integers modulo 3, and equip it with algebraic structure:

```lean
inductive Mod3 where
  | zero | one | two
  deriving Repr, BEq

instance : Add Mod3 where
  add
    | Mod3.zero, b => b
    | a, Mod3.zero => a
    | Mod3.one, Mod3.one => Mod3.two
    | Mod3.one, Mod3.two => Mod3.zero
    | Mod3.two, Mod3.one => Mod3.zero
    | Mod3.two, Mod3.two => Mod3.one

instance : Mul Mod3 where
  mul
    | Mod3.zero, _ => Mod3.zero
    | _, Mod3.zero => Mod3.zero
    | Mod3.one, b => b
    | a, Mod3.one => a
    | Mod3.two, Mod3.two => Mod3.one

instance : Zero Mod3 where
  zero := Mod3.zero

instance : One Mod3 where
  one := Mod3.one

#eval (Mod3.two + Mod3.two : Mod3)    -- outputs Mod3.one
#eval (Mod3.two * Mod3.two : Mod3)    -- outputs Mod3.one
```

# How instance resolution works
%%%
tag := "instance-resolution"
%%%

When Lean encounters an expression like `a + b` where `a b : α`, it needs to find an instance of `Add α`. The resolution proceeds as follows:

1. Lean looks through all registered instances (those declared with `instance`).
2. It tries to unify the goal `Add α` with the type of each instance.
3. If an instance itself requires other instances (e.g., `Add (Prod α β)` might require `Add α` and `Add β`), Lean recursively resolves those.
4. Lean uses the first chain of instances that leads to a solution, trying instances of higher priority first and, among equal priorities, the more recently declared ones first. If no chain exists, it reports an error. Several solutions are no error, so different instances for the same type had better agree ({ref "typeclass-diamonds"}[Typeclass diamonds]).

This process is deterministic and happens at {ref "kernel-elaborator"}[elaboration time] (when Lean checks your code), not at runtime. So there is no performance penalty.

You can trigger instance resolution yourself with the term
`inferInstance`, which asks Lean to synthesize an instance of a stated
type — a handy way to ask "does this type have that structure?":

```lean
-- "Does ℕ have an AddCommMonoid instance?" -- yes.
#check (inferInstance : AddCommMonoid ℕ)
```

If no such instance exists, the command fails with a readable error
message. This is exactly the mechanism the `[...]` arguments rely on
behind the scenes.

# Output parameters
%%%
tag := "outparam"
%%%

By default, instance search treats *all* of a class's arguments as search keys: it must know them to look up an instance. Occasionally one argument is *determined by* the instance rather than given in advance. Marking it `outParam` tells Lean: do not wait for this argument — find the instance from the others, and *read this one off* the result.

The standard example is heterogeneous multiplication `a * b`, whose result type need not match the arguments:

```lean
#check @HMul
-- HMul : Type → Type → outParam Type → Type
```

Because the result `γ` is an `outParam`, Lean resolves `HMul α β ?γ` from `α` and `β` alone and *learns* `γ` from the chosen instance. The same device lets `a ∈ s` infer the element type from the collection — `Membership`'s element type is an `outParam` too. This is why you often see it in Mathlib signatures.

# Propositions as instances: `Fact`
%%%
tag := "fact"
%%%

Instance search finds terms of classes, and nothing else. A hypothesis `hp : p.Prime` is invisible to it, because `Nat.Prime` is a definition and not a class. Sometimes an instance needs such a proposition all the same, and Mathlib's `Fact` turns the proposition into a class:

{docstring Fact}

`Fact p` is a structure with the single field `out : p`, so an instance of `Fact p` is a proof of `p` that instance search can find. The standard case is the one in the docstring. `ZMod p` is a field only for prime `p`, and the field instance asks for primality as an instance argument:

```lean
#check @ZMod.instField
-- (p : ℕ) → [hp : Fact (Nat.Prime p)] → Field (ZMod p)
```

There are three things to do with a `Fact`.

*Require it*, as a hypothesis in square brackets, and read the proof back with `Fact.out`:

```lean
example (p : ℕ) [Fact p.Prime] : 2 ≤ p :=
  (Fact.out : p.Prime).two_le
```

*Provide it for a concrete value*, as an instance. Then `ZMod 7` is a field, and field lemmas such as `mul_inv_cancel₀` apply:

```lean
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

example (a : ZMod 7) (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha
```

*Provide it inside a proof*, from a hypothesis. A `have` whose type is a class adds a local instance, which instance search uses for the rest of the proof:

```lean
example (p : ℕ) (hp : p.Prime) (a : ZMod p)
    (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  exact mul_inv_cancel₀ ha
```

Without the `have`, the proof fails, and the error does not name the missing `Fact`. Lean finds no `Field (ZMod p)` and reports a type mismatch between the `⁻¹` of `ZMod p` and the `⁻¹` of a field:

```lean +error
example (p : ℕ) (hp : p.Prime) (a : ZMod p)
    (ha : a ≠ 0) : a * a⁻¹ = 1 :=
  mul_inv_cancel₀ ha
```

The warning at the end of the docstring means: instance search does not reason. From `Fact (p = 7)` it does not conclude `Fact p.Prime`; every `Fact` that is needed has to be supplied in exactly the form the instance asks for. Mathlib uses `Fact` for a few such side conditions: besides primality mostly `Fact (1 ≤ p)` for the `Lᵖ` spaces, and the dimension of a Euclidean space in geometry.

# Where numerals come from (`OfNat`)
%%%
tag := "ofnat"
%%%

Even a plain numeral is resolved through a typeclass. Writing `2` is sugar for `OfNat.ofNat 2`:

```lean
#check @OfNat.ofNat
-- {α : Type} → (n : ℕ) → [OfNat α n] → α
```

So `(2 : α)` means "the element of `α` denoted by the numeral `2`", available for any `α` that has an `OfNat α 2` instance. That is why the same `2` works across types,

```lean
#check (2 : ℤ)
#check (2 : ℝ)
```

and why you can give a numeral to your own type simply by providing the instance:

```lean
structure Countdown where
  val : Nat

instance (n : Nat) : OfNat Countdown n where
  ofNat := ⟨n⟩

#eval (5 : Countdown).val    -- 5
```

The instance decides what a numeral means. In {ref "pi-types"}[Dependent functions], `#eval` printed `2` for `(7 : ZMod 5)`. `#synth` names the instance Lean finds:

```lean
#synth OfNat (ZMod 5) 7   -- instOfNatAtLeastTwo
```

This instance exists for every type with a cast from ℕ and turns the numeral `7` into `Nat.cast 7`. Mathlib defines the cast into `ZMod (n + 1)` as the cast into `Fin (n + 1)`, and that takes the remainder: `Fin.ofNat n i` is `⟨i % n, _⟩`. So `(7 : ZMod 5)` is `⟨7 % 5, _⟩`, and `rfl` sees it:

```lean
example : (7 : ZMod 5) = 2 := rfl
```

# The `Decidable` typeclass
%%%
tag := "decidable-typeclass"
%%%

`Decidable` sits at the border between *programs* and *proofs*. It has
two constructors, `isTrue h` with a proof `h : P` and `isFalse h` with
a proof `h : ¬P`. An element of `Decidable P` is therefore the
information *which* of the two cases holds, together with a proof.
Programs branch on that information, so the class lives in `Type`, not
`Prop`:

```lean
#check @Decidable
-- Decidable : Prop → Type

-- Many concrete propositions are decidable, and the
-- instance is found by typeclass resolution:
#check (inferInstance : Decidable (2 + 3 = 5))  -- isTrue ..
#check (inferInstance : Decidable (2 + 3 = 6))  -- isFalse ..
```

Two everyday features rest on this instance search:

* An `if P then _ else _` requires a `Decidable P` instance — that is
  how the program knows which branch to take. This is also why
  {ref "deriving"}[`deriving DecidableEq`] (above) is useful: it makes
  `a = b` decidable, so you may branch on equality of your own type.
* The `decide` tactic closes any goal whose proposition is decidable,
  simply by running that algorithm and checking the answer is
  `isTrue`:

```lean
example : 2 + 3 = 5 := by decide
example : ¬(2 + 3 = 6) := by decide
```

An instance can be written by hand. Decidability of "is `n` zero?", by cases on `n`:

```lean
def decZero (n : Nat) : Decidable (n = 0) :=
  match n with
  | 0     => isTrue rfl                    -- a proof that 0 = 0
  | m + 1 => isFalse (Nat.succ_ne_zero m)  -- a proof that m + 1 ≠ 0
```

Each branch supplies a proof, which is why `Decidable` lives in `Type` and carries content. Registered as an `instance`, `decZero` is what `decide` runs and what `if n = 0 then … else …` consults. `deriving DecidableEq` generates such a definition for you.

*A single proposition or a family.* For a single proposition, `Decidable P` asks for no more than a proof of `P` or a proof of `¬P`, and this needs no axiom:

```lean
def decOfProof {P : Prop} (h : P) : Decidable P := isTrue h
```

Decidability says something only for a *family* of propositions. `decZero` above is one function that, for every `n`, computes which case holds. The classes `DecidablePred p` (a `Decidable (p a)` for every `a`) and `DecidableEq α` (a `Decidable (a = b)` for all `a b : α`) ask for such a function. `n % 2 = 0` is decidable in this sense: compute the remainder. Equality of real numbers is not. A real number is given by a Cauchy sequence, and no finite part of the sequence settles whether its limit is `0`. For each single `x` one of `x = 0` and `x ≠ 0` holds, but no algorithm finds out which.

Mathlib nevertheless has an instance of `DecidableEq ℝ`. It is built from the axiom of choice and computes nothing, so a definition that branches on `x = 0` cannot be compiled:

```lean +error
def realIsZero (x : ℝ) : Bool :=
  if x = 0 then true else false
```

The error is `failed to compile definition, consider marking it as 'noncomputable'`. Decidability by an algorithm is the *constructive* half: it works without axioms, and the resulting code is executable. Where no algorithm exists, the instance comes from the axiom of choice.

## The `classical` tactic
%%%
number := false
tag := "classical-tactic"
%%%

The axiom `Classical.choice` (chapter {ref "rules"}[1.5]) gives a `Decidable` instance for every proposition:

```lean
#check @Classical.propDecidable
-- Classical.propDecidable : (a : Prop) → Decidable a
```

It is not an algorithm, only a choice of `isTrue` or `isFalse` that exists by the axiom. It is therefore `noncomputable`, and it is not a global instance. The tactic `classical` makes it a local instance, with low priority, for the rest of the proof. Instances that exist, such as decidable equality on `ℕ`, are still found first.

```lean
example (P : ℕ → Prop) (s : Finset ℕ) :
    ∃ t : Finset ℕ, t ⊆ s ∧ ∀ x ∈ t, P x := by
  classical
  refine ⟨s.filter P, Finset.filter_subset P s, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2
```

`s.filter P` needs `DecidablePred P`. Without the line `classical`, the `refine` fails with `failed to synthesize DecidablePred P`.

Three rules decide where the instance comes from:

* *In a proof*, write `classical`.
* *In a statement*, `classical` comes too late: the statement is elaborated before the proof starts. `(s.image f).card ≤ s.card` needs `DecidableEq β` already in the statement, so the instance is a hypothesis: `[DecidableEq β]`. Whoever uses the result supplies the instance they have.
* *In a definition*, write `open Classical in` in front of it. The definition is then `noncomputable`.

`by_cases h : P` needs none of this: it falls back to the excluded middle by itself.

Mathlib avoids `open Classical` for a whole file. With it, a term may carry the classical instance where a lemma carries the real one. The two are equal, since any two terms of `Decidable P` are, but not syntactically equal, and `rw` and `simp` then fail to match.

# Classes over type constructors
%%%
tag := "type-constructor-classes"
%%%

The classes so far take a type: `Add ℕ`, `Decidable (2 + 3 = 5)`. A class can also take a *type constructor*, a function `Type → Type` such as `Option` or `List`. The two most important are `Functor` and `Monad`.

```lean
#check (Functor : (Type → Type) → Type 1)
#check (Monad : (Type → Type) → Type 1)
```

## Functor
%%%
number := false
tag := "functor-typeclass"
%%%

A `Functor f` provides

* `map : (α → β) → f α → f β`, written `g <$> x`.

It applies a function to what is inside, without changing the shape around it:

```lean
#eval (· + 10) <$> (some 5 : Option ℕ)   -- some 15
#eval (· + 10) <$> (none : Option ℕ)     -- none
#eval (· * 2) <$> [1, 2, 3]              -- [2, 4, 6]
```

`map` cannot turn `none` into `some`, and it cannot shorten a list. Two laws say so: mapping the identity changes nothing, and mapping a composition is mapping twice. They are fields of the class `LawfulFunctor`:

```lean
example (x : Option ℕ) : id <$> x = x := id_map x

example (g h : ℕ → ℕ) (xs : List ℕ) :
    (h ∘ g) <$> xs = h <$> g <$> xs :=
  comp_map g h xs
```

## Monad
%%%
number := false
tag := "monad-typeclass"
%%%

`Option α` is the type of a computation that may fail. Division by zero is the standard case:

```lean
def safeDivide (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)
```

To divide twice, the second division must run on the result of the first, and only if there is one. A `Monad m` provides exactly this:

* `pure : α → m α` turns a value into a computation that returns it;
* `bind : m α → (α → m β) → m β`, written `x >>= f`, runs `x` and passes its result to `f`.

For `Option`, `pure` is `some`, and `bind` passes the failure on:

```lean
def optionBind (x : Option α) (f : α → Option β) :
    Option β :=
  match x with
  | none => none
  | some a => f a

def divideTwice (a b c : ℕ) : Option ℕ :=
  safeDivide a b >>= fun r => safeDivide r c

#eval divideTwice 100 5 4    -- some 5
#eval divideTwice 100 0 4    -- none
```

Every monad is a functor, with `g <$> x = x >>= (pure ∘ g)`.

## The `do`-notation
%%%
number := false
tag := "do-notation"
%%%

A chain of `>>=` and `fun` is hard to read. The `do`-notation writes it as a sequence of steps:

```lean
def divideThrice (a b c d : ℕ) : Option ℕ := do
  let r ← safeDivide a b
  let s ← safeDivide r c
  safeDivide s d

#eval divideThrice 1000 10 5 4    -- some 5
#eval divideThrice 1000 10 0 4    -- none
```

`let r ← e` runs `e` and names its result `r`; Lean translates each such line into a `>>=`. `return a` is `pure a`.

## Lists as a monad
%%%
number := false
tag := "list-monad"
%%%

A list is a computation with several results. `pure a` is `[a]`, and `xs >>= f` applies `f` to each element and concatenates the lists:

```lean
#eval [1, 2] >>= fun x => [x, x * 10]   -- [1, 10, 2, 20]

def pairs : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [10, 20]
  return (x, y)

#eval pairs
-- [(1, 10), (1, 20), (2, 10), (2, 20), (3, 10), (3, 20)]
```

`let x ← [1, 2, 3]` reads "for each `x` in `[1, 2, 3]`". The result is the list version of `{(x, y) | x ∈ {1, 2, 3}, y ∈ {10, 20}}`. The instance comes from Mathlib (`#synth Monad List` names it).

## The monad laws
%%%
number := false
tag := "monad-laws"
%%%

Three laws make the `do`-notation behave as expected. They are fields of `LawfulMonad`:

:::table (align := left) +header
* + law
  + statement
  + Lean
* + left identity
  + `pure a >>= f = f a`
  + `pure_bind`
* + right identity
  + `x >>= pure = x`
  + `bind_pure`
* + associativity
  + `x >>= f >>= g = x >>= fun a => f a >>= g`
  + `bind_assoc`
:::

For `Option` each law is a computation, by cases on `x`:

```lean
example (a : ℕ) (f : ℕ → Option ℕ) :
    (pure a >>= f) = f a := rfl

example (x : Option ℕ) : (x >>= pure) = x := by
  cases x <;> rfl
```

The name comes from category theory. A monad there is a functor `T` with natural transformations `η : Id → T` (here `pure`) and `μ : T ∘ T → T` (here `join`, which is `bind` with the identity), and the three laws are its coherence conditions, for the category of types and functions.

# Coercions
%%%
tag := "coercions"
%%%

A *coercion* is a conversion Lean inserts automatically when a term of one type appears where another is expected, such as a `ℕ` where a `ℤ` is wanted. Coercions are registered as instances of the class `Coe`, so instance resolution drives them too: on a mismatch Lean finds the instance and inserts the conversion, written `↑`.

```lean
example (n : ℕ) : ℤ := n      -- inserted silently
example (n : ℕ) : ℤ := ↑n     -- the same, written explicitly
```

There are three flavours, according to *what* the target is:

:::table (align := left) +header
* + Class
  + Converts a term into ...
  + Example
* + `Coe`
  + ... a term of another type
  + `ℕ → ℤ`; a subtype into its base type
* + `CoeSort`
  + ... a *type* (where a `Sort` is expected)
  + a set as a type; `Bool → Prop`
* + `CoeFun`
  + ... a *function* (in applied position)
  + a bundled morphism `f` applied as `f x`
:::

`Coe` is the ordinary case — one value becomes another:

```lean
example (s : {n : ℕ // n > 0}) : ℕ := s   -- the subtype's `.val`
```

`CoeSort` lets a term stand in for a *type*. It turns `b : Bool` into the proposition `b = true`, and it is how a `Set α` may be written where a type is expected:

```lean
example (b : Bool) : Prop := b
example (s : Set ℕ) : Type := s   -- the subtype ↥s of its members
```

`CoeFun` lets a *bundled* object be applied like a plain function — so an algebra homomorphism can be written `f x` even though `f` is really a structure carrying that function together with its properties:

```lean
example (f : ℕ →+ ℕ) (n : ℕ) : ℕ := f n
```

Mathlib does not write a `CoeFun` instance for each kind of morphism. A structure type whose elements are functions registers this once, through the class `DFunLike`, and the coercion to functions follows from it ({ref "representation-pitfalls"}[How an object is represented]).

Coercions keep statements readable: you write `n + r` for `n : ℕ` and `r : ℝ`, and Lean reads it as `↑n + r`. A goal can also fill with `↑`s that block tactics like `ring` or `linarith`; the {ref "coercion-headaches"}[appendix] covers the numeric chain `ℕ → ℤ → ℚ → ℝ` and the `norm_cast` / `push_cast` tactics that tidy them up.

# The algebraic hierarchy in Mathlib
%%%
tag := "algebraic-hierarchy"
%%%

Mathlib's algebraic structures are typeclasses, and each one `extends` the weaker structures below it. Simplified:

```
class Group (α : Type) extends Monoid α where
  inv : α → α
  inv_mul_cancel : ∀ a : α, inv a * a = 1
```

`extends` makes `Monoid α` a field of `Group α`, and the projection `Group.toMonoid` is registered as an instance. So from `[CommRing α]`, instance resolution reaches `Add α`, `Mul α` and `AddCommGroup α` by walking the `extends` chain:

```lean
example (α : Type) [CommRing α] : AddCommGroup α :=
  inferInstance

#synth AddCommGroup ℤ
```

That is what lets `mul_comm` be stated once, for `CommMonoid`, and hold for `ℕ`, `ℝ`, polynomial rings and matrix rings alike. When two paths lead to the same class, they must give the same instance; when they do not, the result is a *diamond* ({ref "typeclass-diamonds"}[Typeclass diamonds] in the appendix).

Which structures there are and how to move between them is {ref "algebraic-hierarchy-mathlib"}[a chapter of its own] in the Mathematics part.

# Managing instances
%%%
tag := "managing-instances"
%%%

A few further knobs control *which* instance is found. You rarely need them at first, but they show up when reading Mathlib:

* *Priorities.* Every instance has a priority, by default `1000`; `instance (priority := 2000) : …` is tried before the others, `instance (priority := 100) : …` after them. Since Lean takes the first solution it finds, priorities resolve overlaps.
* *`local` and `scoped` instances.* A `local instance` is active only until the end of the current section, namespace, or file; a `scoped instance` is active only inside its namespace or once you `open` it. Mathlib uses `scoped` heavily. `open scoped Classical` switches on classical decidability for a whole section; inside a proof the {ref "classical-tactic"}[`classical` tactic] does the same for that proof alone.
* *Default instances.* `@[default_instance]` supplies a fallback when synthesis would otherwise be ambiguous — it is how a bare numeral like `2` defaults to `ℕ` when nothing else pins down its type.

# Practical tips
%%%
tag := "typeclass-tips"
%%%

* When you get an error like "failed to synthesize instance," it means Lean cannot find a required typeclass instance. Check that your type has the necessary instance defined.
* Use `#check @lemma_name` to see all implicit arguments and understand what instances a lemma requires.
* In Mathlib, most standard types (`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ`) have instances for all the common typeclasses. You rarely need to define instances for these.
* When defining your own types, provide instances for the typeclasses you need. Start with `Repr` (for printing), then `Add`, `Mul`, etc., as needed.
* The `deriving` mechanism can automatically generate instances for some typeclasses (like `Repr`, `BEq`, `Hashable`, `Inhabited`).
