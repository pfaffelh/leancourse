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

The [slides](slides/1-6-typeclasses/) for this chapter follow it section by section. {ref "functors-monads"}[Chapter 1.7] continues with coercions and hierarchies of classes.

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

Use `structure` when the value is data the user manipulates: a `Point`, a `Person`, a `RingHom`. Use `class` when it is a *canonical* piece of structure attached to a type — an `AddGroup` on `ℤ`, an `Add` on `ℕ` — that Lean should find on its own.

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

*Prop classes* have only propositional fields, so they live in `Prop`, and their instances are *proofs*. `Nonempty` from {ref "rules"}[chapter 1.5] is an example: `Nonempty α` says that `α` has an element, and an instance of it is a proof of that. Mathlib's `Fact` is another ({ref "fact"}[Propositions as instances] below).

```lean
#check @Nonempty                      -- Sort u → Prop
```

Being a proposition, a `Prop` class inherits {ref "prop-special"}[proof irrelevance]: any two instances are definitionally equal. That is a feature — such an instance can never *conflict* with another, and it is erased at runtime.

```lean
example (h₁ h₂ : Nonempty ℕ) : h₁ = h₂ := rfl
```

Typeclasses inherit the *proof* / *data* split drawn for terms in general: an instance is data or a proof exactly according to whether its class lives in `Type` or `Prop`.

An instance is a term you construct: that is what `instance … where …` does, and its fields are values you can project and run. You then use it as a *property of the type* — declared once, synthesized wherever `[C α]` is required, rarely named or passed by hand. For a data class it stays data, carried at runtime; for a `Prop` class it is a proof and is erased.

The parallel holds at the term level: `class` is a `structure` marked for instance search, and `instance` is a `def` marked for instance search, and `instance foo : C := …` is `@[instance_reducible, instance] def foo : C := …`. The two names in `@[…]` are *attributes*, marks on the `def`: `instance` registers it for instance search, and `instance_reducible` allows the search to unfold it. Without a name, `instance : C := …` gets a generated one, such as `instInhabitedFoo`. A plain `def` of a class type is a perfectly good term, only invisible to the search.

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

So typeclasses cannot make Lean inconsistent, and they use no axiom. What an instance does decide is what a statement *means*: `≤` and `+` stand for whatever instance is found. The standard example is the order on pairs. Mathlib defines

```
-- Mathlib/Order/Lex.lean
/-- A type synonym to equip a type with its
lexicographic order. -/
def Lex (α : Type*) := α

/-- `toLex` is the identity function to the `Lex`
of a type. -/
def toLex : α ≃ Lex α := Equiv.refl _
```

So `Lex α` has the same elements as `α`, under a new name. Instance search does not look through that name, so `Lex α` can carry instances of its own (chapter 1.8 explains why this needs `def` and not `abbrev`). `toLex` sends an element to the same element, seen in `Lex α`, and `ofLex` goes back. Mathlib writes `α ×ₗ β` for `Lex (α × β)` and gives the two types two `LE` instances:

```
-- Mathlib/Order/Basic.lean
variable [LE α] [LE β]
instance : LE (α × β) where
  le p q := p.1 ≤ q.1 ∧ p.2 ≤ q.2

-- Mathlib/Data/Prod/Lex.lean
instance instLE (α β : Type*) [LT α] [LE β] :
    LE (α ×ₗ β) where
  le := Prod.Lex (· < ·) (· ≤ ·)
```

Both instances have hypotheses: the componentwise order needs `LE` on both factors, the lexicographic one `LT` on the first and `LE` on the second. For `ℕ × ℕ`, instance search therefore first finds `instLENat` and `instLTNat`, and then the instance for the pair. With `pp.explicit` the two `≤` read

```
@Prod.instLE_mathlib ℕ ℕ instLENat instLENat
@Prod.Lex.instLE     ℕ ℕ instLTNat instLENat
```

For a type without `LE`, such as a `structure` without an order, there is no `≤` on the pairs either: `failed to synthesize LE (…)`.

`Prod.Lex ra rb` is an inductive predicate from Lean's core library, with one constructor per case:

```
protected inductive Lex : α × β → α × β → Prop where
  | left  {a₁} (b₁) {a₂} (b₂) (h : ra a₁ a₂) :
      Prod.Lex (a₁, b₁) (a₂, b₂)
  | right (a) {b₁ b₂} (h : rb b₁ b₂) :
      Prod.Lex (a, b₁) (a, b₂)
```

`left`: the first components are strictly ordered, the second ones are arbitrary. `right`: the first components are equal, the second ones decide. In summary:

:::table (align := left) +header
* + type
  + `(a₁, b₁) ≤ (a₂, b₂)` means
  + order
* + `ℕ × ℕ`
  + `a₁ ≤ a₂ ∧ b₁ ≤ b₂`
  + partial: componentwise (`Prod.mk_le_mk`)
* + `Lex (ℕ × ℕ)`
  + `a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ ≤ b₂)`
  + linear: lexicographic (`Prod.Lex.toLex_le_toLex`)
:::

So `(1, 5)` and `(2, 0)` are incomparable in `ℕ × ℕ`, and `(1, 5)` is the smaller one in `Lex (ℕ × ℕ)`:

```lean
example : ¬ ((1, 5) ≤ ((2, 0) : ℕ × ℕ)) := by decide
example : ¬ ((2, 0) ≤ ((1, 5) : ℕ × ℕ)) := by decide
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

#eval (⟨1.0, 2.0⟩ : Vec2) + ⟨3.0, 4.0⟩
-- outputs (4.000000, 6.000000)
```

We defined two instances: `Add Vec2` so we can use `+`, and `ToString Vec2` so Lean can print `Vec2` values. `s!"…{e}…"` is a string with the value of `e` inserted.

A type of your own with three elements and `+`, `*` as in ℤ/3ℤ is sheet `1.6-b`.

# `Decidable` and `DecidableEq`
%%%
tag := "decidable-typeclass"
%%%

`Decidable` was introduced in {ref "prop-special"}[chapter 1.5]. Lean's core library defines it, and two abbreviations built from it, as follows:

```
-- Init/Prelude.lean
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue (h : p) : Decidable p

abbrev DecidablePred {α : Sort u} (r : α → Prop) :=
  (a : α) → Decidable (r a)

abbrev DecidableEq (α : Sort u) :=
  (a b : α) → Decidable (a = b)
```

`class inductive` declares a class that is an inductive type with several constructors rather than a structure. An element of `Decidable p` is the information *which* of the two cases holds, together with a proof. Programs branch on that information, so the class lives in `Type`, not `Prop`.

`DecidablePred` and `DecidableEq` are not classes of their own but abbreviations, which instance search unfolds. An instance of `DecidableEq α` is a function that takes two elements `a b : α` and returns `isTrue h` with `h : a = b` or `isFalse h` with `h : a ≠ b`. An instance of `DecidablePred r` does the same for `r a`, for every `a`.

```lean
#check @Decidable
-- Decidable : Prop → Type

-- Many concrete propositions are decidable, and the
-- instance is found by typeclass resolution:
#eval (inferInstance : Decidable (2 + 3 = 5))  -- isTrue _
#eval (inferInstance : Decidable (2 + 3 = 6))  -- isFalse _
```

Two everyday features rest on this instance search:

* An `if P then _ else _` requires a `Decidable P` instance — that is
  how the program knows which branch to take. With `DecidableEq α`
  you may branch on `a = b` for `a b : α`.
* The `decide` tactic evaluates the `Decidable` instance and succeeds
  if it reduces to `isTrue`:

```lean
example : 2 + 3 = 5 := by decide
example : ¬(2 + 3 = 6) := by decide
```

On `ℝ`, `decide` gets stuck at `Classical.choice` and fails, even on
`(1 : ℝ) + 1 = 2`; the reason is explained in {ref "decidable-instances"}[`Decidable` instances].

*Where the instance for `2 + 3 = 5` comes from.* Instance search finds `DecidableEq ℕ` and applies it to `2 + 3` and `5`:

```lean
#synth Decidable (2 + 3 = 5)
-- instDecidableEqNat (2 + 3) 5
```

Equality `a = b` itself is an inductive proposition and computes nothing. What computes is a Boolean test, `Nat.beq`, defined by recursion on both arguments. `Nat.decEq` runs it and adds the proof that matches the result:

```
-- Init/Prelude.lean
def Nat.beq : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ _ => false
  | succ _, zero   => false
  | succ n, succ m => beq n m

def Nat.decEq (n m : Nat) : Decidable (n = m) :=
  match h : beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)
  | false => isFalse (ne_of_beq_eq_false h)

instance : DecidableEq Nat := Nat.decEq
```

The recursive function `Nat.beq` is the algorithm; the two lemmas say that it computes correctly. The tactic `decide` turns this into a proof:

```lean
example : 2 + 3 = 5 := by show_term decide
-- of_decide_eq_true (Eq.refl true)
```

`of_decide_eq_true : decide p = true → p`. It remains to check `decide (2 + 3 = 5) = true` by `rfl`: the kernel computes `Nat.decEq (2 + 3) 5`, that is `Nat.beq 5 5 = true`, gets `isTrue _`, and `decide` of that is `true`. On numerals the kernel computes `+` and `Nat.beq` with built-in binary arithmetic instead of unary `succ` ({ref "baked-in"}[chapter 2.3]).

An instance can be written by hand. Decidability of "is `n` zero?", by cases on `n`:

```lean
def decZero (n : Nat) : Decidable (n = 0) :=
  match n with
  -- `rfl`: a proof that 0 = 0
  | 0     => isTrue rfl
  -- a proof that m + 1 ≠ 0
  | m + 1 => isFalse (Nat.succ_ne_zero m)
```

Each branch supplies a proof, which is why `Decidable` lives in `Type` and carries content. Registered as an `instance`, `decZero` is what `decide` runs and what `if n = 0 then … else …` consults. `deriving DecidableEq` generates such a definition for you (next section).

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

`#eval` would derive a missing `Repr` on the fly; `deriving Repr` declares it once, as the definition `instReprStudent`. Other classes are not derived on the fly. For a finite type of your own, the one that matters in mathematics is `DecidableEq`: it lets `decide` and `if a = b then … else …` compare elements ({ref "decidable-typeclass"}[above]).

```lean
inductive Signal where
  | red | amber | green
  deriving Repr, DecidableEq

example : Signal.red ≠ Signal.green := by decide
```

Without `deriving DecidableEq`, `decide` fails with `failed to synthesize Decidable (Signal.red ≠ Signal.green)`. The commonly derived classes:

:::table +header
* + Typeclass
  + What it provides
  + Used for
* + `Repr`
  + a way to *display* a value
  + `#eval`
* + `BEq`
  + Boolean equality `a == b`
  + programs
* + `Hashable`
  + a hash function
  + programs (hash maps)
* + `Inhabited`
  + a designated *default* value `default : α`
  + programs
* + `DecidableEq`
  + a *decidable* equality test `a = b` (returns a proof either way)
  + `decide`, `if a = b`, `Finset`
:::

Several instances can be derived at once:

```lean
structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr, DecidableEq
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

## Deriving on a type synonym
%%%
number := false
tag := "deriving-synonym"
%%%

A `def` that names an existing type hides that type's instances. This is what `Lex` uses ({ref "class-universe"}[above]): `Lex (ℕ × ℕ)` does not see the componentwise order of `ℕ × ℕ`. It also hides the instances one wants to keep. Without them, already `a * b` fails:

```lean +error
def MyInt := ℤ

example (a b : MyInt) : a * b = b * a := mul_comm a b
```

The error is `failed to synthesize HMul MyInt MyInt ?m`. A `deriving` clause on the `def` copies the named instances from the type behind it, here `CommRing ℤ`:

```lean
def MyInt' := ℤ
  deriving CommRing

example (a b : MyInt') : a * b = b * a := mul_comm a b
```

This is the main use of `deriving` in Mathlib's mathematics. For instance, the free commutative ring and the residue field of a local ring are defined as

```
def FreeCommRing (α : Type u) := MvPolynomial α ℤ
  deriving CommRing, Inhabited

def ResidueField := R ⧸ maximalIdeal R
  deriving CommRing, Inhabited
```

and only then get instances of their own (`Field (ResidueField R)`).

# The square bracket notation
%%%
tag := "square-bracket-notation"
%%%

When a function needs a typeclass instance, we use square brackets `[...]` in its signature:

```lean
def doubleIt {α : Type} [Add α] (x : α) : α :=
  x + x

#eval doubleIt 5        -- outputs 10
#eval doubleIt (3 : ℤ)  -- outputs 6
```

The `[Add α]` argument tells Lean: "find an `Add` instance for `α` automatically." We do not need to pass it explicitly; Lean's instance resolution handles it.

You can name the instance if you need to refer to it:

```lean
def tripleIt {α : Type} [inst : Add α] (x : α) : α :=
  inst.add x (inst.add x x)
```

But usually the unnamed form `[Add α]` is preferred, since Lean resolves it behind the scenes.

So `[...]` is the *typeclass bracket*: it marks an instance argument, filled by instance search — as opposed to `(...)`, which you supply yourself, and `{...}`, which Lean infers by unification. The four kinds of binder brackets `()`, `{}`, `⦃⦄`, and `[]` are contrasted side by side in {ref "parenthesis"}[the appendix on parentheses].

# Inspecting typeclass arguments with `@`
%%%
tag := "inspecting-typeclasses"
%%%

When working with Mathlib, it is often useful to see all the implicit and typeclass arguments of a lemma. The `@` symbol makes all arguments explicit:

```lean
#check mul_comm
-- mul_comm.{u_1} {G : Type u_1} [CommMagma G]
--   (a b : G) : a * b = b * a
```

The type `G` is implicit, and the instance `[CommMagma G]` (a multiplication that is commutative) is found by instance search. `@` turns every argument into an explicit one, so you can supply them: `@mul_comm ℕ _ 2 3 : 2 * 3 = 3 * 2` (`_` for the instance).

```lean
#check @mul_comm ℕ _ 2 3
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

For `x : ℝ` and `n : ℕ`, the power `x ^ n` is a real number; for a scalar `c` and a vector `v`, `c • v` is a vector. The type of the result is not the type of both arguments, so the class behind the notation has a third parameter for it. A class of this kind, written by hand:

```lean
class Times (α β γ : Type) where
  times : α → β → γ

instance : Times ℕ ℤ ℤ := ⟨fun n z => n * z⟩
```

Using it without saying what the result is fails:

```lean +error
def f (n : ℕ) (z : ℤ) := Times.times n z
```

The error is `typeclass instance problem is stuck`: Lean has to solve `Times ℕ ℤ ?γ` and knows `α = ℕ` and `β = ℤ`, but not `γ`. Instance search does not start while an argument of the class is unknown, because it would not know which instance to look for. In other contexts Lean guesses `γ`, and the guess is wrong. In `0 ≤ Times.times n z ^ 2`, the numeral `0` makes `γ = ℕ`, and the search fails with `failed to synthesize Times ℕ ℤ ℕ`.

An *output parameter* solves this. Marking `γ` as `outParam` tells instance search to start with the other arguments, `α` and `β`, and to take `γ` from the instance it finds:

```lean
class Times' (α β : Type) (γ : outParam Type) where
  times : α → β → γ

instance : Times' ℕ ℤ ℤ := ⟨fun n z => n * z⟩

def f' (n : ℕ) (z : ℤ) := Times'.times n z

example (n : ℕ) (z : ℤ) : 0 ≤ Times'.times n z ^ 2 :=
  sq_nonneg _
```

The input parameters select the instance, the output parameter is read off it. This only makes sense if the inputs determine the output: for given `α` and `β` there should be one instance, and the first one found fixes `γ`.

Lean's arithmetic is built this way. `a * b` is `HMul.hMul a b` with `HMul α β (outParam γ)`, and the same holds for `HAdd`, `HPow` (`^`) and `HSMul` (`•`):

```lean
#check @HMul.hMul
-- @HMul.hMul : {α : Type u_1} → {β : Type u_2} →
--   {γ : outParam (Type u_3)} → [self : HMul α β γ] →
--   α → β → γ
```

For `x ^ n` with `x : ℝ` and `n : ℕ`, instance search finds `HPow ℝ ℕ ℝ` (via `Monoid.npow`) and reads off that the result is real. For `a ∈ s`, the class is `Membership α γ` with the element type `α` as output parameter: from `s : Set ℕ` Lean reads off that `a` must be a natural number.

# Propositions as instances: `Fact`
%%%
tag := "fact"
%%%

*The problem.* `ZMod p` is a field exactly when `p` is prime. As an instance, this is a statement with a condition: for every `p`, if `p` is prime, then `Field (ZMod p)`. But an instance is applied by instance search, and each of its arguments has to be found by unification or by instance search again. A hypothesis `hp : p.Prime` is found by neither, and Lean rejects the declaration:

```lean +error
noncomputable instance (p : ℕ) (hp : p.Prime) :
    Field (ZMod p) :=
  @ZMod.instField p ⟨hp⟩
```

The error is `This instance has 1 argument that cannot be inferred using typeclass synthesis`, namely `(hp : Nat.Prime p)`. Square brackets do not help: `[hp : p.Prime]` is rejected because `Nat.Prime` is a definition and not a class (details below).

*The solution.* Mathlib's `Fact` turns a proposition into a class:

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

*Why the `Fact` is needed.* `mul_inv_cancel₀` requires `[GroupWithZero G₀]`. With `set_option trace.Meta.synthInstance true` one sees how instance search finds `GroupWithZero (ZMod p)`. It starts at the goal, applies an instance whose conclusion matches, and continues with that instance's own hypothesis as the new goal:

:::table (align := left) +header
* + goal
  + instance applied
  + new goal
* + `GroupWithZero (ZMod p)`
  + `DivisionSemiring.toGroupWithZero`
  + `DivisionSemiring (ZMod p)`
* + `DivisionSemiring (ZMod p)`
  + `Semifield.toDivisionSemiring`
  + `Semifield (ZMod p)`
* + `Semifield (ZMod p)`
  + `Field.toSemifield`
  + `Field (ZMod p)`
* + `Field (ZMod p)`
  + `ZMod.instField`
  + `Fact (Nat.Prime p)`
* + `Fact (Nat.Prime p)`
  + `this`, from the `have`
  + —
:::

The search runs from the goal down. The instance is then assembled from the bottom up, and `#synth GroupWithZero (ZMod p)` prints it as `Field.toSemifield.toDivisionSemiring.toGroupWithZero`. At several steps there are other candidates. For `Field (ZMod p)`, the trace lists `NormedField.toField`, `littleWedderburn` and `ZMod.instField`, and the search tries them one after the other.

Without the `have`, the last row is missing, and the search fails. This is correct: for composite `n`, `ZMod n` is not a group with zero. `ZMod n` has a `⁻¹` for every `n` (`ZMod.instInv`), but in `ZMod 4`, `#eval (2 : ZMod 4) * 2⁻¹` gives `2`.

A hypothesis `hp : p.Prime` cannot take the place of the `Fact`. `Nat.Prime` is a `def`, not a class; `[hp : p.Prime]` is rejected with `invalid binder annotation, type is not a class instance`, and only a structure or an inductive type can be declared a class. `Fact` is the smallest such structure: it turns any proposition into a class.

The warning at the end of the docstring means: instance search does not reason. From `Fact (p = 7)` it does not conclude `Fact p.Prime`; every `Fact` that is needed has to be supplied in exactly the form the instance asks for. Mathlib uses `Fact` for a few such side conditions: besides primality mostly `Fact (1 ≤ p)` for the `Lᵖ` spaces, and the dimension of a Euclidean space in geometry.

# `Decidable` instances
%%%
tag := "decidable-instances"
%%%

*A single proposition or a family.* For a single proposition, `Decidable P` asks for no more than a proof of `P` or a proof of `¬P`, and this needs no axiom:

```lean
def decOfProof {P : Prop} (h : P) : Decidable P := isTrue h
```

Decidability says something only for a *family* of propositions. `decZero` above is one function that, for every `n`, computes which case holds. `DecidablePred p` and `DecidableEq α` ({ref "decidable-typeclass"}[above]) ask for such a function. `n % 2 = 0` is decidable in this sense: compute the remainder. Equality of real numbers is not. A real number is given by a Cauchy sequence, and no finite part of the sequence settles whether its limit is `0`. For each single `x` one of `x = 0` and `x ≠ 0` holds, but no algorithm finds out which.

Mathlib nevertheless has an instance of `DecidableEq ℝ`. It is built from the axiom of choice and computes nothing, so a definition that branches on `x = 0` cannot be compiled:

```lean +error
def realIsZero (x : ℝ) : Bool :=
  if x = 0 then true else false
```

The error is `failed to compile definition, consider marking it as 'noncomputable'`. Decidability by an algorithm is the *constructive* half: it works without axioms, and the resulting code is executable. Where no algorithm exists, the instance comes from the axiom of choice ({ref "noncomputable"}[Computable and noncomputable definitions]).

## Local instances: `have` or `let`
%%%
number := false
tag := "local-instances"
%%%

A `have` whose type is a class adds a local instance, as for `Fact` ({ref "fact"}[above]). But `have` keeps only the type and forgets the value. For a Prop class this does not matter, since any two proofs are equal. For a data class it does: `decide` has to evaluate the instance, and a forgotten value cannot be evaluated. In the following, `inferInstanceAs (Decidable (n < 10))` is the instance of `n < 10`, used for `IsDigit n`, which unfolds to it:

```lean
def IsDigit (n : ℕ) : Prop := n < 10
```

```lean +error
example : IsDigit 3 := by
  have : DecidablePred IsDigit :=
    fun n => inferInstanceAs (Decidable (n < 10))
  decide
```

The error says that reduction got stuck at the `Decidable` instance `this 3`. With `let`, the value stays visible, and `decide` works:

```lean
example : IsDigit 3 := by
  let _ : DecidablePred IsDigit :=
    fun n => inferInstanceAs (Decidable (n < 10))
  decide
```

Mathlib also has `haveI` and `letI`. In a proof they behave like `have` and `let`. In the finished term they substitute the value where the instance is used, instead of leaving a `have` or `let` binding:

```lean
def withHave : Bool :=
  have : DecidablePred IsDigit :=
    fun n => inferInstanceAs (Decidable (n < 10))
  decide (IsDigit 3)

def withHaveI : Bool :=
  haveI : DecidablePred IsDigit :=
    fun n => inferInstanceAs (Decidable (n < 10))
  decide (IsDigit 3)

#print withHave   -- have this := …; decide (IsDigit 3)
#print withHaveI  -- decide (IsDigit 3)
```

This matters for definitions and instances, whose terms are unfolded later. A proof is never unfolded, and in proofs Mathlib's linter `linter.style.haveILetI` asks for `have` and `let` instead.

:::table (align := left) +header
* + where
  + class
  + use
* + in a proof
  + Prop class, e.g. `Fact`
  + `have`
* + in a proof
  + data class whose value is needed (`decide`, `rfl`)
  + `let`
* + in a `def` or `instance`
  + any
  + `haveI`, `letI`
:::

## The `classical` tactic
%%%
number := false
tag := "classical-tactic"
%%%

With the axiom `Classical.choice` (chapter {ref "rules-axioms"}[1.5]) every proposition gets a `Decidable` instance. The proof uses three things from chapter 1.5: the excluded middle, restricted elimination, and the axiom of choice. We start with the step that does not work.

*The wrong step.* The excluded middle `Classical.em P : P ∨ ¬P` is a theorem. A case split on it seems to give the instance at once:

```lean +error
def decDirect (P : Prop) : Decidable P :=
  match Classical.em P with
  | .inl h => isTrue h
  | .inr h => isFalse h
```

The error is `recursor Or.casesOn can only eliminate into Prop`. A case split on a proof may only produce a proof (restricted elimination, {ref "prop-special"}[chapter 1.5]), and `Decidable P` is data in `Type`.

*Why Lean forbids it.* Any two proofs of the same proposition are definitionally equal, also when they come from different constructors:

```lean
example : (Or.inl trivial : True ∨ True) = Or.inr trivial :=
  rfl
```

If a case split on a proof could produce data, the function `.inl _ => true`, `.inr _ => false` on `True ∨ True` would send two equal proofs to `true` and `false`, and `true = false` would follow. The proof of `P ∨ ¬P` does not reveal which side holds.

*Step 1: a `Decidable P` exists.* The same case split is allowed when its result is a proposition. `Nonempty (Decidable P)` is one:

```lean
theorem nonempty_decidable (P : Prop) :
    Nonempty (Decidable P) :=
  match Classical.em P with
  | .inl h => ⟨isTrue h⟩
  | .inr h => ⟨isFalse h⟩
```

This says that `Decidable P` has an element. It does not give one.

*Step 2: choice takes one.* `Classical.choice : Nonempty α → α` turns the existence of an element into an element. This step is exactly what the axiom adds:

```lean
noncomputable def decByChoice (P : Prop) : Decidable P :=
  Classical.choice (nonempty_decidable P)
```

Choice enters twice: `Classical.em` is not an axiom either, it is proved from choice (Diaconescu), and `#print axioms Classical.em` gives `[propext, Classical.choice, Quot.sound]`.

Lean's core library does both steps in one expression, `Classical.propDecidable`:

```
-- Init/Classical.lean
noncomputable scoped instance (priority := low)
    propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
```

The `match` is Step 1, `choice` is Step 2. Step 1 has no name of its own there. The instance `Classical.instNonemptyDecidable : Nonempty (Decidable a)` exists, but it is proved afterwards from `propDecidable`, so it cannot replace `nonempty_decidable` above.

"Decidable" therefore means less here than in the previous section. A term of `Decidable P` exists, but nothing computes whether it is `isTrue` or `isFalse`. `decide` evaluates the instance and gets stuck at `Classical.choice`, as on `ℝ`. A proof does not need to know the answer. It needs some term of `Decidable P`, for `if P then … else …` or for `decide P`, and any two such terms are equal.

The instance is `noncomputable`, and it is not a global instance. The tactic `classical` makes it a local instance, with low priority, for the rest of the proof. Instances that exist, such as decidable equality on `ℕ`, are still found first.

```lean
example (P : Prop) : ∃ b : Bool, (b = true ↔ P) := by
  classical
  exact ⟨decide P, decide_eq_true_iff⟩
```

`decide P` needs `Decidable P`. Without the line `classical`, the `exact` fails with `failed to synthesize Decidable P`. The same happens with finite sets (`Finset`: {ref "finite-sets"}[chapter 2.2]):

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
