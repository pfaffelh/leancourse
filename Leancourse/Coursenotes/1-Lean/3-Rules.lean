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

#doc (Manual) "Types II: the rules" =>
%%%
htmlSplit := .never
tag := "rules"
%%%

The {ref "types"}[previous chapter] built types: functions, inductive types, structures, pairs, subtypes, quotients. This chapter gives the rules that decide which terms Lean accepts. Every type of the previous chapter is an instance of them.

The [slides](slides/1-3-rules/) for this chapter follow it section by section.

# The rules of Lean's type theory
%%%
tag := "type-rules"
%%%

Lean accepts a term only if it can be built with a small, fixed set of rules. These rules are all of Lean's logic. There are no separate rules for $`\land`, $`\lor`, $`\forall`, $`\exists` or $`=`: $`\forall` is a function type, and the others are inductive types, defined with the rules below. Set theory is organized differently. ZFC is a theory in first-order logic, which brings its own rules of inference, and on top of it come ten axioms about $`\in` ({ref "comparison-zfc"}[Comparison with ZFC set theory]).

## Judgements and contexts

The rules derive statements of two kinds, called *judgements*:

* $`\Gamma \vdash e : \alpha`: in the context $`\Gamma`, the term $`e` has type $`\alpha`;
* $`\Gamma \vdash e \equiv e'`: in the context $`\Gamma`, the terms $`e` and $`e'` are definitionally equal.

A rule is written as a fraction. If the judgements above the line hold, then so does the one below. A rule with nothing above the line holds outright.

*The context.* $`\Gamma` is a finite list of variables with their types,

$$`\Gamma = x_1 : \alpha_1,\ x_2 : \alpha_2,\ \dots,\ x_n : \alpha_n .`

It records what may be assumed at a given point: the variables in scope and the hypotheses about them.
For example, take

$$`\Gamma = n : \mathbb N,\ h : 0 < n,\ v : \mathrm{Fin}\ n \to \mathbb N .`

In this context `v` is a vector of length `n`, and `h` says that it is not empty. Then $`\Gamma \vdash v\ \langle 0, h\rangle : \mathbb N`: the pair $`\langle 0, h\rangle` is an element of `Fin n`, so `v` can be applied to it. In Lean, the parameters of a declaration form its context:

```lean
example (n : ℕ) (h : 0 < n) (v : Fin n → ℕ) : ℕ :=
  v ⟨0, h⟩
```

Without `h` the term `v ⟨0, _⟩` would not typecheck, because there would be no proof of `0 < n` in the context.

Three points about contexts.

* *Order matters.* The type $`\alpha_i` may mention $`x_1, \dots, x_{i-1}`, but not later variables. A context is built from left to right, one variable at a time, and each new type must be a type in the context to its left. For the example above:

  :::table (align := left) +header
  * + context
    + new type
    + is a type in the context before, because
  * + `n : ℕ`
    + `ℕ : Type`
    + `ℕ` is in the environment
  * + `n : ℕ, h : 0 < n`
    + `0 < n : Prop`
    + `n` is in the context
  * + `n : ℕ, h : 0 < n, v : Fin n → ℕ`
    + `Fin n → ℕ : Type`
    + `n` is in the context
  :::

  In the order `h : 0 < n, n : ℕ` the first step fails: in the empty context `n` is unknown, so `0 < n` is not a type.

* *Variables, not constants.* A variable in $`\Gamma` has a type but no value. It stands for an arbitrary element of its type, or for an arbitrary proof of its proposition.
* *Binders extend it.* A *binder* is a construction that introduces a variable for a part of a term, its *body*. In `fun x => x + 1` the binder `fun x` introduces `x`, and the body is `x + 1`; in `∀ n : ℕ, n < n + 1` the binder is `∀ n : ℕ`. Outside the body the variable does not exist, just as $`i` in $`\sum_{i=1}^n i^2` or $`x` in $`\int_0^1 x^2\,dx` has no meaning outside the sum or the integral. Such a variable is called *bound*, a variable from the context *free*. In Lean the binders are `fun`, `∀` (and the arrow `(x : α) → β`), and `let`; `∃ x, P x` is notation for `Exists (fun x => P x)` and so binds through `fun`. The context grows when a rule goes under a binder. To check `fun x => e` or `∀ x : α, β`, the body is checked in $`\Gamma,\ x : \alpha`; afterwards $`x` is gone again. The rules for functions below are written that way.

You see contexts all the time. The goal

```
n : ℕ
h : 0 < n
⊢ n ≠ 0
```

is the context `n : ℕ, h : 0 < n` together with the type `n ≠ 0`, and proving the goal means finding a term $`e` with $`\Gamma \vdash e : n \neq 0`. The parameters of a theorem form the initial context: `theorem foo (n : ℕ) (h : 0 < n) : n ≠ 0` starts with exactly this goal. The tactic `intro x` moves a binder of the goal into the context, which is the abstraction rule below read backwards.

*The environment.* Besides $`\Gamma` there is the *environment*: the constants declared so far by `def`, `theorem`, `inductive` and `axiom`, such as `Nat.succ` or `Nat.add_comm`. Unlike a variable, a constant is global, and a definition has a value. A declared constant $`c : \alpha` may be used in every context, and if it is defined by $`c := t`, then $`c \equiv t` (the δ-rule). Every rule below has the environment in the background, but it is not written.

The second kind of judgement is what `rfl` checks ({ref "defeq"}[Definitional equality]).

*Where the first types come from.* A derivation has to start somewhere, and two rules have nothing above the line. The universe rule (*Universes* below) gives `Prop`, `Type`, `Type 1`, … without any premise. And every `inductive` declaration puts its type and constructors into the environment, for `ℕ` the judgements $`\vdash \mathbb N : \mathrm{Type}`, $`\vdash \mathrm{zero} : \mathbb N` and $`\vdash \mathrm{succ} : \mathbb N \to \mathbb N` (see *Inductive types* below). Every other type is built from these with the rules for functions. Lean has no built-in basic types: `Nat`, `Bool` and `Eq` are ordinary inductive declarations in `Prelude`, the first file Lean loads.

## Universes

With $`\mathrm{Prop} := \mathrm{Sort}\ 0` and $`\mathrm{Type}\ u := \mathrm{Sort}\ (u+1)`:

$$`\frac{}{\Gamma \vdash \mathrm{Sort}\ u : \mathrm{Sort}\ (u+1)}`

So `Prop : Type`, `Type : Type 1`, and so on. No universe is a member of itself, which is what prevents the paradoxes above. The tower was described in {ref "type-universes"}[the previous chapter].

```lean
#check Sort 0   -- Prop : Type
#check Type 3   -- Type 3 : Type 4
```

## Variables

$$`\frac{(x : \alpha) \in \Gamma}{\Gamma \vdash x : \alpha}`

A hypothesis may be used as it stands. In a proof this is `exact h` for `h` in the context, or the tactic `assumption`.

## Function types

$$`\frac{\Gamma \vdash \alpha : \mathrm{Sort}\ u \qquad \Gamma,\, x : \alpha \vdash \beta : \mathrm{Sort}\ v}{\Gamma \vdash (x : \alpha) \to \beta : \mathrm{Sort}\ (\mathrm{imax}\ u\ v)}`

Here $`\mathrm{imax}\ u\ v` is $`0` if $`v = 0`, and $`\max(u, v)` otherwise.

The type $`\beta` may contain $`x`, so the type of the value may depend on the argument. This one rule covers three things that look different:

* If $`x` does not occur in $`\beta`, then $`(x : \alpha) \to \beta` is the ordinary function type $`\alpha \to \beta`.
* If $`x` occurs in $`\beta`, it is a *dependent* function type, as in `(n : ℕ) → Fin n`, whose values are functions $`f` with $`f(n) \in \{0, \dots, n-1\}`.
* If $`\beta` is a proposition, Lean writes $`\forall x : \alpha,\ \beta`. A universal statement is a function type: a proof of it is a function that takes any $`x : \alpha` to a proof of $`\beta`. In the same way, for propositions $`P` and $`Q` the implication $`P \to Q` is the type of functions from proofs of $`P` to proofs of $`Q`.

The universe of the result is the larger of the two, except that a function type into `Prop` is always in `Prop`, whatever $`\alpha` is. That exception is the *impredicativity* of `Prop`, discussed in {ref "prop-special"}[Why `Prop` is special].

```lean
#check ℕ → ℕ               -- Type    (imax 1 1 = 1)
#check ℕ → Type            -- Type 1  (imax 1 2 = 2)
#check (n : ℕ) → Fin n     -- Type
#check ∀ n : ℕ, n + 0 = n  -- Prop    (imax 1 0 = 0)
#check ∀ p : Prop, p → p   -- Prop    (imax 1 0 = 0)
```

## Abstraction and application

$$`\frac{\Gamma,\, x : \alpha \vdash e : \beta}{\Gamma \vdash (\mathrm{fun}\ x \Rightarrow e) : (x : \alpha) \to \beta} \qquad \frac{\Gamma \vdash f : (x : \alpha) \to \beta \qquad \Gamma \vdash a : \alpha}{\Gamma \vdash f\ a : \beta[x := a]}`

The left rule builds a function: if $`e` has type $`\beta` once $`x : \alpha` is assumed, then `fun x => e` is a function. The right rule applies one. The notation $`\beta[x := a]` means $`\beta` with $`a` substituted for $`x`, so for a dependent function the type of the value depends on the argument.

For proofs, the left rule is the tactic `intro`: to prove $`\forall x, \beta` or $`P \to Q`, assume the argument and prove the rest. The right rule is how a hypothesis $`h : P \to Q` or $`h : \forall x, \beta` is used: `h hP` or `h a`, which is what `apply` and `exact` produce.

```lean
-- application with substitution: Fin (n + 1) at n := 3
#check (fun n : ℕ => (0 : Fin (n + 1))) 3
-- the same two rules, for proofs
example (P Q : Prop) (f : P → Q) (hP : P) : Q := f hP
example (P Q : Prop) (hQ : Q) : P → Q := fun _ => hQ
```

A local definition `let x := a; e` has its own rule, and the ζ-rule replaces it by $`e[x := a]`.

## Conversion

$$`\frac{\Gamma \vdash e : \alpha \qquad \Gamma \vdash \alpha \equiv \beta}{\Gamma \vdash e : \beta}`

A term of type $`\alpha` also has every type that is definitionally equal to $`\alpha`. This is the rule behind `rfl`. The term `rfl` has type `2 + 2 = 2 + 2`. Because `2 + 2 ≡ 4` by computation, conversion gives it the type `2 + 2 = 4` as well.

```lean
example : 2 + 2 = 4 := rfl
example (v : Fin (2 + 2)) : Fin 4 := v
```

Definitional equality $`\equiv` is the smallest equivalence relation in which a subterm may be replaced by an equivalent one (from $`e \equiv e'` follow $`f\ e \equiv f\ e'`, $`\mathrm{fun}\ x \Rightarrow e \equiv \mathrm{fun}\ x \Rightarrow e'` and so on), and which contains

* the reduction rules β, δ, ζ, η and ι ({ref "reduction-rules"}[The reduction rules]);
* *proof irrelevance*: any two proofs of the same proposition are equal,

  $$`\frac{\Gamma \vdash p : \mathrm{Prop} \qquad \Gamma \vdash h : p \qquad \Gamma \vdash h' : p}{\Gamma \vdash h \equiv h'}`

* *η for structures*: a term of a structure type equals the structure built from its fields.

```lean
example (p : Prop) (h h' : p) : h = h' := rfl
example (x : ℕ × ℕ) : x = (x.1, x.2) := rfl
```

Replacing a subterm, with a variable: `n + 0` reduces to `n`, because addition is defined by recursion on its second argument. Hence `Fin (n + 0) ≡ Fin n`, and every `v : Fin n` also has type `Fin (n + 0)`. In `0 + n` the variable `n` stands where the recursion takes place, and the reduction is stuck. `0 + n = n` is a theorem, `Nat.zero_add`, proved by induction, but not a definitional equality:

```lean
example (n : ℕ) : n + 0 = n := rfl
example (n : ℕ) (v : Fin n) : Fin (n + 0) := v
```

```lean +error
example (n : ℕ) : 0 + n = n := rfl
```

The type checker decides $`\equiv` by an algorithm. {citet carneiro2019}[] showed that $`\equiv` as defined here is undecidable, so the algorithm is incomplete: in rare, constructed cases it fails on terms that are definitionally equal. Ordinary mathematics does not meet these cases.

## Inductive types

Every `inductive` declaration adds new constants to the environment: the type itself, its constructors and its *recursor*, together with ι-rules that say how the recursor computes on constructors ({ref "inductive"}[Inductive types]). For `ℕ`:

$$`\vdash \mathbb N : \mathrm{Type} \qquad \vdash \mathrm{zero} : \mathbb N \qquad \vdash \mathrm{succ} : \mathbb N \to \mathbb N`

$$`\vdash \mathrm{Nat.rec} : (m : \mathbb N \to \mathrm{Sort}\ u) \to m\ \mathrm{zero} \to \big((n : \mathbb N) \to m\ n \to m\ (\mathrm{succ}\ n)\big) \to (t : \mathbb N) \to m\ t`

$$`\mathrm{Nat.rec}\ m\ z\ s\ \mathrm{zero} \equiv z \qquad \mathrm{Nat.rec}\ m\ z\ s\ (\mathrm{succ}\ n) \equiv s\ n\ (\mathrm{Nat.rec}\ m\ z\ s\ n)`

Here $`m` stands for the *motive*: for each `t : ℕ` it gives the type $`m\ t` of the result. Lean names this argument `motive`, as `#check @Nat.rec` shows. $`z` is the value at `zero`, and $`s` stands for the *step*: from `n` and the value at `n` it computes the value at `succ n`. The recursor is both recursion and induction: with $`m\ t` a type it defines functions by recursion, with $`m\ t` a proposition it proves statements by induction ({ref "nat"}[The natural numbers]).

The logical connectives other than $`\forall` and $`\to` are inductive types of exactly this kind, and `#print` shows their declarations:

```lean
#print And
#print Or
#print Exists
#print Eq
#print False
```

So `False` is the type with no constructor, `Or` has the two constructors `Or.inl` and `Or.inr` from sheet `L-c`, and `Eq a` has the single constructor `Eq.refl a : a = a`.

A declaration is accepted only under two conditions:

* *Strict positivity*: the type being defined must not occur to the left of an arrow in the type of a constructor argument. Otherwise `False` can be proved without any axiom ({ref "strict-positivity"}[Strict positivity]).
* *Restricted elimination*: for an inductive type in `Prop`, the motive of the recursor must again land in `Prop`. A proof can be used to prove things, but not to compute data. The exceptions are types with at most one constructor whose arguments are all proofs, such as `Eq`, `And`, `True` and `False`.

The second condition is forced by proof irrelevance. For `h : P`, the terms `Or.inl h` and `Or.inr h` are two proofs of `P ∨ P`, hence definitionally equal. A function `P ∨ P → Bool` defined by recursion could send them to `true` and `false`, and then `true ≡ false`.

```lean
#check @Or.rec     -- motive : a ∨ b → Prop
#check @False.rec  -- motive : False → Sort u
```

## Quotients

For a relation $`r : \alpha \to \alpha \to \mathrm{Prop}`, the type `Quot r` of equivalence classes is built in, with the constants `Quot.mk`, `Quot.lift` and `Quot.ind` and one computation rule:

$$`\mathrm{Quot.lift}\ f\ h\ (\mathrm{Quot.mk}\ r\ a) \equiv f\ a`

Here $`h` is a proof that $`f` respects $`r`. That two related elements give the same class is not a rule but an axiom, `Quot.sound` ({ref "quotient-types"}[Quotient types] in the previous chapter).

## Axioms

Beyond the rules, Lean has exactly three axioms:

```lean
#check @propext          -- (a ↔ b) → a = b
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#check @Classical.choice -- Nonempty α → α
```

`propext` says that equivalent propositions are equal. `Quot.sound` says that related elements have the same class. `Classical.choice` picks an element from any nonempty type, with no information about which one. The excluded middle is not among them: `Classical.em` is a theorem, proved from all three (Diaconescu's theorem). Function extensionality `funext` is a theorem as well, proved from `Quot.sound`. `#print axioms` lists the axioms a theorem depends on:

```lean
#print axioms Classical.em
#print axioms funext
```

A theorem whose list is empty holds in the rules alone, and its proof is constructive.

## How Lean implements the rules

Lean has two programs that deal with terms. The *elaborator* turns what you write — notation, implicit arguments, type classes, tactic proofs — into a fully explicit term. It is large and complicated, and it is not trusted. The *kernel* then checks that term against the rules above, and only then is the declaration added to the environment. A tactic can therefore produce a wrong term, but it cannot get one past the kernel.

*Terms.* In the kernel, a term is a value of the type `Lean.Expr`. Its constructors are the term formers of the rules: `sort` for $`\mathrm{Sort}\ u`, `const` for a constant of the environment, `bvar` and `fvar` for variables, `lam` for `fun`, `forallE` for $`(x : \alpha) \to \beta`, `app` for application, `letE` for `let`, and three more for efficiency: `lit` for numerals and strings, `proj` for structure fields, and `mdata` for annotations. Here is `id`, as the kernel stores it:

```lean
open Lean in
#eval show MetaM Unit from do
  let c ← getConstInfo ``id
  IO.println (repr c.value!)
```

The output reads `lam α (sort u) (lam a (bvar 0) (bvar 0))`, that is, `fun {α : Sort u} (a : α) => a`. Bound variables have no names, only indices: `bvar 0` is the nearest enclosing binder. In the type `bvar 0` it refers to `α`, in the body to `a`.

*The context.* When the type checker goes under a binder, it replaces the bound variable by a fresh *free* variable (`fvar`) and records its type in a local context. That local context is $`\Gamma`, and this step is $`\Gamma,\ x : \alpha`.

*The rules.* The type checker is a function `infer_type` that computes the type of a term by a case distinction on its constructor, one case per rule. In the source, `src/kernel/type_checker.cpp` in the Lean repository, the case for `Sort` is

```
case expr_kind::Sort:
    r = mk_sort(mk_succ(sort_level(e)));
```

which is the rule $`\mathrm{Sort}\ u : \mathrm{Sort}\ (u+1)`. The other cases call `infer_fvar` (look the variable up in the local context), `infer_constant` (look it up in the environment), `infer_pi` (compute the levels of domain and codomain and combine them with `mk_imax`), `infer_lambda` and `infer_app`. The last one, slightly shortened:

```
expr f_type = ensure_pi(infer_type(app_fn(e)));
expr a_type = infer_type(app_arg(e));
expr d_type = binding_domain(f_type);
if (!is_def_eq(a_type, d_type))
    throw app_type_mismatch_exception(...);
return instantiate(binding_body(f_type), app_arg(e));
```

This is the application rule. The type of $`f` must be a function type $`(x : \alpha) \to \beta`, the type of the argument must be $`\alpha`, and the result is $`\beta[x := a]`, which `instantiate` computes. The conversion rule does not appear as a step of its own: it is the call `is_def_eq`, which accepts the argument if its type is definitionally equal to $`\alpha` rather than identical. `is_def_eq` reduces both sides with the rules β, δ, ζ, η, ι as far as needed and compares them. The elaborator runs the same test before the kernel does, and its error `Application type mismatch`, which you will see often, is a failure of exactly this check.

*Size.* The whole kernel is about 350 kB of C++ in `src/kernel`, of which `type_checker.cpp` has about 1 400 lines and the checking of inductive declarations (`inductive.cpp`) a similar amount. That is small enough to be read, and there are independent reimplementations that check the same terms: *lean4lean* in Lean, *nanoda* in Rust, and *Con-Leche*, mentioned in {ref "prop-special"}[Why `Prop` is special].

The rest of this chapter treats the universe of a type and `Prop`. A complete account is in Mario Carneiro's [*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory).

# How the universe of a type is determined
%%%
tag := "universe-determined"
%%%

You rarely write universe levels by hand — Lean computes the universe of a compound type from the universes of its parts. A function type `α → β` lands in the *larger* of the two universes involved:

```lean
#check (ℕ → ℕ)        -- Type
#check (ℕ → Type)     -- Type 1  (because `Type : Type 1`)
```

The same holds for a `∀` (a *dependent* function type), whose universe is read off from the universe it ranges over together with that of its body. When the body is data — something in a `Type` — the whole `∀` is forced to grow with the domain:

```lean
-- Type-valued body: the universe grows with the domain.
#check (∀ α : Type, α → α)     -- Type 1
#check (∀ α : Type 5, α → α)   -- Type 6
```

The climbing is what *predicative* means: a predicative definition refers only to things already available below it, so whatever a type quantifies over is strictly smaller and the type it forms never lands back inside its own domain. That is why `∀ α : Type 5, α → α` is pushed up to `Type 6`, above everything it ranges over, and it keeps the hierarchy well-founded. (The term goes back to Poincaré and Russell, who imposed predicativity to outlaw the self-referential definitions behind the set-theoretic paradoxes.)

The bump matters. Suppose `∀ α : Type, α → α` were allowed to have type `Type` rather than `Type 1` — i.e. a `∀` over `Type` could land back inside `Type`. That is the first step toward a universe that contains itself, `Type : Type`, and *that* is fatal: from `Type : Type` one can encode Russell's paradox at the level of types — *Girard's paradox* — and derive an honest proof of `False`, so *every* proposition becomes provable and the system is worthless. Predicativity, by forcing the climb to `Type 1`, is exactly what rules this out. (The proof is not short, and Lean's kernel enforces the bump, so you cannot even state `∀ α : Type, α → α : Type` to try it; carrying the construction out in Lean is {ref "project-girard"}[one of the course projects].)

(A definition can also be made to work at *any* universe level at once; that uses `def`, so we defer it to the {ref "polymorphic-functions"}[chapter on functions].)

There is exactly one universe that is allowed to break this rule — `Prop` — and that exception is the subject of the next section.

# Why `Prop` is special
%%%
tag := "prop-special"
%%%

`Prop` is the type of statements that can be `True` or `False`, so both the hypotheses and the goal live there. A hypothesis has the form `hP : P`: `P` holds, and `hP` is a proof of it. Below, the hypotheses are named `P Q R S` and their proofs `hP hQ hR hS`; the names are arbitrary. A hypothesis `P → Q` states that `P` implies `Q`, written like the function type `f : ℝ → ℝ`.

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

*`Prop` is impredicative*: `Prop` is the one universe that escapes the predicativity of the {ref "universe-determined"}[previous section]. As long as the body of a `∀` statement is a proposition, the whole `∀` is a `Prop` — even when we range over an arbitrarily large universe of types:

```lean
-- Prop-valued body: stays `Prop`, however big the domain.
#check (∀ α : Type, α = α)     -- Prop
#check (∀ α : Type 5, α = α)   -- Prop
-- and the domain may be `Prop` itself.
#check (∀ p : Prop, p → p)     -- Prop
#check (∀ p : Prop, p)         -- Prop
```

Compare this with the `Type`-valued `∀ α : Type 5, α → α`, which had to climb to `Type 6`. The two statements are syntactically parallel and differ only in their body, yet land in wildly different places — `Prop` versus `Type 6`. A `∀` into `Prop` stays small; a `∀` into `Type u` must climb. The last two lines are the sharp case. `∀ p : Prop, p → p` is itself a `Prop`, so it quantifies over a totality *to which it belongs*, and `∀ p : Prop, p` does the same. That is what *impredicative* means: the definition, so to speak, feeds on itself.

It is also exactly what Russell forbade. His vicious circle principle rules out defining an object by quantifying over a collection that contains it, and the ban costs ordinary analysis: the supremum of a set of reals is defined by quantifying over reals. Russell bought it back with a further axiom, reducibility, which says that every such definition is coextensional with a predicative one ({ref "prehistory"}[Introduction]).

Lean needs no such axiom, because it does not apply one rule to everything. The circle is granted in `Prop` and refused for data: a proposition may be defined by quantifying over all propositions, a type may not be defined by quantifying over all types. Russell's supremum is then unproblematic. The cut that defines it is a predicate on $`ℚ` whose body quantifies over all of $`ℝ`, and because that body is a `Prop` it does not climb; what the quantification defines is an ordinary `Set ℚ`, at the same level as any other.

```lean
-- The defining property ranges over all reals ...
#check fun (S : Set ℝ) (q : ℚ) => (∃ x ∈ S, (q : ℝ) < x)  -- ... Prop
-- ... so the cut it carves out is an ordinary set of rationals.
#check fun (S : Set ℝ) => {q : ℚ | ∃ x ∈ S, (q : ℝ) < x}    -- Set ℚ
```

That this is consistent is not obvious, and it is not a convention. Impredicativity in the syntax need not be circularity in the meaning: `Prop` can be modelled as a fixed collection of truth values, given in advance, and a `∀` over it is then a meet of members of that collection, hence a member again. The definition picks something out; it does not enlarge the totality. For a first-order theory, being consistent and having a model are the same thing — that is Gödel's completeness theorem of 1929 ({ref "hilbert-programme"}[Introduction]). Lean's logic is not first-order: its quantifiers range over types and over propositions, not only over the elements of one domain, so that equivalence is unavailable and the model has to be built by hand. Mario Carneiro built the set-theoretic model and proved Lean consistent relative to ZFC with $`n` inaccessible cardinals for each finite $`n`{citep carneiro2019}[]. The assumption is of the right strength, since Lean itself proves that models of ZFC with $`n` inaccessibles exist. The proof is not closed, however. An error was found in the thesis, and basic properties of Lean's type theory remain unproved, among them unique typing and Pi-injectivity; as of October 2026 there is no complete public relative-consistency proof for the type theory Lean implements{citep hales2026}[]. What stands in its place is weaker, in two directions. {citet werner1997}[] embeds ZFC into the CIC, and a dialect of the CIC back into ZFC with inaccessibles — a result about the CIC, not about the system Lean implements. And Joachim Breitner's [*Con-Leche*](https://github.com/leanprover/con-leche) is an external checker for Lean, written in Lean, with a proof in Lean that it never accepts a proof of `False`. That proof does not close the gap above: it is carried out *inside* Carneiro's framework, so it inherits the framework's open questions. What it establishes is that the checker is faithful to the model, not that the model is there. Consistency is therefore well supported, not settled.

One level up the same move is fatal: `Type : Type` is inconsistent by Girard's paradox, which is why `Type u : Type (u+1)` and why `∀ α : Type 5, α → α` has to climb. And impredicativity is not free in `Prop` either. It is paid for by the restriction in the next item: if a proof could be taken apart to yield data *and* propositions could be formed impredicatively, the paradox would return.

*Restricted (subsingleton) elimination.* A type's constructors *introduce* its values — they are the ways we build them (`Or.inl`, `isTrue`, `Nat.succ`, and so on). *Eliminating* a value is the opposite: we *use* it, by looking at which constructor produced it. This is what a `match` does — the {ref "pattern-matching"}[pattern-matching] construct `match h with | … => …`, taken up properly in the chapter on terms — and it is ultimately the job of the type's {ref "inductive"}[recursor] (see the {ref "nat-intro"}[introduction]). For a *proposition* `P : Prop`, then, eliminating a proof means running `P`'s own recursor — `Or.rec`, `And.rec`, and the like (the error below names `Or.casesOn`, the `match`-friendly form of `Or.rec`) — and the restriction we are about to meet is a restriction on exactly that recursor. To *eliminate into a type `T`* means that this case analysis returns a result of type `T`; eliminating into `T`, defining a function into `T` by the recursor, and letting that recursor compute are three names for one act. A proof carries no observable content, so Lean does not let us *read data off a proof* in this way: otherwise the result could depend on *which* proof we started from, and proof irrelevance says there is no such difference to observe. So eliminating a proposition may, in general, only produce further propositions, never data. For example, deciding as a {ref "bool"}[`Bool`] which side of a disjunction holds is rejected:

```lean +error
example (a b : Prop) (h : a ∨ b) : Bool :=
  match h with
  | Or.inl _ => true
  | Or.inr _ => false
```

The error message is telling: `recursor 'Or.casesOn' can only eliminate into 'Prop'`. There is one exception, called *subsingleton elimination*. If a proposition has *at most one constructor* and all of its fields are *themselves proofs*, then it has at most one inhabitant, so eliminating it can reveal nothing — and Lean does allow it into *any* type. This covers `False` (no constructors at all, which is exactly why `False.elim` closes *any* goal), `Eq` (which is why we may `rw` even in goals that carry data), and `And` (both of its fields are proofs). It does *not* cover `Or` (the {ref "disjunction-sum"}[disjunction] `∨`, which has two constructors) or `∃` (its first field is a genuine witness, not a proof). None of this applies to `Type`: an inductive type in `Type` always eliminates into anything.

Consistency forces this. For `Or`, what cannot escape is not a *witness*, as it would be for `∃`, but the *tag*: the information about *which* of the two branches holds. Take a true `a` and consider the proposition `a ∨ a`. Its two constructors give definitionally equal terms, by proof irrelevance:

```lean
example {a : Prop} (h : a) :
    (Or.inl (b := a) h) = Or.inr (b := a) h := rfl
```

Here `h : a` is a proof of the (true) proposition `a`. "Left or right?" is simply not a well-posed question about a proof of `a ∨ a`: the tag is not distinguishable content. So if the rejected `(a ∨ b) → Bool` above were allowed — call the resulting function `which` — then setting `b := a` would give `which (Or.inl h) = true` and `which (Or.inr h) = false`; but `Or.inl h ≡ Or.inr h` (they are {ref "defeq"}[definitionally equal], the `≡` from the previous chapter), so we would get `true ≡ false`, a contradiction. Because proofs are indistinguishable, the tag has to stay trapped — just as a leaked `∃`-witness would have forced `3 ≡ 5`.

We cannot *build* such a `which` — Lean rejects it — but we can *assume* one exists for *every* `a ∨ b` (with its left- and right-branch computation rules as hypotheses) and then instantiate at `b := a`, where the two injections collide. Watch `true = false` — hence `False` — drop out:

```lean
example
    (which : ∀ {a b : Prop}, a ∨ b → Bool)
    (left : ∀ {a b : Prop} (h : a),
      which (Or.inl h : a ∨ b) = true)
    (right : ∀ {a b : Prop} (h : a),
      which (Or.inr h : b ∨ a) = false) :
    False := by
  -- at `a, b := True`, the injections collide:
  have htf : true = false := by
    rw [← left (a := True) (b := True) trivial,
        right (a := True) (b := True) trivial]
  revert htf
  decide
```

The way out mirrors the one for `∃`, one level up. The data-carrying counterpart of `a ∨ ¬a` is `Decidable a` (the {ref "decidable-typeclass"}[`Decidable` typeclass]), which — crucially — lives in `Type`, not `Prop` (its declaration uses the constructor-list `where` from the {ref "bool"}[`Bool` section]):

{docstring Decidable}

Because `Decidable p` is in `Type`, it *may* eliminate into `Type` — which is exactly why `if h : p then _ else _` (a *dependent* `if`, whose `h : p` names the proof made available in the then-branch) and the {ref "decide"}[`decide`] tactic compute.

`Decidable` is one of many such twins. Almost every logical type has a data version, and Lean keeps the two apart because every type lives in exactly one universe and is never lifted into another. So `List Empty` is a type, while `List False` is an error: `List` expects an argument in `Type`, and `False` is in `Prop`. The last column of the table says what the `Prop` version keeps hidden. Where nothing is hidden (at most one constructor, all fields proofs), subsingleton elimination lets the proposition eliminate into `Type` after all, as `False.elim` does. Where something is hidden, only the data version can hand it out:

:::table (align := left) +header
* + Proposition (in `Prop`)
  + Data version (in `Type`)
  + what stays hidden
* + `False`
  + `Empty`
  + nothing (no constructor)
* + `True`
  + `Unit`
  + nothing (one constructor, no fields)
* + `P ∧ Q`
  + `α × β`
  + nothing (one constructor, fields are proofs)
* + `P ∨ Q`
  + `α ⊕ β`
  + the *tag* (which side)
* + `a ∨ ¬a`
  + `Decidable a`
  + the *tag* (which side)
* + `∃ x, q x`
  + {ref "sigma-types"}[`Σ x, q x`]
  + the *witness*
:::

The classical route mirrors `Classical.choose` in the same way: `Classical.em : a ∨ ¬a` is always available (it is a `Prop`), but its data-carrying counterpart `Classical.propDecidable : Decidable a` goes through `Classical.choice` and is therefore `noncomputable` — a keyword marking a definition Lean cannot turn into runnable code, needed here because `Classical.choice` has no computational content to execute (this is the usual trigger for `noncomputable`, though not the only one). So the two halves — `∃`/`Σ`/`choose` for the *witness*, `∨`/`Decidable`/`em` for the *tag* — are really the same story: computationally relevant information can leave the `Prop` world only if we put it in `Type` from the start, or pay for it noncomputably with the axiom of choice. (The `Nonempty`/`Classical.choice` form of this is taken up in the {ref "curry-howard"}[chapter on propositions and proofs].)
