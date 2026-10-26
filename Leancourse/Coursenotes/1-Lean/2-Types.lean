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

#doc (Manual) "Types" =>
%%%
htmlSplit := .never
tag := "types"
%%%

Lean has the data types every programming language has — `int`, `string`, `float` — and you can define your own, as you will in this course. Throughout, `x : α` means that `x` is a term of type `α`: `false : Bool`, `42 : ℕ`, `f : ℕ → ℝ` for a function from ℕ to ℝ (itself a type), and `0 ≠ 1 : Prop` for the proposition that 0 and 1 differ. Terms and types can depend on variables, e.g. in `∀ (n : ℕ), n < n + 1 : Prop` (the term `n < n + 1` depends on `n : ℕ`) and `f : (n : ℕ) → (Fin n → ℝ)` where `Fin n` is the type which carries `{0, ..., n-1}` (here, the type `Fin n → ℝ` depends on `n : ℕ`), which is a function `f` with domain `ℕ` such that `f n ∈ ℝ^n`.

Two words for terms recur throughout, depending on their type: a term `h : P` whose type `P` is a `Prop` is called a *proof* (of `P`), while a term `a : α` whose type `α` is a `Type u` (where `u` will be called a universe) is called *data*. So `42 : ℕ` and `true : Bool` are data, whereas any term of the proposition `0 ≠ 1` is a proof of it. (The two kinds of universe, `Prop` and `Type u`, are the subject of the next section.)

These data types are abstract: Lean treats `ℕ` and `ℝ` as genuinely infinite, not as floating-point approximations. `ℕ` is the `zero`/`succ` construction of the {ref "nat"}[introduction]; `ℝ` is built from an equivalence relation on Cauchy sequences, a {ref "quotient-types"}[quotient type] (end of this chapter).

In Lean every object is a term, and every term has a type. A type is itself a term, so it has a type as well.

The [slides](slides/1-2-types/) for this chapter follow it section by section.

# Where types come from
%%%
tag := "types-history"
%%%

Types were invented to stop a contradiction. Bertrand Russell's letter of 1902 broke the system of Gottlob Frege's *Grundgesetze der Arithmetik* with the set $`R = \{x : x \notin x\}`, which is a member of itself exactly if it is not ({ref "prehistory"}[Introduction]). Russell's repair, published in 1908, was to introduce a hierarchy. Every object gets a type, a type may be applied only to objects of lower type, and `x ∈ x` is then not a false statement but no statement at all. *Principia Mathematica* is written in that theory. Leon Chwistek and Frank Ramsey simplified it in the 1920s to what is now called the simple theory of types.

Ernst Zermelo's answer of the same year restricts which sets exist: `x ∈ x` stays a well-formed formula there; that it holds for no set is the axiom of foundation, added by John von Neumann in 1925 and Zermelo in 1930, and foundation is not what repairs the paradox. Set theory has a hierarchy as well, the cumulative hierarchy of ranks $`V_\alpha`, but it is a theorem about which sets there are, not a rule of the language. In type theory the hierarchy *is* the language, and well-formedness is decidable. A proof assistant needs that: the type checker settles whether an expression means anything before anyone asks whether it is true.

Mathematics took the other road for reasons that were good at the time. Russell's ramified theory needed a further axiom, reducibility, before ordinary analysis could be recovered, and it forced every definition and every theorem to be repeated at every level. Zermelo's axioms left mathematical practice as it was, and they settled a question mathematicians already cared about, the well-ordering theorem. The balance reverses once a machine does the checking: an untyped term tells the checker nothing, and every object has to be coded as a set. *Mizar*, the one large system built on set theory, carries a layer of soft types on top of it.

Alonzo Church made the simple theory of types a calculus in 1940. His own lambda calculus of 1932 was inconsistent as a logic, as Stephen Kleene and J. Barkley Rosser showed in 1935, and the repair was again types: terms carry types, types are built from base types and `→`, and a term applied to itself is not well-formed. That system is the simply typed lambda calculus. *Isabelle/HOL* still rests on it.

Two independent lines added *dependent* types, in which a type may mention a term. Nicolaas Govert de Bruijn built them into Automath from 1967. Per Martin-Löf developed intuitionistic type theory from 1971; his first version was again inconsistent, by an argument of Jean-Yves Girard, and the repair is the universe hierarchy of the next section. Thierry Coquand and Gérard Huet added impredicative quantification in the Calculus of Constructions in 1985, and Christine Paulin-Mohring added inductive types in 1990. Lean's type theory is a variant of the result, the {ref "cic"}[Calculus of Inductive Constructions].

The same move occurs three times. A system lets an object be applied to itself, a contradiction follows, and types forbid it. In Lean the ban is visible as `Type 0 : Type 1 : Type 2 : ...`, which is why there is no type of all types.

Lean's answer can be written out in full, as a short list of rules; the box below gives it. The axioms of ZFC, and what replaces each of them in Lean, are in {ref "comparison-zfc"}[Comparison with ZFC set theory].

::::example "The rules of Lean's type theory"
Lean's type theory has no logic underneath it. It consists of inference rules for two kinds of judgement: $`\Gamma \vdash e : \alpha` (in the context $`\Gamma`, the term $`e` has type $`\alpha`) and $`\Gamma \vdash e \equiv e'` ($`e` and $`e'` are definitionally equal). A context is a list of variables with their types, $`x_1 : \alpha_1, \dots, x_n : \alpha_n`. A rule says: if the judgements above the line hold, so does the one below. The rules are not formulas, and $`\land`, $`\lor`, $`\exists` and $`=` do not occur in them; these are defined later as inductive types.

*Universes.* With $`\mathrm{Prop} := \mathrm{Sort}\ 0` and $`\mathrm{Type}\ u := \mathrm{Sort}\ (u+1)`,

$$`\frac{}{\Gamma \vdash \mathrm{Sort}\ u : \mathrm{Sort}\ (u+1)}`

*Variables.*

$$`\frac{(x : \alpha) \in \Gamma}{\Gamma \vdash x : \alpha}`

*Function types.* Here $`\mathrm{imax}\ u\ v` is $`0` if $`v = 0` and $`\max(u, v)` otherwise. The case $`v = 0` is the impredicativity of `Prop` ({ref "prop-special"}[below]).

$$`\frac{\Gamma \vdash \alpha : \mathrm{Sort}\ u \qquad \Gamma,\, x : \alpha \vdash \beta : \mathrm{Sort}\ v}{\Gamma \vdash (x : \alpha) \to \beta : \mathrm{Sort}\ (\mathrm{imax}\ u\ v)}`

*Abstraction and application.* Lean writes `fun x => e` for $`\lambda x.\, e`.

$$`\frac{\Gamma,\, x : \alpha \vdash e : \beta}{\Gamma \vdash \lambda x.\, e : (x : \alpha) \to \beta} \qquad \frac{\Gamma \vdash f : (x : \alpha) \to \beta \qquad \Gamma \vdash a : \alpha}{\Gamma \vdash f\ a : \beta[x := a]}`

*Conversion.*

$$`\frac{\Gamma \vdash e : \alpha \qquad \Gamma \vdash \alpha \equiv \beta}{\Gamma \vdash e : \beta}`

*Definitional equality* is the smallest congruence containing the reduction rules β, δ, ζ, η and ι ({ref "reduction-rules"}[The reduction rules]) and two more: proof irrelevance, and η for structures.

$$`\frac{\Gamma \vdash p : \mathrm{Prop} \qquad \Gamma \vdash h : p \qquad \Gamma \vdash h' : p}{\Gamma \vdash h \equiv h'}`

*Inductive types.* Each `inductive` declaration adds the type, its constructors and its recursor as constants, together with an ι-rule ({ref "inductive"}[Inductive types]). A declaration is accepted only if it is strictly positive ({ref "strict-positivity"}[strict positivity]), and the recursor of a type in `Prop` eliminates only into `Prop`, apart from a few exceptions such as `Eq` and `And`.

*Quotients.* `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` are built in, with the computation rule `Quot.lift f h (Quot.mk r a) ≡ f a` ({ref "quotient-types"}[Quotient types]).

*Axioms.* Beyond the rules there are exactly three.

```lean
#check @propext          -- (a ↔ b) → a = b
#check @Quot.sound       -- r a b → Quot.mk r a = Quot.mk r b
#check @Classical.choice -- Nonempty α → α
```

The excluded middle is not among them: `Classical.em` is a theorem, proved from these three (Diaconescu's theorem). Function extensionality `funext` is a theorem as well, proved from `Quot.sound`.

A full account of the rules is in Mario Carneiro's [*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory).
::::

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

`Type` (which is the same as `Type 0`) is the universe of ordinary data types (`ℕ`, `ℝ`, `Bool`, `List α`, ...), and `Prop` (which is the universe of *propositions*, i.e. True/False-statements). But `Type` cannot contain itself — that would be paradoxical — so `Type` in turn lives in a larger universe `Type 1`, which lives in `Type 2`, and so on without end:

```lean
#check (Type 0 : Type 1)    -- `Type 0`, i.e. `Type`, lives in `Type 1`
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

So `Sort` is the umbrella that unifies `Prop` and all the `Type u`, and the one rule governing the hierarchy is `Sort u : Sort (u+1)`. There is deliberately no `Type : Type`; *why* this restriction is needed — it blocks a type-theoretic version of Russell's paradox — is taken up in the {ref "universe-determined"}[next section].
:::

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

It is also exactly what Russell forbade. His vicious circle principle rules out defining an object by quantifying over a collection that contains it, and the ban costs ordinary analysis: the supremum of a set of reals is defined by quantifying over reals. Russell bought it back with a further axiom, reducibility, which says that every such definition is coextensional with a predicative one ({ref "types-history"}[Where types come from]).

Lean needs no such axiom, because it does not apply one rule to everything. The circle is granted in `Prop` and refused for data: a proposition may be defined by quantifying over all propositions, a type may not be defined by quantifying over all types. Russell's supremum is then unproblematic. The cut that defines it is a predicate on $`ℚ` whose body quantifies over all of $`ℝ`, and because that body is a `Prop` it does not climb; what the quantification defines is an ordinary `Set ℚ`, at the same level as any other.

```lean
-- The defining property ranges over all reals ...
#check fun (S : Set ℝ) (q : ℚ) => (∃ x ∈ S, (q : ℝ) < x)  -- ... Prop
-- ... so the cut it carves out is an ordinary set of rationals.
#check fun (S : Set ℝ) => {q : ℚ | ∃ x ∈ S, (q : ℝ) < x}    -- Set ℚ
```

That this is consistent is not obvious, and it is not a convention. Impredicativity in the syntax need not be circularity in the meaning: `Prop` can be modelled as a fixed collection of truth values, given in advance, and a `∀` over it is then a meet of members of that collection, hence a member again. The definition picks something out; it does not enlarge the totality. For a first-order theory, being consistent and having a model are the same thing — that is Gödel's completeness theorem of 1929 ({ref "hilbert-programme"}[Introduction]). Lean's logic is not first-order: its quantifiers range over types and over propositions, not only over the elements of one domain, so that equivalence is unavailable and the model has to be built by hand. Mario Carneiro built the set-theoretic model and proved Lean consistent relative to ZFC with $`n` inaccessible cardinals for each finite $`n` ([*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory), 2019). The assumption is of the right strength, since Lean itself proves that models of ZFC with $`n` inaccessibles exist. The proof is not closed, however. An error was found in the thesis, and basic properties of Lean's type theory remain unproved, among them unique typing and Pi-injectivity; as of October 2026 there is no complete public relative-consistency proof for the type theory Lean implements{citep hales2026}[]. What stands in its place is weaker, in two directions. {citet werner1997}[] embeds ZFC into the CIC, and a dialect of the CIC back into ZFC with inaccessibles — a result about the CIC, not about the system Lean implements. And Joachim Breitner's [*Con-Leche*](https://github.com/leanprover/con-leche) is an external checker for Lean, written in Lean, with a proof in Lean that it never accepts a proof of `False`. That proof does not close the gap above: it is carried out *inside* Carneiro's framework, so it inherits the framework's open questions. What it establishes is that the checker is faithful to the model, not that the model is there. Consistency is therefore well supported, not settled.

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

# Inductive types
%%%
tag := "inductive"
%%%

`Nat`, `List`, `Option`, `Bool` and `Empty` are all *inductive* types; `Nat` and `Bool` were dissected in the {ref "nat-intro"}[previous chapter]. What follows is how to declare such a type yourself, and which declarations Lean accepts.

You declare an inductive type by giving a name, the type's universe, and a list of *constructors*, each saying how to build a new element out of existing pieces. Declaring the natural numbers by hand reproduces exactly the structure of `Nat`:

```lean
inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat
```

As with `Nat`, this single declaration introduces three things at once: the type `MyNat`; its two constructors `MyNat.zero` and `MyNat.succ`, so every element is either `zero` or `succ n`; and a *recursor* `MyNat.rec` — the type's *eliminator*, the counterpart of its constructors — of the same shape as `Nat.rec`, into which pattern matching, `cases`, and `induction` all translate. Its {ref "reduction-rules"}[iota rule], `MyNat.rec z s (.succ n) ⟶ s n (MyNat.rec z s n)`, is the firing we watched for `Nat`. And a recursor is not special to `inductive`: since a `structure` is a single-constructor inductive, it too has one — `Point.rec` (from the next section) takes a single case, a function of the fields, and the projections `Point.x`, `Point.y` are defined through it.

With {ref "type-universes"}[universes] available, the recursor can be stated in full generality. The introduction used its *non-dependent* form, into a fixed result type; the true `MyNat.rec` lets that type *depend* on the value being consumed, a dependency recorded by a *motive* `MyNat → Sort u` (the leading `@` in `@MyNat.rec` makes Lean's normally-hidden implicit arguments — here the `motive` — explicit, so that `#check` prints them; see {ref "strict-implicit"}[the appendix on parentheses]):

```lean
#check @MyNat.rec
-- {motive : MyNat → Sort u} →
--   motive .zero →                      -- zero case
--   ((n : MyNat) → motive n →
--      motive n.succ) →                 -- succ case
--   (t : MyNat) → motive t
```

With a data-valued `motive` this is the *recursion* the introduction showed; with a `Prop`-valued one it is precisely the *induction principle*. Recursion and induction are thus two readings of the single primitive `MyNat.rec` — which is why the `induction` tactic and recursive definitions feel so alike.

The declaration only *forms the type*. How to actually build its elements and *define functions* on it — typically by pattern matching on the constructors — is the subject of {ref "terms"}[the next chapter], on constructing terms.

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

Inductive types are the main mechanism by which new data types enter Lean, and `Mathlib` uses them throughout. They also settle the universe question from the other side: the universe of an inductive type must be large enough to hold all of its constructor arguments.

Not every `inductive` declaration is accepted. A constructor may mention the type being defined, but only *positively*: never to the *left* of an arrow inside one of its arguments. This *strict positivity* condition keeps inductive types well-founded and free of paradox. An *infinitely-branching* tree — where a `node` carries one subtree for each natural number — is fine, because in the `node` constructor `MyTree` occurs only to the *right* of `→`:

```lean
inductive MyTree where
  | leaf : ℕ → MyTree              -- a leaf holds a value
  | node : (ℕ → MyTree) → MyTree   -- positive occurrence

-- leaves now carry data, and trees can be built:
example : MyTree := .leaf 7
example : MyTree := .node (fun n => .leaf n)
```

The `leaf` case is what gets the type off the ground. Positivity constrains only *where* `MyTree` may occur, not whether the type has any elements: drop `leaf`, and the declaration is *still accepted*, but no closed `MyTree` can ever be built — every `node` already demands a whole family `ℕ → MyTree` of subtrees, with nothing to start from, so the type is *empty* (like `Empty`; one can even prove `MyTree → False`). With `leaf` present you build upward — `leaf 7`, then `node (fun n => leaf n)`, then trees over those. Note that `leaf` here *carries* a `ℕ`, so different leaves are genuinely different; a bare `leaf : MyTree` would give a single, featureless leaf, indistinguishable from every other.

Because `node` takes a *function* `ℕ → MyTree`, every node has one child per natural number — it branches *infinitely*. It is not that *every* `MyTree` is infinite: a leaf is finite (`leaf 7` is a complete tree), so only trees that actually use `node` are. The infinite branching comes from the function-typed argument. A finitely-branching tree would be `node : MyTree → MyTree → MyTree`, where `MyTree` occurs directly rather than inside a function, so the right-of-`→` case would not arise.

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

so `neg : Bad → False`. Then `Bad.mk neg : Bad`, and `neg (Bad.mk neg) : False` is a closed proof of `False` (it even loops, `neg (Bad.mk neg) ⟶ neg (Bad.mk neg)` — the untyped Ω combinator smuggled into the theory). Strict positivity outlaws exactly the negative occurrence that ties this self-applying knot — the same consistency concern that rules out `Type : Type`. (That positivity is also *sufficient* for consistency — every strictly positive type is the least fixed point of a monotone functor, so the theory has a model — is a deep metatheorem, not something Lean proves about itself.)

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

This declares a type `Point` whose elements are records with two `ℕ` fields. There is a single constructor, so both fields must be supplied. The declaration also produces that constructor `Point.mk` and one projection per field, whose types can be inspected without building a value:

```lean
#check (Point.mk : ℕ → ℕ → Point)
#check (Point.x : Point → ℕ)
#check (Point.y : Point → ℕ)
```

A value of a structure is determined by its fields: `p` and `Point.mk p.x p.y` are *definitionally* equal, so `rfl` proves it. This is the η rule of the {ref "reduction-rules"}[reduction rules], here *for structures*. It holds for every structure, for instance for pairs `ℕ × ℕ`:

```lean
example (p : Point) : p = Point.mk p.x p.y := rfl
example (p : ℕ × ℕ) : p = (p.1, p.2) := rfl
```

For a general inductive type there is no such rule: `n : ℕ` is not definitionally `0` or a successor, and to split on it you need `cases`.

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

and a structure may bundle *data together with a property* — here a linear map, carrying both a function and a proof that it respects addition (the square brackets `[Add α]` are an *instance-implicit* argument, requiring `α` to carry an addition; see {ref "square-bracket-notation"}[the typeclasses chapter]):

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

The fourth way to form a type, after universes, function types and inductive types, is the *quotient*. Given a type `α` and a relation `r : α → α → Prop`, the type `Quot r` glues together elements that `r` relates: `α` seen up to `r`. This makes `ℝ` as Cauchy sequences up to equivalence an actual construction. `ℤ`, `ℚ`, `Multiset α` (lists up to reordering) and `ZMod n` are quotients too.

Its entire interface is four constants:

```lean
#check @Quot.mk     -- (r : α → α → Prop) → α → Quot r
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#check @Quot.lift   -- (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β
#check @Quot.ind
```

- `Quot.mk r` sends each element to its class.
- `Quot.sound` is the crux: if `r a b`, then the two classes are *the same term*. It is one of Lean's few genuine axioms — the `#print axioms name` command traces a constant back to the axioms it depends on, and here `#print axioms Quot.sound` reports `[Quot.sound]`.
- `Quot.lift` defines a function *out of* the quotient — but only once you *prove* it respects `r` (the `∀ a b, r a b → f a = f b` argument), which is exactly the mathematician's "check that this is well-defined". And it computes: `Quot.lift f h (Quot.mk r a)` reduces to `f a`.
- `Quot.ind` proves a property of every quotient element by checking it on the classes `Quot.mk r a`.

The computation rule of `Quot.lift` is a {ref "reduction-rules"}[reduction rule] of its own, like ι for recursors, so `rfl` proves it:

```lean
example (r : Nat → Nat → Prop) (f : Nat → Nat)
    (h : ∀ a b, r a b → f a = f b) (a : Nat) :
    Quot.lift f h (Quot.mk r a) = f a := rfl
```

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

Addition is the first use of `Quot.lift`. Two reals are added by adding *representative* sequences termwise, which is well-defined because `+` respects the relation: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`. With that checked, `Quot.lift` yields the computation rule that `mk` is an additive homomorphism:

```lean
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

This `mk (f) + mk (g) = mk (f + g)` equation *is* the `Quot.lift f h (Quot.mk r a) ⟶ f a` reduction from the {ref "reduction-rules"}[reduction rules], applied to a two-argument operation.
:::
::::
