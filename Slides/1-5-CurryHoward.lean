import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Propositions and proofs" (Curry-Howard) of the
Lean part. It follows the chapter section by section: history, the two
proof modes, then one slide per connective, `Nonempty`, how tactics
build terms, the dictionary, and the step to practice.
-/

namespace SlidesCurryHoward
#doc (Slides) "Propositions and proofs" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Propositions and proofs

Lean and its type theory — the Curry-Howard correspondence

:::class "key"
Propositions are types. Proofs are terms.
:::

# Historical context

- *Curry*, 1934: types of combinators correspond to axiom schemes.
- *Howard*, 1969 (published 1980): natural deduction and simply typed lambda calculus.
- *de Bruijn*, 1968: found it independently, for Automath.
- *Martin-Löf*, from 1971: dependent types, predicate logic.

Lean descends from Martin-Löf's type theory, with features of the
Calculus of Inductive Constructions (Coq).

# Propositions as types

Every proposition `P : Prop` is a type.
A proof of `P` is a term `h : P`.

- inhabited type: the proposition is true
- empty type: the proposition is false

The connectives get a constructive meaning: the BHK interpretation
(Brouwer, Heyting, Kolmogorov).

# Tactic mode and term mode

Term mode: write the term. Tactic mode: after `by`, build it step by
step. The proof state shows hypotheses above `⊢`, the goal after it.

```lean -panel -stretch
example (P : Prop) : False → P := False.elim

example (P : Prop) : False → P := by
  exact False.elim
```

:::class "key"
`exact` is calling a function.
:::

# `intro` takes an argument

```lean -panel -stretch
example (s t : Set ℝ) (hst : s ⊆ t) (x : ℝ) :
    x ∈ s → x ∈ t := fun hx ↦ hst hx

example (s t : Set ℝ) (hst : s ⊆ t) (x : ℝ) :
    x ∈ s → x ∈ t := by
  intro hx
  exact hst hx
```

:::class "key"
`intro` names the argument of a function.
:::

# True and False

`True`: one constructor, always inhabited.
`False`: no constructor, no proof can be built.

```lean -panel -stretch
example : True := True.intro

example (C : Prop) : False → C :=
  fun h => nomatch h
```

:::class "key"
From `False`, any goal: _ex falso quodlibet_, `False.elim`.
:::

# Implication = function type

A proof of `P → Q` turns a proof of `P` into a proof of `Q`.

```lean -panel -stretch
example (P Q : Prop) (hP : P) (hPQ : P → Q) :
    Q :=
  hPQ hP

example (P Q R : Prop) :
    (P → Q) → (Q → R) → (P → R) :=
  fun hPQ hQR hP => hQR (hPQ hP)
```

Modus ponens is application; chaining is composition.

# Conjunction = product type

A proof of `P ∧ Q` is a pair `⟨hP, hQ⟩`.

```lean -panel -stretch
example (P Q : Prop) (hP : P) (hQ : Q) :
    P ∧ Q :=
  ⟨hP, hQ⟩

example (P Q : Prop) (h : P ∧ Q) : P := h.1
example (P Q : Prop) (h : P ∧ Q) : Q := h.2
```

Constructor `And.intro`, projections `And.left`, `And.right`.

# Disjunction = sum type

A proof of `P ∨ Q` is a proof of `P` tagged `Or.inl`,
or a proof of `Q` tagged `Or.inr`.

```lean -panel -stretch
example (P Q : Prop) (hP : P) : P ∨ Q :=
  Or.inl hP

example (P Q R : Prop) (h : P ∨ Q)
    (hPR : P → R) (hQR : Q → R) : R :=
  h.elim hPR hQR
```

Using a disjunction is case analysis.

# Negation = function to False

`¬P` is defined as `P → False`.

```lean -panel -stretch
example (P : Prop) : (¬P) = (P → False) := rfl

example (P : Prop) (hP : P) (hnP : ¬P) :
    False :=
  hnP hP
```

:::class "key"
A proof of `¬P` turns a proof of `P` into a contradiction.
:::

# Universal quantifier = Pi type

`∀ (x : α), P x` is the dependent function type `(x : α) → P x`.

```lean -panel -stretch
example : ∀ (n : ℕ), n = n := by
  intro n
  rfl

example : ∀ (n : ℕ), n = n :=
  fun n => rfl
```

`∀` and the dependent arrow are the same thing. If the codomain does
not depend on the input, it is the ordinary arrow.

# Existential quantifier = Sigma type

A proof of `∃ (x : α), P x` is a witness `a` with a proof of `P a`.

```lean -panel -stretch
example : ∃ (n : ℕ), n > 0 := by
  use 1; norm_num

example : ∃ (n : ℕ), n + n = 10 :=
  ⟨5, by norm_num⟩
```

`∃` lives in `Prop`, `Σ` lives in `Type`.

# Nonempty

`Nonempty α` is a proposition: `α` has an element, but none is given.
This is the propositional truncation of `α`.

```lean -panel -stretch
example {α : Type} (a : α) : Nonempty α :=
  ⟨a⟩

noncomputable example {α : Type}
    (h : Nonempty α) : α :=
  Classical.choice h
```

:::class "key"
Getting the element back needs the axiom `Classical.choice`.
:::

# Tactics build terms

Each tactic changes the proof state; the block produces a term.
`show_term` or `#print` shows which.

```lean -panel -stretch
example (P Q R : Prop) :
    (P ∧ Q) → R → (R ∧ P) := by
  intro ⟨hP, _⟩ hR
  exact ⟨hR, hP⟩

example (P Q R : Prop) :
    (P ∧ Q) → R → (R ∧ P) :=
  fun ⟨hP, _⟩ hR => ⟨hR, hP⟩
```

# The dictionary

:::table +colHeaders
*
  * Logic
  * Type theory
  * Lean
*
  * proposition / proof
  * type / term
  * `P : Prop`, `h : P`
*
  * implication
  * function type
  * `P → Q`
*
  * conjunction
  * product type
  * `P ∧ Q`
*
  * disjunction
  * sum type
  * `P ∨ Q`
*
  * True / False
  * unit / empty type
  * `True`, `False`
*
  * negation
  * function to empty
  * `P → False`
*
  * for all
  * dependent function
  * `(x : α) → P x`
*
  * exists
  * dependent pair
  * `⟨a, ha⟩ : ∃ x, P x`
:::

# From correspondence to practice

To prove a statement, construct a term of its type.
Goldbach's conjecture is a well-formed `Prop`:

```lean -panel -stretch
theorem goldbach : ∀ (n : ℕ) (_ : n > 2)
    (_ : Even n), ∃ (i j : ℕ),
    (Prime i) ∧ (Prime j) ∧ (n = i + j) := by
  sorry
```

A term replacing the `sorry` is a proof. Tactics come in the
exercises; the full list is in the Tactics appendix.

# Summary

- A proposition is a type, a proof is a term.
- `→` is a function, `∧` a pair, `∨` a tagged choice.
- `¬P` is `P → False`; `False` has no proof.
- `∀` is a dependent function, `∃` a witness with a proof.
- A tactic proof builds a term; a term proof is a program.
