import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open MyDef

set_option pp.rawOnError true

#doc (Manual) "The Curry-Howard Correspondence" =>
%%%
htmlSplit := .never
tag := "curry-howard"
%%%

The Curry-Howard correspondence is one of the most profound ideas in the foundations of mathematics and computer science. It establishes a deep connection between logic and type theory: **propositions correspond to types**, and **proofs correspond to terms** (programs) of those types. In Lean 4, this correspondence is not merely a theoretical curiosity -- it is the very foundation on which the proof assistant is built.

# Historical context
%%%
tag := "curry-howard-history"
%%%

The correspondence is named after Haskell Curry and William Alvin Howard, but its roots go deeper:

- **Haskell Curry** (1934) observed that the types of combinators in combinatory logic correspond to axiom schemes in propositional logic.
- **William Howard** (1969, published 1980) extended this to a full correspondence between natural deduction and simply typed lambda calculus.
- **Nicolaas Govert de Bruijn** independently discovered the correspondence while developing the Automath system (1968), one of the first proof checkers.
- **Per Martin-Löf** (1971 onwards) developed intuitionistic type theory, extending the correspondence to predicate logic with dependent types.

Lean's type theory is a descendant of Martin-Löf's work, enriched with features from the Calculus of Inductive Constructions (as used in Coq).

# Propositions as types, proofs as terms
%%%
tag := "props-as-types"
%%%

In Lean, every proposition `P : Prop` is a type. A proof of `P` is a term `h : P` -- that is, an inhabitant of the type `P`. If a type is inhabited, the corresponding proposition is true; if it is empty, the proposition is false.

This idea is sometimes called the **BHK interpretation** (Brouwer-Heyting-Kolmogorov), which gives a constructive meaning to the logical connectives. Let us see how each connective maps to a type-theoretic construction.

# Implication = function type
%%%
tag := "implication-function"
%%%

The most fundamental instance of the correspondence: **implication corresponds to the function type**.

If `P` and `Q` are propositions, then `P → Q` is the type of functions from `P` to `Q`. A proof of `P → Q` is a function that, given a proof of `P`, produces a proof of `Q`.

Here is the same theorem proved in two ways -- by tactic and by term:

```lean
-- Tactic proof
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  exact hPQ hP

-- Term proof: just function application!
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q :=
  hPQ hP
```

A proof of `P → Q → R` is a function of two arguments (curried):

```lean
-- Tactic proof
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hPQ hQR hP
  exact hQR (hPQ hP)

-- Term proof: composition of functions
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
  fun hPQ hQR hP => hQR (hPQ hP)
```

# Conjunction = product type
%%%
tag := "conjunction-product"
%%%

The conjunction `P ∧ Q` corresponds to the product type `P × Q` (more precisely, it is defined as a structure with two fields). A proof of `P ∧ Q` is a pair `⟨hP, hQ⟩` consisting of a proof of `P` and a proof of `Q`.

```lean
-- Tactic proof
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact ⟨hP, hQ⟩

-- Term proof: just construct the pair
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨hP, hQ⟩

-- Eliminating a conjunction: projections
example (P Q : Prop) (h : P ∧ Q) : P :=
  h.1

example (P Q : Prop) (h : P ∧ Q) : Q :=
  h.2
```

Note that `And.intro` is the constructor, and `And.left` / `And.right` (equivalently `.1` / `.2`) are the projections -- exactly like a product type.

# Disjunction = sum type
%%%
tag := "disjunction-sum"
%%%

The disjunction `P ∨ Q` corresponds to the sum type (coproduct). A proof of `P ∨ Q` is either a proof of `P` (tagged with `Or.inl`) or a proof of `Q` (tagged with `Or.inr`).

```lean
-- Tactic proof
example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP

-- Term proof: inject into the left summand
example (P Q : Prop) (hP : P) : P ∨ Q :=
  Or.inl hP

-- Eliminating a disjunction: case analysis
example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R :=
  h.elim hPR hQR
```

# Negation = function to False
%%%
tag := "negation-false"
%%%

Negation `¬P` is defined as `P → False`. That is, a proof of `¬P` is a function that takes a hypothetical proof of `P` and derives a contradiction.

```lean
-- Negation is just a function to False
example (P : Prop) : ¬P = (P → False) := rfl

-- Tactic proof
example (P : Prop) (hP : P) (hnP : ¬P) : False := by
  exact hnP hP

-- Term proof: function application
example (P : Prop) (hP : P) (hnP : ¬P) : False :=
  hnP hP

-- Ex falso: from False, anything follows
example (P : Prop) (h : False) : P :=
  h.elim
```

# Universal quantifier = dependent function type (Pi type)
%%%
tag := "forall-pi"
%%%

The universal quantifier `∀ (x : α), P x` corresponds to the **dependent function type** (Pi type) `(x : α) → P x`. A proof is a function that, for each `x : α`, produces a proof of `P x`.

```lean
-- Tactic proof
example : ∀ (n : ℕ), n = n := by
  intro n
  rfl

-- Term proof: a dependent function (lambda)
example : ∀ (n : ℕ), n = n :=
  fun n => rfl
```

Notice that in Lean, `∀` and the dependent arrow `→` are actually the same thing. When the codomain does not depend on the input, the dependent function type degenerates to the ordinary function type.

# Existential quantifier = dependent pair type (Sigma type)
%%%
tag := "exists-sigma"
%%%

The existential quantifier `∃ (x : α), P x` corresponds to the **dependent pair type**. A proof consists of a witness `a : α` together with a proof that `P a` holds.

```lean
-- Tactic proof
example : ∃ (n : ℕ), n > 0 := by
  use 1

-- Term proof: construct the dependent pair
example : ∃ (n : ℕ), n > 0 :=
  ⟨1, by norm_num⟩

-- Another example
example : ∃ (n : ℕ), n + n = 10 :=
  ⟨5, by norm_num⟩
```

Note: There is an important distinction between `∃` (which lives in `Prop`) and `Σ` (which lives in `Type`). We discuss this further in the chapter on dependent types.

# How tactic proofs build terms behind the scenes
%%%
tag := "tactic-to-term"
%%%

When you write a tactic proof in Lean, the tactic block constructs a term behind the scenes. Every tactic manipulates the proof state and ultimately produces a term of the goal type. You can use `show_term` (or look at the output of `#print`) to see what term a tactic proof generates.

```lean
-- Use show_term to see what the tactic proof builds
-- (Hover over show_term in VS Code to see the output)
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  show_term
  exact ⟨hP, hQ⟩
```

Here is a more complex example where the term proof is less obvious:

```lean
-- Tactic proof
example (P Q R : Prop) : (P ∧ Q) → R → (R ∧ P) := by
  intro ⟨hP, _⟩ hR
  exact ⟨hR, hP⟩

-- Equivalent term proof
example (P Q R : Prop) : (P ∧ Q) → R → (R ∧ P) :=
  fun ⟨hP, _⟩ hR => ⟨hR, hP⟩
```

# Summary table
%%%
tag := "curry-howard-summary"
%%%

Here is a summary of the Curry-Howard dictionary:

| Logic | Type Theory | Lean notation |
|---|---|---|
| Proposition | Type | `P : Prop` |
| Proof | Term (inhabitant) | `h : P` |
| Implication `P → Q` | Function type | `P → Q` |
| Conjunction `P ∧ Q` | Product type | `P ∧ Q` / `And P Q` |
| Disjunction `P ∨ Q` | Sum type | `P ∨ Q` / `Or P Q` |
| True | Unit type | `True` |
| False | Empty type | `False` |
| Negation `¬P` | Function to empty | `P → False` |
| `∀ (x : α), P x` | Dependent function (Π) | `(x : α) → P x` |
| `∃ (x : α), P x` | Dependent pair (Σ) | `⟨a, ha⟩ : ∃ x, P x` |

Understanding this correspondence is key to becoming fluent in Lean: when you write a tactic proof, you are really constructing a term; when you write a term proof, you are programming a function. The two perspectives are equivalent, and switching between them often leads to deeper understanding.
