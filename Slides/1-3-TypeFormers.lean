import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Types and terms II: pairs, subtypes, families,
quotients" of part 1 (Lean and its type theory). It follows the
chapter section by section: Σ-types, subtypes, type families, indexed
families, the logical connectives as types with tactic and term mode, quotient
types, the table of the four steps, and some history.
-/

namespace SlidesTypeFormers
#doc (Slides) "Types and terms II: pairs, subtypes, families, quotients" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
.reveal section .small table, .reveal section table.small { font-size: 0.5em; }
.reveal section .small table code, .reveal section table.small code { font-size: 0.95em; }
.reveal section .small td, .reveal section table.small td { padding: 0.1em 0.6em; }
```

# Types and terms II

Lean and its type theory — chapter 3: pairs, subtypes, families, quotients

:::class "key"
Each type former again in four steps: formation, construction, use, computation.
:::

# Pairs and Σ-types

```lean -panel -stretch
def aPair : (n : ℕ) × Fin (n + 1) :=
  ⟨3, Fin.last 3⟩
#eval aPair.1   -- 3
example (p : ℕ × ℕ) : p = (p.1, p.2) := rfl
```

- _Formation_: `(x : α) × β x`, also `Σ x, β x`; `α × β` if nothing depends
- _Construction_: `⟨a, b⟩`
- _Use_: `.1`, `.2` (also `.fst`, `.snd`)
- _Computation_: `⟨a, b⟩.1 ⟶ a`

:::class "key"
In sets: the disjoint union $`\coprod_x \beta(x)`.
:::

# Sum and product

`Fintype.card α` is the number of elements; `decide` computes both sides.

```lean -panel -stretch
-- Σ: 1 + 2 + 3 + 4
example : Fintype.card
    ((n : Fin 4) × Fin (n + 1)) = 10 := by decide
-- Π: 1 · 2 · 3 · 4
example : Fintype.card
    ((n : Fin 4) → Fin (n + 1)) = 24 := by decide
```

:::table +colHeaders
*
  * non-dependent
  * dependent
  * for propositions
*
  * `α → β`
  * `(x : α) → β x`
  * `∀ x, P x`
*
  * `α × β`
  * `(x : α) × β x`
  * `∃ x, P x`
:::

# Subtypes

```lean -panel -stretch
def BigNat : Type := {n : ℕ // n > 5}

def seven : BigNat := ⟨7, by decide⟩
#eval seven.val  -- 7
```

- _Formation_: `{x : α // P x}`, i.e. `Subtype P`
- _Construction_: `⟨a, h⟩` with `h : P a`
- _Use_: `.val`, `.property`
- _Computation_: `⟨a, h⟩.val ⟶ a`

:::class "key"
Proof irrelevance: two elements are equal iff their values are (`Subtype.ext`).
:::

# Subtypes and sets

- Many Mathlib objects are subtypes, e.g. `{n : ℕ // Nat.Prime n}`.
- `Fin n` carries the same data as `{i : ℕ // i < n}`, but is a type of its own.
- A set `s : Set α` selects elements, which keep their type `α`.
- The subtype `{x : α // P x}` is a _new_ type.

# Type families

A type family is a function that returns a type.

```lean -panel -stretch
def BoolFamily : Bool → Type
  | true  => ℕ
  | false => String

def fiber (f : ℕ → ℕ) (b : ℕ) : Type :=
  {a : ℕ // f a = b}

def fiberExample : fiber (· * 2) 10 := ⟨5, rfl⟩
```

# Vectors and matrices

`![a, b, c]` is the function on `Fin 3` with values `a`, `b`, `c`.

```lean -panel -stretch
def myVec : Fin 3 → ℕ := ![10, 20, 30]
#eval myVec 2   -- 30

def myMatrix : Fin 2 → Fin 3 → ℕ :=
  ![![1, 2, 3], ![4, 5, 6]]
#eval myMatrix 1 2  -- 6
```

:::class "key"
Index 5 of a 3-element vector does not exist. A dimension mismatch is a type error.
:::

# Indexed families

```lean -panel -stretch
inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons {n : ℕ} : α → Vec α n →
      Vec α (n + 1)

def Vec.head {α : Type} {n : ℕ} :
    Vec α (n + 1) → α
  | .cons a _ => a
```

`α` is a _parameter_, fixed for all constructors. The `ℕ` is an _index_: each constructor chooses it.

:::class "key"
`head` needs no case for `nil`: its index `0` is not `n + 1`.
:::

# Inductive predicates

```lean -panel -stretch
inductive MyEven : ℕ → Prop where
  | zero : MyEven 0
  | add_two (n : ℕ) : MyEven n → MyEven (n + 2)

example : ¬ MyEven 1 := by
  intro h
  cases h
```

The constructors are the only ways to prove `MyEven n`. `cases h` keeps the constructors whose index fits.

:::class "key"
`≤` on `ℕ` and `=` are inductive predicates of this kind.
:::

# Propositions as types

A proposition `P : Prop` is a type; a proof is a term `h : P`. The connectives are the type formers, with values in `Prop`.

```lean -panel -stretch
example (P : Prop) : (¬P) = (P → False) := rfl

example : True := True.intro
example (C : Prop) (h : False) : C := nomatch h
```

- `→`, `∀`: function types; `¬P` is `P → False`
- `True`: one constructor; `False`: none, so `nomatch` needs no branch

# Proofs of implications

A proof of `P → Q` is a function from proofs of `P` to proofs of `Q`.

```lean -panel -stretch
example (P Q : Prop) (hP : P) (hPQ : P → Q) :
    Q :=
  hPQ hP

example (P Q R : Prop) :
    (P → Q) → (Q → R) → (P → R) :=
  fun hPQ hQR hP => hQR (hPQ hP)
```

Modus ponens is application; chaining is composition.

# Tactic mode and term mode

```lean -panel -stretch
example (P Q R : Prop) (hQR : Q → R) (hPQ : P → Q) :
    P → R := by
  intro hP
  exact hQR (hPQ hP)

example (P Q R : Prop) (hQR : Q → R) (hPQ : P → Q) :
    P → R := fun hP ↦ hQR (hPQ hP)
```

After `by`, each tactic changes the proof state: hypotheses above `⊢`, the goal after it. `show_term` prints the term built.

:::class "key"
`intro` builds a `fun`; `exact` supplies a term.
:::

# Conjunction and disjunction

```lean -panel -stretch
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.2, h.1⟩

example (P Q R : Prop) (h : P ∨ Q)
    (hPR : P → R) (hQR : Q → R) : R :=
  match h with
  | Or.inl hP => hPR hP
  | Or.inr hQ => hQR hQ
```

`And`: a structure, like `α × β`. `Or`: an inductive type with `Or.inl`, `Or.inr`.

:::class "key"
A match on `P ∨ Q` may only prove propositions: which side holds cannot be turned into data.
:::

# The existential quantifier

```lean -panel -stretch
example : ∃ n : ℕ, n > 5 := ⟨7, by decide⟩

example (P Q : ℕ → Prop) (h : ∃ n, P n ∧ Q n) :
    ∃ n, Q n :=
  match h with
  | ⟨n, hn⟩ => ⟨n, hn.2⟩
```

`Exists`: one constructor, a witness and a proof. Like the subtype `{n : ℕ // n > 5}`, but in `Prop`: the witness can be used in proofs, not computed with.

:::class "key"
`∃` is the propositional truncation of `Σ`: it forgets which witness was given.
:::

# The dictionary

:::table +colHeaders +rowSeps
*
  * proposition
  * type former
  * a proof is
*
  * `P → Q`, `∀ x, P x`
  * Π-type
  * a function
*
  * `P ∧ Q`
  * structure, like `α × β`
  * `⟨hP, hQ⟩`
*
  * `P ∨ Q`
  * inductive, like a disjoint union
  * `Or.inl hP`, `Or.inr hQ`
*
  * `∃ x, P x`
  * inductive, like a Σ-type
  * `⟨a, h⟩`
*
  * `True`, `False`
  * one, no constructor
  * `True.intro`; none
*
  * `¬P`
  * `P → False`
  * a function into `False`
:::

# Quotient types

`Quot r`: the type `α` seen up to a relation `r`. Examples: `ℤ`, `ℚ`, `ℝ`, `Multiset α`, `ZMod n`.

- _Formation_: `Quot r`
- _Construction_: `Quot.mk r a`, the class of `a`
- _Use_: `Quot.lift f h`, with `h` a proof that `f` respects `r`
- _Computation_: `Quot.lift f h (Quot.mk r a) ⟶ f a`

:::class "key"
`Quot.lift` is the mathematician's "check that this is well-defined".
:::

# One axiom

```lean -panel -stretch
#check @Quot.sound  -- r a b → Quot.mk r a = Quot.mk r b
#print axioms Quot.sound
```

That related elements have the _same_ class does not follow from the four steps. Lean assumes it as an _axiom_.

# The real numbers as a quotient

A real number: a Cauchy sequence of rationals; sequences whose difference tends to `0` give the same number.

::::class "small"
:::table +colHeaders +rowSeps
*
  * step
  * in Mathlib
  * type former
*
  * Cauchy sequences
  * `CauSeq ℚ abs` = `{f : ℕ → ℚ // IsCauSeq abs f}`
  * subtype
*
  * their classes
  * `CauSeq.Completion.Cauchy abs`, by `f ≈ g ↔ f - g → 0`
  * quotient
*
  * `ℝ`
  * `structure Real` with one field `cauchy`
  * structure
:::
::::

```lean -panel -stretch
example (f g : CauSeq ℚ abs) :
    f ≈ g ↔ (f - g).LimZero := Iff.rfl
```

# Adding real numbers

```lean -panel -stretch
example (f g : CauSeq ℚ abs) :
    CauSeq.Completion.mk f + CauSeq.Completion.mk g
      = CauSeq.Completion.mk (f + g) :=
  CauSeq.Completion.mk_add f g
```

Add representatives termwise. Well defined: `f ≈ f'` and `g ≈ g'` give `f + g ≈ f' + g'`; then `Quot.lift` gives `+` on the classes.

:::class "key"
This equation is the computation rule `Quot.lift f h (Quot.mk r a) ⟶ f a`.
:::

# The four steps at a glance

::::class "small"
:::table +colHeaders +rowSeps
*
  * type
  * formation
  * construction
  * use
  * computation
*
  * function
  * `(x : α) → β x`
  * `fun x => e`
  * `f a`
  * β
*
  * inductive
  * `inductive T`
  * constructors
  * pattern matching
  * ι
*
  * structure
  * `structure S`
  * `⟨a, b⟩`
  * `s.x`
  * `(S.mk a b).x ⟶ a`
*
  * Σ-type
  * `(x : α) × β x`
  * `⟨a, b⟩`
  * `.1`, `.2`
  * `⟨a, b⟩.1 ⟶ a`
*
  * subtype
  * `{x : α // P x}`
  * `⟨a, h⟩`
  * `.val`
  * `⟨a, h⟩.val ⟶ a`
*
  * indexed family
  * `inductive T : I → Sort u`
  * constructors
  * `cases`
  * ι
*
  * quotient
  * `Quot r`
  * `Quot.mk r a`
  * `Quot.lift f h`
  * `… ⟶ f a`
:::
::::

:::class "key"
Chapter 1.4 states these steps as the rules of Lean's type theory.
:::

# Some history

Russell's set $`R = \{x : x \notin x\}` broke Frege in 1902. Russell's repair (1908): `x ∈ x` is not a statement at all.

:::table +colHeaders +rowSeps
*
  * system
  * broken by
  * repaired by
*
  * Frege, _Grundgesetze_
  * Russell, 1902
  * types, 1908
*
  * Church's lambda calculus, 1932
  * Kleene, Rosser, 1935
  * simple types, 1940
*
  * Martin-Löf, 1971
  * Girard
  * universe hierarchy
:::

Curry (1934), Howard (1969): propositions are types, proofs are terms. Then the Calculus of Constructions (1985) and inductive types (1990).

# Summary

- `(x : α) × β x`: dependent pairs, a disjoint union. Subtypes: the second component is a proof.
- Type families are functions into a universe; with `inductive`, the constructors fix the index.
- A proof of `P → Q` is a function; `intro` builds it, `exact` supplies a term.
- The connectives are these type formers in `Prop`: `∧` a structure, `∨`, `∃`, `False` inductive types.
- `Quot r`: a type up to a relation, with the axiom `Quot.sound`. `ℝ`: Cauchy sequences up to null sequences.
