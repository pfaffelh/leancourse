import Mathlib

/-!
# 1.3-c -- Proofs as terms

*Notes chapters 1.2 and 1.3, week 5.*

A proof is a term, and most of the tactics from the logic sheets
only build one step by step. On this sheet you write the terms
yourself, without `by`. Read *Proofs of implications* in chapter 1.2
and *Propositions as types* in chapter 1.3 first.

## Introduced here

| term                    | proves                     | tactic it replaces    |
|-------------------------|----------------------------|-----------------------|
| `fun hP => t`           | `P → Q`, given `t : Q`     | `intro hP`            |
| `f hP`                  | `Q`, from `f : P → Q`      | `apply f`, `exact`    |
| `⟨hP, hQ⟩`              | `P ∧ Q`                    | `constructor`         |
| `h.1`, `h.2`            | `P`, `Q` from `h : P ∧ Q`  | `obtain ⟨hP, hQ⟩ := h` |
| `Or.inl hP`, `Or.inr hQ` | `P ∨ Q`                   | `left`, `right`       |
| `h.elim f g`            | `R`, from `h : P ∨ Q`      | `obtain hP \| hQ := h` |
| `(h : False).elim`      | anything                   | `exfalso`             |
| `⟨a, h⟩`                | `∃ x, P x`                 | `use a`               |

`show_term` in front of tactics prints the term they build, which
helps when you are stuck.
-/

variable (P Q R S : Prop)

/-! ## Part 1: Implication, conjunction, disjunction -/

-- Exercise 1) The identity function.
example : P → P :=
  sorry

-- Exercise 2) A function that ignores its second argument.
example : P → Q → P :=
  sorry

-- Exercise 3) Composition.
example : (P → Q) → (Q → R) → P → R :=
  sorry

-- Exercise 4)
example (hP : P) (hQ : Q) : P ∧ Q :=
  sorry

-- Exercise 5)
example (h : P ∧ Q) : P :=
  sorry

-- Exercise 6)
example : P ∧ Q → Q ∧ P :=
  sorry

-- Exercise 7)
example (hP : P) : P ∨ Q :=
  sorry

-- Exercise 8) `h.elim` takes one function per case.
example : P ∨ Q → (P → R) → (Q → R) → R :=
  sorry

-- Exercise 9)
example : P ∨ Q → Q ∨ P :=
  sorry

-- Exercise 10)
example : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  sorry

/-! ## Part 2: Negation

`¬P` is `P → False`, so a proof of `¬P` is a function, and applying
it to a proof of `P` gives `False`. -/

-- Exercise 11)
example : (P → Q) → ¬Q → ¬P :=
  sorry

-- Exercise 12)
example : P → ¬P → Q :=
  sorry

-- Exercise 13)
example : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  sorry

/-! ## Part 3: The same proof twice

Give a tactic proof and a term proof of each statement. Then put
`show_term` in front of your tactics and compare. -/

-- Exercise 14a)
example : (P → Q) → (P → R) → P → Q ∧ R := by
  sorry

-- Exercise 14b)
example : (P → Q) → (P → R) → P → Q ∧ R :=
  sorry

-- Exercise 15a)
example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  sorry

-- Exercise 15b)
example : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  sorry

/-! ## Part 4: Quantifiers

A proof of `∀ x, P x` is a function `fun x => …`, a proof of
`∃ x, P x` a pair `⟨a, h⟩`. Inside a term, `by decide` or
`by omega` may prove a numerical fact. -/

-- Exercise 16)
example : ∀ (n : ℕ), n + 0 = n :=
  sorry

-- Exercise 17)
example : ∃ (n : ℕ), n * n = 16 :=
  sorry

-- Exercise 18) Use `h` at one point.
example (h : ∀ (n : ℕ), n < n + 1) : ∃ (n : ℕ), n < n + 1 :=
  sorry

-- Exercise 19)
example : ∀ (n : ℕ), P → n = n :=
  sorry

-- Exercise 20) The second component is itself a pair.
example : ∃ (n : ℕ), n > 10 ∧ n < 15 :=
  sorry

/-! ## Part 5: More -/

-- Exercise 21) `P ↔ Q` is a structure with fields `mp : P → Q` and
-- `mpr : Q → P`, so a proof is a pair of functions.
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  sorry

-- Exercise 22) For each `n` a witness and a proof.
example : ∀ (n : ℕ), ∃ (k : ℕ), n + n = 2 * k :=
  sorry

-- Exercise 23) `def` and `theorem` do the same thing: name a term.
-- (The linter prefers `theorem` for proofs, hence the option.)
set_option linter.defProp false in
def modusPonens : (P → Q) → P → Q :=
  sorry

-- Exercise 24) Swapping the arguments of a function is the
-- commutativity of `∧` in another form.
set_option linter.defProp false in
def flip' (f : P → Q → R) : Q → P → R :=
  sorry
