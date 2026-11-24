import Mathlib

/-!
# 1.5-a -- Rules, equality and choice

*Notes chapter 1.5, week 6.*

The rules of chapter 1.5 in practice: in which universe a type
lives, when two terms are equal by computation, why proofs carry no
data, functions as terms, and the axioms `funext`, `propext` and
`Classical.choice`. Read chapter 1.5 first. Sheet `2.3-a` (week 12)
returns to the axioms.

## Introduced here

| notation / tactic     | use it when                                |
|-----------------------|--------------------------------------------|
| `change t`            | like `show t`: replace the goal by `t`     |
| `change t at h`       | the same for a hypothesis `h`              |
| `let f := e`          | give a term a name inside a proof          |
| `ext x`               | goal `f = g`: prove `f x = g x`            |
| `propext h`           | `P = Q` from `h : P ↔ Q`                   |
| `Classical.choose h`  | a witness of `h : ∃ x, P x`, without code  |
| `Nat.find h`          | least witness of `h : ∃ n, P n`, with code |
| `choose f hf using h` | from `h : ∀ x, ∃ y, R x y` a function `f`  |

## Tactics from earlier sheets

| sheet   | tactics                              |
|---------|--------------------------------------|
| `L-a`   | `trivial`, `intro`, `exact`, `apply` |
| `L-b`   | `constructor`, `obtain`              |
| `L-c`   | `left`, `right`                      |
| `1.1-a` | `rfl`, `rw`, `show`                  |
| `1.1-b` | `decide`                             |
| `1.2-a` | `use`                                |
| `L-e`   | `by_cases`                           |
| `L-f`   | `have`, `rintro`                     |
| `1.1-c` | `simp`, `omega`                      |
| `L-g`   | `tauto`                              |

`fun x => e` is known from `1.4-b`.
-/

variable (α β : Type)

/-! ## Part 1: Universes

`#check T` shows the type of `T`, so for a type `T` its universe. -/

-- Exercise 1) Decide the universe of each type before you put the
-- cursor on the line. Which rule of chapter 1.5 gives the answer?
#check ℕ → ℕ
#check ℕ → Type
#check Type → Type
#check ∀ n : ℕ, n + 0 = n
#check ∀ p : Prop, p → p
#check (γ : Type) → γ → γ

-- Exercise 2) A term of each type. The second one is a function
-- whose values are types; the third one takes a type as argument.
example : Type 1 := sorry
example : ℕ → Type := sorry
example : (γ : Type) → γ → γ := sorry

/-! ## Part 2: Conversion

Two terms that compute to the same term are definitionally equal,
and `rfl` proves their equality. The steps are β (apply a `fun`),
δ (unfold a definition) and ι (a recursor meets a constructor). -/

def dbl (n : ℕ) : ℕ := n + n

example : dbl 3 = 6 := by
  rfl

-- Exercise 3)
example : (fun n : ℕ => n * n + 1) 3 = 10 := by
  sorry

-- Exercise 4) `¬P` is *by definition* `P → False`.
example (P : Prop) : ¬P ↔ (P → False) := by
  sorry

/-! `change t` replaces the goal by `t`, `change t at h` the
hypothesis `h`. Both work only if the two are definitionally equal. -/

example (P : Prop) (h : ¬¬P) (hn : ¬P) : False := by
  change (P → False) → False at h
  exact h hn

-- Exercise 5) Write the goal as a function type first, then `intro`.
example (P : Prop) (hP : P) : ¬¬P := by
  sorry

/-! ## Part 3: Proofs carry no data

Any two proofs of the same proposition are definitionally equal. -/

example (P : Prop) (h₁ h₂ : P) : h₁ = h₂ := by
  rfl

-- Exercise 6) An element of `Fin 5` is a number and a proof.
example (h₁ h₂ : 2 < 5) : (⟨2, h₁⟩ : Fin 5) = ⟨2, h₂⟩ := by
  sorry

/-! A proof of `∃` cannot be taken apart to define data. Remove the
comment marks: the error says that `Exists.casesOn` "can only
eliminate into `Prop`". -/

-- def witness (h : ∃ n : ℕ, 3 < n) : ℕ :=
--   match h with
--   | ⟨n, _⟩ => n

-- Exercise 7) Taking `h` apart is allowed here, because the goal is
-- a proposition.
example (h : ∃ n : ℕ, 3 < n) : ∃ n : ℕ, 2 < n := by
  sorry

/-! ## Part 4: Functions and predicates

A function is a term `fun x => e`, so `use` can supply one as the
witness of an `∃`. `let` gives it a name first. -/

example (a : α) : ∃ (f : α → α), ∀ x, f x = a := by
  use fun _ => a
  intro x
  rfl

example (a : α) : ∃ (f : α → α), ∀ x, f x = a := by
  let f : α → α := fun _ => a
  use f
  intro x
  rfl

/-! A predicate is a function into `Prop`, built the same way. -/

example (f g : α → Prop) :
    ∃ (h : α → Prop), ∀ x, h x = (f x ∧ g x) := by
  use fun x => f x ∧ g x
  intro x
  rfl

-- Exercise 8) Give `f` and `g` explicitly. Constant functions do.
example : ∃ (f g : α → Prop), ∀ x, f x ↔ ¬(g x) := by
  sorry

-- Exercise 9) The same with `Bool`. Put the cursor on `xor` and
-- press `F12` to see its definition.
example : ∃ (f g : α → Bool), ∀ x, xor (f x) (g x) := by
  sorry

/-! ## Part 5: Equal functions

Two functions are equal if they agree at every point (`funext`,
proved from `Quot.sound` in chapter 1.4). `ext x` turns the goal
`f = g` into `f x = g x`. Here `rfl` fails: `0 + n` does not compute
to `n` for a variable `n`. -/

example : (fun n : ℕ => 0 + n) = (fun n => n) := by
  ext n
  simp

-- Exercise 10) One direction is `ext`, the other is `rw`.
example (f g : α → β) : (∀ x, f x = g x) ↔ f = g := by
  sorry

-- Exercise 11) The right-hand side says that `β` has at most one
-- element. Apply the hypothesis to two constant functions, and
-- evaluate at `a`.
example (a : α) :
    (∀ (f g : α → β), f = g) → (∀ (y₁ y₂ : β), y₁ = y₂) := by
  sorry

/-! ## Part 6: Equal propositions

`propext : (P ↔ Q) → P = Q` is an axiom. -/

example (P Q : Prop) (h : P ↔ Q) : P = Q := propext h

-- Exercise 12) A proposition with a proof equals `True`.
example (P : Prop) (hP : P) : P = True := by
  sorry

-- Exercise 13) For functions into `Prop`, `ext x` leaves the goal
-- `P x ∧ Q x ↔ Q x ∧ P x`: it uses `funext` and `propext`.
example (P Q : α → Prop) :
    (fun x => P x ∧ Q x) = (fun x => Q x ∧ P x) := by
  sorry

/-! With `propext`, `rw [h]` also works for `h : P ↔ Q`: it replaces
`P` by `Q`, because the two are now equal. The following `l1` says
that an implication is a disjunction; it is in Mathlib as
`imp_iff_or_not`. -/

lemma l1 (P Q : Prop) : (P → Q) ↔ (Q ∨ ¬P) := by
  constructor
  · intro hPQ
    by_cases h : P
    · left
      exact hPQ h
    · right
      exact h
  · intro h hP
    obtain (h1 | h2) := h
    · exact h1
    · exact absurd hP h2

-- Exercise 14) Peirce's law. `rw [l1]` rewrites the innermost
-- implication; three times turn the goal into a statement about `∨`
-- and `¬`. Then `by_cases` on `P`. `rintro (h1 | h2)` splits a
-- disjunction while introducing it.
example (P Q : Prop) : ((P → Q) → P) → P := by
  rw [l1, l1, l1]
  sorry

-- Exercise 15) `exact?` finds this one (`not_imp_not`). Do it with
-- `rw` instead: rewrite both sides with `l1`, then `tauto`. `l1`
-- takes the two propositions as arguments, so you can say which
-- instance you mean.
lemma l2 (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  rw [l1 P Q, l1 (¬Q) (¬P)]
  sorry

/-! ## Part 7: Choice

`Classical.choice : Nonempty α → α` is the only way from a proof back
to data. `Classical.choose h` uses it to get a witness of
`h : ∃ x, P x`, and `Classical.choose_spec h` says that the witness
works. A definition that uses it has no code and must be marked
`noncomputable`. -/

noncomputable def pick (h : ∃ n : ℕ, 5 < n) : ℕ :=
  Classical.choose h

example (h : ∃ n : ℕ, 5 < n) : 5 < pick h :=
  Classical.choose_spec h

/-! On `ℕ`, for a decidable property, there is a witness with code:
`Nat.find h` is the least one, and `Nat.find_spec h` says that it
works. -/

-- Exercise 16) Define `pick'` with `Nat.find`, without
-- `noncomputable`. Then remove the comment mark in front of `#eval`.
def pick' (h : ∃ n : ℕ, 5 < n) : ℕ :=
  sorry

-- #eval pick' ⟨10, by decide⟩

-- Exercise 17)
example (h : ∃ n : ℕ, 5 < n) : 5 < pick' h := by
  sorry

/-! The tactic `choose` makes a whole family of choices at once: from
`h : ∀ x, ∃ y, R x y` it gets a function `f` and a proof
`hf : ∀ x, R x (f x)`. -/

example (h : ∀ n : ℕ, ∃ m, n < m) : ∃ f : ℕ → ℕ, ∀ n, n < f n := by
  choose f hf using h
  exact ⟨f, hf⟩

-- Exercise 18)
example (R : α → α → Prop) (h : ∀ x, ∃ y, R x y)
    (hR : ∀ x y, R x y → R y x) : ∃ f : α → α, ∀ x, R (f x) x := by
  sorry

/-! `Nonempty α` says that `α` has an element, without naming one.
It is a proposition, so the rule of Part 3 applies. -/

-- Exercise 19) `obtain ⟨x⟩ := h` is allowed here.
example (h : Nonempty α) : ∃ x : α, x = x := by
  sorry

-- Exercise 20) Here the result is data and `obtain` fails. Use
-- `Classical.choice`.
noncomputable def someElement (h : Nonempty α) : α :=
  sorry
