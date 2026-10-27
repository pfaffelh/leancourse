import Mathlib

/-!
# (witness) 1.4-a -- Predicates and equality

*Notes chapter 1.4, week 7.*

The setting is the one of sheet `1.2-a` (week 3): a type `α` and
predicates on it. New here is equality — between terms, and between
functions.

## Tactics introduced here

| tactic                | use it when                                    |
|-----------------------|------------------------------------------------|
| `ext x`               | goal `f = g`: prove `f x = g x` for every `x`  |
| `change t`            | replace the goal by a definitionally equal `t` |
| `fun x ↦ e`           | the function sending `x` to `e`                |
| `let f := e`          | give a term a name inside a proof              |
| `choose f hf using h` | `h : ∀ x, ∃ y, R x y`: get the function `f`    |

`rfl`, `rw`, `exact?` and `apply?` are known from `1.1-a` and `L-g`.
-/

variable (α β : Type) [Inhabited α]
variable (P Q : α → Prop)
variable (R : α → α → Prop)
variable (S T : Prop)

/-! ## Equality and `rfl`

`rfl` proves `a = a`, and more generally any `a = b` where the two
sides reduce to the same term. The same tactic also proves `A ↔ B`
when the two are definitionally equal, because `↔` on definitionally
equal propositions is reflexive in the same way. -/

example (x : α) : x = x := by
  rfl

-- Exercise 1) `¬P` is *by definition* `P → False` (sheet `L-d`), so
-- this needs nothing but reflexivity.
example (P : Prop) : ¬P ↔ (P → False) := by
  rfl

/-! ## Finding the lemma

Most of what you need is in Mathlib already. `exact?` looks for a
lemma that closes the goal, `apply?` for one that reduces it. Here
`exact?` finds the statement under a name worth remembering: -/

example (P Q : Prop) : ((P → Q) ∧ (Q → P)) ↔ (P ↔ Q) := by
  -- exact?
  exact iff_def.symm

/-! ## `rw`

`rw [h]` rewrites with `h : a = b` left to right, `rw [← h]` right to
left. It works on `↔` as well, because a proposition may be replaced
by an equivalent one anywhere. -/

example (x y z : α) : (x = y) → (y = z) → (x = z) := by
  intro h1 h2
  rw [h1]
  rw [h2]

/-! The same statement, rewriting the other way round. Compare the
goal after the first line in each. -/

example (x y z : α) : (x = y) → (y = z) → (x = z) := by
  intro h1 h2
  rw [← h2]
  rw [h1]

/-! To rewrite with an `↔` you first need one. This one says that an
implication is a disjunction in disguise; it is in Mathlib as
`imp_iff_or_not`, but proving it is two case splits. -/

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

-- Exercise 2) Peirce's law, which `L-e` left you to do by hand.
-- Here `rw [l1]` rewrites the innermost implication; repeating it
-- three times turns the goal into one about `∨` and `¬`, and then
-- `by_cases` on `P` finishes it. `rintro (h1 | h2)` splits the
-- disjunction as you introduce it.
example (P Q : Prop) : (((P → Q) → P) → P) := by
  rw [l1, l1, l1]
  by_cases hP : P
  · left
    exact hP
  · right
    rintro (h1 | h2)
    · exact hP h1
    · exact h2 (Or.inr hP)

-- Exercise 3) `exact?` finds this one outright (the name is
-- `not_imp_not`). Do it with `rw [l1 ...]` instead: rewrite both
-- sides, then `tauto`. Note that `l1` takes its two propositions as
-- arguments, so you can say which instance you mean.
lemma l2 (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  rw [l1 P Q, l1 (¬Q) (¬P)]
  tauto

/-! ## Functions

`fun x ↦ e` is the function sending `x` to `e`; `f x` is what the
rest of mathematics writes `f(x)`. -/

example : ∃ (f : α → α), f = f := by
  use fun _ ↦ default

/-! `let` gives the function a name first. -/

example : ∃ (f : α → α), f = f := by
  let f : α → α := fun _ ↦ default
  use f

/-! A predicate is a function into `Prop`, so the same notation
builds one. -/

example (f g : α → Prop) : ∃ (h : α → Prop), ∀ x, h x = (f x ∧ g x) := by
  use fun x ↦ f x ∧ g x
  intro x
  rfl

-- Exercise 4) Give `f` and `g` explicitly. Constant functions do.
example : ∃ (f g : α → Prop), ∀ x, (f x) ↔ ¬(g x) := by
  use fun _ ↦ True, fun _ ↦ False
  intro x
  simp

-- Exercise 5) Same idea with `Bool`. Put the cursor on `xor` and
-- press `F12` to see its definition.
example : ∃ (f g : α → Bool), ∀ x, xor (f x) (g x) := by
  use fun _ ↦ true, fun _ ↦ false
  intro x
  simp

-- Exercise 6) Turning a `∀ x, ∃ y` into a function is exactly what
-- `choose` does; it uses the axiom of choice (chapters 1.4, 2.2).
example : (∀ (x : α), ∃ (y : α), R x y) →
    ∃ (f : α → α), ∀ (x : α), R x (f x) := by
  intro h
  choose f hf using h
  exact ⟨f, hf⟩

/-! ## When are two functions equal?

When they agree at every point. `ext x` turns the goal `f = g` into
`f x = g x` for an arbitrary `x`. (Both functions must have the same
type for `f = g` to be stated at all.) -/

example (f g : α → Prop) (h : ∀ x, f x = ¬¬(g x)) : f = g := by
  ext x
  rw [h x]
  rw [not_not]

-- Exercise 7) One direction is `ext`, the other is `rw`.
example (f g : α → β) : (∀ x, ((f x) = (g x))) ↔ f = g := by
  constructor
  · intro h
    ext x
    exact h x
  · intro h x
    rw [h]

/-! ## `change`

`change t` replaces the goal by `t`, provided the two are
definitionally equal. It changes nothing for the kernel and
everything for the reader. -/

example (x : α) (f : α → Prop) : (¬(f x)) ↔ ((f x) → False) := by
  change (¬(f x)) ↔ (¬(f x))
  rfl

-- Exercise 8) The right-hand side says that `β` has at most one
-- element. Apply the hypothesis to two constant functions.
example : (∀ (f g : α → β), f = g) → (∀ (y1 y2 : β), y1 = y2) := by
  intro h y1 y2
  have hfg := h (fun _ ↦ y1) (fun _ ↦ y2)
  exact congrFun hfg default
