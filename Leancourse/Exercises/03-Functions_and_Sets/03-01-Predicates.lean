import Mathlib

/-
  We will learn a few more tactics here that will be important in the following. Overall, we continue to move within the framework of the last page and consider the following scenario:-/

variable (α β : Type) [Inhabited α]
variable (P Q : α → Prop )
variable (R : α → α → Prop )
variable (S T: Prop)

/-
  We start simple and prove `x = x`. The equality of a term with itself (or a term that is identical by definition). This is the `rfl` tactic. (Recall that reflexivity of a relation `R` means that `R x x` for all `x`. The `=` is reflexive, meaning that each term is equal to itself.)
-/

example (x : α) : x = x := by
  rfl

-- Exercise 1: This also works differently, but it is faster using `rfl`.
example (P : Prop) : ¬P ↔ (P → False) := by
  sorry

/-
  Mathlib is already full of statements. To search through it, there are the tactics `apply?` and `exact?`; see script. Here is an example:-/

example (P Q : Prop) : ((P → Q) ∧ (Q → P)) ↔ (P ↔ Q) := by
  -- both, `apply?` and `exact?` give -- not true xxx
  exact Iff.symm iff_iff_implies_and_implies
  -- However, this is not the shortest solution, which is
  -- exact iff_def.symm

/-
  There is another tactic whicch we will need frequencly: `rw`; see manuscript. Here is an example:
-/

example (x y z : α) : (x = y) → (y = z) → (x = z) := by
  intro h1 h2
  rw [h1]
  rw [h2]

-- What is the difference to the last proof?
example (x y z : α) : (x = y) → (y = z) → (x = z) := by
  intro h1 h2
  rw [← h2]
  rw [h1]

-- The `rw` tactic works with `=` assertions, as well as with `↔` assertions. Let us prove a `↔` goal:
lemma l1 (P Q : Prop ) : (P → Q) ↔ (Q ∨ ¬P ) := by
  constructor
  · intro hPQ
    by_cases h : P
    · left
      exact hPQ h
    · right
      exact h
  · intro h hP
    cases' h with h1 h2
    · exact h1
    · exfalso
      exact h2 hP

-- Exercise 2: Now we can use `l1` in order to solve the difficult exercise from `01-e`. `push_neg` can be useful as well.
example (P Q : Prop): (((P → Q) → P) → P) := by
  rw [l1]
  sorry

-- Exercise 3:
-- Here you can use library_search directly, but we now want to use l1 from above (with rw). Can you do that?
lemma l2 (P Q : Prop ) : (P → Q) ↔ (¬Q → ¬P) := by
  rw [l1 P Q]
  sorry

/-
  We now come to defining functions, for which we need a notation that is equivalent to `f : ↦ f x` (where `f x` is the lean way of writing `f(x)`; computer scientists sometimes use parentheses sparingly...) This is done with `fun`: the expression `fun x ↦ 2*x`
  is the function `x ↦ 2*x`. Here are two examples:-/

example : (∃ (f : α → α), true) := by
  use fun x ↦ default

/-
  If you want to give the last example an explicit name, you can do so as follows:-/

example : (∃ (f : α → α), true) := by
  let f : α → α := fun x ↦ default
  use f

-- Yet another example:
example (f g : α → Prop) : ∃ (h : α → Prop), ∀ x, h x = (f x ∧ g x) := by
  use fun x ↦ f x ∧ g x
  intro x
  rfl

-- Exercise 4: Here it is best to explicitly state `f` and `g`.
example : ∃ (f g : α → Prop), ∀ x, (f x) ↔ ¬(g x) := by
  sorry

-- Exercise 5: Another hint that we will use often. Why don't you move the cursor to the xor and press `F12`. You will then be guided to the definition of `xor`. After that, the exercise is no more difficult than the last one.
example : ∃ (f g : α → Bool), ∀ x, xor (f x) (g x) := by
  sorry

-- Exercise 6: Here you can either use `apply?`, or you can manage to understand Mathlib so well that you can manage your own proof.
example : (∀ (x : α), ∃ (y : α), R x y) → ∃ (f : α → α), ∀ (x : α), R x (f x) := by
  sorry

/-
  When are two functions `f` and `g` equal? In Lean, this is the case when all function values are the same at all points. (Caution: in order to be able to claim that `f = g` at all, both functions must have the same type, i.e. domain and co-domain must match.) To turn the goal `f = g` into the goal that `f` and `g` are equal at all points, we use the `ext` (which stands for _extensionality_) tactic.
-/

example (f g : α → Prop) (h : ∀ x, f x = ¬¬(g x)) : f = g := by
  ext x
  rw [h x]
  rw [not_not]

-- Exercise 7: This should be easy with the example above.
example (f g : α → β) : (∀ x, ((f x) = (g x))) ↔ f = g := by
  sorry

/-
  Here is another helpful tactic: `change`. This changes the goal or a statement into a definition-identical statement:
  -/

example (x : α) (f : α → Prop) : (¬(f x)) ↔ ((f x) → False) := by
  change (¬(f x)) ↔ (¬(f x))
  rfl


-- Exercise 8: Here, the right-hand side is a version saying that β contains only one element.
example : (∀ (f g : α → β), f = g) → (∀ (y1 y2 : β), y1 = y2) := by
  sorry
