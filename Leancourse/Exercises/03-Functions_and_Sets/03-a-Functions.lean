/- This time, we only import the tactics, i.e. you will not have access to the whole Mathlib! -/
import Mathlib.Tactic

/-!

# Functions

We already know that we write `f : α → β` for a function `f` with domain `α` and co-domain `β`. Using the usual terminology in Lean, this means that `α → β` is the type of all such functions and `f` is one representative. Please keep in mind that `f : α → β` can be evaluated at `x : α` using `f x : β`. Moreover, if `g : β → γ`, we can write `g (f x) : γ`, or `(g ∘ f) x` for their composition. (Since brackets are left-associative, the brackets must not be left out here.)

The goal is to deal with injectivity and surjectivity of functions. We open the namespace `Function` such that we don't need to write e.g. `Function.Injective`, but `Injective`. Here are the definitions:

-/
open Function

variable (α β γ : Type)

#print Injective
-- ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂

#print Surjective
-- ∀ (b : β), ∃ a, f a = b


-- Let's prove two theorems, which are simply true _by definition_!
theorem injective_def (f : α → β) : Injective f ↔ ∀ a b : α, f a = f b → a = b := by
  rfl

theorem surjective_def (f : α → β) : Surjective f ↔ ∀ b : β, ∃ a : α, f a = b := by
  rfl

-- similarly, `id x = x` by definition:
theorem id_eval (x : α) : id x = x := by
  rfl

-- Composition is written as follows:.
theorem comp_eval (f : α → β) (g : β → γ) (x : α) : (g ∘ f) x = g (f x) := by
  rfl

-- Let us start simply and show that the identity is both, surjective and injective.
example : Injective (id : α → α) := by
  rw [injective_def]
  -- Note that the following line does not work with `rw` since it is _under a binder_, i.e. the `∀`!
  simp_rw [id_eval]
  intro a b hab
  exact hab

example : Surjective (id : α → α) := by
  intro x
  use x
  rw [id_eval]

-- Exercise 1: The composition of two maps is injective.
example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  rw [injective_def] at *
  sorry

-- Exercise 2: The composition of two surjective functions is surjective.
example (f : α → β) (g : β → γ) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  rw [surjective_def] at *
  sorry

-- Exercise 3: A constant function on a type with at least two elements
-- is not injective.
example (a b : α) (h : a ≠ b) (c : β) :
    ¬ Injective (fun _ : α => c) := by
  sorry

-- Exercise 4: The identity is a bijection
-- (Bijective = Injective ∧ Surjective).
example : Bijective (id : α → α) := by
  sorry

-- Exercise 5: If g ∘ f is injective, then f is injective.
example (f : α → β) (g : β → γ) (h : Injective (g ∘ f)) :
    Injective f := by
  sorry

-- Exercise 6: If g ∘ f is surjective, then g is surjective.
example (f : α → β) (g : β → γ) (h : Surjective (g ∘ f)) :
    Surjective g := by
  sorry

-- Exercise 7: An injective function from α to β, composed with
-- a left inverse, is the identity.
example (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Injective f := by
  sorry

-- Exercise 8: A function with a right inverse is surjective.
example (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Surjective f := by
  sorry

-- Exercise 9: The successor function on ℕ is injective.
example : Injective (fun n : ℕ => n + 1) := by
  sorry

-- Exercise 10: The successor function on ℕ is not surjective
-- (0 is not in the image).
example : ¬ Surjective (fun n : ℕ => n + 1) := by
  sorry

-- Exercise 11: Composition is associative at the level of values.
example (f : α → β) (g : β → γ) {δ : Type} (h : γ → δ) (x : α) :
    (h ∘ g ∘ f) x = h (g (f x)) := by
  sorry

-- Exercise 12: Composition with the identity on the left.
example (f : α → β) : id ∘ f = f := by
  sorry

-- Exercise 13: Composition with the identity on the right.
example (f : α → β) : f ∘ id = f := by
  sorry
