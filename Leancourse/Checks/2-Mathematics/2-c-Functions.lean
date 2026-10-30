import Mathlib.Tactic

/-!
# (witness) 2.2-c -- Injective and surjective functions

*Notes chapter 2.2, week 10.*
-/

open Function

variable (α β γ : Type)

theorem injective_def (f : α → β) : Injective f ↔ ∀ a b : α, f a = f b → a = b := by
  rfl

theorem surjective_def (f : α → β) : Surjective f ↔ ∀ b : β, ∃ a : α, f a = b := by
  rfl

theorem id_eval (x : α) : id x = x := by
  rfl

theorem comp_eval (f : α → β) (g : β → γ) (x : α) : (g ∘ f) x = g (f x) := by
  rfl

example : Injective (id : α → α) := by
  rw [injective_def]
  -- `rw` cannot rewrite _under a binder_, i.e. below the `∀`. `simp_rw`
  -- can: it rewrites with the given lemmas like `simp`, which does go
  -- under binders, but uses only the lemmas you name.
  simp_rw [id_eval]
  intro a b hab
  exact hab

example : Surjective (id : α → α) := by
  intro x
  use x
  rw [id_eval]

-- Exercise 1
example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  rw [injective_def] at *
  intro a b hab
  exact hf a b (hg (f a) (f b) hab)

-- Exercise 2
example (f : α → β) (g : β → γ) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  rw [surjective_def] at *
  intro c
  obtain ⟨b, hb⟩ := hg c
  obtain ⟨a, ha⟩ := hf b
  exact ⟨a, by rw [comp_eval, ha, hb]⟩

-- Exercise 3
example (a b : α) (h : a ≠ b) (c : β) :
    ¬ Injective (fun _ : α => c) := by
  intro hinj
  exact h (@hinj a b rfl)

-- Exercise 4
example : Bijective (id : α → α) :=
  ⟨fun _ _ hab => hab, fun x => ⟨x, rfl⟩⟩

-- Exercise 5
example (f : α → β) (g : β → γ) (h : Injective (g ∘ f)) :
    Injective f := by
  intro a b hab
  exact h (by simp only [comp_eval, hab])

-- Exercise 6
example (f : α → β) (g : β → γ) (h : Surjective (g ∘ f)) :
    Surjective g := by
  intro c
  obtain ⟨a, ha⟩ := h c
  exact ⟨f a, ha⟩

-- Exercise 7
example (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Injective f := by
  intro a b hab
  rw [← h a, ← h b, hab]

-- Exercise 8
example (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Surjective f := by
  intro y
  exact ⟨g y, h y⟩

-- Exercise 9
example : Injective (fun n : ℕ => n + 1) := by
  intro a b hab
  simpa using hab

-- Exercise 10
example : ¬ Surjective (fun n : ℕ => n + 1) := by
  intro hs
  obtain ⟨n, hn⟩ := hs 0
  exact absurd hn (Nat.succ_ne_zero n)

-- Exercise 11
example (f : α → β) (g : β → γ) {δ : Type} (h : γ → δ) (x : α) :
    (h ∘ g ∘ f) x = h (g (f x)) := by
  rfl

-- Exercise 12
example (f : α → β) : id ∘ f = f := by
  rfl

-- Exercise 13
example (f : α → β) : f ∘ id = f := by
  rfl
