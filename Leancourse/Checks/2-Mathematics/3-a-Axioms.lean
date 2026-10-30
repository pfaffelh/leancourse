import Mathlib

/-!
# (witness) 2.3-a -- The axioms of Lean

*Notes chapter 2.3, week 10.*
-/

/- ## Part 1: Function extensionality -/

example : (fun n : ℕ => n + 0) = (fun n : ℕ => n) := by
  funext n
  simp

example : (fun (m n : ℕ) => m + n) = (fun (m n : ℕ) => n + m) := by
  funext m n
  omega

/- ## Part 2: Propositional extensionality -/

example : (True ∧ True) = True :=
  propext ⟨fun _ => trivial, fun h => ⟨h, h⟩⟩

example (P : Prop) (hP : P) : (P ∧ True) := by
  have h : (P ∧ True) = P := propext ⟨fun x => x.1, fun x => ⟨x, trivial⟩⟩
  rw [h]
  exact hP

/- ## Part 3: Excluded middle -/

example (P : Prop) : ¬¬P → P := by
  intro h
  by_contra h2
  exact h h2

example (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) := by
  intro h
  by_cases hp : P
  · right
    intro hq
    exact h ⟨hp, hq⟩
  · left
    exact hp

/- ## Part 4: Choice -/

noncomputable def existsToSubtype {α : Type} {P : α → Prop}
    (h : ∃ (x : α), P x) : {x : α // P x} :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

example (h : ∀ (n : ℕ), ∃ (m : ℕ), m > n) :
    ∃ (f : ℕ → ℕ), ∀ n, f n > n := by
  choose f hf using h
  exact ⟨f, hf⟩

example {α : Type} (a : α) : Nonempty α := ⟨a⟩

/- ## Part 5: Reading the axiom footprint -/

theorem contrapositive (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  intro hq hp
  exact hq (h hp)

#print axioms contrapositive      -- does not depend on any axioms

theorem contrapositive_conv (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  intro hp
  by_contra hq
  exact h hq hp

#print axioms contrapositive_conv -- Classical.choice

/- ## Part 6: What the kernel bakes in -/

theorem two_plus_two : (2 : ℕ) + 2 = 4 := by
  rfl

#print axioms two_plus_two        -- does not depend on any axioms

-- Exercise 13
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

-- Exercise 14
example (n : ℕ) (h1 h2 : 0 < n) :
    (⟨n, h1⟩ : {m : ℕ // 0 < m}) = ⟨n, h2⟩ := rfl
