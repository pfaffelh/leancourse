import Mathlib

/-!
# 2.9-a -- Monads in mathematics

*Notes chapter 2.9, week 15.*

`map`, `pure` and `bind` from chapter 1.6 (sheet `1.6-c`) occur in
mathematics under other names: the image of a set, the union over a
family, the pushforward of a filter. Read the section *Monads in
mathematics* of chapter 2.9 first.

| type       | `pure a`  | `map f`          | `bind s f`          |
|------------|-----------|------------------|---------------------|
| `Set α`    | `{a}`     | `f '' s`         | `⋃ a ∈ s, f a`      |
| `Finset α` | `{a}`     | `s.image f`      | `s.biUnion f`       |
| `Filter α` | `𝓟 {a}`   | `Filter.map f F` | `Filter.bind F f`   |

Nothing new is introduced. Most exercises are one lemma or `rfl`; find
the lemma with `exact?` where you do not know it.
-/

open Filter

/-! ## Part 1: Sets

`Set` is a `Functor`, and `map` is the image. The monad structure
`Set.monad` is not an instance; `attribute [local instance]` switches
it on until the end of the section. -/

-- Exercise 1) `map` is the image, by definition.
example (f : ℕ → ℕ) (s : Set ℕ) : f <$> s = f '' s := by
  sorry

-- Exercise 2) `simp` with the lemma `Set.image_insert_eq`.
example : (· * 2) '' ({1, 2, 3} : Set ℕ) = {2, 4, 6} := by
  sorry

-- Exercise 3) The first functor law, for sets.
example {α : Type} (s : Set α) : id '' s = s := by
  sorry

-- Exercise 4) The second functor law, for sets.
example {α β γ : Type} (f : α → β) (g : β → γ) (s : Set α) :
    (g ∘ f) '' s = g '' (f '' s) := by
  sorry

section SetMonad
attribute [local instance] Set.monad

-- Exercise 5) `bind` is the union, by definition.
example {α β : Type} (s : Set α) (f : α → Set β) :
    (s >>= f) = ⋃ a ∈ s, f a := by
  sorry

-- Exercise 6) `simp` with the lemma `Set.bind_def`.
example {α β : Type} (s : Set α) (f : α → Set β) (b : β) :
    b ∈ (s >>= f) ↔ ∃ a ∈ s, b ∈ f a := by
  sorry

end SetMonad

/-! ## Part 2: Finite sets

`Finset.image` and `Finset.biUnion` need `DecidableEq β`. For `ℕ` the
instance exists, and `decide` computes. -/

-- Exercise 7)
example : ({1, 2, 3} : Finset ℕ).image (· * 2) = {2, 4, 6} := by
  sorry

-- Exercise 8) The instance is a hypothesis, because the statement
-- needs it.
example {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) :
    (s.image f).card ≤ s.card := by
  sorry

-- Exercise 9) Here only the proof needs the instance. Start with
-- `classical`, then use `s.image f` as the witness.
-- `Finset.mem_image_of_mem` is the second lemma you need.
example {α β : Type} (f : α → β) (s : Finset α) :
    ∃ t : Finset β, t.card ≤ s.card ∧ ∀ a ∈ s, f a ∈ t := by
  sorry

-- Exercise 10)
example : ({1, 2} : Finset ℕ).biUnion (fun n => {n, 10 * n})
    = {1, 2, 10, 20} := by
  sorry

/-! ## Part 3: Filters

`Filter` is a `Functor`, and `map` is the pushforward. -/

-- Exercise 11)
example {α β : Type} (m : α → β) (F : Filter α) :
    m <$> F = Filter.map m F := by
  sorry

-- Exercise 12) Membership in the pushforward is membership of the
-- preimage, by definition.
example {α β : Type} (m : α → β) (F : Filter α) (t : Set β) :
    t ∈ Filter.map m F ↔ m ⁻¹' t ∈ F := by
  sorry

-- Exercises 13 and 14) The two functor laws, for filters.
example {α : Type} (F : Filter α) : Filter.map id F = F := by
  sorry

example {α β γ : Type} (f : α → β) (g : β → γ) (F : Filter α) :
    Filter.map g (Filter.map f F) = Filter.map (g ∘ f) F := by
  sorry

-- Exercise 15) `pure a` is the filter of all sets containing `a`.
example {α : Type} (a : α) (s : Set α) :
    s ∈ (pure a : Filter α) ↔ a ∈ s := by
  sorry

-- Exercise 16)
example {α β : Type} (f : α → β) (a : α) :
    Filter.map f (pure a) = pure (f a) := by
  sorry

-- Exercise 17) A limit is a statement about `map`, by definition.
example {α β : Type} (f : α → β) (F : Filter α) (G : Filter β) :
    Tendsto f F G ↔ Filter.map f F ≤ G := by
  sorry
