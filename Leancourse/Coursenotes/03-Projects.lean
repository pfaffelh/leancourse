import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Projects" =>
%%%
htmlSplit := .never
tag := "projects"
%%%

**Summary:** In the second phase of this course, students can assign themselves projects. For this, they were asked to look for simple exercises, e.g. from their first year courses. Here comes a list of exercises they used.

# Induction (Luis Jaschke und Felicitas Kissel)

Prove the following equalities using induction:

```lean
example (n : ℕ) :
    ∑ k ≤ n, k * k = n * (n + 1) * (2*n + 1) / 6 := by
  sorry
```

```lean
example (n : ℕ) :
    ∑ k ≤ n, k * k * k = n * n * (n + 1) * (n + 1) / 4 := by
  sorry
```

Compute the following sums and products, and show your result by induction.

```lean
example (n : ℕ) : ∑ k ≤ n, 2 * k - 1 = sorry := by
  sorry
```

```lean
example (n : ℕ) : ∏ k ≤ n, (1 + 1 / (k + 1)) = sorry := by
  sorry
```

```lean
example (n : ℕ) : ∏ k ≤ n, (1 - 1 / (k + 1)) = sorry := by
  sorry
```

# Own addition on ℚ (Adrian Eckstein und Debora Ortlieb)

```lean

def own_add (a b : ℚ) : ℚ := a * b + 2 * a + 2 * b + 2

notation a " ⊕ " b:60 => own_add a b

lemma own_mul_komm (a b : ℚ) : (a ⊕ b) = b ⊕ a := by
  sorry

lemma own_mul_assoc (a b c : ℚ) :
    ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) := by

  sorry

lemma own_mul_right_neutral (a : ℚ) : (a ⊕ (-1)) = a := by
  sorry

lemma own_mul_left_neutral (a : ℚ) : ((-1) ⊕ a) = a := by
  sorry

```

```lean
example (n : ℕ) : ∏ k ≤ n, (1 - 1 / (k + 1)) = sorry := by
  sorry
```

# Fixed points and contractions (Jule Kiesele, Anna Vitiello)

Jede Kontraktion hat genau einen Fixpunkt

# Path-connected spaces (Jasper Ganten)

```lean

open Set

section PathConnected

variable {X : Type*} [TopologicalSpace X]

/--
An intuitive definition of path connectedness:
A set `S` is path connected if it is nonempty and any two
points in `S` can be joined by a continuous path in `S`.
-/
def IsPathConnected' (S : Set X) : Prop :=
  S.Nonempty ∧
  ∀ x y : X, x ∈ S → y ∈ S →
    ∃ γ : Set.Icc (0 : ℝ) 1 → X,
      Continuous γ ∧
      γ 0 = x ∧
      γ 1 = y ∧
      ∀ t, γ t ∈ S

/--
`IsPathConnected'` is equivalent to Mathlib's
`IsPathConnected`.
-/
theorem pathConnected_iff (A : Set X) :
    IsPathConnected A ↔ IsPathConnected' A := by
  constructor
  · -- Mathlib ⇒ Intuitive
    intro ⟨p1, ⟨hp1, h1⟩⟩
    -- show that the set is nonempty
    refine ⟨⟨p1, hp1⟩, ?_⟩
    intro p2 p3 hp2 hp3
    -- construct a path from p2 to p3 by using the
    -- transitivity of the JoinedIn relation
    obtain ⟨γ, hγ⟩ := (h1 hp2).symm.trans (h1 hp3)
    exact ⟨γ, γ.continuous, γ.source, γ.target, hγ⟩
  · -- Intuitive ⇒ Mathlib
    rintro ⟨hne, hC⟩
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, hx, fun {y} hy => ?_⟩
    obtain ⟨γ, γ_cont, γ0, γ1, hγ⟩ := hC x y hx hy
    -- construct a Path type from my intuitive definition
    let p : Path x y := {
      toFun := γ,
      continuous_toFun := γ_cont,
      source' := γ0,
      target' := γ1
    }
    exact ⟨p, hγ⟩

/--
If `A` and `B` are path connected, and their intersetion
is nonempty, `A ∪ B` is pathconnected.
-/
theorem my_task {A B : Set X} (hA : IsPathConnected A)
    (hB : IsPathConnected B) (hAB : (A ∩ B).Nonempty) :
    IsPathConnected (A ∪ B) := by
  -- select a point z in the intersection
  obtain ⟨x, hxA, hxB⟩ := hAB
  use x
  refine ⟨Set.mem_union_left B hxA , fun {y} hy => ?_⟩
  -- split in cases depending on where y is
  rcases hy with hyA | hyB
  · -- y ∈ A then x and y are joined in A
    have joinedInA := hA.joinedIn x hxA y hyA
    -- but then also in the superset A ∪ B
    exact joinedInA.mono subset_union_left
  · -- y ∈ A then x and y are joined in B
    have joinedInB := hB.joinedIn x hxB y hyB
    -- but then also in the superset A ∪ B
    exact joinedInB.mono subset_union_right

end PathConnected
```


# Parallel inequality (Moritz Graßnitzer, Natalie Jahnes)

Parallel inequality, or a homomorphism is injective iff its kernel is trivial.

# There is only one prime triplet (Patrick Nasdala, Max Lehr)

There is only one prime triplet, i.e. only one `n : ℕ` prime, such that `n + 2` and `n + 4` are prime as well.

```lean

example (n : ℕ) :
    Nat.Prime n ∧ Nat.Prime (n + 2) ∧
    Nat.Prime (n + 4) → n = 3 := by
  sorry
```
# An equivalence on sets (Emma Reichel, Luisa Caspary)

We have `U ⊆ V ↔ U = U ∩ V ↔ V = U ∪ V`. So, the following needs to be proved:

```lean

variable (U V : Set α)

example : (U ⊆ V) → U = U ∩ V := by
  sorry

example : U = U ∩ V → V = U ∪ V:= by
  sorry

example : V = U ∪ V → U ⊆ V := by
  sorry
```
