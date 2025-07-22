import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual

set_option maxRecDepth 10000

set_option pp.rawOnError true

#doc (Manual) "Projects" =>
%%%
htmlSplit := .never
tag := "projects"
%%%

**Summary:** In the second phase of this course, students can assign themselves projects. For this, they were asked to look for simple exercises, e.g. from their first year courses. Here comes a list of exercises they used.

# Induction (Luis Jaschke und Felicitas Kissel)

Compute the following sums and products, and show your result by induction.


```lean
open Finset

example (n : ℕ) :
    ∑ k ∈ range (n + 1), (k:ℝ) ^ 2 =
      n * (n + 1) * (2*n + 1) / 6 := by
  induction n with
  |  zero => simp
  | succ n ih =>
      rw [sum_range_succ]
      rw [ih]
      ring_nf
      field_simp
      ring
```

```lean
example (n : ℕ) :
  ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 3 =
    n * n * (n + 1) * (n + 1) / 4  := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    ring_nf
    field_simp
    ring
```

```lean
example (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) = (n : ℝ)^2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      ring
```

```lean
open Finset

example (n : ℕ) :
 ∏ k ∈ Finset.range n, (1 + 1 / (k + 1 : ℚ)) = n + 1
  := by
  -- gleicher Nenner: 1 + (1/(k+1)) = (1+2)/(k+1)
  have h_gleicher_Nenner :
    ∏ k ∈ Finset.range n, (1 + 1 / (k + 1 : ℚ)) =
    ∏ k ∈ Finset.range n, ((k + 2) : ℚ) / (k + 1)
    := by

    apply Finset.prod_congr rfl
    intro k hk
    field_simp [Nat.cast_add]
    ring
  rw [h_gleicher_Nenner]

  -- Nun zur Induktion
  induction n with
   | zero => simp
   | succ n kh =>
    rw [range_succ, prod_insert not_mem_range_self]
    have h' := kh (by
      apply Finset.prod_congr rfl
      intro k hk
      field_simp [Nat.cast_add]
      ring)
    rw [h']
    field_simp [Nat.cast_add]
    ring
```

```lean
example (q : ℝ) (hq : abs q  < 1) :
    Filter.Tendsto (fun n ↦ q^n) atTop (nhds 0) := by
  sorry
```

# Own addition on ℚ (Adrian Eckstein und Debora Ortlieb)

```lean
open   Rat
open   BigOperators

-- Zu bearbeiten war das `Blatt 1` der Vorlesung `Lineare Algebra I` im _WiSe 2021/22_
--      an der _Universität Freiburg_ bei _Prof. Dr. Heike Mildenberger_.

-- `Aufgabe 1`: Betrachten Sie auf der Menge der rationalen Zahlen ℚ die folgende Verknüpfung.
-- Definiere die Operation _star_: a ∗ b := ab + 2a + 2b + 2

def star (a b : ℚ) : ℚ
  := a * b + 2 * a + 2 * b + 2
```
```lean
-- `Aufgabe 1a`: Ist _(ℚ, star)_ kommutativ?
-- Beweis der Kommutativität: a ∗ b = b ∗ a

theorem LA1_Sheet1_Task1a (a b : ℚ) : star a b = star b a := by
  unfold _root_.star
  ring


-- `Aufgabe 1b`: Ist _(ℚ, star)_ assoziativ?
-- Beweis der Assoziativität: (a ∗ b) ∗ c = a ∗ (b ∗ c)

theorem LA1_Sheet1_Task1b (a b c : ℚ) :
  star (star a b) c = star a (star b c)
  := by
  unfold _root_.star
  ring

-- `Aufgabe 1c`: Besitzt _(ℚ, star)_ ein neutrales Element?
-- Beweis: -1 ist das neutrale Element, d.h. -1 ∗ a = a und a ∗ (-1) = a

```
```lean
theorem LA1_Sheet1_Task1c (a : ℚ) :
  star (-1) a = a ∧ star a (-1) = a
  := by
  unfold _root_.star
  constructor
  · ring
  · ring

-- `Aufgabe 1d`: Ist _(ℚ, star)_ eine Gruppe?
-- Zeige: Nein, da -2 kein Inverses bezüglich _star_ hat.

theorem LA1_Sheet1_Task1d : ¬ ∃ b : ℚ, star (-2) b = -1
    := by
  intro h
  obtain ⟨b, hb⟩ := h
  unfold _root_.star at hb
  ring_nf at hb
  norm_num at hb

```
```lean

-- Außerdem bearbeitet wurde das `Blatt 1` der Vorlesung `Analysis I` im _WiSe 2021/22_
--      an der _Universität Freiburg_ bei _Prof. Dr. Sebastian Goette_.

-- `Aufgabe 3`:  Berechnen Sie die folgenden Summen und Produkte, und beweisen Sie Ihr
-- Ergebnis jeweils mit vollständiger Induktion.

-- `Aufgabe 3d`: ∏_(i=1)^n      1 - (1/i)     = 0 für n > 0
--    bzw. hier: ∏_(i=0)^(n-1)  1 - (1/(i+1)) = 0 für n > 1

theorem Ana1_Sheet1_Task3d (n : ℕ) (hn : 1 < n) :
  ∏ i ∈ Finset.range n, (1 - 1 / (i + 1 : ℚ)) = 0
  := by
  have h_mem : 0 ∈ Finset.range n
  := by
    have h_pos : 0 < n := Nat.zero_lt_of_lt hn
    simp [Finset.mem_range, h_pos]
  apply Finset.prod_eq_zero h_mem
  norm_num
```

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


# A homomorphism is injective iff its kernel is trivial (Moritz Graßnitzer, Natalie Jahnes)

```lean
structure our_Group where
  uni : Type
  mul : uni → uni → uni
  one : uni
  inv : uni → uni
  mul_assoc : ∀ a b c : uni, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : uni, mul one a = a
  mul_one : ∀ a : uni, mul a one = a
  mul_inv : ∀ a : uni, mul a (inv a) = one
  inv_mul : ∀ a : uni, mul (inv a) a = one


lemma our_unique_inv {G : our_Group} (a b : G.uni) : G.mul a b = G.one → b = G.inv a := by
  intro h
  have h1 : G.mul a (G.inv a) = G.one := G.mul_inv a
  rw [←h] at h1
  have h2 : G.mul (G.inv a) (G.mul a b) = G.mul (G.inv a) G.one := by rw [h]
  have h3 : G.mul (G.mul (G.inv a) a) b = G.mul (G.inv a) G.one := by rw [G.mul_assoc, h2]
  have h4 : G.mul (G.one) b = G.mul (G.inv a) G.one := by
    rw [G.inv_mul a] at h3
    exact h3
  have h5 : b = G.mul (G.inv a) G.one := by
    rw [G.one_mul b] at h4
    exact h4
  have h6 : b = G.inv a := by
    rw [G.mul_one (G.inv a)] at h5
    exact h5
  exact h6


lemma our_unique_inv_inv {G : our_Group} (a : G.uni) : a = G.inv (G.inv a) := by
  have h1 : G.mul (G.inv a) a = G.one := G.inv_mul a
  apply our_unique_inv (G.inv a) a at h1
  exact h1


```

# There is only one prime triplet (Patrick Nasdala, Max Lehr)

There is only one prime triplet, i.e. only one `n : ℕ` prime, such that `n + 2` and `n + 4` are prime as well.

```lean
lemma div3 (n : ℕ) : (3 ∣ n) ∨ (3 ∣ (n+1)) ∨ (3 ∣ (n+2)) := by
  induction n with
  | zero =>
    left
    exact Nat.dvd_zero 3
  | succ n hn =>
    ring_nf
    by_cases h0 : 3 ∣ n
    · right
      right
      exact Nat.dvd_add_self_left.mpr h0
    · by_cases h1 : 3 ∣ n + 1
      · left
        rw[Nat.add_comm n 1] at h1
        exact h1
      · by_cases h2 : 3 ∣ n + 2
        · right
          left
          rw[Nat.add_comm n 2] at h2
          exact h2
        · exfalso
          cases' hn with l0 lr
          · exact h0 l0
          · cases' lr with l1 l2
            · exact h1 l1
            · exact h2 l2


lemma lem1 (n : ℕ) : (n < 3) → ¬ (Nat.Prime n ∧ Nat.Prime (n + 2) ∧ Nat.Prime (n + 4)) := by
  intro hns3
  by_contra h
  obtain ⟨ pn, pn2, pn4 ⟩ := h

  by_cases hnge2 : 2 ≤ n
  · have hne2 : n = 2 := by linarith
    have hnp4 : ¬ Nat.Prime 4 := of_decide_eq_false rfl
    rw[hne2] at pn2
    simp at pn2
    exact hnp4 pn2

  · by_cases hnge1 : 1 ≤ n
    · have hne1 : n = 1 := by linarith
      have hnp1 : ¬ Nat.Prime 1 := Nat.not_prime_one
      rw[hne1] at pn
      exact hnp1 pn

    · by_cases hnge0 : 0 ≤ n
      · have hne0 : n = 0 := by linarith
        have hnp0 : ¬ Nat.Prime 0 := Nat.not_prime_zero
        rw[hne0] at pn
        exact hnp0 pn
      · linarith


lemma lem2 (n : ℕ) : (3 < n) → ¬ (Nat.Prime n ∧ Nat.Prime (n + 2) ∧ Nat.Prime (n + 4)) := by
  intro hng3
  by_contra h
  obtain ⟨ pn, pn2, pn4 ⟩ := h
  have super := div3 n

  cases' super with k0 kr
  · obtain ⟨ x, g ⟩ := k0
    obtain ⟨ u1, u2 ⟩ := pn
    simp at u1 u2
    rw[g] at u2
    have u3 := u2 3 x
    simp at u3
    exfalso
    linarith

  · cases' kr with k1 k2
    · obtain ⟨ x, g ⟩ := k1
      obtain ⟨ u1, u2 ⟩ := pn4
      simp at u1 u2
      have gp3: n + 4 = 3 * (x + 1) := Eq.symm (Mathlib.Tactic.Ring.mul_add (id (Eq.symm g)) rfl rfl)
      rw[gp3] at u2
      have u3 := u2 3 (x+1)
      simp at u3
      exfalso
      linarith

    · obtain ⟨ x,g ⟩ := k2
      obtain ⟨ u1,u2 ⟩ := pn2
      simp at u1 u2
      rw[g] at u2
      have u3 := u2 3 x
      simp at u3
      exfalso
      linarith


theorem pt_forward (n : ℕ) : Nat.Prime n ∧ Nat.Prime (n + 2) ∧ Nat.Prime (n + 4) → n = 3 := by
  intro h
  by_cases hns3 : n < 3
  · exfalso
    have hn := lem1 n hns3
    exact hn h

  · by_cases hng3: 3 < n
    · exfalso
      have hn := lem2 n hng3
      exact hn h

    · linarith


theorem pt_backward (n : ℕ) : n = 3 → Nat.Prime n ∧ Nat.Prime (n + 2) ∧ Nat.Prime (n + 4) := by
  intro hne3
  rw[hne3]
  simp
  constructor
  · exact Nat.prime_three
  · constructor
    · exact Nat.prime_five
    · exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl


theorem prime_tripple (n : ℕ) : Nat.Prime n ∧ Nat.Prime (n + 2) ∧ Nat.Prime (n + 4) ↔ n = 3 := by
  constructor
  · exact pt_forward n
  · exact pt_backward n
```
# An equivalence on sets (Emma Reichel, Luisa Caspary)

We have `U ⊆ V ↔ U = U ∩ V ↔ V = U ∪ V`. So, the following needs to be proved:

```lean

variable (U V : Set α)

example : (U ⊆ V) → U = U ∩ V := by
  intro h
  ext x
  constructor
  · intro hxU
    exact ⟨hxU, h hxU⟩
  · intro ⟨hxU, hxV⟩
    exact hxU

example : U = U ∩ V → V = U ∪ V:= by
  intro h
  ext x
  constructor
  · intro hxV
    exact Or.inr hxV
  · intro h'
    cases h' with
    | inl hxU =>
      rw [h] at hxU
      exact hxU.2
    | inr hxV => exact hxV

example : V = U ∪ V → U ⊆ V := by
  intro h
  intro x hxU
  rw [h]
  exact Or.inl hxU
```
