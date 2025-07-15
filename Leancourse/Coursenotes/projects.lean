import Mathlib

open Finset

-- Induction (Luis Jaschke und Felicitas Kissel)

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

example (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1) = (n : ℝ)^2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      ring


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

example (q : ℝ) (hq : abs q  < 1) :
    Filter.Tendsto (fun n ↦ q^n) atTop (nhds 0) := by
  sorry

-- Own addition on ℚ (Adrian Eckstein und Debora Ortlieb)

open   Rat
open   BigOperators

-- Zu bearbeiten war das `Blatt 1` der Vorlesung `Lineare Algebra I` im _WiSe 2021/22_
--      an der _Universität Freiburg_ bei _Prof. Dr. Heike Mildenberger_.

-- `Aufgabe 1`: Betrachten Sie auf der Menge der rationalen Zahlen ℚ die folgende Verknüpfung.
-- Definiere die Operation _star_: a ∗ b := ab + 2a + 2b + 2

def star (a b : ℚ) : ℚ
  := a * b + 2 * a + 2 * b + 2
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


-- Fixed points and contractions (Jule Kiesele, Anna Vitiello)

variable{I : Set ℝ} (hI_closed : IsClosed I)(hne : I.Nonempty)
variable(f : ℝ → ℝ)(hf: ∀ x, x ∈ I → f x ∈ I)
variable(q : NNReal)(hq: 0 < q ∧ q < 1) --NNReal sind nichtnegative reelle Zahlen
variable(hKon: ∀ x y, x ∈ I → y ∈ I → |f x - f y|≤ q * |x-y|)


--Eindeutigkeit des Fixpunkts
example: ∀ x y, x∈ I → y ∈  I → f x = x → f y = y → x = y:= by
    intros x y hx hy hfx hfy
    by_contra h
    have hxy: 0 < |x-y|:= by
        rw[abs_pos, sub_ne_zero]
        exact h
    have h': |f x - f y| ≤ q * |x - y|:= by exact hKon x y hx hy
    have h'': |f x - f y| > q * |x - y|:= by
        calc |f x - f y| = |x - y|:= by rw[hfx, hfy]
            _ > q * |x - y|:= by
                simp
                nth_rw 2[← one_mul |x-y|]
                exact mul_lt_mul_of_pos_right hq.2 hxy
    linarith


--Existenz eines Fixpunkts
example (a : ℕ → ℝ)(ha0:a 0 ∈ I)(ha : ∀ (n : ℕ), a (n+1) = f (a n)): ∃ x: ℝ, f x = x:= by
    have hKon2: ∀ x y, x ∈ I → y ∈ I → dist (f x) (f y)≤ q * dist x y:= by
        intros x y hx hy
        rw[Real.dist_eq (f x) (f y),Real.dist_eq x y]
        exact hKon x y hx hy
    have haI:  ∀ (n : ℕ), a n ∈ I:= by
        intro n
        induction n with
        |zero =>
            exact ha0
        |succ n hn =>
            rw[ha n]
            exact hf (a n) hn
    have h1: ∀ (n : ℕ), |a (n+1) - a n| ≤ q^n * |a 1 - a 0|:= by
        intro n
        induction n with
        |zero =>
            rw[pow_zero,one_mul]
        |succ n hn =>
            calc |a (n + 1 + 1) - a (n + 1)| = |f (a (n+1)) - f (a n)| := by
                    rw[ha (n+1)]
                    nth_rw 2[ha n]
            _ ≤ q * |a (n+1) - a n|:= by exact hKon (a (n+1)) (a n) (haI (n+1)) (haI n)
            _≤ q * (q ^n * |a 1 - a 0|):= by exact mul_le_mul_of_nonneg_left hn (hq.1.le)
            _ = q^(n+1) * |a 1 - a 0|:= by
                nth_rw 1 [← mul_assoc]
                rw[pow_succ]
                linarith
    have h2: ∀ (m n : ℕ), |a (n+m)-a n|≤ q^n * (1/(1-q))*|a 1 - a 0|:= by
        intros m n
        calc |a (n + m) - a n| = |∑ i ∈ Finset.range m, (a (n+i+1) - a (n+i))| := by
                have tel_sum:∑ i ∈ Finset.range m, (a (n+i+1) - a (n+i))=a (n + m) - a n:= by
                    induction m with
                    |zero => simp
                    |succ m ih =>
                        have last_summ: ∑ i ∈ Finset.range (m + 1), (a (n + i + 1) - a (n + i)) = a (n + m + 1) - a (n + m) + ∑ i ∈ Finset.range m , (a (n + i + 1) - a (n + i)) := by
                            simp
                            rw[Finset.range_succ]
                            rw[Finset.sum_insert]
                            · rw[Finset.sum_insert]
                              · ring
                              · exact Finset.not_mem_range_self
                            · exact Finset.not_mem_range_self
                        rw[last_summ,ih]
                        simp
                        rw[add_assoc]
                rw[tel_sum]
        _≤ ∑ i ∈ Finset.range m, (|a (n+i+1) - a (n+i)|):= by exact Finset.abs_sum_le_sum_abs (fun k => a (n+k+1) - a (n+k)) (Finset.range m)
        _≤ ∑ i ∈ Finset.range m, (q^(n+i) * |a 1 - a 0|) := by
            have h1':∀ i ∈ Finset.range m, |a (n + i + 1) - a (n + i)| ≤ ↑q ^ (n + i) * |a 1 - a 0| := by
                intros i hi
                exact h1 (n+i)
            exact Finset.sum_le_sum h1'
        _= ∑ i ∈ Finset.range m, (q^i*q^n * |a 1 - a 0|):= by
            congr 1
            ext i
            rw[pow_add]
            simp
            left
            rw[mul_comm]
        _=∑ i ∈ Finset.range m, (q^i*(q^n * |a 1 - a 0|)):= by
            congr 1
            ext i
            rw[mul_assoc]
        _=q^n * |a 1 - a 0| * ∑ i ∈ Finset.range m, q^i:= by
            rw [← Finset.sum_mul,mul_comm]
            simp
        _=q^n * |a 1 - a 0| * ↑((1-q^m)/(1-q)) := by
            rw[geom_sum_of_lt_one hq.2 m]
        _≤  q^n *|a 1 - a 0| * ↑(1/(1-q)):= by
            have hq_div: (1-q^m)/(1-q) ≤ 1/(1-q):= by
                apply (div_le_div_iff_of_pos_right _).mpr
                · simp
                · simp
                  exact hq.2
            exact mul_le_mul_of_nonneg_left hq_div (mul_nonneg ((pow_pos hq.1 n).le) (abs_nonneg (a 1 - a 0)))
        _=q^n * (1/(1-q))*|a 1 - a 0|:= by
            rw[NNReal.coe_div,NNReal.coe_sub hq.2.le,NNReal.coe_one]
            ring
    have hcau: IsCauSeq (fun x => |x|) a := by
        intro ε hε
        have hcau_ε: ∃ N, q^N * (1 / (1 - q)) * |a 1 - a 0| < ε:= by
            set C :=  (1 / (1 - q)) * |a 1 - a 0| with hC
            have hC_nonneg: 0 ≤ C:= by
                apply mul_nonneg _ (abs_nonneg (a 1 - a 0))
                exact one_div_nonneg.mpr (le_of_lt (sub_pos_of_lt hq.2))
            have hC_pos_or_zero := lt_or_eq_of_le hC_nonneg
            cases hC_pos_or_zero with
            |inl hC_pos =>
                have hh: Filter.Tendsto (fun n:ℕ => q ^n * C) Filter.atTop (nhds (0*C)) := by
                    apply Filter.Tendsto.mul_const C
                    simp
                    exact hq.2
                simp only[zero_mul] at hh
                obtain ⟨N, h_evtl⟩:= Filter.Eventually.exists ((tendsto_order.1 hh).2 ε hε)
                use N
                rw[mul_assoc]
                rw[← hC]
                exact h_evtl
            |inr hC_zero =>
                use 0
                rw[mul_assoc,← hC,← hC_zero, mul_zero]
                exact hε
        obtain ⟨N, hN⟩ := hcau_ε
        use N
        intro j hj
        have hjN: |a j - a N| ≤ q^N * (1 / (1 - q)) * |a 1 - a 0| := by
            specialize h2 (j-N) N
            rw[add_comm N (j-N)] at h2
            rw[← Nat.sub_add_cancel hj]
            exact h2
        simp
        linarith
    have h3: ∃ x ∈ I, Filter.Tendsto a Filter.atTop (nhds x) := by
        obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (isCauSeq_iff_cauchySeq.mp hcau)
        have pI: p ∈ I := by
            rw[← hI_closed.closure_eq]
            exact mem_closure_of_tendsto hp (Filter.Eventually.of_forall haI)
        exact ⟨p, pI, hp⟩
    obtain ⟨x, hx⟩ := h3
    have h4: dist (f x) x = 0:= by
        have h_fa: ∀(n : ℕ), dist (f x) x <= q * dist x (a n) + dist x (a (n + 1)):= by
            intro n
            calc  dist (f x) x <= dist (f x) (f (a n)) + dist (f (a n)) x:= by exact dist_triangle (f x) (f (a n)) x
            _=dist (f x) (f (a n)) + dist (a (n + 1)) x:= by rw[ha n]
            _<= q * dist x (a n) + dist (a (n + 1)) x := by exact add_le_add_right (hKon2 x (a n) hx.1 (haI n)) (dist (a (n + 1)) x)
            _=  q * dist x (a n) + dist x (a (n + 1)) := by rw[dist_comm (a (n + 1)) x]
        have h_xa: Filter.Tendsto (fun n:ℕ => dist x (a n)) Filter.atTop (nhds 0):= by
            rw[← dist_self x]
            exact Filter.Tendsto.dist (by simp) hx.2
        have h_xa1: Filter.Tendsto (fun n:ℕ => dist x (a (n+1))) Filter.atTop (nhds 0):= by
            rw[← dist_self x]
            exact Filter.Tendsto.dist (by simp) (Filter.Tendsto.comp hx.2 (Filter.tendsto_add_atTop_nat 1))
        have h_qxa: Filter.Tendsto (fun n:ℕ => q * dist x (a n)) Filter.atTop (nhds (q*0)):= by exact Filter.Tendsto.const_mul ↑q h_xa
        simp only[mul_zero] at h_qxa
        have h0: Filter.Tendsto (fun n:ℕ => q * dist x (a n) + dist x (a (n + 1))) Filter.atTop (nhds (0+0)):= by exact Filter.Tendsto.add h_qxa h_xa1
        simp only [add_zero] at h0
        apply le_antisymm _ (dist_nonneg)
        apply ge_of_tendsto' h0
        exact h_fa
    use x
    apply sub_eq_zero.mp
    exact abs_eq_zero.mp h4

variable {α : Type u_1} [MetricSpace α] [cs : CompleteSpace α]
variable (f : α → α)
variable (h_con : ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ x y, dist (f x) (f y) ≤ q * dist x y)
variable (x y : α)

--Eindeutigkeit des Fixpunkts
example (hx : f x = x )(hy : f y = y ): x = y:= by
  obtain ⟨q, hq_pos, hq_one, hq⟩ := h_con
  by_contra h
  have h': 0 < dist x y:= by exact dist_pos.mpr h
  have h'': dist (f x) (f y) ≤ q *  dist x y:= by exact hq x y
  have h''': dist (f x) (f y) > q * dist x y:= by
       calc dist (f x ) (f y) = dist x y := by rw[hx, hy]
        _ > q * dist x y := by
         simp
         nth_rw 2[← one_mul (dist x y)]
         exact mul_lt_mul_of_pos_right hq_one h'
  linarith



variable {q : NNReal}
variable {f : α → α} (hf : ContractingWith q f) (x : α) (hx : edist x (f x) ≠ ⊤)

-- Existenz des Fixpunktes
example : ∃ x, Function.IsFixedPt f x := by
  obtain ⟨ x ,h ⟩ :=  (ContractingWith.exists_fixedPoint hf x hx)
  use x
  exact h.1

-- Path-connected spaces (Jasper Ganten)

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

-- Parallel inequality (Moritz Graßnitzer, Natalie Jahnes)


-- There is only one prime triplet (Patrick Nasdala, Max Lehr)


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

-- An equivalence on sets (Emma Reichel, Luisa Caspary)


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
