/- # Fixed points and contractions (Jule Kiesele, Anna Vitiello)

```lean

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
```


```lean

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
```

Second solution:
```lean

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
```
-/
