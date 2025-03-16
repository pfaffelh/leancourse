import data.real.basic
import tactic

noncomputable theory
open_locale classical

-- Mengen einführen

example (n : ℕ) : n = 0 + n :=
begin
  induction n with d hd, 
  refl,
  rw nat.add_succ, rw ← hd,  
end


example (x y : ℕ) (h : x = y) (f : ℕ → ℕ): (f (x + y)) = (f (y + x)) :=
begin
  congr' 2, 
  exact h, 
end


def up_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x}

/-- Die Aussage `is_maximum a A` means `a` ist ein Maximum von `A` -/
def is_maximum (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A

example (x y : ℝ) (hx : x ≤ y) (hy : y ≤ x) : x = y :=
begin
  exact le_antisymm hx hy, 
end

lemma unique_max (A : set ℝ) (x y : ℝ) (hx : is_maximum x A) (hy : is_maximum y A) : x = y :=
begin
  have h1 : x ≤ y, apply hy.2 x hx.1, 
  have h2 : y ≤ x, apply hx.2 y hy.1, 
  exact le_antisymm h1 h2,  
end

/-- The set of lower bounds of a set of real numbers ℝ -/
def low_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, x ≤ a}

/-
Jetzt definieren wir das Infimum einer Menge reeller Zahlen.
-/
def is_inf (x : ℝ) (A : set ℝ) := is_maximum x (low_bounds A)

lemma inf_lt {A : set ℝ} {x : ℝ} (hx : is_inf x A) : ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  intros y hy, 
--  simp [is_inf, is_maximum, low_bounds, up_bounds] at hx, 
  cases hx with hx1 hx2, 
  simp at *, 
  by_contra h, 
  push_neg at h, 
  specialize hx2 y h,
  linarith,
end

example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := 
begin
  library_search, 
end

-- y > x → ∃ ε > 0, y ≥ x + ε  

lemma le_of_le_add_eps_iff {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) ↔  y ≤ x :=
begin
  split,
  {
    contrapose!, 
    -- äquivalent zu
    -- rw ← not_imp_not, 
    -- push_neg, 
    intro h2, 
    use (y-x)/2, 
    split; 
    linarith, 
  },
  {
    intros h eps heps, 
    linarith, 
  }
end

/-- The sequence `u` tends to `l` -/
def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

-- If y ≤ u n for all n and u n goes to x then y ≤ x
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limit u x) (ineq : ∀ n, y ≤ u n) : y ≤ x :=
begin
  rw ← le_of_le_add_eps_iff, 
  intros eps heps, 
  rw [limit] at hu, 
  cases hu eps heps with N hN, 
  specialize hN N rfl.ge, 
  specialize ineq N, 
  have h : u N - x < eps, exact lt_of_abs_lt hN,
  linarith,  
end

lemma inv_succ_pos : ∀ n : ℕ, 1/(n+1 : ℝ) > 0 :=
begin
  intro n, exact nat.one_div_pos_of_nat, 
end

--archimedean_iff_nat_le : ∀ {α : Type} [_inst_1 : linear_ordered_field α], archimedean α ↔ ∀ (x : α), ∃ (n : ℕ), x ≤ ↑n



example (x : ℝ) : ∃ n : ℕ, x < (n : ℝ) :=
begin
  revert x, 
  apply archimedean_iff_nat_lt.1,
  apply_instance, 
end


example ( a b : ℝ ) (ha : a > 0) (hb : b > 0) : 1/a < b ↔ 1 < a*b :=
begin
  exact div_lt_iff' ha, 
end

example (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h1: a ≤ b*d) (h2 : b ≤ c) : b*d ≤ c*d :=
begin
  exact (mul_le_mul_right hd).mpr h2,   
end


lemma limit_inv_succ : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) < ε :=
begin
  intros eps heps,
  cases (archimedean_iff_nat_lt.1 _ (1/eps)) with w hw,
  use w, 
  intros n nw, 
  apply (div_lt_iff' _).2,
  rw div_lt_iff heps at hw, 
  have h1 : w ≤ n+1, linarith, 
  have h2 : (w : ℝ) ≤ (n+1 : ℝ), norm_cast, exact h1, 
  have h3 : (w : ℝ)*eps ≤ (n+1)*eps, 
  exact (mul_le_mul_right heps).mpr h2,
  linarith, 
  norm_cast, simp,
  apply_instance,
end

/-
We can now put all pieces together, with almost no new things to explain.
-/

lemma l {a b eps : ℝ} (heps : eps > 0) : |a - b| < eps → a < b + eps :=
begin
  intro h, simp [abs] at *, cases h, linarith, 
end


lemma inf_seq (A : set ℝ) (x : ℝ) :
  (is_inf x A) ↔ (x ∈ low_bounds A ∧ ∃ u : ℕ → ℝ, limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  {
    intro h, 
    split, exact h.1,
    have seq : ∀ (n : ℕ), ∃ a ∈ A, a < x + 1/(n+1 : ℝ),
    {
      intro n, 
      apply inf_lt h,  
      simp,
      norm_cast, simp,
    },
    choose u hu1 hu2 using seq,
    use u, 
    refine ⟨_, hu1⟩,
    have hu3 : ∀ n, x ≤ u n, 
    {
      intro n, 
      simp [is_inf, is_maximum, low_bounds] at h, 
      apply h.1 (u n) (hu1 n),
    },
    have hu4 : ∀ n, |u n - x| < 1 / (n + 1 : ℝ),
    {
      intro n, 
      specialize hu2 n, 
      specialize hu3 n, 
      simp [abs] at *, 
      split; 
      linarith, 
    },
    intros eps heps, 
    cases archimedean_iff_nat_le.1 (by apply_instance) (1/eps) with N hN,
    use N, intros n hn, 
    have hu5 : 1 / (n + 1 : ℝ) < eps, 
    {
      simp at *,
      rw inv_lt _ _,
      have h1 : eps⁻¹ ≤ n, apply le_trans hN _, norm_cast, exact hn, linarith, norm_cast, exact nat.zero_lt_succ n, exact heps,
    },
    exact lt_trans (hu4 n) hu5, 
  },
  {
    rintro ⟨ h1, u, h2, h3 ⟩,
    refine ⟨ h1, _⟩,
    simp [up_bounds], 
    intros a ha, 
    apply le_of_le_add_eps_iff.1,
    intros eps heps, 
    have h1 : ∃ n, u n < x + eps,
    cases h2 eps heps with N hN,  
    use N, 
    apply l heps, 
    refine hN N rfl.ge,
    cases h1 with n hn, 
    by_contra h, 
    push_neg at h, 
    have h2 : ∃ b ∈ A, b < a, use [u n, h3 n], 
    exact lt_trans hn h, 
    cases h2 with b hb, cases hb with hb1 hb2, 
    have hb3 : b < b, 
    exact lt_of_lt_of_le hb2 (ha b hb1),
    linarith, 
  },
end



