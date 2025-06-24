import Mathlib

open ENNReal MeasureTheory PMF

variable {α β γ: Type}

namespace PMF

-- PMF is a nice monad
noncomputable example : Monad PMF := by exact PMF.instMonad

example : LawfulMonad PMF :=  by exact instLawfulMonad

-- pure
noncomputable def pureDo (P : PMF α) : (PMF α) := do
    let X ← P
    return X

-- pureDo gives P itself
theorem pureDo_eq_pure (P : PMF α) : P.pureDo = P := by
  simp only [pureDo, _root_.bind_pure]


-- map
noncomputable def mapDo (P : PMF α) (f : α → β) : (PMF β) := do
    let X ← P
    return f X

-- only notation
lemma map_eq (P : PMF α) (f : α → β) : map f P =
  f <$> P := rfl

/-- f <$> P is the image measure of P under f. -/
lemma mapDo_eq (P : PMF α) (f : α → β) : mapDo P f =
  f <$> P :=
    rfl

-- bind
noncomputable def bindDo (P : PMF α) (f : α → PMF β) : (PMF β) := do
    let X ← P
    let Y ← f X
    return Y

-- only notation
lemma bind_eq (P : PMF α) (f : α → PMF β) : bind P f = (P >>= f) := by
  rfl

-- If P is a PMF on α and f is a kernel from α to β, then P >>= f is their product
lemma bindDo_eq (P : PMF α) (f : α → PMF β) : bindDo P f = (P >>= f) := by
  simp [bind, bindDo]

noncomputable def seqDo (P : PMF (α → β)) (Q : PMF α) : (PMF β) := do
    let X ← Q
    let Z ← P
    return Z X

noncomputable def seqDo' (P : PMF (α → β)) (Q : PMF α) : (PMF β) := do
    let Z ← P
    let X ← Z <$> Q
    return X

lemma seqDo_iff (P : PMF (α → β)) (Q : PMF α) : seqDo P Q = seqDo' P Q := by
  simp [seqDo, seqDo']
  sorry

-- only notation
theorem seq_eq (P : PMF (α → β)) (Q : PMF α) : seq P Q = P <*> Q := by
  rfl

-- If P is the distribution of a random map f : α → β, and X ∼ P then f X ∼ P <*> Q
theorem seqDo'_eq (P : PMF (α → β)) (Q : PMF α) : seqDo' P Q = P <*> Q := by
  simp [seqDo', seq]
  rfl


-- mapmap
-- In fact, I believe that in the construction X and Y are independent
noncomputable def mapmapDo (P : PMF α) (Q : PMF β) (f : α → β → γ) : (PMF γ) := do
    let X ← P
    let Y ← Q
    return f X Y

theorem mapmapDo_eq_mapseq (P : PMF α) (Q : PMF β) (f : α → β → γ) : mapmapDo P Q f = (f <$> P) <*> Q := by
  simp [mapmapDo, bind, map]
  rw [← seqDo'_eq, ← mapDo_eq]
  sorry

theorem integral_sum [AddSemigroup α] [Fintype α][MeasurableSpace α] [MeasurableSingletonClass α] (P Q : PMF α) (f : α → ℝ)  : ∫ a, f a ∂  (((· + ·) <$> P) <*> Q).toMeasure = ∫ a, f a ∂P.toMeasure + ∫ a, f a ∂Q.toMeasure := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  sorry

end PMF


example : Nat.Prime 2 := by
  simp [Nat.Prime]
  constructor
  · simp only [Nat.isUnit_iff, OfNat.ofNat_ne_one, not_false_eq_true]
  · intro a b hab
    rw [Nat.isUnit_iff, Nat.isUnit_iff]
    by_contra! h
    obtain ⟨h1, h2⟩ := h
    apply h1

    sorry
