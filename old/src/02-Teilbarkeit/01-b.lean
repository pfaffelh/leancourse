import tactic -- lade lean-Taktiken
open nat has_dvd

lemma firstlemma (k l : ℕ) : k ∣ l ↔ ∃ (c : ℕ), l = k * c :=
begin
  refl,
end

lemma secondlemma (n : ℕ) : n ∣ n :=
begin
  use 1,
  simp,
end

lemma thirdlemma (j k l : ℕ) (hjk : j ∣ k) (hkl : k ∣ l) : j ∣ l :=
begin
  rw firstlemma at *,
  cases hjk with a ha,
  cases hkl with b hb, 
  use a*b,
  rw [hb,ha],
  ring,
end

