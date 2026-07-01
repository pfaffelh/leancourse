import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Tactics Cheatsheet" =>
%%%
tag := "cheatsheet"
%%%

:::table (align := left) +header
* + Proof state
  + Tactic
  + New proof state
* + `⊢ P → Q`
  + `intro hP`
  + `hP : P` {br}[] `⊢ Q`
* + `⊢ P → Q → R`
  + `intro hP hQ`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `p : α → Prop` {br}[] `⊢ ∀ (x : α), f x`
  + `intro x`
  + `f: α → Prop` {br}[] `x : α` {br}[] `⊢ p x`
* + `h : P` {br}[] `⊢ P`
  + `exact h`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ P`
  + `assumption`
  + `no goals 🎉`
* + `h : P → Q` {br}[] `⊢ P`
  + `apply h`
  + `⊢ Q`
* + `h₁ : P → Q` {br}[] `h₂ : Q → R` {br}[] `⊢ R`
  + `apply h₂ h₁`
  + `h₁ : P → Q` {br}[] `h₂ : Q → R` {br}[] `⊢ P`
* + `⊢ P ∧ Q → P`
  + `tauto` oder `tauto!`
  + `no goals 🎉`
* + `⊢ true`
  + `triv`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ Q`
  + `exfalso`
  + `h : P` {br}[] `⊢ false`
* + `⊢ P`
  + `by_contra h`
  + `h : ¬P` {br}[] `⊢ false`
* + `⊢ P`
  + `by_cases h : Q`
  + `h : Q` {br}[] `⊢ P` {br}[] `h : ¬Q` {br}[] `⊢ P`
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `cases' h with hP hQ`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∧ Q` {br}[] `⊢ R`
  + `obtain ⟨hP, hQ⟩ := h`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∨ Q` {br}[] `⊢ R`
  + `cases' h with hP hQ`
  +  `hP : P` {br}[] `⊢ R` {br}[] `hQ : Q ⊢ R`
* + `h : false` {br}[] `⊢ P`
  + `cases h`
  + `no goals 🎉`
* + `⊢ : P → false`
  + `change ¬P`
  + `⊢ ¬P`
* + `⊢ P ∧ Q`
  + `constructor`
  + `⊢ P` {br}[] `⊢ Q`
* + `⊢ P ↔ Q`
  + `constructor`
  + `⊢ P → Q` {br}[] `⊢ Q → P`
* + `⊢ P ↔ P` oder {br}[] `⊢ P = P`
  + `rfl`
  + `no goals 🎉`
* + `h : P ↔ Q` {br}[] `⊢ P`
  + `rw h`
  + `h : P ↔ Q` {br}[] `⊢ Q`
* + `h : P ↔ Q` {br}[] `hP : P`
  + `rw h at hP`
  + `h : P ↔ Q` {br}[] `hP : Q`
* + `h : P ↔ Q` {br}[] `⊢ Q`
  + `rw ← h`
  + `h : P ↔ Q` {br}[] `⊢ P`
* + `h : P ↔ Q` {br}[] `hQ : Q`
  + `rw ← h at hQ`
  + `h : P ↔ Q` {br}[] `hQ : P`
* + `⊢ P ∨ Q`
  + `left`
  + `⊢ P`
* + `⊢ P ∨ Q`
  + `right`
  + `⊢ Q`
* + `⊢ 2 + 2 < 5`
  + `norm_num`
  + `no goals 🎉`
* + `p : α → Prop` {br}[] `y : α` {br}[] `⊢ ∃ (x : α), f x`
  + `use y`
  + `p : α → Prop` {br}[] `y : α` {br}[]  `⊢ f y`
* + `x y : ℝ` {br}[] `⊢ x + y = y + x`
  + `ring`
  + `no goals 🎉`
* + `p : α → Prop` {br}[] `⊢ ∀ (x : α), p x`
  + `intro x`
  + `p : α → Prop` {br}[] `x : α` {br}[] `p x`
* + `h₁ : a < b` {br}[] `h₂ : b ≤ c` {br}[] `⊢ a < c`
  + `linarith`
  + `no goals 🎉`
* + `h : P` {br}[] `⊢ Q`
  + `clear h`
  + `⊢ Q`
* + `p : ℕ → Prop` {br}[] `h : ∀ (n : ℕ), p n` {br}[]  `⊢ P`
  + `specialize h 13`
  + `p : ℕ → Prop` {br}[] `h : p 13` {br}[] `⊢ P`
* + `p : ℕ → ℕ → Prop` {br}[] `h : ∀ (n : ℕ), ∃ (m : ℕ), f n m`
  + `obtain ⟨m, hm⟩ := h 27`
  + `f : ℕ → ℕ → Prop` {br}[] `h : ∀ (n : ℕ), ∃ (m : ℕ), f n m` {br}[] `m : ℕ` {br}[] `hm : f 27 m`
* + `⊢ R`
  + `have h : P ↔ Q`
  + `⊢ P ↔ Q` {br}[] `h : P ↔ Q` {br}[] `⊢ R`
* + `h₁ : a < b` {br}[] `h₂ : b < c` {br}[] `⊢ a < c`
  + `apply?`
  + `no goals 🎉` {br}[] Try this: {br}[]  `exact lt_trans h₁ h₂`
* + `hQ : Q` {br}[] `⊢ P ∧ Q`
  + `refine ⟨ _, hQ ⟩`
  + `hQ : Q` {br}[] `⊢ P`
* + `⊢ P ∨ Q → R`
  + `rintro (hP | hQ)` {br}[] = {br}[] `intro h` {br}[] `cases h with hP hQ`
  + `hP : P` {br}[] `⊢ R` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `⊢ P ∧ Q → R`
  + `rintro ⟨hP , hQ⟩` {br}[] = {br}[] `intro h` {br}[] `cases h with h1 h2`
  + `hP : P` {br}[] `hQ : Q` {br}[] `⊢ R`
* + `h : P ∧ Q ∨ P ∧ R` {br}[] `⊢ S`
  + `rcases h with (⟨hP1,hQ⟩|⟨hP2,hR⟩)`
  + `hP1 : P` {br}[] `hQ : Q` {br}[] `⊢ S` {br}[] `hP2 : P` {br}[] `hR : R` {br}[] `⊢ S`
* + `⊢ n + 0 = n`
  + `simp`
  + `no goals 🎉`
* + `h : n + 0 = m` {br}[] `⊢ P`
  + `simp at h`
  + `h : n = m` {br}[] `⊢ P`
* + `f g : ℝ → ℝ` {br}[] `⊢ f = g`
  + `ext x` or `funext x`
  + `f g : ℝ → ℝ` {br}[] `x : ℝ` {br}[] `⊢ f x = g x`
* + `a b : ℕ` {br}[] `h : a ≤ b` {br}[] `⊢ a ≤ b + 1`
  + `omega`
  + `no goals 🎉`
* + `x : ℝ` {br}[] `⊢ 0 ≤ x ^ 2 + 1`
  + `nlinarith [sq_nonneg x]`
  + `no goals 🎉`
* + `a a' b : ℝ` {br}[] `h : a ≤ a'` {br}[] `⊢ a + b ≤ a' + b`
  + `gcongr`
  + `⊢ a ≤ a'`
* + `a b : ℝ` {br}[] `hb : b ≠ 0` {br}[] `⊢ a / b + 1 = (a + b) / b`
  + `field_simp`
  + `⊢ a + b = a + b`
* + `x : ℝ` {br}[] `⊢ (x + 1) * (x - 1) + 1 = x ^ 2`
  + `ring_nf`
  + `no goals 🎉`
* + `n : ℕ` {br}[] `⊢ ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1`
  + `push_cast`
  + `no goals 🎉`
* + `⊢ Continuous (fun x : ℝ => x^2 + Real.sin x)`
  + `fun_prop`
  + `no goals 🎉`
* + `hp : ∀ᶠ x in F, p x` {br}[] `hq : ∀ᶠ x in F, q x` {br}[] `⊢ ∀ᶠ x in F, p x ∧ q x`
  + `filter_upwards [hp, hq] with x hp hq`
  + `x : α` {br}[] `hp : p x` {br}[] `hq : q x` {br}[] `⊢ p x ∧ q x`
* + `h : False` {br}[] `⊢ P`
  + `contradiction`
  + `no goals 🎉`
* + `⊢ (P → Q)`
  + `contrapose`
  + `⊢ (¬Q → ¬P)`
* + `⊢ (2 + 2 : ℕ) = 4`
  + `decide`
  + `no goals 🎉`
* + `⊢ True`
  + `trivial`
  + `no goals 🎉`
* + `⊢ a = b`
  + `symm`
  + `⊢ b = a`
* + `⊢ 1 + 1 = 2`
  + `show 2 = 2`
  + `⊢ 2 = 2`
* + `a b : ℕ` {br}[] `⊢ a + b + (a + b) = 2*(a+b)`
  + `set s := a + b with hs`
  + `s := a + b` {br}[] `⊢ s + s = 2 * s`
* + `f : ℕ → ℕ` {br}[] `h : ∀ n, f n = 0` {br}[] `⊢ ∀ n, f n + 1 = 1`
  + `simp_rw [h]`
  + `⊢ ∀ n, 0 + 1 = 1`
* + `n : ℕ` {br}[] `⊢ (n : ℝ) + 1 = ((n+1 : ℕ) : ℝ)`
  + `norm_cast`
  + `no goals 🎉`
* + `x : ℝ` {br}[] `hx : 0 < x` {br}[] `⊢ 0 < x ^ 2 + 1`
  + `positivity`
  + `no goals 🎉`
:::
