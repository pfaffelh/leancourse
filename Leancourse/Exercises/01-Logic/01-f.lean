import Mathlib

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop)

/-
  We now come to a few abbreviating tactics, namely `rintro`, `rcases` and `obtain`. First of all, two parenthesis notations are important here, namely `⟨hP, hQ⟩` and `(hP | hQ)`. The first notation represents the simultaneous introduction of `hP` and `hQ` as a pair of hypothesis, the second notation represents two goals, one with `hP`, the other with `hQ`. (Exactly the same as with the `cases'` tactic. However, here we can also process more than two terms, for example `⟨hP, hQ, hR⟩` for a joint introduction of `hP`, `hQ` and `hR`. It is also possible to nest, for example `⟨(hP | hQ), hR ⟩`).
  The three tactics are abbreviations, namely `rintro` for `intro` + `cases'`, `rcases` for a more flexible version of `cases'`, and `obtain` for `intros` + `have`. We'll start with examples.-/

-- An example for `rintro`
example : (P ∨ Q) → (¬Q → P) := by
  rintro (hP | hQ) h
-- identical with
-- intro h1 h
-- cases' h1 with hP hQ
  · exact hP
  · exfalso
    exact h hQ

-- An example with `rcases`
example (h : P ∧ Q ∧ R) : (P ∨ Q ∨ R) := by
  rcases h with ⟨ hP, hQ, hR ⟩
  -- identical with
  -- cases' h with hP hQR
  -- cases' hQR with hQ hR
  left
  exact hP

-- An example with `obtain`
example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P := by
  intro hP
  obtain hQ := hPQ hP
  obtain hnQ := hPnQ hP
  exact hnQ hQ

/-
  We note that we can apply the same notation with `⟨hP, hQ⟩` and `(hP | hQ)` to other tactics.  -/

example (hP : P) (hQ : Q) : P ∧ Q := by
  exact ⟨hP, hQ⟩

-- Exercise 1) This can be done in a single line.
example (hR : R) (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( Q ∧ T) := by
  sorry

-- Exercise 2) Here, `rintro` is helpful
example (h : P → Q → R → S) : (P ∧ Q ∧ R) → S := by
  sorry

-- Exercise 3) The same applies here...
example : (P ∨ Q) → (¬Q → P) := by
  sorry


-- Exercise 4) Yet another time...
example : (P → Q) ∧ (Q → R) → (P → R) := by
  sorry

-- For `refine`, you can use the same notation with `⟨.,.⟩` and `( | )`. In addition, using `?_`, you can leave holes which you must fill in later.

example (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨?_, ?_⟩
  · exact hP
  · exact hQ

-- You can even circumvent many `intro`s using the fact that they _just_ introfuce new variables which need to be plugged into functions.
example : P ↔ P := by
  refine ⟨fun hP ↦ ?_, fun hP ↦ ?_⟩
  · exact hP
  · exact hP

-- Exercise 5)
example : (P → Q) ↔ (Q ∨ ¬P) := by
  refine ⟨fun h ↦ ?_, fun h hP ↦ ?_⟩
  · sorry
  · sorry
