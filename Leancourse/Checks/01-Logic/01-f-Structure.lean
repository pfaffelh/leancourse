import Mathlib

/-!
# (witness) 01-f -- Structuring a proof

No new logic on this sheet. The statements are the kind you can
already do. What is new is how to write the proof down: name
intermediate steps, split a goal into holes, take hypotheses apart in
one line.

## Tactics introduced here

| tactic              | use it when                                 |
|---------------------|---------------------------------------------|
| `have h : P := ...` | record an intermediate fact                 |
| `suffices h : P`    | the same, backwards                         |
| `refine ⟨?_, ?_⟩`   | build a term and leave holes                |
| `rintro ⟨hP, hQ⟩`   | `intro` and take apart in one step          |
| `rcases h with ...` | the flexible form of `obtain`               |
-/

variable (P Q R S T : Prop)

/-! ## `have`

`have h : P := proof` adds `h : P` to the context. Use it to name a
step instead of nesting everything into one term.

Compare. First without: -/

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P := by
  intro hP
  exact (hPnQ hP) (hPQ hP)

/-! Now with. Longer, but you can read what happens: -/

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P := by
  intro hP
  have hQ : Q := hPQ hP
  have hnQ : ¬Q := hPnQ hP
  exact hnQ hQ

/-! If the fact needs its own proof, write `:= by` and indent: -/

example (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  have hQ : Q := by
    apply hPQ
    exact hP
  exact hQR hQ

-- Exercise 1) Name the two steps.
example (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  have hQ : Q := hPQ hP
  have hR : R := hQR hQ
  exact hRS hR

-- Exercise 2) `have` the same fact once, use it twice.
example (h : P → Q) (hP : P) : Q ∧ Q := by
  have hQ : Q := h hP
  exact ⟨hQ, hQ⟩

-- Exercise 3) A case split recorded as a `have`.
example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q := by
  have h : P ∨ ¬P := by
    exact Classical.em P
  obtain (hp | hnp) := h
  · exact hPQ hp
  · exact hnPQ hnp

/-! ## `suffices`

`suffices h : P` is `have` the other way round. It says: if I had
`P`, I would be done. The first goal uses `h : P` to close the
original goal; the second goal is `⊢ P`. -/

example (hPQ : P → Q) (hP : P) : Q := by
  suffices h : P by
    exact hPQ h
  exact hP

-- Exercise 4) Reduce to `R`, then prove it.
example (hR : R) (hRP : R → P) : P := by
  suffices h : R by
    exact hRP h
  exact hR

/-! ## `refine`

`refine` takes a term with holes `?_` and leaves each hole as a goal.
It is `exact` with gaps. -/

example (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨?_, ?_⟩
  · exact hP
  · exact hQ

/-! Holes may be anywhere, and parts you already know can be filled
in directly: -/

example (hP : P) (hQR : Q → R) (hQ : Q) : P ∧ R := by
  refine ⟨hP, ?_⟩
  exact hQR hQ

-- Exercise 5) Two holes.
example (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  refine ⟨?_, ?_⟩
  · exact hPQ
  · exact hQP

-- Exercise 6) One hole is enough here.
example (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  refine ⟨hP, ?_⟩
  exact ⟨hQ, hR⟩

/-! ## `rintro` and `rcases`

`rintro` is `intro` followed by taking the hypothesis apart. The
patterns are the ones you know: `⟨_, _⟩` for `∧`, `(_ | _)` for `∨`,
and they nest. -/

example (h : P → Q → R) : (P ∧ Q) → R := by
  rintro ⟨hP, hQ⟩
  exact h hP hQ

example : (P ∨ Q) → (Q ∨ P) := by
  rintro (hP | hQ)
  · right
    exact hP
  · left
    exact hQ

/-! `rcases h with ...` applies the same patterns to a hypothesis you
already have. `obtain` from 01-b and 01-c is the same tactic with
nicer syntax. -/

example (h : P ∧ Q ∧ R) : Q := by
  rcases h with ⟨hP, hQ, hR⟩
  exact hQ

-- Exercise 7) One `rintro`, then one line.
example (h : P → Q → R → S) : (P ∧ Q ∧ R) → S := by
  rintro ⟨hP, hQ, hR⟩
  exact h hP hQ hR

-- Exercise 8) Nested pattern: `⟨(_ | _), _⟩`.
example (hPR : P → R) (hQR : Q → R) : ((P ∨ Q) ∧ S) → R := by
  rintro ⟨(hP | hQ), _⟩
  · exact hPR hP
  · exact hQR hQ

-- Exercise 9) `rintro` with two patterns in a row.
example : (P ∨ Q) → (¬Q → P) := by
  rintro (hP | hQ) hnQ
  · exact hP
  · exact absurd hQ hnQ

-- Exercise 10) Nothing new, but write it in as few lines as you can.
example : ((P → Q) ∧ (Q → R)) → (P → R) := by
  rintro ⟨hPQ, hQR⟩ hP
  exact hQR (hPQ hP)

/-! ## Term mode

`intro` introduces a variable, so a proof of `P → Q` can be written
as `fun hP ↦ ...` directly. Combined with `refine` this makes short
proofs of `↔`: -/

example : P ↔ P := by
  refine ⟨fun hP ↦ ?_, fun hP ↦ ?_⟩
  · exact hP
  · exact hP

-- Exercise 11) Fill both holes.
example : (P ∧ Q) ↔ (Q ∧ P) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.2, h.1⟩
