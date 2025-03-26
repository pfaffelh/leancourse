import tactic -- lade lean-Taktiken
import data.real.basic
-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

example (n : ℕ) : n + 0 = n :=
begin
  squeeze_simp,
end

example (n : ℕ) (h : n + 0 = n) : P := 
begin
  simp? at h, 
end


example (h : ¬(P ∨ Q)): ¬(P ∨ Q) :=
begin
  push_neg at h,
  push_neg, exact h,
--  change ¬P ∨ ¬ Q,
end


example (h : P → Q → R) : R :=
begin
  apply h,

end


/- 
Mit intro verwandelt man die Aussage links des ersten → in eine Hypothese und die restliche Aussage in das neue Ziel.
Stimmt ein Ziel mit einer Hypothese überein, so genügt assumption für das Schließen des Ziels. Alterantiv liefert exact den Schluss: 
 -/

example : P → P := 
begin
  intro hP, 
  assumption,
end

example : P → P := 
begin
  intro hP, 
  exact hP,
end

/- 
Ab hier folgen die Aufgaben: -/
-- Aufgabe 1) Wenn P gilt, dann folgt P aus P. 
-- Ersetzen Sie das sorry durch geeignete Befehle mit intro und exact.
example : P → (P → P):= 
begin
  intro hP1,
  intro hP2, 
  exact hP2,
end

-- Aufgabe 2) 
-- Hier beginnt der Beweis gleich mit einer Hypothese, ohne sie mit intro erzeugt zu haben.
example (hQ : Q) : (P → Q) := 
begin
  intro hP, 
  exact hQ, 
end

-- Aufgabe 3) Versuchen Sie doch mal, mit 
-- intros hP hPQ
-- anzufangen. Dies kürzt ein wenig ab.
example : P → (P → Q) → Q :=
begin
  intros hP hPQ, -- ersetzt intro hP, introhPQ 
  exact hPQ hP,
end

-- Aufgabe 4) Überlegen Sie, welche der drei folgenden examples stimmen (und warum).
example : P → Q → P :=
begin
  intros hP hQ, exact hP,
end

example : P → P → Q :=
begin
  sorry, -- stimmt nicht 
end

example : P → Q → Q :=
begin
  intros hP hQ, 
  exact hQ,
end




-- 1b) apply (refine comes later)

example (hP : P) (hPQ : P → Q) : Q :=
begin
  apply hPQ,
  exact hP,
end

example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R :=
begin
  exact hQR (hPQ hP),
--  apply hQR (hPQ hP), 
--  refine hQR (hPQ hP), 
--  refine hQR (hPQ _), 
end

--change a bit
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  split, 
  { 
    split,
    exact hQR,
    intro hR, 
    exact hPQ (hTP (hRT hR)),
  },
  split, 
  exact hRT,
  intro hT,
  exact hQR (hPQ (hTP hT)),
end


-- 1c) split, cases, left, right

-- split, exact, intro
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  split, 
  { 
    split,
    exact hQR,
    intro hR, 
    exact hPQ (hTP (hRT hR)),
  },
  split, 
  exact hRT,
  intro hT,
  exact hQR (hPQ (hTP hT)),
end
↔
example : (P ∧ Q) → (P ∨ Q) := 
begin
intro h, left, 
cases h with hP hQ, 
--  rintro ⟨ hP, hQ ⟩, 
exact hP,
end

example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := 
begin
  split,
  intro h, 
  cases h with hP hQ, 
  left, exact hP, 
  by_cases P, 
  left, exact h, 
  right, 
  intro nQ, 
  exfalso, apply nQ, exact hQ, 
  sorry, 
end



-- 1d) add exfalso, triv, negation, by_cases
-- intro, exfalso, exact
example : (¬ P ↔ (P → false)) := 
begin
  split,
  { 
    intros h1 h2, 
    apply h1, 
    exact h2,
  },
  { 
    intro h1, 
--    change P → false, 
    exact h1, 
  }
end

example : (P ∨ ¬P) → true :=
begin
  rintro (hP | hnP);
  triv,  
end

 -- intro, cases
example : (P ∧ ¬P) → false :=
begin
  intro h, cases h with hP hnP, 
--  rintro ⟨hP, hnP⟩, 
  apply hnP,
  exact hP, 
end

example : false → P :=
begin
  intro h, 
  exfalso,
  exact h,
end

-- intro, triv
example : P → true :=
begin
  intro hP,
  triv, 
end

example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,  
  intros hPQ hnQ hP,
  exact hnQ (hPQ hP),
--  apply hnQ,
--  exact hPQ hP,
  intros h1 hP,
  by_contra, 
  exact h1 h hP,
end

-- intro, by_cases, left, exact, cases, apply, exfalso
example : (P → Q) ↔ (Q ∨ ¬ P) :=
begin
  split, 
  {
    intro hPQ, 
    by_cases P,
    { 
      left, 
      exact hPQ h, 
    },
    {
      right, 
      exact h, 
    }, 
  },
  { 
    intros hPQ hP,
    cases hPQ,
    {
      exact hPQ,
    },
    {
      exfalso, 
      apply hPQ,
      exact hP,
    },
  },
end


-- 1e) add exfalso, triv, by_contra
example : true ↔ ¬ false :=
begin
  split,
  {
    intros h1 h2, 
    exact h2,   
  },
  {
    intros h1, 
    triv, 
  },
end


-- by_contra
example : P ↔ ¬¬P := 
begin
  split, 
  intros hP hnP,
  apply hnP, exact hP,
  intro hnnP,
  by_contra, 
  apply hnnP,
  exact h, 
end

example : (P → Q) ↔ (¬Q → ¬P) := 
begin
  split, intro h, by_contra, 
end


-- 1f) refl
example : P ↔ P := 
begin
  refl,
end

example : P = P :=
begin
  refl, 
end


-- 1g) add by_cases
example : (P ∨ ¬P ) :=
begin
  by_cases P with hP hnP,
  left, exact h,
  right, exact h,
end

-- 2) have

example : P → P := 
begin
  have h : P ↔ P, refl, apply h.1,
end



-- 3) Abkürzzungen
-- 3a) rintro(s), rcases, obtain

example : (P → Q) ∧ (Q → R) → (P → R) := 
begin
  rintro ⟨ hPQ, hQR ⟩ hP,
  exact hQR (hPQ hP), 
end

-- intro, cases, exact
-- rintro 

example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q :=
begin
  by_cases P,
  exact hPQ h, 
  exact hnPQ h,  
end

-- obtain

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  obtain hQ := hPQ hP,
  obtain hnQ := hPnQ hP,
  apply hnQ, 
  exact hQ,
end

example : (P ∨ Q) → (¬Q → P) := 
begin
  rintros (hP | hQ) h, 
  exact hP,
  exfalso, 
  apply h, 
  exact hQ, 
end









/-
  Nun kommen wir zu binären Verknüpfungen von Aussagen, also P ∧ Q bzw P ∨ Q. Diese können entweder als Hypothese auftreten, oder als Ziel. Entsprechend gibt es vier verschiedene Fälle, wie wir mit solchen Fällen umgehen können.
-/




-- 1c) split, cases, left, right

-- split, exact, intro
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  split, 
  { 
    split,
    exact hQR,
    intro hR, 
    exact hPQ (hTP (hRT hR)),
  },
  split, 
  exact hRT,
  intro hT,
  exact hQR (hPQ (hTP hT)),
end

example : (P ∧ Q) → (P ∨ Q) := 
begin
intro h, left, 
cases h with hP hQ, 
--  rintro ⟨ hP, hQ ⟩, 
exact hP,
end

example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := 
begin
  split,
  intro h, 
  cases h with hP hQ, 
  left, exact hP, 
  by_cases P, 
  left, exact h, 
  right, 
  intro nQ, 
  exfalso, apply nQ, exact hQ, 
  sorry, 
end



-- 1d) add exfalso, triv, negation, by_cases
-- intro, exfalso, exact

example : (P ∨ ¬P) → true :=
begin
  rintro (hP | hnP);
  triv,  
end

 -- intro, cases
example : (P ∧ ¬P) → false :=
begin
  intro h, cases h with hP hnP, 
--  rintro ⟨hP, hnP⟩, 
  apply hnP,
  exact hP, 
end








-- 2) Einführung neuer Hypothesen mit by_cases und have

-- 1g) add by_cases
example : (P ∨ ¬P ) :=
begin
  by_cases P with hP hnP,
  left, exact h,
  right, exact h,
end

example : P → P := 
begin
  have h : P ↔ P, refl, apply h.1,
end



-- 3) Abkürzzungen


-- 1f) refl, rw
example : P ↔ P := 
begin
  refl,
end

example : P = P :=
begin
  refl, 
end

-- 3a) rintro(s), rcases, obtain



example : (P → Q) ∧ (Q → R) → (P → R) := 
begin
  rintro ⟨ hPQ, hQR ⟩ hP,
  exact hQR (hPQ hP), 
end

-- intro, cases, exact
-- rintro 

example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q :=
begin
  by_cases P,
  exact hPQ h, 
  exact hnPQ h,  
end

-- obtain

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  obtain hQ := hPQ hP,
  obtain hnQ := hPnQ hP,
  apply hnQ, 
  exact hQ,
end


example : (P → Q) ↔ (Q ∨ ¬P) :=
begin
  split,
  {
    intro h,
    by_cases h1 : P,
    {
      left,
      exact h h1,
    },
  right,
  exact h1,
  },
  {
    intros h h1,
    cases h with h2 h3,
    {
      exact h2,
    },
    {
      exfalso,
      exact h3 h1,
    },
  },
end


























--change a bit
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  split, 
  { 
    split,
    exact hQR,
    intro hR, 
    exact hPQ (hTP (hRT hR)),
  },
  split, 
  exact hRT,
  intro hT,
  exact hQR (hPQ (hTP hT)),
end

example : (P ∧ ¬P) ↔ false :=
begin
  split,
  rintro ⟨ hP, hnP ⟩,
  exact hnP hP, 
  intro h, cases h,
end



-- 

lemma l3 : (P → Q) ↔ (Q ∨ ¬P) :=
begin
  split,
  {
    intro h,
    by_cases h1 : P,
    {
      left,
      exact h h1,
    },
  right,
  exact h1,
  },
  {
    intros h h1,
    cases h with h2 h3,
    {
      exact h2,
    },
    {
      exfalso,
      exact h3 h1,
    },
  },
end










-- 1f) refl, push_neg, change, refine
example : P ↔ P := 
begin
  refl,
end

example : P = P :=
begin
  refl, 
end














import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Bisher haben wir immer ein _example_ bewiesen, ohne auf andere Ergebnisse zu verweisen. Die Mathematik lebt ja aber gerade von der Anwendung bereits bekannter Ergebnisse. Dies können wir etwa durch Anwendung der Taktiken _apply_ und _rw_ (für rewrite) erreichen. Dazu müssen wir allerdings unsere Resultate nicht mehr als _example_ formulieren, sondern als _lemma_ oder _theorem_.

  Wir führen nun zwei Lemmas l1 und l2 ein, um anschließend ein example zu beweisen. Der Taktik _rw_ gibt es dabei jeweils in zwei Versionen, und kann nur für Resultate verwendet werden, die eine Gleichheit oder ein ↔ postulieren. Bei _rw_ wird die Aussage des anzuwendenden Resultats von links nach recht, bei _rw ←_ von rechts nach linke angewendet.
-/

lemma l1 : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,  
  {
    intros hPQ hnQ hP,
    apply hnQ (hPQ hP),
  },
  {  
    intros h1 hP,
    by_contra h, 
    apply h1 h hP,
  },
end

lemma l2 : P ↔ ¬¬P := 
begin
  split,
  {
    intros hP hnP,
    apply hnP hP,
  },
  {
    intros h1,
    by_contra,
    apply h1 h,
  },  
end

-- Diese Aussage kennen wir bereits, und beweisen Sie nochmals neu. Diesmal verwenden wir l1 und l2 und die Taktik _rw_.
example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  rw l1 at hPnQ,
  rw ← l2 at hPnQ,
  exact (hPnQ (hPQ hP)) hP,
end


/-
  Bisher haben wir immer ein _example_ bewiesen, ohne auf andere Ergebnisse zu verweisen. Die Mathematik lebt ja aber gerade von der Anwendung bereits bekannter Ergebnisse. Dies können wir etwa durch Anwendung der Taktiken _apply_ und _rw_ (für rewrite) erreichen. Dazu müssen wir allerdings unsere Resultate nicht mehr als _example_ formulieren, sondern als _lemma_ oder _theorem_.

  Wir führen ein Lemma l1 ein, um anschließend ein example zu beweisen. Der Taktik _rw_ gibt es dabei jeweils in zwei Versionen, und kann nur für Resultate verwendet werden, die eine Gleichheit oder ein ↔ postulieren. Bei _rw_ wird die Aussage des anzuwendenden Resultats von links nach recht, bei _rw ←_ von rechts nach links angewendet.
-/

lemma l1 : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,  
  {
    intros hPQ hnQ hP,
    apply hnQ (hPQ hP),
  },
  {  
    intros h1 hP,
    by_contra h, 
    apply h1 h hP,
  },
end

/-
  Die nächste Aussage kennen wir bereits, und beweisen Sie nochmals neu. Diesmal verwenden wir rw, und zwar mit l1 und 
  ```
  theorem not_not : ¬¬a ↔ a 
  ```
-/ 
example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  rw l1 at hPnQ,
  rw not_not at hPnQ,
  intro hP,
  exact (hPnQ (hPQ hP)) hP,
end





-- Noch eines:
example (f : X → Prop) : (∃ x, f x) ↔ ¬(f = λ x, false) :=
begin
  split, intros h h1, cases h with x h2,
  rw h1 at h2, exact h2, 
  intro h, by_contra h1, apply h, push_neg at h1, ext, split, intro h2, apply h1 x, exact h2, intro h, exfalso, exact h,  
end


variable X : Type

example (P : X → Prop) : ¬ ∃ (x : X), P x :=
begin
  push_neg, 
end

example (P Q : Prop) (hP : P) : Q :=
begin
  revert hP,
end

example (n : ℝ): (n+1)^2 = n^2 + 2*n + 1 :=
begin
  ring,
end

example : | (1 : ℝ) | = 1 :=
begin
  norm_num,
end

example : ∃ (n : ℕ) (h : n > 0), n^2 = 9 :=
begin
  refine ⟨3, _, by norm_num⟩,  
end



example (f : X → Prop) (x : X) (h : f x) : (∀ x, f x) :=
begin
  revert x,
end

example (n : ℕ) : n < n+1 :=
begin
  revert n,
  exact lt_add_one, 
end










