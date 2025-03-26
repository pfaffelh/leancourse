import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Nun kommen wir zu binären Verknüpfungen von Aussagen, also P ∧ Q bzw P ∨ Q. Diese können entweder als Hypothese auftreten, oder als Ziel. Entsprechend gibt es vier verschiedene Fälle, wie wir mit solchen Fällen umgehen können.
-/

/-
  Wir hatten bereits gesehen, dass wir bei einem Ziel P ↔ Q mit _split_ zwei Ziele für die beiden Richtungen erstellen können. Der Grund ist, dass P ↔ Q definitorisch gleich (P → Q) ∧ (Q → P) ist. Für jede solche Verknüpfung bringt uns die _split_-Taktik weiter.
-/
example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split, 
  exact hP,
  exact hQ,
end

-- Aufgabe 1) Das ist ein Schritt mehr als eben...
example (hP : P) (hQ : Q) (hR : R): P ∧ (Q ∧ R) :=
begin
  sorry,
end

/-
  Bei P ∨ Q als Ziel ist es etwas anders. Hier genügt es ja, eine der beiden Aussagen (P bzw Q) zu zeigen. Entsprechend gibt es die Taktiken _left_ und _right_, je nachdem ob man das erste oder zweite Ziel verfolgt.
-/
example (hP : P) : P ∨ Q :=
begin
  left, 
  exact hP,
end

example (hQ : Q) : P ∨ Q :=
begin
  right,
  exact hQ,
end

-- Aufgabe 2) Wenn es drei Aussagen sind, die mit ∨ verknüpft sind, ist implizit P ∨ Q ∨ R als P ∨ (Q ∨ R) geklammert. Das sollte helfen, dieses Ziel zu erreichen:
example (hQ : Q) : P ∨ Q ∨ R :=
begin
  sorry,
end

-- Aufgabe 3) Auch geschachtelte _split_-Taktiken sind möglich.
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  sorry,
end

/- 
  Wenn eine ∧ oder ∨ Verknüpfung in einer Hypothese vorkommt, bringt und die _cases_ Taktik weiter. 

  Bei einem ∧ in einer Hypothese entstehen so zwei Hypothesen. Da ja beide gelten müssen, ist dies identisch mit der Ausgangshypothese.
-/

example (hPQ : P ∧ Q) : P :=
begin
  cases hPQ with hP hQ, 
  exact hP,
end

/-
  Übrigens kann man in einer Hypothese h : P ∧ Q mit h.1 und h.2 direkt auf P und Q zugreifen.
-/

example (hPQ : P ∧ Q) : P :=
begin
  exact hPQ.1,
end

/-
  Ist die Hypothese h : P ↔ Q (was ja P → Q ∧ Q → P bedeutet), so kann man stattdessen auch h.mp und h.mpr anwenden: 
-/
example (hP : P) (hPQ : P ↔ Q) : Q :=
begin
  apply hPQ.mp,
  exact hP,
end

example (hQ : Q) (hPQ : P ↔ Q) : P :=
begin
  apply hPQ.mpr,
  exact hQ,
end

/- 
  Bei einer Verknüpfung h : P ∨ Q entstehen durch _cases_ zwei Ziele. Bei einem gilt P, bei der anderen Q. Da ja unter beiden Bedingungen das Ziel erreicht werden muss, ist dies identisch mit der Ausgangshypothese.
-/
example (hPQ : P ∨ Q) : Q ∨ P :=
begin
  cases hPQ with hP hQ, 
  {
    right, 
    exact hP,
  },
  {
    left, 
    exact hQ,
  },
end

-- Aufgabe 4) Ein einfacher logischer Schluss.
example : (P ∧ Q) → (P ∨ Q) := 
begin
  sorry,
end

-- Aufgabe 5) P und ¬P können nicht gleichzeitig gelten...
example : (P ∧ ¬P) ↔ false :=
begin
  sorry,
end

-- Aufgabe 6a) eine deMorgan'sche Regel für die Negation:
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q) :=
begin
  sorry,
end


-- Aufgabe 6b) eine weitere deMorgan'sche Regel für die Negation:
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q) :=
begin
  sorry,
end

-- Aufgabe 7a) Jetzt könnten wir die deMorgan'schen Regeln für ∧ und ∨ beweisen. Hier die erste:
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  sorry,
end

-- Aufgabe 7b) Hier die zweite:
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  sorry,
end

