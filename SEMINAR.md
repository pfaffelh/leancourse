# Lean-Seminar, Sommersemester 2027

Im Anschluss an die Vorlesung *Interactive Theorem Proving using Lean*
(WS 2026/27). Hier werden Themen gesammelt.

Pro Thema: worum es geht, was man aus der Vorlesung voraussetzt,
Quellen. Die Stichworte sind Anhaltspunkte und vor dem Vortrag zu
prüfen.

## Themen

### `grind` und wie es funktioniert

- *Worum es geht:* `grind` ist Leans allgemeine Automatisierung. Wie
  arbeitet die Taktik intern, wofür ist sie gut, und wo scheitert
  sie?
- *Stichworte:*
  - Beweis durch Widerspruch: die Negation des Ziels wird angenommen;
  - Kongruenzabschluss auf einem E-Graphen;
  - E-Matching: Instanziieren von Lemmas mit `@[grind]`-Attribut;
  - Fallunterscheidungen;
  - Hilfslöser, etwa für lineare Arithmetik und kommutative Ringe;
  - am Ende ein Beweisterm, den der Kern prüft.
- *Bezug zur Vorlesung:* `grind` löst alle beweisbaren Aussagen von
  Blatt 01 (gemessen, siehe `CLAUDE.md`, Eintrag 2026-10-10). Auf
  `L-g` wird es als *finishing tactic* eingeführt. `grind` benutzt
  `Classical.choice` auch dort, wo die Aussage konstruktiv ist, etwa
  bei `P → ¬¬P`.
- *Voraussetzungen:* Kapitel 1 der Vorlesung und die Blätter `L-a`
  bis `L-g`.
- *Quellen:*
  - das Kapitel zu `grind` im Lean Reference Manual;
  - Anhang des Skripts, Seite `grind`
    (`Leancourse/Coursenotes/4-Appendix/Tactics/Grind.lean`).

### Funktoren und Monaden

- *Worum es geht:* Klassen über Typkonstruktoren statt über Typen.
  `Functor` und `Monad` in Lean, ihre Gesetze, und wo dieselbe
  Struktur in der Mathematik auftritt.
- *Stichworte:*
  - `class Functor` mit `map` und der Voreinstellung
    `mapConst := map ∘ Function.const β` (überschrieben z.B. in
    `ReaderT` und `WittVector`); `<$>`; eine Instanz von Hand;
  - `LawfulFunctor` (`map_const`, `id_map`, `comp_map`); eine gültige
    Instanz, die `id_map` verletzt (`List` mit `reverse`);
  - `Bind`, `Applicative`, `Monad`: welche Felder Voreinstellungen
    haben (nur `pure` und `bind` nicht), `map` aus `bind`;
  - `Option` für Rechnungen, die scheitern können, `List` für mehrere
    Ergebnisse; die `do`-Notation als Kette von `>>=`;
  - die Monadengesetze und `LawfulMonad`; Monaden in der
    Kategorientheorie (`η = pure`, `μ = join`);
  - in der Mathematik: `Set` (Bild, Vereinigung; `Functor Set` global,
    `Set.monad` nur lokal), `Finset` (braucht `DecidableEq`), `Filter`
    (`Filter.monad` ist keine Instanz), `PMF` (globale Monade).
- *Bezug zur Vorlesung:* stand bis November 2026 in Kapitel 1.7 und
  auf Blatt `1.7-a`; gestrichen, weil die Mathematik nur `map` und
  `bind` auf konkreten Typen braucht. Der alte Text liegt in der
  Git-Historie (`Leancourse/Coursenotes/1-Lean/7-FunctorsMonads.lean`,
  `Slides/1-7-FunctorsMonads.lean`,
  `Leancourse/Exercises/1-Lean/7-a-Monads.lean`, Stand vor dem
  27.11.2026).
- *Voraussetzungen:* Typklassen (Kapitel 1.6), Mengen und Filter
  (2.2, 2.6).
- *Quellen:*
  - *Functional Programming in Lean*, Kapitel zu Funktoren,
    Applicatives und Monaden;
  - Lean-Quelltext `Init/Prelude.lean` und `Init/Control/Lawful`;
  - Mathlib: `Mathlib/Data/Set/Functor.lean`,
    `Mathlib/Order/Filter/Map.lean`,
    `Mathlib/Probability/ProbabilityMassFunction/Monad.lean`.
