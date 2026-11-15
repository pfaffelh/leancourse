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
