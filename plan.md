# Semesterplan -- Interactive Theorem Proving using Lean

Universität Freiburg, Wintersemester 2026/27.

## Eckdaten

| | |
|---|---|
| Umfang | 6 ECTS ohne Projekt, 9 ECTS mit Projekt |
| Termine | Vorlesung Mo, Labor Mi, je 90 Minuten |
| Beginn | Mo 19.10.2026 |
| Weihnachtspause | 23.12.2026 -- 06.01.2027 |
| Ende | Sa 13.02.2027 (letzter Termin Mi 10.02.) |
| Personal | Dozent + ein Tutor |
| Prüfung | mündlich (Fragenkatalog in `exam.md`) |
| Zulassung | 3 von 5 Kurztests bestanden |

**Workload (6 ECTS).** 180 h gesamt, davon 43,5 h Kontaktzeit
(15 Vorlesungen + 14 Labore à 1,5 h). Bleiben rund 136 h, also gut
9 h pro Woche Eigenarbeit. Zwei Übungsblätter pro Woche sind damit
knapp kalkuliert, nicht großzügig.

## Format

**Jede Woche: Montag Vorlesung, Mittwoch Labor.** Kein Termin
halb-halb -- das zerfasert.

Bei Formalisierung ist nicht Vortragszeit der Engpass, sondern
Tastaturzeit. Im Labor arbeiten alle am Rechner, Dozent und Tutor
gehen herum. Dort entsteht auch das Bild davon, wer was kann.

Die Aufteilung gilt ab Woche 1. Nur der Mittwoch der ersten Woche
weicht ab: dort wird installiert.

### Was das am Anfang kostet

Das Verhältnis stimmt in den ersten Wochen nicht von selbst. „So
funktioniert `intro`" ist nach zwanzig Minuten erzählt, und der
Mittwoch bräuchte das Doppelte, weil alle langsam tippen.

Die Antwort ist nicht, die Termine zu mischen, sondern den Montag ab
Woche 2 durch das Skript laufen zu lassen, von Kapitel 1.1 an. Die
Übung bleibt derweil bei der Logik und nimmt das Blatt zur Vorlesung
zusätzlich mit. Zwei Wochen lang sind das drei Blätter; siehe
*Wochenplan*. `02-b` (`Bool`) liegt dabei eine Woche hinter seiner
Vorlesung -- das Kapitel 1.1 ist an einem Montag durch.

### Woche 1, Mittwoch: Installationstermin

Das erste Labor geht vollständig für die Einrichtung drauf. VS Code,
die Lean-Erweiterung, `git clone`, `lake exe cache get` -- bei zwanzig
Leuten mit drei Betriebssystemen ist das ein Termin, kein
Viertelstündchen. Einplanen statt erleben.

Entsprechend liegt Test 1 erst in Woche 4: davor scheitern noch Leute
an `lake exe cache get`, und das will man nicht prüfen.

### Die erste Sitzung, Mo 19.10.

Kein Üben -- installiert ist noch nichts. **30 Minuten Organisation,
60 Minuten Kontext.**

**Organisation.** Format, ECTS, die fünf Tests mit der 3-von-5-Regel,
Projekt im Anschluss, mündliche Prüfung. Tutor vorstellen. Zwei Dinge,
die sonst untergehen:

- *KI ist in den Hausaufgaben erlaubt -- und warum.* Nicht aus
  Großzügigkeit: `grind` löst 127 der 128 Aussagen von Blatt 01 ohne
  jede KI. Ein Verbot wäre Theater. Geprüft wird auf Papier. Am ersten
  Tag gesagt, gibt es später keine Diskussion.
- *Für Mittwoch: Laptop mit Administratorrechten.* Häufigster Grund,
  warum der Installationstermin bei Einzelnen scheitert, und nur
  vorher lösbar.

**Kontext, drei Blöcke.**

*Geschichte (15 min).* Frege 1879, Russells Brief 1902. Principia
Mathematica: `1+1=2` in Band II, mit der Anmerkung der Autoren „The
above proposition is occasionally useful." De Bruijn, Automath 1967;
1977 geht Landaus *Grundlagen der Analysis* komplett durch die
Maschine. Vierfarbensatz (Appel-Haken 1976, Gonthier 2005) --
*Computerbeweis ist nicht computergeprüfter Beweis*. Kepler: Hales
1998, zwölf Gutachter, vier Jahre, dann „zu 99 % sicher, mehr geht
nicht"; Flyspeck 2014 -- *Peer Review ist an eine Grenze gestoßen*.
Pointe: die Idee ist 150 Jahre alt, das Werkzeug 20.

*Mathlib ansehen (20 min).* Nicht erzählen, klicken. Zahlen aus dem
eigenen Checkout rechnen, nicht von der Folie -- Stand 15.09.2026:
8.529 Dateien, 2,33 Mio Zeilen, rund 189.000 Theoreme, 64.000
Definitionen, 34.768 Commits, 1.031 Beitragende. Entscheidend ist die
letzte Zahl: **820 Commits in 30 Tagen, also 27 pro Tag.** Alle anderen
sagen „groß", diese sagt „lebt". Dann: `intermediate_value_Icc` im
Quelltext aufmachen; ein offener PR mit Review-Diskussion; Zulip; die
„1000+ theorems"-Liste der Community; Loogle live. Mathematik als
gemeinsam gepflegtes Artefakt -- dazu gibt es keinen zweiten
Gegenstand.

*Aktuelle Entwicklungen (25 min).* Der Umschwung: Liquid Tensor
Experiment, Dezember 2020 stellt Scholze seinen eigenen Satz zur
Debatte; Juli 2022 fertig; Buzzards ICM-Plenarvortrag 2022 als
Markierung. Verteiltes Arbeiten: Taos PFR (Nov. 2023, drei Wochen),
Equational Theories Project 2024, Buzzards *Formalising Fermat* seit
2024. Die KI-Welle: Erdős' unit distance (OpenAI, Mai 2026),
Anthropics Fermat-Formalisierung, Navier-Stokes-Blowup, zwei
unabhängige Poincaré-Formalisierungen, seit Anfang 2026 rund
achtfache Zunahme der arXiv-Preprints mit Lean.

Und dann die Einordnung, die die Sitzung ehrlich macht (Material:
`1.1-pertinence.md` im MSCA-Antrag): diese Projekte sind *goal-driven*
-- kürzester Weg zum Schlagzeilensatz, Zwischenresultate nicht in
natürlicher Allgemeinheit, teils schrullige Definitionen, fragil
gegenüber Versionswechseln. Zwei liefen bei Firmen: das Ergebnis ist
öffentlich, der Weg dahin nicht. Deshalb braucht es Leute, die das
Handwerk können.

Schlusssatz: Sprachmodelle produzieren überzeugend aussehende falsche
Beweise. Der Proof Assistant ist die einzige Prüfinstanz, die
mitskaliert. Das ist der Grund, warum KI in den Hausaufgaben erlaubt
ist und in den Tests nicht.

## Termine

Gerechnet für Mo/Mi vom 19.10.2026 bis 13.02.2027, ohne
Weihnachtspause. Allerheiligen (01.11.2026) fällt auf einen Sonntag
und kostet nichts.

Die Pause frisst **drei Mittwoche** (23.12., 30.12., 06.01.), aber nur
**zwei Montage** (28.12., 04.01.). Daher 15 Vorlesungen, aber nur
14 Labore: der **Montag 21.12. hat kein Labor**.

## Wochenplan

| W | Mo | Mi | Vorlesung | Kapitel | Blätter | |
|---|---|---|---|---|---|---|
| 1 | 19.10. | 21.10. | Warum formalisieren? · *Mi: Installation* | Einleitung | 01-a | |
| 2 | 26.10. | 28.10. | `Nat`, `Bool`, Reduktionsregeln | 1.1 | 01-b, 01-c, 02-a | |
| 3 | 02.11. | 04.11. | Typen, Strukturen, Quotienten | 1.2 | 01-d, 01-e, 02-b | |
| 4 | 09.11. | 11.11. | Terme und Pattern Matching | 1.3 | 01-f, 01-g | **Test 1** |
| 5 | 16.11. | 18.11. | Typklassen | 1.4 | 02-c, 02-d | |
| 6 | 23.11. | 25.11. | Curry-Howard | 1.5 | 02-e, 03-00 | |
| 7 | 30.11. | 02.12. | Abhängige Typen und Notation | 1.6, 1.7 | 03-01, 03-a | **Test 2** |
| 8 | 07.12. | 09.12. | Mengen und Typen | 2.1 | 03-b, 03-c | |
| 9 | 14.12. | 16.12. | Universen und Axiome | 2.2 | 05-a, 05-b | **Test 3** |
| 10 | 21.12. | -- | Proof Engineering; `conv` | Appendix | 07-a, 07-b, 04-a | |
| | | | *Pause 23.12. -- 06.01.* | | | |
| 11 | 11.01. | 13.01. | Ordnungen, algebraische Hierarchie | 2.4, 2.5 | 06-a | |
| 12 | 18.01. | 20.01. | Filter | 2.6 | 06-d | |
| 13 | 25.01. | 27.01. | Topologie | 2.7 | 06-b | **Test 4** |
| 14 | 01.02. | 03.02. | Maßtheorie | 2.8 | 06-c, 06-e | |
| 15 | 08.02. | 10.02. | Monaden und Wahrscheinlichkeit | 2.9 | 04-b, 06-f | **Test 5** |

29 der 32 Blätter. Nicht im Pflichtprogramm sind `05-c`, `05-d` und
das Bonusblatt `08-a`; siehe unten.

**Woche 1 trägt nur ein Blatt.** Montag ist reiner Kontext, Mittwoch
reine Installation -- in dieser Woche sieht niemand eine geführte
Minute Lean. Zwei Blätter wären dort Unfug.

**Die Wochen 2 und 3 tragen drei.** Die Logik läuft weiter (`01-b`
bis `01-e`), und die beiden Blätter zu Kapitel 1.1 kommen dazu: `02-a`
zu `Nat.rec`, `02-b` zu `Bool`. So wird die Vorlesung der ersten
Wochen gleich geübt, obwohl die Logik noch nicht fertig ist.

Dafür verliert Woche 5 ihre vier Blätter -- die schlimmste Woche des
alten Plans. Der Schnitt bleibt bei zwei Blättern pro Woche.

Wenn drei zu viel sind, rutscht `02-b`: `Bool` wird in den späteren
Blättern kaum gebraucht.

### Vorlesung und Skript

Die Spalte *Kapitel* läuft durch das Skript, von 1.1 bis 2.9, ohne
Ausnahme. Jeder Montag hat sein Kapitel und seinen Foliensatz. Übrig
bleibt nur 2.3, das ohnehin Projektmaterial ist.

**Ein Kapitel ist eine Vorlesung.** Die sieben vorhandenen Decks sind
alle 16 bis 19 Folien lang, unabhängig davon, wie lang das Kapitel
ist -- sie wurden von Anfang an auf 90 Minuten geschnitten. 15 Kapitel
auf 13 Vorlesungen (Woche 1 ist die Einleitung, Woche 10 der Appendix)
heißt also: zweimal müssen zwei Kapitel zusammen. Das sind 1.6 mit 1.7
in Woche 7 und 2.4 mit 2.5 in Woche 11, jeweils die beiden kürzesten
benachbarten.

Zur Gleichverteilung, gemessen in Zeilen Skript je Termin: Mittel 466,
Spanne 263 (Woche 8, Mengen und Typen) bis 768 (Woche 15,
Wahrscheinlichkeit). 2.9 ist das längste Kapitel des Skripts und steht
zuletzt; dort ist am ehesten zu kürzen.

Ab Woche 3 läuft die Vorlesung der Übung voraus, um ein bis drei
Wochen. Das ist gewollt: die Theorie hat man im Hinterkopf, während
die Finger an den Logikblättern weiterarbeiten. Die Blätter erklären
sich selbst, und im Labor stehen zwei Leute daneben.

**Was es kostet.** Die BHK-Interpretation steht in 1.5, konstruktiv
gegen klassisch in 2.2 -- also in den Wochen 6 und 9. Die Blätter
`01-d` und `01-e` liegen in Woche 3 und laufen damit drei bis sechs
Wochen vor ihrer Theorie. Woche 2 federt das teilweise ab: dort ist
`False` dran, und `¬P` ist `P → False`. Für den Rest reichen die
Taktikeinträge im Appendix (`by_cases`, `push Not`, `itauto` gegen
`tauto`).

### Der Faden der ersten Wochen

**Woche 1 -- Warum überhaupt formalisieren?** Geschichte, Mathlib,
aktuelle Lage; ausgearbeitet oben unter *Die erste Sitzung*. Null
Vorwissen nötig, und es erklärt, wofür die nächsten Wochen Mühe gut
sind.

**Woche 2 -- Kapitel 1.1, ganz.** `Nat` mit zwei Konstruktoren,
`Nat.rec`, definitionelle Gleichheit, die Reduktionsregeln, und am
Ende `Bool`, `True`, `False`. Der Foliensatz hat dafür 18 Folien, die
letzten vier sind `Bool` und die beiden Propositionen. Das Kapitel
steht seit Juli 2026 bewusst *vor* *Types* -- diese Entscheidung
trägt genau hier, denn `Nat` ist der konkreteste mögliche Einstieg in
die Typentheorie.

**Ab Woche 3 -- das Skript der Reihe nach.** Eine gewöhnliche
Vorlesung, ein Kapitel pro Woche.

**Die Gewichtung ist Absicht.** Neun Wochen Handwerk vor der Pause,
fünf Wochen Mathematik danach. Die Mathlib-Kapitel sind der Ertrag des
Kurses, nicht die Zugabe; ein früherer Entwurf gab ihnen zwei Wochen
und war damit verkehrt herum. Der Kurs endet mit Wahrscheinlichkeit,
nicht mit `conv`.

### Der 21.12. -- Proof Engineering

Montag vor der Pause, kein Labor dahinter. Das passt hier trotzdem,
und zwar besser als alles andere: Proof Engineering und `conv` sind
für alle wichtig, die später zu Mathlib beitragen wollen, und die
Blätter `07-a` und `07-b` sind in sich geschlossen.

**Drei Blätter laufen als Ferienaufgabe über die Pause:** `07-a`,
`07-b` und dazu `04-a` (Rekursion, Pattern Matching, Funktionen höherer
Ordnung). Pattern Matching war in Woche 4 dran, mit Kapitel 1.3; der
Rest von `04-a` steht für sich, genau wie die beiden anderen Blätter.
Drei Wochen sind dafür reichlich, und das erste Labor nach der Pause
(13.01., ohne Test) beginnt mit Fragen dazu.

`conv` kommt damit *vor* Filter und Topologie -- genau rechtzeitig,
denn dort lässt zum ersten Mal jemand `rw` an der falschen Stelle
treffen.

### Nicht im Pflichtprogramm

Drei Blätter fallen heraus:

- `05-c-Notation` -- kurz, und Kapitel 1.7 ist in Woche 7 vorgetragen;
  taugt als Selbststudium.
- `05-d-WellFoundedness` -- ohnehin Projektmaterial
  (Cantor-Schröder-Bernstein, ℤ als Quotient). Das zugehörige Kapitel
  2.3 ist das einzige, das keinen Termin hat.
- `08-a-Puzzles` -- Bonusblatt mit den drei Rätseln aus der
  Beweismaschine.

## Kurztests

**Fünf Tests, drei müssen bestanden sein.** Jeweils zu Beginn des
Labors, 10 Minuten, auf Papier.

Termine: **11.11., 02.12., 16.12., 27.01., 10.02.**

Drei vor der Pause, zwei danach. Test 1 erst in Woche 4, aus dem
Grund, der oben unter *Format* steht. Test 3 liegt auf dem letzten
Labor vor der Pause, nicht auf dem ersten danach: ein Test am ersten
Tag nach dreieinhalb Wochen Pause wäre unfair, und vor der Pause hebt
ein Test zuverlässig die Anwesenheit.

### Regel

> Es gibt fünf Kurztests. Zur Prüfung zugelassen wird, wer mindestens
> drei besteht. Ein Test gilt als bestanden, wenn zwei der drei Fragen
> richtig sind. Nicht mitgeschriebene Tests gelten als nicht bestanden;
> Fehlzeiten werden nicht gesondert behandelt.

Keine Teilpunkte, keine Prozentrechnung. Der Tutor korrigiert das in
zehn Minuten, und jede und jeder weiß sofort, wo er steht. Zwei freie
Fehlversuche decken Krankheit ab; wer dreimal fehlt, ist ein echter
Härtefall und selten genug für eine Einzelfallentscheidung.

Die Regel muss in Woche 1 feststehen und danach unverändert bleiben.

### Was geprüft wird -- und was nicht

**Nicht Syntax.** Lemmanamen aus dem Kopf schreiben zu lassen ist genau
das, wofür `exact?` da ist. Wer das prüft, erzieht zum Falschen.

Geprüft werden Beweiszustände und Verständnis. Die Fragebank steht
schon: `Coursenotes/04-Appendix/Tactics/Cheatsheet.lean` ist exakt
dieses Format. Beispiele:

1. Beweiszustand `h : P ∧ Q`, Ziel `⊢ R`. Du schreibst
   `obtain ⟨hP, hQ⟩ := h`. Wie sieht der Zustand danach aus?
2. Ist `¬(P ∧ Q) → (¬P ∨ ¬Q)` konstruktiv beweisbar? Wenn nein: an
   welcher Stelle geht das ausgeschlossene Dritte ein?
3. Dieser Beweis scheitert mit „no binders to introduce". Warum?

Frage 2 in Variation ist die beste wöchentliche Frage: nicht
nachschlagbar, braucht genau das Verständnis, um das es geht, und
Blatt 01-g hat beigebracht, wie man die Antwort selbst nachprüft.

## Hausaufgaben und KI

**KI-Nutzung bei den Hausaufgaben ist erlaubt.** Das wird in Woche 1
ausdrücklich gesagt. Unklarheit ist schlimmer als Erlaubnis -- sonst
sitzen die Ehrlichen neun Stunden und die anderen zwei.

**Hausaufgaben sind unbenotet.** Einziges Kriterium: kompiliert, kein
`sorry`. Das ist ein Teilnahmesignal, mehr nicht.

Zwei Messungen stützen das, beide in `CLAUDE.md` dokumentiert.

**Erstens, KI.** Ein Lauf mit dem kleinsten verfügbaren Modell löste
**68 von 72 lösbaren Aufgaben auf Blatt 01 (94 %)**, in einem
Durchgang, ohne Lean-Feedback.

**Zweitens, und wichtiger: `grind`.** Die eingebaute Automatik von Lean
löst **127 von 128 Aussagen aller sieben Logikblätter** -- mit einem
Taktikaufruf ohne Argumente. Der einzige Fehlschlag ist `P → P → Q`,
also die Aussage, die absichtlich nicht gilt. `grind` schafft damit
100 % des Beweisbaren auf Blatt 01. Dafür braucht niemand ein
Sprachmodell; die Taktik steht im eigenen Appendix.

Eine korrekt abgegebene Hausaufgabe sagt also nichts über die
Studierenden aus, und das wäre auch ohne KI so. Das ehrlich zu nennen
ist besser, als Korrektheit zu benoten, die niemand verifizieren kann.

Eine Deklarationspflicht für unbenotete Hausaufgaben wäre Bürokratie
ohne Zweck. Für das Projekt gilt sie.

**Die unbeeinflussten Signale sind die Kurztests und die mündliche
Prüfung.** Wer einen Beweis nicht erklären kann, hat ihn nicht gemacht,
und das zeigt sich in fünf Minuten.

**Peer Review im Labor.** Jede Woche liest jemand den Beweis eines
anderen und sagt, was daran besser ginge. Fremden Code kritisch lesen
ist die Kernkompetenz, und es verlangt Verständnis, das man sich nicht
generieren lassen kann.

Aufgabentypen, die mit einem Modell im Raum weiter funktionieren, weil
ihr Ergebnis kein Beweis ist: „kürze diesen 20-Zeilen-Beweis", „warum
trifft `rw` hier diese Stelle und nicht jene", „welchen der drei
Beweise würdest du in Mathlib haben wollen und warum".

## Projekt (3 zusätzliche ECTS)

**Nach den 15 Wochen**, in der vorlesungsfreien Zeit. 90 h, also etwa
drei Wochen Vollzeit oder sechs Wochen halbtags. Die fünf Vorschläge in
`Coursenotes/05-Projects.lean` sind so geschnitten.

Vorteil der Verlagerung nach hinten: beide Gruppen sitzen 15 Wochen im
selben Kurs, nichts läuft parallel, und die Projektwahl fällt mit
vollem Überblick über den Stoff.

Vorher festzulegen:

- **Abgabetermin** -- sonst zieht sich das ins nächste Semester.
- **Verteidigungstermin** als Blocktag.
- **Deklarationspflicht für KI-Nutzung** -- das Projekt wird benotet.

## Organisation

**Tutor.** Mit zwei Leuten ist das Labor bis etwa 25 Teilnehmende
entspannt. Arbeitsteilung: der Tutor korrigiert die Kurztests (bei
Zustandsfragen rund 15 Minuten pro Woche), der Dozent schaut
stichprobenartig drüber. Im Labor geht einer herum, der andere sitzt
ansprechbar.

Der Tutor bekommt Zugriff auf **dieses** Repository, nicht nur auf
`leancourse_exercises`. In `Leancourse/Checks/` liegt ein
durchgerechneter Beweis zu jeder Aufgabe -- siehe
`Leancourse/Checks/README.md`.

**Studierende** brauchen nur
<https://github.com/pfaffelh/leancourse_exercises>.

## Offene Punkte

- Prüfungsordnung: Ist „3 von 5 Kurztests" als Studienleistung in der
  vorgesehenen Form zulässig?
- Raumbuchung Mo/Mi, Rechnerausstattung im Labor.
- `03-Functions_and_Sets/03-00-Quantifiers` und `03-01-Predicates` sind
  aus `01-Logic` hierher verschoben, aber noch im alten Stil und mit
  bekannten Fehlern (siehe `CLAUDE.md`). Vor Woche 6 überarbeiten.
- Abgabe- und Verteidigungstermin für die Projekte.
