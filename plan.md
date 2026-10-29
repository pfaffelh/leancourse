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
| Workload | 180 h, davon 43,5 h Kontaktzeit; rund 9 h/Woche Eigenarbeit |

15 Vorlesungen, 14 Labore: die Pause frisst drei Mittwoche (23.12.,
30.12., 06.01.), aber nur zwei Montage (28.12., 04.01.). Der Montag
21.12. hat kein Labor. Allerheiligen (01.11.) fällt auf einen Sonntag.

Mi 21.10. ist Installationstermin (VS Code, Lean-Erweiterung,
`git clone`, `lake exe cache get`). Mo 19.10. ist Organisation und
Kontext, ohne Lean.

## Wochenplan

| W | Mo | Mi | Vorlesung | Kapitel | Blätter | |
|---|---|---|---|---|---|---|
| 1 | 19.10. | 21.10. | Warum formalisieren? · *Mi: Installation* | Einleitung | L-a | |
| 2 | 26.10. | 28.10. | `Nat`, `Bool`, Reduktionsregeln | 1.1 | L-b, L-c, 1.1-a | |
| 3 | 02.11. | 04.11. | Typen und Terme I: Universen, Funktionen, induktive Typen, Strukturen | 1.2 | L-d, 1.2-a, 1.1-b | |
| 4 | 09.11. | 11.11. | Pattern Matching und Rekursion | 1.3 | L-e, L-f, 1.1-c, 1.3-a | **Test 1** |
| 5 | 16.11. | 18.11. | Typen und Terme II: Σ, Subtypen, Typfamilien, Quotienten | 1.4 | L-g, 1.2-b, 1.4-a, 1.4-b · *extra:* X-a | |
| 6 | 23.11. | 25.11. | Typen III: die Regeln, `Prop` | 1.5 | 1.4-c, 1.5-a | |
| 7 | 30.11. | 02.12. | Typklassen; Notation | 1.6, 1.7 | 1.6-a, 1.6-b, 1.7-a | **Test 2** |
| 8 | 07.12. | 09.12. | Mengen und Typen; Fundiertheit | 2.1, 2.3 | 2.0-a, 2.1-a, 2.1-b | |
| 9 | 14.12. | 16.12. | Universen und Axiome | 2.2 | 2.1-c, 2.2-a, 2.3-a | **Test 3** |
| 10 | 21.12. | -- | Proof Engineering; `conv` | Anhang | A-a, A-b | |
| | | | *Pause 23.12. -- 06.01.* | | | |
| 11 | 11.01. | 13.01. | Ordnungen, algebraische Hierarchie | 2.4, 2.5 | 2.4-a, 2.5-a | |
| 12 | 18.01. | 20.01. | Filter | 2.6 | 2.6-a, 2.6-b | |
| 13 | 25.01. | 27.01. | Topologie | 2.7 | 2.7-a | **Test 4** |
| 14 | 01.02. | 03.02. | Maßtheorie | 2.8 | 2.8-a | |
| 15 | 08.02. | 10.02. | Monaden und Wahrscheinlichkeit | 2.9 | 2.9-a, 2.9-b | **Test 5** |

36 Pflichtblätter, dazu `X-a` als Extrablatt in Woche 5. `A-a` und
`A-b` laufen als Ferienaufgabe über die Pause.

Drei Kapitelpaare teilen sich einen Termin: 1.6+1.7 (W7), 2.1+2.3
(W8), 2.4+2.5 (W11). Notation (1.7) bekommt keine eigene Vorlesung:
eigene Notation führen Studierende kaum ein. Seit dem 27.10.2026 gibt
es kein eigenes Kapitel *Terme* mehr: 1.2 *Typen und Terme I*
(Universen, Funktionen, induktive Typen, Strukturen) und 1.4 *Typen
und Terme II* (Σ, Subtypen, Typfamilien, indizierte Familien,
Junktoren als Typen, Quotienten) beschreiben jeden Typbildner in vier
Schritten (Formation, Konstruktion, Benutzung, Berechnung); 1.5
*Typen III* gibt die Regeln dahinter, `imax` und `Prop`. Seit
demselben Tag gibt es auch kein eigenes Kapitel *Curry-Howard* mehr:
die Junktoren als Typen und Taktik-/Termmodus stehen in 1.4
(*Propositions as types*), `Nonempty` und `Classical.choice` in 1.5.

Seit dem 29.10.2026 ist *Pattern Matching und Rekursion* ein eigenes
Kapitel 1.3 (vorher der letzte Teil von 1.2, der damit auf 922
Skriptzeilen kam). Es nimmt die Vorlesung, die am 30.11. frei war;
alle späteren Kapitel von Teil 1 rücken eine Woche nach.

Skriptzeilen je Termin: Mittel 474, Spanne 330 (W2) bis 768 (W15).
Woche 11 ist zugleich die schwerste Übungswoche (67 Aufgaben, `2.4-a`
allein 38). Wenn gekürzt werden muss, dann in W11 und W15.

Wenn drei Blätter zu viel sind, rutscht `1.1-b`.

### Benennung

Ein Blatt heißt nach seinem Kapitel: `1.1-a` bis `1.1-c` zu Kapitel
1.1, `2.6-a` und `2.6-b` zu den Filtern. Dateien entsprechend,
`Exercises/1-Lean/1-a-NatRec.lean`,
`Exercises/2-Mathematics/6-b-Filters.lean`. `L-a` bis `L-g` ist der
Logikblock ohne Kapitel, `A-a`/`A-b` der Anhang, `X-a` das Extrablatt.
`2.0-a` (Suchen in Mathlib: `exact?`, `rw?`, `apply?`, Namen,
`#loogle`) eröffnet den Mathematikteil und hat kein Kapitel; der
Abschnitt *Finding theorems* in 1.2 ist dafür am 29.10. entfallen.

Kein Blatt läuft vor seinem Kapitel. Der Logikblock `L-b` bis `L-g`
läuft in den Wochen 2 bis 5 und damit vor seiner Theorie (1.4 und
2.2).

Die Logik ist nach Woche 5 abgeschlossen.

### Woche 10 (21.12.), Anhang

Vorgetragen werden die Abschnitte, die `A-a` verlangt:

| Teil von `A-a` | Thema | Abschnitt |
|---|---|---|
| A, E | Welche Automatiktaktik? | *Tactics* |
| B | Das richtige Lemma finden | *Navigating Mathlib* |
| C, D | Koerzionen, kaputte Beweise | *Common Pitfalls* |
| `A-b` | `conv` | *Tactics/Conv* |

*File Structure* und *Small Reference Topics* bleiben draußen.

### Ohne eigenes Blatt

Seit dem 27.10.2026 hat jedes Kapitel von Teil 1 ein Blatt. Eigene
induktive Typen, Mustervergleich und `termination_by` stehen auf
`1.3-a` (dazu der Rekursor eines eigenen Typs), Strukturen mit
`extends`, `Fin` und `ZMod` auf `1.2-b`, induktive Prädikate und ein
Quotient (ℤ aus ℕ × ℕ) auf `1.4-c`, Termmodus und Junktoren auf
`1.4-b`. Kapitel 1.5 hat `1.5-a` (Gleichheit, `ext`, `choose`,
`change`). Die Regeln selbst, `imax` und die eingeschränkte
Elimination werden gelesen, nicht geübt; die Universen stehen auf
`1.4-a`.

Gelöscht: das frühere `04-a-Basics` (Inhalt liegt auf `1.1-a`,
`1.1-b`, `2.9-a`).

`2.1-c` und `2.3-a` (Kapitel 2.1 und 2.3, gelesen in Woche 8)
liegen in Woche 9, damit Woche 8 nicht vier Blätter hat. Beweisirrelevanz steht seit 29.10.
auf `2.2-a`.
`1.7-a` hat nur eine Aufgabe und ist eher ein Leseblatt.

## Kurztests

Fünf Tests, jeweils zu Beginn des Labors, 20 Minuten, auf Papier.
Termine: **11.11., 02.12., 16.12., 27.01., 10.02.**

> Es gibt fünf Kurztests. Zur Prüfung zugelassen wird, wer mindestens
> drei besteht. Ein Test gilt als bestanden, wenn zwei der drei Fragen
> richtig sind. Nicht mitgeschriebene Tests gelten als nicht bestanden;
> Fehlzeiten werden nicht gesondert behandelt.

Keine Teilpunkte. Die Regel steht ab Woche 1 fest.

Geprüft werden Beweiszustände und Verständnis, keine Lemmanamen und
keine Syntax. Format und Fragebank:
`Coursenotes/4-Appendix/Tactics/Cheatsheet.lean`.

## Hausaufgaben und KI

KI-Nutzung ist erlaubt, wird in Woche 1 gesagt. Hausaufgaben sind
unbenotet; einziges Kriterium ist: kompiliert, kein `sorry`. Keine
Deklarationspflicht. Für das Projekt gilt sie.

Zwei Messungen (dokumentiert in `CLAUDE.md`):

- Das kleinste verfügbare Modell löste 68 von 72 lösbaren `sorry`s des
  Logikblocks (94 %), in einem Durchgang, ohne Lean-Feedback.
- `grind` löst 127 von 128 Aussagen des Logikblocks mit einem Aufruf
  ohne Argumente. Der einzige Fehlschlag ist `P → P → Q` auf `L-a`,
  die absichtlich falsche Aussage.

Im Labor jede Woche Peer Review: eine Person liest den Beweis einer
anderen.

## Projekt (3 zusätzliche ECTS)

Nach den 15 Wochen, in der vorlesungsfreien Zeit. 90 h. Fünf
Vorschläge in `Coursenotes/3-Projects.lean`. Benotet, mit
Deklarationspflicht für KI-Nutzung.

Festzulegen: Abgabetermin, Verteidigungstermin als Blocktag.

## Organisation

Der Tutor korrigiert die Kurztests (rund 15 min/Woche) und braucht
Zugriff auf **dieses** Repository, nicht nur auf
`leancourse_exercises`. Zu jeder Aufgabe liegt ein durchgerechneter
Beweis in `Leancourse/Checks/`, siehe `Leancourse/Checks/README.md`.

Studierende brauchen nur
<https://github.com/pfaffelh/leancourse_exercises>.

## Offene Punkte

- Prüfungsordnung: Ist „3 von 5 Kurztests" als Studienleistung
  zulässig?
- Raumbuchung Mo/Mi, Rechnerausstattung im Labor.
- Foliensätze fehlen für die Wochen 8 bis 15; der Filtersatz hat erst
  neun Folien.
- Abgabe- und Verteidigungstermin für die Projekte.
