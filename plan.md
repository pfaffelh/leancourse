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
| 3 | 02.11. | 04.11. | Typen, induktive Typen, Quotienten | 1.2 | L-d, 1.2-a, 1.1-b | |
| 4 | 09.11. | 11.11. | Terme und Pattern Matching | 1.3 | L-e, L-f, 1.1-c | **Test 1** |
| 5 | 16.11. | 18.11. | Typklassen | 1.4 | L-g, 1.4-a, 1.4-b · *extra:* X-a | |
| 6 | 23.11. | 25.11. | Curry-Howard | 1.5 | 1.5-a, 1.5-b | |
| 7 | 30.11. | 02.12. | Abhängige Typen und Notation | 1.6, 1.7 | 1.6-a, 1.7-a | **Test 2** |
| 8 | 07.12. | 09.12. | Mengen und Typen; Fundiertheit | 2.1, 2.3 | 2.1-a, 2.1-b, 2.1-c | |
| 9 | 14.12. | 16.12. | Universen und Axiome | 2.2 | 2.2-a, 2.3-a | **Test 3** |
| 10 | 21.12. | -- | Proof Engineering; `conv` | Anhang | A-a, A-b | |
| | | | *Pause 23.12. -- 06.01.* | | | |
| 11 | 11.01. | 13.01. | Ordnungen, algebraische Hierarchie | 2.4, 2.5 | 2.4-a, 2.5-a | |
| 12 | 18.01. | 20.01. | Filter | 2.6 | 2.6-a, 2.6-b | |
| 13 | 25.01. | 27.01. | Topologie | 2.7 | 2.7-a | **Test 4** |
| 14 | 01.02. | 03.02. | Maßtheorie | 2.8 | 2.8-a | |
| 15 | 08.02. | 10.02. | Monaden und Wahrscheinlichkeit | 2.9 | 2.9-a, 2.9-b | **Test 5** |

32 Pflichtblätter, dazu `X-a` als Extrablatt in Woche 5. `A-a` und
`A-b` laufen als Ferienaufgabe über die Pause.

Drei Kapitelpaare teilen sich einen Termin: 1.6+1.7 (W7), 2.1+2.3
(W8), 2.4+2.5 (W11). Es sind die vier kürzesten Kapitel (1.7 5,8k,
2.1 8,1k, 2.3 8,6k, 2.5 8,9k Zeichen); jedes Paar bleibt unter 1.4
allein.

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

Kein Blatt läuft vor seinem Kapitel. Der Logikblock `L-b` bis `L-g`
läuft in den Wochen 2 bis 5 und damit vor seiner Theorie (1.5 und
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

Kapitel 1.2 und 1.3. Pattern Matching und Rekursoren stehen auf
`1.1-a` und `1.1-b`, die Universen auf `1.6-a`. Strukturen,
Quotiententypen und eigene induktive Typen werden gelesen, nicht
geübt.

Gelöscht: das frühere `04-a-Basics` (Inhalt liegt auf `1.1-a`,
`1.1-b`, `2.9-a`).

`2.3-a` liegt in Woche 9, nicht 8: Teile 3 und 4 sind Kapitel 2.2.
`1.7-a` hat nur eine Aufgabe und ist eher ein Leseblatt.

## Kurztests

Fünf Tests, jeweils zu Beginn des Labors, 10 Minuten, auf Papier.
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
- `1.2-a-Quantifiers` und `1.5-a-Predicates` sind noch im alten Stil
  und mit bekannten Fehlern (siehe `CLAUDE.md`). `1.2-a` vor dem
  02.11. überarbeiten, `1.5-a` bis Woche 6.
- Foliensätze fehlen für die Wochen 8 bis 15; der Filtersatz hat erst
  neun Folien.
- Zeugen fehlen für die acht Mathlib-Blätter der Wochen 10 bis 15.
- Abgabe- und Verteidigungstermin für die Projekte.
