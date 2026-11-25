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
| Prüfung | mündlich (Fragenkatalog in `~/bwSyncShare/leancourse/exam.md`) |
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
| 3 | 02.11. | 04.11. | Universen, Funktionen, induktive Typen, Strukturen | 1.2 | L-d, 1.2-a, 1.1-b | |
| 4 | 09.11. | 11.11. | Pattern Matching und Rekursion | 1.3 | L-f, 1.1-c | **Test 1** |
| 5 | 16.11. | 18.11. | Σ, Subtypen, Typfamilien, Quotienten | 1.4 | L-e, L-g, 1.2-b · *extra:* X-a | |
| 6 | 23.11. | 25.11. | Regeln zum Bau von Typen, `Prop` | 1.5 | 1.3-a, 1.4-b | |
| 7 | 30.11. | 02.12. | Typklassen: Instanzen, Suche, `Decidable`, `classical` | 1.6 | 1.4-a, 1.4-c, 1.5-a | **Test 2** |
| 8 | 07.12. | 09.12. | Funktoren und Monaden, Koerzionen, Hierarchien | 1.7 | 1.6-a, 1.6-b | |
| 9 | 14.12. | 16.12. | Notation | 1.8 | 1.7-a, 1.7-b | **Test 3** |
| 10 | 21.12. | -- | Zahlen | 2.1 | 1.8-a, 2.0-a, 2.1-a | |
| | | | *Pause 23.12. -- 06.01.* | | | |
| 11 | 11.01. | 13.01. | Mengen und Typen | 2.2 | 2.2-a, 2.2-b, 2.2-c | |
| 12 | 18.01. | 20.01. | Grundlagen: Universen, Axiome, Fundiertheit | 2.3 | 2.3-a, 2.3-b, A-a, A-b | |
| 13 | 25.01. | 27.01. | Ordnungen, algebraische Hierarchie | 2.4, 2.5 | 2.4-a, 2.5-a | **Test 4** |
| 14 | 01.02. | 03.02. | Filter | 2.6 | 2.6-a, 2.6-b | |
| 15 | 08.02. | 10.02. | Monaden und Wahrscheinlichkeit | 2.8 | 2.8-a, 2.8-b | **Test 5** |

37 Pflichtblätter, dazu die Extrablätter `X-a` (Woche 5) und `2.7-a`
(Topologie, ohne Vorlesung). Über die Pause laufen `1.8-a`, `2.0-a`
und `2.1-a`.

Seit dem 24.11.2026 (Variante C): Proof Engineering hat keine Vorlesung
mehr, `A-a` und `A-b` laufen als Blätter in W12 (nicht früher: `A-a`
benutzt Mengen aus 2.2, und `2.6-a` braucht `field_simp` aus
`A-a`). Topologie (2.7) ist Lesestoff,
kein späteres Kapitel hängt daran. Die zwei freien Termine gehen an
Notation (1.8, durch die Notationstabelle gewachsen) und an die
Trennung von 2.1 und 2.2, die je eine eigene Vorlesung und ein
eigenes Deck bekommen. Es bleibt kein Puffer.

Seit dem 24.11.2026 ist das frühere Typklassenkapitel in zwei Kapitel
geteilt, eins pro Vorlesung: 1.6 *Typeclasses* (bis `Decidable` und
`classical`, Deck `1-6-typeclasses`) und 1.7 *Functors, monads,
coercions, hierarchies* (Deck `1-7-functors-monads`). Notation ist
damit 1.8. Blätter umbenannt: `1.6-d` (Trool) -> `1.6-b`, `1.6-c`
(Monaden) -> `1.7-a`, `1.6-b` (Koerzionen) -> `1.7-b`, `1.7-a`
(Notation) -> `1.8-a`.
Davor, seit dem 30.10.2026, bekamen die Typklassen (1.6) zwei Vorlesungen:
W7 Instanzen, Instanzsuche, `Decidable` und die Taktik `classical`;
W8 Klassen über Typkonstruktoren (`Functor`, `Monad` mit `Option` und
`List`, die Gesetze), Koerzionen mit `DFunLike`, `extends` und
Hierarchien, dazu Notation (1.7). Die Monaden kehren in 2.2 (Bild als
`map`), 2.6 (`Filter.map`) und 2.8 (`PMF`) als Rückverweis wieder;
`IO`, `StateM` und `Except` sind aus 2.8 gestrichen. Dafür entfällt
die Vorlesung zur Maßtheorie. Alles ab W8 rückt eine Woche nach.
Seit dem 24.11.2026 ist das Kapitel Maßtheorie mitsamt Extrablatt
gestrichen; Wahrscheinlichkeit ist jetzt Kapitel 2.8 (`2.8-a`,
`2.8-b`, vorher `2.9-a`, `2.9-b`).

Ein Kapitelpaar teilt sich einen Termin: 2.4+2.5 (W13). Notation (1.8)
hat seit dem 24.11.2026 eine eigene Vorlesung (W9). Seit dem 27.10.2026 gibt
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
alle späteren Kapitel von Teil 1 rücken eine Woche nach. Die Blätter
der Wochen 4 bis 6 sind danach so verteilt, dass keine Übung mehr als
rund 50 Aufgaben hat (W4 vorher 54 plus Test 1, W5 vorher 70): `1.3-a`
läuft in W5, `1.4-a`/`1.4-b` in W6, `1.4-c` in W7.

Am 11.11.2026 war die Übung mit Test 1 und drei Blättern zu voll.
Seitdem: `L-e` in W5 (vor `L-g`), `1.3-a` in W6, `1.4-a` in W7. `1.4-b` bleibt in W6, weil
`1.5-a` `fun` von dort voraussetzt; `1.4-a` braucht vor W8 niemand.
Übungen mit Test sollen höchstens zwei längere Blätter haben.
Am 25.11.2026 waren W6 (74 Aufgaben), W12 (66) und W13 (65 mit Test 4)
zu voll. Seitdem rücken die Blätter ab W6 bis zur Pause je eine Woche
nach: `1.5-a` in W7, `1.6-a` in W8, `1.7-a`/`1.7-b` in W9, `1.8-a` und
`2.0-a` über die Pause. Die Blätter zu 1.5 bis 1.8 laufen damit eine
Woche nach ihrer Vorlesung. `1.4-a` ist auf rund 10 Aufgaben neu geschrieben; gekürzt
sind `A-a` (Teile B und C, Wiederholungen von `1.7-b`, `2.0-a`,
`2.2-b`), `2.4-a` (Aufgaben 1–13 und 27), `2.5-a` (Aufgaben 1–5, 10,
12, 13) und `2.8-b` (die Monadengesetze, die `2.8-a` schon übt).
`1.3-a` und `1.4-b` blieben unverändert (schon ausgegeben).
Am 15.11.2026 fiel `L-g` Aufgabe 5 (`itauto` gegen `tauto`) weg, das
vorgerechnete Beispiel bleibt. Ebenso der Schlussteil *Searching
outside Lean* mit zwei Aufgaben (`#loogle`/`#search` kommen schon auf
`1.1-c`). Der Anfang übt nur noch `apply?` (`exact?` ist von `1.1-c`), `L-g` hat
jetzt 8 Aufgaben. `1.2-b` verliert Teil 3 (`ZMod`, eine Aufgabe; die
Idee steht als `sevenMod` in 1.2).

Skriptzeilen je Termin (Stand 29.10.2026): Mittel 474, Spanne 330
(W2) bis 768 (damals W15, seitdem um `IO`/`StateM`/`Except` gekürzt).
Die schwerste Übungswoche war W13 (65 Aufgaben, `2.4-a` allein 37,
dazu Test 4); am 25.11.2026 gekürzt, siehe oben.

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
2.3).

Die Logik ist nach Woche 5 abgeschlossen.

### Anhang (ohne Vorlesung, Blätter in W12)

Gelesen werden die Abschnitte, die `A-a` verlangt:

| Teil von `A-a` | Thema | Abschnitt |
|---|---|---|
| A, C, D | Welche Automatiktaktik? | *Tactics* |
| B | Kaputte Beweise | *Common Pitfalls* |
| `A-b` | `conv` | *Tactics/Conv* |

*File Structure* und *Small Reference Topics* bleiben draußen.

### Ohne eigenes Blatt

Seit dem 27.10.2026 hat jedes Kapitel von Teil 1 ein Blatt. Eigene
induktive Typen, Mustervergleich und `termination_by` stehen auf
`1.3-a` (dazu der Rekursor eines eigenen Typs), Strukturen mit
`extends` und `Fin` auf `1.2-b`, induktive Prädikate und ein
Quotient (ℤ aus ℕ × ℕ) auf `1.4-c`, Termmodus und Junktoren auf
`1.4-b`. Kapitel 1.5 hat `1.5-a` (Universen, Konversion mit `change`,
Beweisirrelevanz und eingeschränkte Elimination, `ext`/`funext`,
`propext`, `Classical.choose` gegen `Nat.find`, `choose`,
`Nonempty`). Die Regeln als Brüche und `imax` werden gelesen,
nicht geübt.

Gelöscht: das frühere `04-a-Basics` (Inhalt liegt auf `1.1-a`,
`1.1-b`, `1.7-a`). `1.7-a` (Funktoren und Monaden) übernimmt die
`Option`- und Listen-Aufgaben des alten `2.9-a`; das Blatt (heute
`2.8-a`) ist jetzt
*Monads in mathematics* (`Set`, `Finset`, `Filter`).

Seit dem 30.10.2026 beginnt Teil 2 mit dem Kapitel 2.1 *Numbers*
(Zahlbereiche als Typbildner aus Teil 1, Müllwerte, drei Potenzen,
`ℝ≥0`/`ℝ≥0∞`, Casts) und dem Blatt `2.1-a`. Damit Teil 2 bei neun
Kapiteln bleibt, sind die früheren 2.2 (Universen und Axiome) und 2.3
(Fundiertheit) zu 2.3 *Foundations* zusammengelegt; Mengen ist jetzt
2.2. Blätter: `2.1-a/b/c` -> `2.2-a/b/c`, `2.2-a` -> `2.3-a`,
`2.3-a` -> `2.3-b`. Seit dem 24.11.2026 hat 2.2 eine eigene
Vorlesung (W11), alle drei Blätter zu 2.2 laufen dort.
Beweisirrelevanz steht auf `2.3-a`.
`1.8-a` hat 19 Aufgaben (Stand 24.11.2026), die meisten sind Notationsdeklarationen zum Auskommentieren.

## Kurztests

Fünf Tests, jeweils zu Beginn des Labors, 20 Minuten, auf Papier.
Termine: **11.11., 02.12., 16.12., 27.01., 10.02.**

> Es gibt fünf Kurztests. Zur Prüfung zugelassen wird, wer mindestens
> drei besteht. Ein Test hat sechs Aufgaben und gilt als bestanden,
> wenn drei davon richtig sind. Nicht mitgeschriebene Tests gelten als nicht bestanden;
> Fehlzeiten werden nicht gesondert behandelt.

Keine Teilpunkte. Die Regel steht ab Woche 1 fest.

Geprüft werden Beweiszustände und Verständnis, keine Lemmanamen und
keine Syntax. Aufgabentypen: Beweiszustand nach einer Taktik,
Multiple Choice, Antwort mit einem Wort oder Satz. Die Tests liegen
in `~/bwSyncShare/leancourse/tests/` (außerhalb des Repos), Test 1 vom 29.10.
mit Lösungsschlüssel.

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
- Foliensätze für Teil 2 stehen, je einer pro Vorlesung (W10-W15),
  dazu einer für Topologie (Lesestoff).
- Abgabe- und Verteidigungstermin für die Projekte.
