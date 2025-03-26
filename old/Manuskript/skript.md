::: titlepage
[Schulmathematik mit dem]{.smallcaps}

![image](lean_logo2){width="50%"}

Peter Pfaffelhuber

Sommersemester 2023

![image](UFR-vorlage-designsystem-typo-farben-V1.92.png){width="50%"}

2025-03-26
:::

# Vorbereitung zur Nutzung des Skriptes {#S:vorbereitung}

Dies sind die Notizen zu einem Kurs zum formalen Beweisen mit dem
interaktiven Theorem-Prover Lean3 (im folgenden schreiben wir nur Lean)
im Sommersemester 2023 an der Universität Freiburg. Um den Kurs sinnvoll
durcharbeiten zu können, sind folgende technische Vorbereitungen zu
treffen:

1.  Lokale Installation von Lean und der dazugehörigen Tools: Folgen Sie
    bitte den Hinweisen auf
    <https://leanprover-community.github.io/get_started.html>.

2.  Installation von `vscode`. Bitte befolgen Sie die Download-Hinweise
    auf <https://code.visualstudio.com/download>.

3.  Installation des Repositories des Kurses: Navigieren Sie zu einem
    Ort, wo Sie die Kursunterlagen ablegen möchten und verwenden Sie\
    `leanproject get https://github.com/pfaffelh/schulmathematik_mit_lean`{.Lean}\
    Dies sollte die Kursunterlagen herunterladen. Anschließend finden
    Sie das Manuskript unter `Manuskript/skript.pdf`, und Sie können die
    Übungen mit `code schulmathematik_mit_lean`{.Lean} öffnen. Die
    Übungen befinden sich dabei in `src`. Wir empfehlen, dieses
    Verzeichnis zunächst zu kopieren, etwa nach `mysrc`. Andernfalls
    kann es sein, dass durch ein Update des Repositories die lokalen
    Dateien überschrieben werden. Um die Kursunterlagen auf den neuesten
    Stand zu bringen, geben Sie `git pull` im Verzeichnis
    `schulmathematik_mit_lean`{.Lean} ein.

# Einleitung

Der Kurs hat einen Fokus auf das Lehramts-Studium Mathematik an
Gymnasien und hat mindestens zwei Ziele:

-   Erlernen der Techniken zum interaktiven, formalen Beweisen mit Hilfe
    der funktionalen Programmiersprache Lean: In den letzten Jahren
    haben in der Mathematik Bemühungen drastisch zugenommen,
    computergestützte Beweise zu führen. Während vor ein paar
    Jahrzehnten eher das konsequente Abarbeiten vieler Fälle dem
    Computer überlassen wurde, sind interaktive Theorem-Prover anders.
    Hier kann ein sehr kleiner Kern dazu verwendet werden, alle
    logischen Schlüsse eines mathematischen Beweises nachzuvollziehen
    oder interaktiv zu generieren. Der Computer berichtet dann
    interaktiv über den Fortschritt im Beweis und wann alle Schritte
    vollzogen wurden.

-   Herstellung von Verbindungen zur Schulmathematik: Manchmal geht im
    Mathematik-Studium der Bezug zur Schulmathematik verloren. Dieser
    Kurs ist der Versuch, diesen einerseits wieder herzustellen, und auf
    dem Weg ein tieferes Verständnis für die bereits verinnerlichte
    Mathematik zu bekommen. Um einem Computer zu *erklären*, wie ein
    Beweis (oder eine Rechnung oder ein anderweitiges Argument)
    funktioniert, muss man ihn erstmal selbst sehr gut verstanden haben.
    Außerdem muss man den Beweis -- zumindest wenn er ein paar Zeilen
    übersteigt -- gut planen, damit die eingegebenen Befehle (die wir
    Taktiken nennen werden) zusammenpassen.

### Formalisierung in der Mathematik {#formalisierung-in-der-mathematik .unnumbered}

Obwohl Mathematik den Anspruch hat, sauber zu argumentieren, finden sich
in mathematischen Veröffentlichungen Fehler. Oftmals sind diese nicht
entscheidend für die Richtigkeit der Aussage, die zu beweisen war.
Manchmal wird eine Voraussetzung vergessen, und manchmal gibt es auch
echte Fehler. Stellt ein Theorem Prover die Richtigkeit eines Beweises
fest, so ist die Glaubwürdigkeit deutlich größer. Zwar muss man sich
immer noch auf die Fehlerfreiheit des Kerns (also etwa 10000 Zeilen
Code) der Programmiersprache verlassen, sonst jedoch nur noch darauf,
dass man die zu beweisende Aussage auch versteht und richtig
interpretiert.

Heute wächst die Anzahl an Aussagen, die formal bewiesen werden, immer
noch deutlich langsamer als die Anzahl an Veröffentlichungen in der
Mathematik. Andererseits gibt es mittlerweile eine Community des
formalen Beweisens, die von der Zukunftsfähigkeit von Theorem Provers
überzeugt ist.

### Interactive Theorem Prover {#interactive-theorem-prover .unnumbered}

Mittlerweile gibt es einige Theorem Prover. Wir werden hier Lean (von
Microsoft Research) verwenden. Grund für diese Wahl ist vor allem, dass
es hier die größte Anzahl an Mathematikern gibt, die die
`mathlib`{.Lean}, also die mathematische Bibliothek, die auf formal
bewiesenen Aussagen mit dem Theorem Prover besteht, weiterentwickeln.

Momentan steht der Wechsel von Lean3 zu Lean4 an. Da insbesondere noch
nicht die gesamte `mathlib`{.Lean} in Lean4 zur Verfügung steht, werden
wir Lean3 verwenden.

### Zum Inhalt {#zum-inhalt .unnumbered}

Dieses Manuskript gliedert sich in drei Abschnitte. In
Kapitel [3](#S:mathe){reference-type="ref" reference="S:mathe"} werden
wir die Mathematik besprechen, die wir in den Übungen formal beweisen
werden. Dies wird mit einfachen logischen Schlüssen anfangen, und am
Ende werden einige Aussagen der Schulmathematik formal bewiesen. Dieser
Teil ist der einzige Teil, den man von vorne nach hinten entlang der
Übungsaufgaben abarbeiten sollte.
Kapitel [4](#S:lean){reference-type="ref" reference="S:lean"} gibt
nützliche Hinweise zu Lean und `vscode`{.Lean}, von der Installation,
über die Syntax, bis hin zu verwendetetn Gleichheitsbegriffen. Im
Kapitel [5](#S:tactics){reference-type="ref" reference="S:tactics"}
werden wir alle verwendeten Befehle (also die *Taktiken*) besprechen.
Diese werden hier als Nachschlagewerk zur Verfügung gestellt, wobei in
den Übungen jeweils darauf verwiesen wird, welche neuen Taktiken gerade
zu erlernen sind.

# Mathematik {#S:mathe}

## Logik

Wir beginnen mit einfachen logischen Aussagen. Wir unterscheiden immer
(wie auch in jedem mathematischen Theorem) zwischen den Hypothesen und
der Aussage. Um unsere Hypothesen einzuführen, führen wir sie in allen
`lean`{.Lean}-Dateien auf einmal mit
`variables (P Q R S T: Prop)`{.Lean} ein. Für die Lean-Syntax bemerken
wir, dass hier kein üblicher Doppelpfeil $\Longrightarrow$ verwendet
wird, sondern ein einfacher `→`{.Lean}. Wir gehen hier folgende logische
Schlüsse durch:

-   Blatt 01-a:\
    Die Aussage `⊢ P → Q`{.Lean} (d.h. aus `P`{.Lean} folgt `Q`{.Lean})
    bedeutet ja, dass `Q`{.Lean} gilt, falls man annehmen darf, dass die
    Hypothese `P`{.Lean} richtig ist. Dieser Übergang von
    `⊢ P → Q`{.Lean} zur Hypothese `hP : P`{.Lean} mit Ziel `⊢ Q`{.Lean}
    erfolgt mittels `intro hP`{.Lean}. Mehrere `intro`{.Lean}-Befehle
    kann man mittels `intros h1 h2...`{.Lean} abkürzen.\
    Gilt die Hypothese `hP : P`{.Lean}, und wir wollen `⊢ P`{.Lean}
    beweisen, so müssen wir ja nur `hP`{.Lean} auf das Ziel anwenden.
    Ist Ziel und Hypothese identisch, so geschieht dies mit
    `exact hP`{.Lean}. Etwas allgemeiner sucht `assumption`{.Lean} alle
    Hypothesen danach durch, ob sie mit dem Ziel definitorisch gleich
    sind.

-   Blatt 01-b:\
    Will man `⊢ Q`{.Lean} beweisen, und weiß, dass `hPQ : P → Q`{.Lean}
    gilt, so genügt es, `⊢ P`{.Lean} zu beweisen (da mit `hPQ`{.Lean}
    daraus dann `⊢ Q`{.Lean} folgt). Mit `apply hPQ`{.Lean} wird in
    diesem Fall das Ziel nach `⊢ P`{.Lean} geändert.\
    Hinter einer Äquivalenz-Aussage `⊢ P ↔ Q`{.Lean} stehen eigentlich
    die beiden Aussagen `⊢ P → Q`{.Lean} und `⊢ Q → P`{.Lean}. Mittels
    `split`{.Lean} wandelt man das Ziel `⊢ P ↔ Q`{.Lean} in zwei Ziele
    für die beiden Richtungen um.\
    Die logische Verneinung wird in Lean mit `¬`{.Lean} notiert. Die
    Aussage `¬P`{.Lean} ist dabei definitorisch gleich
    `P → false`{.Lean}, wobei `false`{.Lean} für eine falsche Aussage
    steht.

-   Blatt 01-c: Aus falschem folgt Beliebiges ist eigentlich die Aussage
    `⊢ false → P`{.Lean}. Ist das aktuelle Ziel `⊢ P`{.Lean}, und wendet
    man die Aussage `⊢ false → P`{.Lean} mittels `apply`{.Lean} an, so
    ist das äquivalent zur Anwendung von `exfalso`{.Lean}.\
    Die beiden Ausdrücke `false`{.Lean} und `true`{.Lean} stehen für
    zwei Aussagen, die falsch bzw. wahr sind. Also sollte `true`{.Lean}
    leicht beweisbar sein. Dies liefert die Taktik `triv`{.Lean}.\
    Bei einem Beweis durch Widerspruch beweist man statt `⊢ P`{.Lean}
    die Aussage `⊢ ¬P → false`{.Lean} (was nach `intro h`{.Lean} zur
    Annahme `h : ¬P`{.Lean} und dem neuen Ziel `⊢ false`{.Lean} führt).
    Dies ist logisch korrekt, da `P`{.Lean} genau dann wahr ist, wenn
    `¬P`{.Lean} auf einen Widerspruch, also eine falsche Aussage, führt.
    Die Umwandlung des Goals auf diese Art und Weise erreicht man mit
    der Taktik `by_contra`{.Lean} bzw. `by_contra h`{.Lean}.

-   Blatt 01-d:\
    Für *und*- bzw. *oder*-Verknüpfungen von Aussagen stellt Lean die
    üblichen Bezeichnungen `∧`{.Lean} bzw. `∨`{.Lean} zur Verfügung. Mit
    diesen Verbindungen verknüpfte Aussagen können sowohl in einer
    Hypothese als auch im Ziel vorkommen. Nun gibt es folgende vier
    Fälle:\
    `⊢ P ∧ Q`{.Lean} Hier müssen also die beiden Aussagen `P`{.Lean} und
    `Q`{.Lean} bewiesen werden. Mit `split`{.Lean} werden genau diese
    beiden Ziele (mit denselben Voraussetzungen) erzeugt, also
    `⊢ P`{.Lean} und `⊢ Q`{.Lean}. Sind diese beiden nämlich gezeigt,
    ist offebar auch `⊢ P ∧ Q`{.Lean} gezeigt.\
    `⊢ P ∨ Q`{.Lean} Um dies zu zeigen, genügt es ja, entweder
    `P`{.Lean} zu zeigen, oder `Q`{.Lean} zu zeigen. Im ersten Fall wird
    mit `left`{.Lean} das Ziel durch `⊢ P`{.Lean} ersetzt, mit
    `right`{.Lean} wird das Ziel mit `⊢ Q`{.Lean}. `h : P ∧ Q`{.Lean}
    Offenbar zerfällt die Hypothese `h`{.Lean} in zwei Hypothesen, die
    beide gelten müssen. Mittels `cases h with hP hQ`{.Lean} wird aus
    `h : P ∧ Q `{.Lean} zwei Hypothesen generiert, nämlich
    `hP : P`{.Lean} und leanstatehQ : Q.\
    `h : P ∨ Q`{.Lean} Ähnlich wie im letzten Fall erzeugt
    `cases h with hP hQ`{.Lean} nun zwei neue Goals, nämlich eines bei
    dem `h : P ∨ Q`{.Lean} durch `hP : P`{.Lean} ersetzt wurde, und
    eines bei dem `h : P ∨ Q`{.Lean} durch `hQ : Q`{.Lean} ersetze
    wurde. Dies ist logisch in Ordnung, weil man ja so gerade die Fälle,
    bei denen `P`{.Lean} oder `Q`{.Lean} gelten, voneinander treffen
    kann.

-   Blatt 01-e:\
    Hier geht es um die Einführung neuer Hypothesen. Bei der
    `by_cases`{.Lean}-Taktik -- angewandt auf eine Hypothese
    `h : P`{.Lean} -- werden alle Möglichkeiten durchgegangen, die
    `P`{.Lean} annehmen kann. Diese sind, dass `P`{.Lean} entweder
    `true`{.Lean} oder `false`{.Lean} ist. Mit `by_cases h : P`{.Lean}
    werden also zwei neue Ziele eingeführt, eines mit der Hypothese
    `h : P`{.Lean} und eines mit der Hypothese `h : ¬P`{.Lean}.\
    Eine sehr allgemeine Taktik ist `have`{.Lean}. Hier können beliebige
    Hypothesen formuliert werden, die zunächst gezeigt werden müssen.

-   Blatt 01-f:\
    Nun kommen wir zu abkürzenden Schreibweisen. Zunächst führen wir die
    abkürzenden Schreibweise `⟨ hP, hQ, hR ⟩`{.Lean} für die
    `∧`{.Lean}-Verknüpfung der Aussagen `hP`{.Lean}, `hQ`{.Lean} und
    `hR`{.Lean}. (Dies funktioniert ebenfalls mit nur zwei oder mehr als
    drei Hypothesen). Analog ist `(hP | hQ)`{.Lean} eine Schreibweise
    für `hP ∨ hQ`{.Lean}. Diese beiden Schreibweisen können ebenso
    verschachtelt werden. Die drei Taktiken, die wir hier besprechen,
    sind `rintros`{.Lean} für `intros`{.Lean} $+$ `cases`{.Lean},
    `rcases`{.Lean} für eine flexiblere Version von `cases`{.Lean}, bei
    der man die gerade eingeführten Schreibweisen verwenden kann, und
    `obtain`{.Lean} für `intros`{.Lean} $+$ `have`{.Lean}.

-   Blatt 01-g: Quantoren\
    Quantoren wie $\forall$ und $\exists$ sind (zwar nicht aus der
    Schule, aber) seit dem ersten Semester bekannt. Diese können
    ebenfalls in `lean`{.Lean} auftreten. Wir unterscheiden dabei, ob
    diese Quantoren im Goal oder einer Hypothese auftreten. Es folgt
    eine kleine Tabelle, welche Taktiken sich jeweils anbieten. Genaue
    Erklärungen sind in `01-g.lean`{.Lean}.

    ::: center
      Quantor                 im Goal             in Hypothese `h : _`{.Lean}
      ----------------------- ------------------- -----------------------------
      `∀ (x : X), _`{.Lean}   `intro x,`{.Lean}   `apply h _,`{.Lean}
                                                  `specialize h _`{.Lean}
      `∃ (x : X), _`{.Lean}   `use _`{.Lean}      `cases h,`{.Lean}
    :::

-   Blatt 01-h:\
    Langsam aber sicher arbeiten wir uns zu Anwendungen mit *richtiger*
    Mathematik vor, aber ein paar Sachen fehlen noch. In diesem Blatt
    lernen wir, Gleichheiten mittels `refl`{.Lean} zu beweisen. Für das
    spätere Arbeiten mit `=`{.Lean}- oder `↔`{.Lean}-Aussagen ist
    `rw`{.Lean} sehr wichtig, weil man hier Sachen umschreiben kann,
    d.h. man kann propositionelle Gleichheiten verwenden. Da es in der
    `mathlib`{.Lean} sehr viele Aussagen bereits gibt, ist es gut, eine
    Art Suchfunktion zu haben. Diese wird durch `library_search`{.Lean}
    bzw. `suggest`{.Lean} bereitgestellt. Außerdem lernen wir,
    Funktionen zu definieren. Dies geschieht in `lean`{.Lean} mit der
    `λ`{.Lean}-Notation (übrigens genau wie an vielen Stellen in anderen
    Programmiersprachen, etwa `python`{.Lean}. Als Beispiel steht
    `λ x, 2*x`{.Lean} für die Funktion $x \mapsto 2x$. Hat man etwa
    `let f : X → X := λ x, 2*x`{.Lean}, so gibt `f 1`{.Lean} den
    Funktionswert bei `x = 1`{.Lean}.

## Natürliche Zahlen

Um etwas mathematischer zu werden, führen wir nun die natürlichen Zahlen
ein. Dieser Typ (abgekürzt `ℕ`{.Lean})ist so definiert (siehe
02-a.lean), dass `0 : ℕ`{.Lean} und `succ (n : ℕ) : ℕ`{.Lean}, d.h. mit
`n`{.Lean} ist auch `succ n`{.Lean} eine natürliche Zahl. Dabei steht
`succ n`{.Lean} für den Nachfolger von `n`{.Lean}. Weiter werden wir
hier die Typen `set ℕ`{.Lean} und `finset ℕ`{.Lean} kennenlernen. Dies
sind die Teilmengen von `ℕ`{.Lean} bzw. die endlichen Teilmengen von
`ℕ`{.Lean}.

-   Blatt 02-a: Natürliche Zahlen und der `calc`{.Lean}-Modus\
    Nach einer Einführung, wie die natürlichen Zahlen in `lean`{.Lean}
    implementiert sind, führen wir den `calc`{.Lean}-Modus ein. Dieser
    erlaubt es, schrittweise Rechnungen durchzuführen, und dabei vorher
    bereits bewiesene Aussagen zu verwenden. So können wir etwa
    binomische Formeln beweisen. Wir lernen außerdem die sehr mächtigen
    Taktiken `ring`{.Lean}, `norm_num`{.Lean}, `linarith`{.Lean} und
    `simp`{.Lean} kennen, die viel Arbeit erleichtern können. Hier
    lernen wir auch die `λ`{.Lean}-Notation zur Definition von
    Funktionen.

-   Blatt 02-b: Teilbarkeit\
    Für `m n : ℕ`{.Lean} (oder `m n : ℤ`{.Lean}) bedeutet
    `h : m | n`{.Lean}, dass `n`{.Lean} von leanstatem geteilt wird.
    Anders ausgedrückt gibt es `a : ℕ`{.Lean} mit `n = a * m`{.Lean}.
    Mit dieser Definition ist das Ziel dieses Blattes, die lange
    bekannte Aussage zu zeigen, dass eine Zahl genau dann durch 3
    (oder 9) teilbar ist, wenn ihre Quersumme durch 3 (oder 9) teilbar
    ist. Dies werden wir hier nur im begrenzten Zahlenraum bis $10000$
    durchführen.\
    **Bonusaufgabe:** Eine besonders einfache Methode, die
    Teilbarkeitsregel durch 3 in Lean zu beweisen, ist durch folgendes
    Lean-File (hier ist `\%`{.Lean} das modulo-Zeichen und
    `digits 10`{.Lean} ist die endliche Liste der Dezimaldarstellung der
    Zahl `n`{.Lean}):

    ``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
          import data.nat.digits
          open nat 
          example  (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum := 
          begin
          refine dvd_iff_dvd_digits_sum 3 10 _ n, 
          norm_num,
          end
    ```

    Dieser Beweis basiert auf folgender Aussage:

    ``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
          lemma dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
          b ∣ n ↔ b ∣ (digits b' n).sum 
    ```

    Geben Sie einen Skript-Beweis dieser Aussage.

-   Blatt 02-c: $\sqrt 2$\
    Hier geht es um den Beweis $\sqrt 2 \notin \mathbb Q$. Hier ist der
    Beweis, wie man ihn in einem Skript (oder Schulbuch) lesen würde:
    Angenommen, es gäbe $m$ und $n$ mit $\sqrt{2} = m/n$. Dann wäre
    $2n^2 = m^2$. OBdA seien $m$ und $n$ teilerfremd. Dann wäre also
    $2 ∣ m^2$. Da daher $m^2$ gerade ist, muss $m$ ebenfalls gerade
    sein, also $m = 2*a$ für ein $a$. Damit wäre $2*n^2 = 4 * a^2$ oder
    $n^2 = 2 * a^2$. Das bedeutet, dass $n^2$ gerade ist, und wie soeben
    argumentiert, wäre damit $n$ gerade. Dies widerspricht jedoch der
    Teilerfremdheit von $m$ und $n$. Dieser Beweis wird hier
    formalisiert. (Es sei angemerkt, dass der hier gegebene Beweis nur
    für $\sqrt 2$ funktioniert, nicht aber für $\sqrt 3$. Der Grund ist,
    dass wir verwenden, dass für jedes $m\in\mathbb N$ entweder $m$ oder
    $m+1$ gerade (also durch 2 teilbar) ist. Dies ist für $3$ offenbar
    falsch.)

-   Blatt 02-d: Vollständige Induktion\
    Seit dem ersten Semester kennt man die vollständige Induktion: Zeigt
    man für eine Aussage `P : ℕ → Prop`{.Lean} sowohl `P 0`{.Lean}, als
    auch `∀ d : ℕ, P d → P d+1`{.Lean}, dann hat man
    `∀ n : ℕ, P n`{.Lean} gezeigt. Dies ist die sogenannte *schwache*
    Induktion, die wir hier für ein paar Aussagen verwenden werden.
    Außerdem werden wir den Wohlordnungssatz von `ℕ`{.Lean} zeigen, der
    besagt, dass jede nicht-leere Teilmenge von ℕ ein kleinstes Element
    enthält.

-   Blatt 02-e: Schubfachprinzip\
    Verteilt man $m$ Kugeln auf $n<m$ Schubfächer, so landen mindestens
    zwei Kugeln im gleichen Schubfach. Etwas mathematischer ausgedrückt
    gibt es keine injektive Abbildung einer $m$-elementigen Menge in
    eine $n<m$-elementige. Um dies zu beweisen, führen wir zunächst
    injektive Abbildungen ein und verwenden ein Induktionsprinzip für
    `finset`{.Lean}s.

## Reelle Zahlen

Wir kommen nun zu reellen Zahlen, ohne uns deren Definition (die
Cauchy-Folgen verwendet) anzusehen.

-   Blatt 03-a: Untere Schrank eine Menge\
    Wir führen die Menge der unteren Schranken einer Menge
    $A \subseteq \mathbb R$ ein. Die größte untere Schrank ist dann
    bekanntlich das $\inf A$. Um das Hauptresultat zu formulieren,
    führen wir auch den Grenzwert einer Folge ein. Schließlich beweisen
    wir, dass $x = \inf A$ genau dann gilt, wenn es eine Folge in $A$
    gibt die gegen $x$ konvergiert.

-   Blatt 03-b: Die Ableitung von $x\mapsto x^{n+1}$\
    Bekanntlich ist die Ableitung von $x\mapsto x^{n+1}$ durch
    $x\mapsto (n+1)x^n$ gegeben. Um dies zu zeigen, benötigen wir den
    Begriff der Ableitung (hier als Folgen-Grenzwert), sowie die
    Produktregel. Wir werden alles auf Rechenregeln von Grenzwerten
    zurückführen, etwa dass der Grenzwert des Produkts zweier
    konvergenter Folgen durch das Produkt der Grenzwerte gegeben ist.
    Nach diesen Vorarbeiten beweisen wir die Formel durch Induktion.

# Hinweise zu Lean {#S:lean}

In Abschnitt [1](#S:vorbereitung){reference-type="ref"
reference="S:vorbereitung"} haben wir uns bereits mit der Installation
von Lean und `vscode` befasst. Hier folgt eine kurze, unzusammenhängende
Einführung. Wir beginnen mit einem sehr einfachen Beispiel. (Die
Taktiken `intro`{.Lean} und `exact`{.Lean} bitte in
Kapitel [5](#S:tactics){reference-type="ref" reference="S:tactics"}
nachlesen.) Wenn wir die Aussage `P → P`{.Lean} (d.h. aus `P`{.Lean}
folgt`P`{.Lean}) beweisen wollen, geben wir in `vscode`{.Lean} auf der
linken Seite folgendes ein:

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
example (P : Prop) : P → P := 
begin
  sorry,
end
```

Auf der rechten Seite findet sich, abhängig von der Position des
Cursors, der *proof state*. Ist der Cursor diirekt nach `begin`{.Lean},
so ist der *proof-state*

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="white"}
P : Prop
⊢ P → P
```

Hier ist wichtig zu wissen, dass hinter `⊢`{.Lean} die Behauptung steht,
und alles darüber Hypothesen sind. (Im gezeigten Fall ist dies nur die
Tatsache, dass `P`{.Lean} eine Behauptung/Proposition ist. Diese
Darstellung entspricht also genau der Behauptung. Ist der Cursor nach
dem `sorry`{.Lean}, so steht nun zwar **goals accomplished** ,
allerdings ist die `sorry`{.Lean}-Taktik nur da, um erst einmal
unbewiesene Behauptungen ohne weitere Handlung beweisen zu können und es
erfolgt eine Warnung in `vscode`. Löscht man das `sorry`{.Lean} und
ersetzt es durch ein `intro hP`{.Lean}, so erhält man

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
P : Prop
hP : P
⊢ P
```

Wir haben also die Aussage `P → P`{.Lean} überführt in einen Zustand,
bei dem wir `hP : P`{.Lean} annehmen, und `P`{.Lean} folgern müssen.
Dies lässt sich nun leicht mittels `assumption,`{.Lean} lösen (bitte das
Komma nicht vergessen), und es erscheint das gewünschte **goals
accomplished** . Die `assumption`{.Lean}-Taktik such nach einer
Hypothese, die identisch mit der Aussage ist und schließt den Beweis.
Etwas anders ist es mit der `exact`{.Lean}-Taktik. Hier muss man wissen,
welche Hypothese genau gemeint und, und kann hier mit `exact hP`{.Lean}
den Beweis schließen

## Dependent type theory

Lean ist eine funktionale Programmiersprache (d.h. es besteht eigentlich
nur aus Funktionen) und basiert auf der *dependent type theory*. Typen
in Programmiersprachen wir etwa Python sind `bool`, `int`, `double` etc.
Lean lebt davon, eigene Typen zu definieren und zu verwenden. Wir werden
sehen imd Verlauf des Kurses sehen, dass man über die entstehenden Typen
wie Mengen denken kann. Der Typ `ℕ`{.Lean} wird etwa die Menge der
natürlichen Zahlen, und `ℝ`{.Lean} die Menge der reellen Zahlen sein.
Allerdings steht `ℕ`{.Lean} in der Tat für eine unendliche Menge, die
dadurch charakterisiert ist, dass sie `0`{.Lean} enthält, und wenn sie
`n`{.Lean} enthält, so enthält sie auch den Nachfolger von `n`{.Lean}
(der mitt `succ n`{.Lean} dargestellt wird). Entsprechend sind die
reellen Zahlen durch eine Äquivalenzrelation auf Cauchy-Folgen
definiert, was schon recht aufwändig ist. Typen können dabei von anderen
Typen abhängen, und deshalb sprechen wir von *depoendent types*. Etwa
ist der Raum $\mathbb R^n$ abhängig von der Dimension $n$. Wie wir sehen
werden, sind mathematische Aussagen ebenfalls solche Typen.

Zur Notation: Bei Mengen sind wir gewohnt, etwa $n\in\mathbb N$ zu
schreiben, falls $n$ eine natürliche Zahl ist. In der Typentheorie
schreiben wir `n : ℕ`{.Lean} und sagen, dass `n`{.Lean} ein Term
(Ausdruck) vom Typ `ℕ`{.Lean} ist. Etwas allgemeiner hat jeder Ausdruck
einen Typ und bei der Einführung jedes Ausdrucks überprüft Lean dessen
Typ. (Übrigens kann das durchaus verwirrend sein: etwa ist die Aussage
`(x : ℕ) → (x : ℤ)`{.Lean}, d.h. (jede natürliche Zahl ist auch eine
Ganze Zahl) für `lean`{.Lean} gar nicht verständlich. Denn `x`{.Lean}
ist ein Term vom Typ `ℕ`{.Lean} (und damit von keinem anderen Typ), so
dass `x : ℤ`{.Lean} für `lean`{.Lean} gar keinen Sinn ergibt. Die Lösung
ist eine *unsichtbare Abbildung* `coe : ℕ → ℤ`{.Lean}.)

## Von Universen, Typen und Termen

In Lean gibt es drei Ebenen von Objelten: Universen, Typen und Terme.
Wir befassen uns hier mit den letzten beiden. Von besonderem Interesse
ist der Typ `Prop`, der aus Aussagen besteht, die wahr oder falsch sein
können. Er umfasst mathematische Aussagen, also entweder die Hypothesen,
oder das Goal dessen, was zu beweisen ist. Eine Hypothese in Lean hat
die Form `hP : P`{.Lean}, was soviel sagt wie `P`{.Lean} gilt, und diese
Aussage heißt `hP`{.Lean}. Es kann auch bedeuten, dass `P`{.Lean} gilt
und `hP`{.Lean} ein Beweis von `P`{.Lean} ist. Dabei haben die
Hypothesen hier Namen `P Q R S`{.Lean}, und die Namen der Hypothesen
`hP hQ hR hS`{.Lean}. Alle Namen können beliebig sein. Weiter gibt es
Hypothesen der Form `P → Q`{.Lean}, also die Aussage, dass aus
`P`{.Lean} die Aussage `Q`{.Lean} folgt.

## Funktionedefinition

In `Lean`{.Lean} wird etwa die Funktion
$f : \mathbb N \to \mathbb N, x \mapsto 2x$ definiert als

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
  f : ℕ → ℕ := λ x, 2*x
```

oder (falls man keinen Funktionsnamen vergeben will) `λ x, 2*x`{.Lean}.
Man denkt dabei, dass das `x`{.Lean} nur eben mal eigeführt wird um
`f`{.Lean} zu definieren. Die Anwendung von `f`{.Lean} auf ein
`x : ℕ`{.Lean} erfolgt dann mittels `f x`{.Lean}. (Die Schreibweise
`f x`{.Lean} ist abkürzend für $f(x)$, da `lean`{.Lean} sparsam mit
Klammern ist.)

## Gleichheit

In Lean gibt es drei Arten von Gleichheit:

-   Syntaktische Gleichheit: Wenn zwei Terme Buchstabe für Buchstabe
    gleich sind, so sind sie syntaktisch gleich. Allerdings gibt es noch
    ein paar weitere Situationen, in denen zwei Terme syntaktisch gleich
    sind. Ist nämlich ein Term nur eine Abkürzung für den anderen (etwa
    ist `x=y`{.Lean} eine Abkürzung für `eq x y`{.Lean}), so sind diese
    beiden Terme syntaktisch gleich. Ebenfalls gleich sind Terme, bei
    denen global quantifizierte Variablen andere Buchstababen habe. Etwa
    sind `∀ x, ∃ y, f x y`{.Lean} und `∀ y, ∃ x, f y x`{.Lean}
    syntaktisch gleich.

-   Definitorische Gleichheit: Manche Terme sind in Lean per Definition
    gleich. Für `x : ℕ`{.Lean} ist `x + 0`{.Lean} per Definition
    identisch zu `x`{.Lean}. Allerdings ist `0 + x`{.Lean} nicht
    definitorisch identisch zu `x`{.Lean}. Dies hat offenbar nur mit der
    internen Definition der Addition natürlicher Zahlen in Lean zu tun.

-   Propositionelle Gleichheit: Falls es einen Beweis von `x = y`{.Lean}
    gibt, so heißen `x`{.Lean} und `y`{.Lean} und propositionell gleich.
    Analog heißen Terme `P`{.Lean} und `Q`{.Lean} propositionell gleich,
    wenn man `P ↔ Q`{.Lean} beweisen kann.

Manche Lean-Taktiken arbeiten nur bis hin zur syntaktische Gleichheit
(etwa `rw`{.Lean}), andere (die meisten) bis hin zur definitorischen
Gleichheit (etwa `apply, exact,...`{.Lean} Das bedeutet, dass von der
Taktik Terme automatisch umgeformt werden, wenn sie syntaktisch
bzw. definitorisch gleich sind.

Eine besondere Art von Gleichheit gibt es bei Mengen und Funktionen zu
beachten. Etwa sind zwei Funktionen genau dann gleich, wenn sie für alle
Werte des Definitionsbereiches denselben Wert liefern. Dieses verhalten
nennt man in der Theorie der Programmiersprachen *Extensionalität*.
(Gilt Extensionalität, so sind beispielsweise zwei Sortier-Algorithmen
gleich, falls sie immer dasselbe Ergebnis liefern.)

## Verschiedene Klammern in `Lean`{.Lean}

Es gibt (im wesentlichen) drei verschiedene Arten von Klammern in
`lean`{.Lean}-Aussagen. Die einfachste ist dabei `(...)`{.Lean}, die wie
im üblichen Gebrauch ene Klammerung im Sinne davon, was zusammengehört,
bedeutet. Man muss jedoch einmal lernen, wie `lean`{.Lean} intern
klammert, wenn keine `(...)`{.Lean}-Klammern angegeben sind: Binäre
Operatoren wir *und* (`∧`{.Lean}), *oder* (`∨`{.Lean}), sind
rechts-assoziativ, also z.B. `P ∧ Q ∧ R`{.Lean} $:=$
`P ∧ (Q ∧ R)`{.Lean}. Die Hintereinanderausführung von Funktionen, etwa
`f : ℕ→ ℝ`{.Lean} und `g : : ℝ→ ℝ `{.Lean}, angewendet auf
`n : ℕ`{.Lean} ist `g (f n)`{.Lean}, denn `g`{.Lean} erwartet einen
Input vom Typ `ℝ`{.Lean}, und dies liefert `f n`{.Lean}. Dabei kann man
`(...)`{.Lean} nicht weglassen, d.h. in diesem Fall ist die Klammerung
links-assoziativ.

Komment wir nun zu den Klammern `[...]`{.Lean} und `{...}`{.Lean}. Sehen
wir uns hierzu beispielsweise `#check@ gt_iff_lt`{.Lean} (die Aussage,
dass $a>b$ genau dann gilt, wenn $b<a$ gilt) an, wo beide Typen
vorkommen . Dies liefert

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
gt_iff_lt : ∀ {α : Type u_1} [_inst_1 : has_lt α] {a b : α}, a > b ↔ b < a
```

Bei der Anwendung dieses Resultats werden die Aussagen in `{...}`{.Lean}
und `[...]`{.Lean} von `lean`{.Lean} selbst hinzugefügt. Die Aussagen in
`{...}`{.Lean} werden dabei vom Typ der Objekte, die angegeben werden
müssen, ab, und können deshalb inferiert werden. (Oben müssen ja bei der
Anwendung von `gt_iff_lt`{.Lean} die Variablen `a`{.Lean} und `b`{.Lean}
angegeben werden. Deshalb ist auch deren Typ bekannt, und man muss
`α`{.Lean} nicht explizit angeben. Da die Anwendung auf ein konkretes
`α`{.Lean} erfolgt (etwa `ℕ`{.Lean}), und `lean`{.Lean} eine Menge über
die natürlichen Zahlen weiß, kann das Typ-Klassen-System viele
Eigenschaften von `ℕ`{.Lean} nachsehen, und findet dabei auch, dass
`has_lt ℕ`{.Lean} gilt (d.h. auf `ℕ`{.Lean} ist wenigstens eine
Halbordnung definiert).

## Namen von `mathlib`{.Lean}-Resultaten

Namen wie
`zero_add, add_zero, one_mul, add_assoc, succ_ne_zero, lt_of_succ_le,...`{.Lean}
wirken kryptisch. Klar ist, dass einzelne relativ klar verständliche
Kürzel (`zero, one, mul, add, succ,...`{.Lean}) durch `_`{.Lean}
getrennt sind. Generell gelten für die Namensgebung folgende zwei
Regeln:

-   Beschrieben wird das zu beweisende Goal der Aussage;

-   werden Hypothesen im Namen hinzugefügt, so mit `of_`{.Lean}.

Die Aussage `lt_of_succ_le`{.Lean} ist also eine `<`{.Lean}-Aussage,
wobei `succ ≤`{.Lean} gilt. In der Tat: `#check @lt_of_succ_le`{.Lean}
ergibt

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
  lt_of_succ_le : ∀ {a b : ℕ}, a.succ ≤ b → a < b
```

Auf diese Weise kann man oftmals die Namen von Aussagen, die man
verwenden will, erraten.

# Taktiken {#S:tactics}

## Cheatsheet

::: {#foot:simp}
+----------------------+----------------------+----------------------+
| **Proof state**      | **Kommando**         | **Neuer proof        |
|                      |                      | state**              |
+:=====================+:=====================+:=====================+
| `⊢ P → Q`{.Lean}     | `intro hP`{.Lean}    | `hP : P`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `                    | `intro x,`{.Lean}    | `f: α → Prop`{.Lean} |
| f : α → Prop`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢ ∀                 |                      | `x : α`{.Lean}       |
| (x : α), f x`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ f x`{.Lean}       |
+----------------------+----------------------+----------------------+
| `h : P`{.Lean}       | `exact h,`{.Lean}    | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+
| `h : P`{.Lean}       | `assumption,`{.Lean} | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+
| `h : P → Q`{.Lean}   | `apply h,`{.Lean}    | `h : P → Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `⊢ Q`{.Lean}         |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ P → Q → R`{.Lean} | `i                   | `hP : P`{.Lean}      |
|                      | ntros hP hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ P                 | `tauto,`{.Lean} oder | **goals accomplished |
|  ∧ Q → P`{.Lean}[^5] | `tauto!,`{.Lean}     | **                   |
+----------------------+----------------------+----------------------+
| `⊢ true`{.Lean}      | `triv,`{.Lean}       | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `h : P`{.Lean}       | `exfalso,`{.Lean}    | `h : P`{.Lean}       |
+----------------------+----------------------+----------------------+
| `⊢ Q`{.Lean}         |                      | `⊢ false`{.Lean}     |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         | `                    | `h : ¬P`{.Lean}      |
|                      | by_contra h,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ false`{.Lean}     |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         | `by_                 | `h : Q`{.Lean}       |
|                      | cases h : Q,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
|                      |                      | `h : ¬Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ∧ Q`{.Lean}   | `cases h             | `hP : P`{.Lean}      |
|                      |  with hP hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ R`{.Lean}         |                      | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ∨ Q`{.Lean}   | `cases h             | `hP : P`{.Lean}      |
|                      |  with hP hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ R`{.Lean}         |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
|                      |                      | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : false`{.Lean}   | `cases h,`{.Lean}    | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢                   | `change ¬P,`{.Lean}  | `⊢ ¬P`{.Lean}        |
|  : P → false`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q`{.Lean}     | `split,`{.Lean}      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ P ↔ Q`{.Lean}     | `split,`{.Lean}      | `⊢ P → Q`{.Lean}     |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ Q → P`{.Lean}     |
+----------------------+----------------------+----------------------+
| `⊢ P ↔ P`{.Lean}     | `refl,`{.Lean}       | **goals accomplished |
| oder                 |                      | **                   |
+----------------------+----------------------+----------------------+
| `⊢ P = P`{.Lean}     |                      |                      |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `rw h,`{.Lean}       | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `rw ← h,`{.Lean}     | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `⊢ Q`{.Lean}         |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `rw h at hP,`{.Lean} | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `hP : P`{.Lean}      |                      | `hP : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `r                   | `h : P ↔ Q`{.Lean}   |
|                      | w ← h at hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `hQ : Q`{.Lean}      |                      | `hQ : P`{.Lean}      |
+----------------------+----------------------+----------------------+
| `⊢ P ∨ Q`{.Lean}     | `left,`{.Lean}       | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ P ∨ Q`{.Lean}     | `right,`{.Lean}      | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ 2                 | `norm_num,`{.Lean}   | **goals accomplished |
|  + 2 < 5`{.Lean}[^6] |                      | **                   |
+----------------------+----------------------+----------------------+
| `                    | `use y,`{.Lean}      | `                    |
| f : α → Prop`{.Lean} |                      | f : α → Prop`{.Lean} |
+----------------------+----------------------+----------------------+
| `y : α`{.Lean}       |                      | `y : α`{.Lean}       |
+----------------------+----------------------+----------------------+
| `⊢ ∃                 |                      | `⊢ f y`{.Lean}       |
| (x : α), f x`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
| `x y : ℝ`{.Lean}     | `ring,`{.Lean}       | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `⊢ x + y             |                      |                      |
|  = y + x`{.Lean}[^7] |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢ P → Q`{.Lean}     | `intro hP`{.Lean}    | `hP : P`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `                    | `intro x,`{.Lean}    | `f: α → Prop`{.Lean} |
| f : α → Prop`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢ ∀                 |                      | `x : α`{.Lean}       |
| (x : α), f x`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ f x`{.Lean}       |
+----------------------+----------------------+----------------------+
| `h1 : a < b`{.Lean}  | `linarith,`{.Lean}   | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `h2 : b ≤ c`{.Lean}  |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢ a < c`{.Lean}[^8] |                      |                      |
+----------------------+----------------------+----------------------+
| `h : P`{.Lean}       | `clear h,`{.Lean}    | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ Q`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+
| `                    | `spec                | `f: ℕ → Prop`{.Lean} |
| f : ℕ → Prop`{.Lean} | ialize h 13,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `h : ∀               |                      | `h : f 13`{.Lean}    |
| (n : ℕ), f n`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `f :                 | `obta                | `f:                  |
| ℕ → ℕ → Prop`{.Lean} | in ⟨ m, hm ⟩`{.Lean} | ℕ → ℕ → Prop`{.Lean} |
+----------------------+----------------------+----------------------+
| `h : ∀ (n : ℕ), ∃ (m | `                    | `h : ∀ (n : ℕ),      |
|  : ℕ), f n m`{.Lean} |     := h 27,`{.Lean} |  ∃ (m : ℕ), `{.Lean} |
+----------------------+----------------------+----------------------+
|                      |                      | `                    |
|                      |                      |        f n m`{.Lean} |
+----------------------+----------------------+----------------------+
|                      |                      | `m : ℕ`{.Lean}       |
+----------------------+----------------------+----------------------+
|                      |                      | `hm : f 27 m`{.Lean} |
+----------------------+----------------------+----------------------+
| `⊢ R`{.Lean}         | `have                | `⊢ P ↔ Q`{.Lean}     |
|                      |  h : P ↔ Q, `{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h1 : a < b`{.Lean}  | `lib                 | **goals accomplished |
|                      | rary_search,`{.Lean} | **                   |
+----------------------+----------------------+----------------------+
| `h2 : b < c`{.Lean}  |                      | `Try this: `{.Lean}  |
+----------------------+----------------------+----------------------+
| `⊢ a < c`{.Lean}     |                      | `exact lt            |
|                      |                      | _trans h1 h2`{.Lean} |
+----------------------+----------------------+----------------------+
| `hQ : Q`{.Lean}      | `refin               | `hQ : Q`{.Lean}      |
|                      | e ⟨ _, hQ ⟩,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q`{.Lean}     |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ P ∨ Q → R`{.Lean} | `rintro              | `hP : P`{.Lean}      |
|                      | ( hP | hQ ),`{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      | $=$                  | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
|                      | `intro h,`{.Lean}    | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      | `cases h             | `⊢ Q`{.Lean}         |
|                      |  with hP hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q → R`{.Lean} | `rintro              | `hP : P`{.Lean}      |
|                      | ⟨ hP , hQ ⟩,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      | $=$                  | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      | `intro h,`{.Lean}    | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
|                      | `cases h             |                      |
|                      |  with h1 h2,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `h : P               |                      |                      |
| ∧ Q ∨ P ∧ R`{.Lean}\ |                      |                      |
| `⊢ P`{.Lean}         |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `rc                  |                      |                      |
| ases h with`{.Lean}\ |                      |                      |
| `(⟨hP1,hQ            |                      |                      |
| ⟩|⟨hP2,hR⟩),`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `hP1 : P`{.Lean}\    |                      |                      |
| `hQ : Q`{.Lean}\     |                      |                      |
| `⊢ P`{.Lean}\        |                      |                      |
| `hP2 : P `{.Lean}\   |                      |                      |
| `hR : R`{.Lean}\     |                      |                      |
| `⊢ P`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+
:::

## `apply`{.Lean} {#apply .unnumbered}

### Zusammenfassung {#zusammenfassung .unnumbered}

Angenommen, das Goal ist `⊢ Q`{.Lean}, wobei bereits ein Beweis für
`h : P → Q`{.Lean} zur Verfügung steht. Deshalb braucht man nur noch
einen Beweis für `⊢ P`{.Lean} zu finden. Diese Umwandlung passiert mit
`apply h`{.Lean}.

### Beispiele {#beispiele .unnumbered}

  **Proof state**      **Kommando**        **Neuer proof state**
  -------------------- ------------------- -----------------------
  `h : P → Q`{.Lean}   `apply h,`{.Lean}   `h : P → Q`{.Lean}
  `⊢ Q`{.Lean}                             `⊢ P`{.Lean}
  `h : ¬P`{.Lean}      `apply h`{.Lean}    `h : ¬P`{.Lean}
  `⊢ false`{.Lean}                         `⊢ P`{.Lean}

 

Die Taktik `apply`{.Lean} wendet sich iterativ an. Das bedeutet: liefert
`apply h`{.Lean} (identisch mit `refine h _`{.Lean}) keinen Fortschritt,
so wird es mit `refine h _ _`{.Lean} versucht:

  

+-------------------------+--------------+-----------------------+
| **Proof state**         | **Kommando** | **Neuer proof state** |
+:========================+:=============+:======================+
| `h : P → Q → R`{.Lean}\ |              |                       |
| `⊢ R`{.Lean}            |              |                       |
|                         |              |                       |
| &                       |              |                       |
|                         |              |                       |
| `apply h`{.Lean}        |              |                       |
|                         |              |                       |
| &                       |              |                       |
|                         |              |                       |
| `h : P → Q → R`{.Lean}\ |              |                       |
| `⊢ P`{.Lean}\           |              |                       |
| `h : P → Q → R`{.Lean}\ |              |                       |
| `⊢ Q`{.Lean}            |              |                       |
+-------------------------+--------------+-----------------------+

### Anmerkungen {#anmerkungen .unnumbered}

1.  `apply`{.Lean} arbeitet bis hin zur definitorischen Gleichheit. Dies
    kann man im zweiten Beispiel sehen, da `¬P`{.Lean} per Definition
    gleich `P → false`{.Lean} ist:\

2.  `apply h`{.Lean} ist identisch zu `refine h _`{.Lean}, bzw. (wie im
    zweiten Beispiel oben) zu `refine h _ _`{.Lean}.

## `assumption`{.Lean} {#assumption .unnumbered}

### Zusammenfassung {#zusammenfassung-1 .unnumbered}

Ist eine der Annahmen identisch mit dem Goal, dann schließt
`assumption,`{.Lean} das Goal.

### Beispiele {#beispiele-1 .unnumbered}

+-------------------------+----------------------+-------------------------+
| **Proof state**         | **Kommando**         | **Neuer proof state**   |
+:========================+:=====================+:========================+
| `h : P`{.Lean}          | `assumption,`{.Lean} | **goals accomplished ** |
+-------------------------+----------------------+-------------------------+
| `⊢ P`{.Lean}            |                      |                         |
+-------------------------+----------------------+-------------------------+
| `h : ¬P`{.Lean}\        |                      |                         |
| `⊢ P → false`{.Lean}    |                      |                         |
|                         |                      |                         |
| &                       |                      |                         |
|                         |                      |                         |
| `assumption,`{.Lean}    |                      |                         |
|                         |                      |                         |
| &                       |                      |                         |
|                         |                      |                         |
| **goals accomplished ** |                      |                         |
+-------------------------+----------------------+-------------------------+

### Anmerkungen {#anmerkungen-1 .unnumbered}

1.  Wie andere Taktiken auch arbeitet `assumption`{.Lean} bis zur
    definitorischen Geichheit.

2.  Hier ein Trick: Verwendet man als Abschluss einer Taktik ein
    Semicolon `;`{.Lean}, so wird die nachfolgende Taktik auf alle Goals
    angewendet:

 

+-----------------------------+--------------+-----------------------+
| **Proof state**             | **Kommando** | **Neuer proof state** |
+:============================+:=============+:======================+
| `hP : P`{.Lean}\            |              |                       |
| `hQ : Q`{.Lean}\            |              |                       |
| `⊢ : P ∧ Q`{.Lean}          |              |                       |
|                             |              |                       |
| &                           |              |                       |
|                             |              |                       |
| `split; assumption,`{.Lean} |              |                       |
|                             |              |                       |
| &                           |              |                       |
|                             |              |                       |
| **goals accomplished **     |              |                       |
+-----------------------------+--------------+-----------------------+

## `by_cases`{.Lean} {#by_cases .unnumbered}

### Zusammenfassung {#zusammenfassung-2 .unnumbered}

Hat man einen Term `P : Prop`{.Lean} als Hypothese, so liefert
`by_cases hP : P`{.Lean} zwei Goals. Beim ersten gibt es zusätzlich
`hP : P`{.Lean}, beim zweiten `hP : ¬P`{.Lean}. Diese Taktik ist also
identisch mit `have hP : P ∨ ¬ P, exact em P, cases hP,`{.Lean}. (Der
zweite Ausdruck ist `em : ∀ (p : Prop), p ∨ ¬p`{.Lean}.

### Beispiele {#beispiele-2 .unnumbered}

+-----------------------------+--------------------------+-----------------------+
| **Proof state**             | **Kommando**             | **Neuer proof state** |
+:============================+:=========================+:======================+
| `⊢ P`{.Lean}                | `by_cases h : Q,`{.Lean} | `h : Q`{.Lean}        |
+-----------------------------+--------------------------+-----------------------+
|                             |                          | `⊢ P`{.Lean}          |
+-----------------------------+--------------------------+-----------------------+
|                             |                          | `h : ¬Q`{.Lean}       |
+-----------------------------+--------------------------+-----------------------+
|                             |                          | `⊢ P`{.Lean}          |
+-----------------------------+--------------------------+-----------------------+
| `x: bool`{.Lean}\           |                          |                       |
| `⊢ x = tt ∨ x = ff`{.Lean}  |                          |                       |
|                             |                          |                       |
| &                           |                          |                       |
|                             |                          |                       |
| `by_cases x=tt,`{.Lean}     |                          |                       |
|                             |                          |                       |
| &                           |                          |                       |
|                             |                          |                       |
| `x: bool`{.Lean}\           |                          |                       |
| `h: x = tt`{.Lean}\         |                          |                       |
| `⊢ x = tt ∨ x = ff`{.Lean}\ |                          |                       |
| `x: bool`{.Lean}\           |                          |                       |
| `h: ¬x = tt`{.Lean}\        |                          |                       |
| `⊢ x = tt ∨ x = ff`{.Lean}  |                          |                       |
+-----------------------------+--------------------------+-----------------------+

  

Im zweiten Beispiel verwenden wir eine Variable vom Typ `bool`{.Lean}
Diese ist folgendermaen definiert:

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
inductive bool : Type
| ff : bool
| tt : bool
```

Eine Bool'sche Variable hat also nur die Möglichkeiten `tt`{.Lean} (für
`true`{.Lean}) und `ff`{.Lean} (für `false`{.Lean}).

### Anmerkungen {#anmerkungen-2 .unnumbered}

1.  Offenbar benutzt die `by_cases`{.Lean}-Taktik (genau wie
    `by_contradiction`{.Lean}, dass eine Aussage entweder wahr oder
    falsch ist. Dies ist auch bekannt unter dem Gesetz des
    ausgeschlossenen Dritten. In der Mathematik nennt man Beweise, die
    diese Regel nicht verwenden, konstruktiv.

2.  Für Terme vom Typ `Prop`{.Lean} kann die Taktik `tauto`{.Lean}
    (bzw. `tauto!`{.Lean}) durch eine Wahrheitstabelle viele Schlüsse
    ziehen.

## `by_contra`{.Lean} {#by_contra .unnumbered}

### Zusammenfassung {#zusammenfassung-3 .unnumbered}

Die `by_contra`{.Lean}-Taktik stellt einen Beweis durch Widerspruch dar.
Es wird deshalb angenommen (d.h. in eine Hypothese überführt), dass die
Aussage (hinter `⊢`{.Lean}) nicht wahr ist, und dies muss zu einem
Widerspruch geführt werden, d.h. es muss ein Beweis von `false`{.Lean}
gefunden werden.

### Beispiele {#beispiele-3 .unnumbered}

+---------------------------+-----------------------+-----------------------+
| **Proof state**           | **Kommando**          | **Neuer proof state** |
+:==========================+:======================+:======================+
| `⊢ P`{.Lean}              | `by_contra h,`{.Lean} | `h : ¬P`{.Lean}       |
+---------------------------+-----------------------+-----------------------+
|                           |                       | `⊢ false`{.Lean}      |
+---------------------------+-----------------------+-----------------------+
| `h: ¬¬P`{.Lean}\          |                       |                       |
| `⊢ P`{.Lean}              |                       |                       |
|                           |                       |                       |
| &                         |                       |                       |
|                           |                       |                       |
| `by_contra hnegP,`{.Lean} |                       |                       |
|                           |                       |                       |
| &                         |                       |                       |
|                           |                       |                       |
| `h: ¬¬P`{.Lean}\          |                       |                       |
| `hnegP: ¬P`{.Lean}\       |                       |                       |
| `⊢ false`{.Lean}          |                       |                       |
+---------------------------+-----------------------+-----------------------+

### Anmerkungen {#anmerkungen-3 .unnumbered}

Diese Taktik ist stärker als `exfalso`{.Lean}. Dort wird ja schließlich
das Goal nur in `false`{.Lean} überführt, ohne eine neue Hypothese
hinzuzufügen. Bei `by_contra`{.Lean} ist das neue Goal zwar auch
`false`{.Lean}, aber es gibt noch eine neue Hypothese.

## `calc`{.Lean} {#calc .unnumbered}

### Zusammenfassung {#zusammenfassung-4 .unnumbered}

Wie das Wort schon andeutet, geht es bei `calc`{.Lean} um konkrete
Berechnungen. Dies ist kein Taktik, sondern ein `lean`{.Lean}-Modus. Das
bedeutet, dass man diesen Modus betreten kann (mit dem Wort
`calc`{.Lean}) Rechenschritte eingibt und Beweise dafür, dass jeder
einzelne Rechenschritt stimmt.

### Beispiele {#beispiele-4 .unnumbered}

Hier ein Beweis der ersten binomischen Formel, der nur durch Umschreiben
von Recheneigenschaften aus der `mathlib`{.Lean} zustande kommt.

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 :=
begin
  have h : n + n = 2*n, 
  {
    nth_rewrite 0 ← one_mul n,
    nth_rewrite 1 ← one_mul n,
    rw ← add_mul,
  },
   calc (n+1)^2 = (n+1) * (n+1) : by { rw pow_two, }
  ... = (n+1)*n + (n+1) * 1: by {rw mul_add, }
  ... = n*n + 1*n + (n+1) : by {rw add_mul, rw mul_one (n+1),}
  ... = n^2 + n + (n+1) : by {rw one_mul, rw ← pow_two,}
  ... = n^2 + (n + n+1) : by {rw add_assoc, rw ← add_assoc n n 1,}
  ... = n^2 + 2*n + 1 : by { rw ← add_assoc, rw ← h, },
end
```

Dasselbe kann man auch ohne den `calc`{.Lean}-Modus erreichen, etwa so:

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 :=
begin
  have h : n + n = 2*n, by { nth_rewrite 0 ← one_mul n,
        nth_rewrite 1 ← one_mul n, rw ← add_mul, },
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul,
    ← pow_two,  add_assoc, ← add_assoc n n 1,
    ← add_assoc, ← h],
end
```

Dies ist jedoch deutlich schlechter lesbar.

### Anmerkungen {#anmerkungen-4 .unnumbered}

## `cases`{.Lean} {#cases .unnumbered}

### Zusammenfassung {#zusammenfassung-5 .unnumbered}

Ist eine Hypothese zusammengesetzt, d.h. lässt sich in zwei oder mehr
Fälle erweitern, so liefert `cases`{.Lean} genau das. Dies kann nicht
nur bei Hypothesen `h : P ∨ Q`{.Lean} oder `h : P ∧ Q`{.Lean} angewendet
werden, sondern auch bei Strukturen, die aus mehreren Fällen bestehen,
wie `∃...`{.Lean} (hier gibt es eine Variable und eine Aussage) und
`x : bool`{.Lean} oder `n : ℕ`{.Lean}.

### Beispiele {#beispiele-5 .unnumbered}

+----------------------+----------------------+----------------------+
| **Proof state**      | **Kommando**         | **Neuer proof        |
|                      |                      | state**              |
+:=====================+:=====================+:=====================+
| `h : P ∧ Q`{.Lean}   | `cases h             | `hP : P`{.Lean}      |
|                      |  with hP hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ R`{.Lean}         |                      | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ∨ Q`{.Lean}   | `cases h             | `hP : P`{.Lean}      |
|                      |  with hP hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ R`{.Lean}         |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
|                      |                      | `hQ : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : false`{.Lean}   | `cases h,`{.Lean}    | **goals accomplished |
|                      |                      | **                   |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+
| `                    |                      |                      |
| P: ℕ → Prop`{.Lean}\ |                      |                      |
| `h: ∃ (              |                      |                      |
| m : ℕ), P m`{.Lean}\ |                      |                      |
| `⊢ Q`{.Lean}         |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `cases x             |                      |                      |
|  with m h1, `{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `P                   |                      |                      |
|  : ℕ → Prop`{.Lean}\ |                      |                      |
| `m : ℕ`{.Lean}\      |                      |                      |
| `h1 : P m`{.Lean}\   |                      |                      |
| `⊢ Q`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+

### Anmerkungen {#anmerkungen-5 .unnumbered}

1.  Die Anwendung `cases n`{.Lean} für `n : ℕ`{.Lean} ist strikt
    schwächer als die vollständige Induktion (siehe `induction`{.Lean}).
    Durch `cases`{.Lean} wird ja nur `n : ℕ`{.Lean} in die beiden Fälle
    `0`{.Lean} und `succ n`{.Lean} umgewandelt, aber man darf nicht die
    Aussage für `n-1`{.Lean} verwenden, um die Aussage für `n`{.Lean} zu
    beweisen.

2.  Ein besonderer Fall ist es, wenn `h`{.Lean} unmöglich ist und damit
    gar keine Konstrukturen hat. Ist etwa `h : false`{.Lean}, so
    schließt `cases h`{.Lean} jedes Goal.

3.  Eine etwas flexiblere Version von `cases`{.Lean} ist
    `rcases`{.Lean}.

## `change`{.Lean} {#change .unnumbered}

### Zusammenfassung {#zusammenfassung-6 .unnumbered}

Ändert das Goal (bzw. eine Hypothese) in ein Goal (bzw. eine Hypothese),
das (die) definitorisch gleich ist.

### Beispiele {#beispiele-6 .unnumbered}

+---------------------------------+---------------------+-----------------------+
| **Proof state**                 | **Kommando**        | **Neuer proof state** |
+:================================+:====================+:======================+
| `⊢ : P → false`{.Lean}          | `change ¬P,`{.Lean} | `⊢ ¬P`{.Lean}         |
+---------------------------------+---------------------+-----------------------+
| `h : ¬P`{.Lean}\                |                     |                       |
| `⊢ Q`{.Lean}                    |                     |                       |
|                                 |                     |                       |
| &                               |                     |                       |
|                                 |                     |                       |
| `change P → false at h,`{.Lean} |                     |                       |
|                                 |                     |                       |
| &                               |                     |                       |
|                                 |                     |                       |
| `h: P → false`{.Lean}\          |                     |                       |
| `⊢ Q`{.Lean}                    |                     |                       |
+---------------------------------+---------------------+-----------------------+

### Anmerkungen {#anmerkungen-6 .unnumbered}

1.  Wie man am vorletzten Beispiel sieht, funktioniert `change`{.Lean}
    auch bei Hypothesen.

2.  Da viele Taktiken sowieso auf definitorische Gleichheit testen, ist
    `change`{.Lean} oftmals nicht nötig. Es kann aber helfen, den Beweis
    lesbarer zu machen.

## `clear`{.Lean} {#clear .unnumbered}

### Zusammenfassung {#zusammenfassung-7 .unnumbered}

Mit `clear h`{.Lean} wird die Hypothese `h`{.Lean} aus dem Goal state
entfernt (vergessen).

### Beispiele {#beispiele-7 .unnumbered}

  **Proof state**   **Kommando**        **Neuer proof state**
  ----------------- ------------------- -----------------------
  `h : P`{.Lean}    `clear h,`{.Lean}   `⊢ Q`{.Lean}
  `⊢ Q`{.Lean}                          

## `congr`{.Lean} {#congr .unnumbered}

### Zusammenfassung {#zusammenfassung-8 .unnumbered}

Muss man eine Gleichheit `f x = f y`{.Lean} zeigen, so verwendet
`congr`{.Lean} die Aussage, dass die Gleichheit insbesondere dann gilt,
wenn `x = y`{.Lean}.

### Beispiele {#beispiele-8 .unnumbered}

  **Proof state**        **Kommando**      **Neuer proof state**
  ---------------------- ----------------- -----------------------
  `⊢ P x = P y`{.Lean}   `congr,`{.Lean}   `⊢ x = y`{.Lean}

### Anmerkungen {#anmerkungen-7 .unnumbered}

Die verwandte Taktik `congr'`{.Lean} verwendet noch einen Parameter, der
bestimmt, wieviele rekursive Schichten im Goal eliminiert werden. Dies
ist etwa hilfreich in folgenden Beispielen:

 

+----------------------------------+--------------+-----------------------+
| **Proof state**                  | **Kommando** | **Neuer proof state** |
+:=================================+:=============+:======================+
| `⊢ f (x + y) = f (y + x)`{.Lean} |              |                       |
|                                  |              |                       |
| &                                |              |                       |
|                                  |              |                       |
| `congr,`{.Lean}                  |              |                       |
|                                  |              |                       |
| &                                |              |                       |
|                                  |              |                       |
| `⊢ x = y`{.Lean}\                |              |                       |
| `⊢ y = x`{.Lean}                 |              |                       |
+----------------------------------+--------------+-----------------------+

## `exact`{.Lean} {#exact .unnumbered}

### Zusammenfassung {#zusammenfassung-9 .unnumbered}

Ist das Goal durch einen einzigen Befehl zu lösen, dann durch die
`exact`{.Lean} Taktik. Wie viele andere Taktiken auch funktioniert
`exact`{.Lean} auch bei definitorischen gleichen Termen.

### Beispiele {#beispiele-9 .unnumbered}

+----------------------------+-------------------+-------------------------+
| **Proof state**            | **Kommando**      | **Neuer proof state**   |
+:===========================+:==================+:========================+
| `h : P`{.Lean}             | `exact h,`{.Lean} | **goals accomplished ** |
+----------------------------+-------------------+-------------------------+
| `⊢ P`{.Lean}               |                   |                         |
+----------------------------+-------------------+-------------------------+
| `hP: P`{.Lean}\            |                   |                         |
| `hQ: Q`{.Lean}\            |                   |                         |
| `⊢ P ∧ Q`{.Lean}           |                   |                         |
|                            |                   |                         |
| &                          |                   |                         |
|                            |                   |                         |
| `exact ⟨ hP, hQ ⟩,`{.Lean} |                   |                         |
|                            |                   |                         |
| &                          |                   |                         |
|                            |                   |                         |
| **goals accomplished**     |                   |                         |
+----------------------------+-------------------+-------------------------+

### Anmerkungen {#anmerkungen-8 .unnumbered}

Beim dritten Beispiel sollte man sich die Reihenfolge einprägen, in der
die beiden Hapothesen `hP`{.Lean} und `hnP`{.Lean} angewendet werden.
Die erste Hypothese nach `exact`{.Lean} ist immer die, deren rechte
Seite mit dem Goal übereinstimmt. Benötigt diese weiteren Input, wird er
danach fortgeschrieben.

## `exfalso`{.Lean} {#exfalso .unnumbered}

### Zusammenfassung {#zusammenfassung-10 .unnumbered}

Die Aussage `false → P`{.Lean} is für alle `P`{.Lean} wahr. Ist das
momentane Goal also `⊢ P`{.Lean}, und man würde diese wahre Aussage
mittels `apply`{.Lean} anwenden, wäre das neue Goal `⊢ false`{.Lean}.
Genau dies macht die `exfalso`{.Lean}-Taktik.

### Beispiele {#beispiele-10 .unnumbered}

+--------------------+-------------------+-----------------------+
| **Proof state**    | **Kommando**      | **Neuer proof state** |
+:===================+:==================+:======================+
| `h : P`{.Lean}     | `exfalso,`{.Lean} | `h : P`{.Lean}        |
+--------------------+-------------------+-----------------------+
| `⊢ Q`{.Lean}       |                   | `⊢ false`{.Lean}      |
+--------------------+-------------------+-----------------------+
| `hP: P`{.Lean}\    |                   |                       |
| `hnP: ¬P`{.Lean}\  |                   |                       |
| `⊢ Q`{.Lean}       |                   |                       |
|                    |                   |                       |
| &                  |                   |                       |
|                    |                   |                       |
| `exfalso, `{.Lean} |                   |                       |
|                    |                   |                       |
| &                  |                   |                       |
|                    |                   |                       |
| `hP: P`{.Lean}\    |                   |                       |
| `hnP: ¬P`{.Lean}\  |                   |                       |
| `⊢ false`{.Lean}   |                   |                       |
+--------------------+-------------------+-----------------------+

### Anmerkungen {#anmerkungen-9 .unnumbered}

Falls man diese Taktik anwendet, verlässt man den Bereich der
konstruktiven Mathematik. (Diese verzichtet auf die Regel des
ausgeschlossenen Dritten.)

## `have`{.Lean} {#have .unnumbered}

### Zusammenfassung {#zusammenfassung-11 .unnumbered}

Mittels `have`{.Lean} führt man eine neue Behauptung ein, die man
zunächst beweisen muss. Anschließend steht sie als Hypothese in allen
weiteren Goals zur Verfügung. Dies ist identisch damit, zunächst ein
Lemma `h`{.Lean} mit der Aussage nach `have h : `{.Lean} zu beweisen,
und es dann an gegebener Stelle im Beweis wieder zu verwenden (etwa mit
`apply`{.Lean} oder `rw`{.Lean}.

### Beispiele {#beispiele-11 .unnumbered}

+----------------------+----------------------+----------------------+
| **Proof state**      | **Kommando**         | **Neuer proof        |
|                      |                      | state**              |
+:=====================+:=====================+:=====================+
| `⊢ R`{.Lean}         | `have                | `⊢ P ↔ Q`{.Lean}     |
|                      |  h : P ↔ Q, `{.Lean} |                      |
+----------------------+----------------------+----------------------+
|                      |                      | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
|                      |                      | `⊢ R`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `have h1 :           |                      |                      |
|  ∃ (m : ℕ),`{.Lean}\ |                      |                      |
| `                    |                      |                      |
| f 27 m, ...`{.Lean}\ |                      |                      |
| `cases               |                      |                      |
| h1 with m hm`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `m : ℕ`{.Lean}\      |                      |                      |
| `hm: f 27 m`{.Lean}\ |                      |                      |
| `⊢ P`{.Lean}         |                      |                      |
+----------------------+----------------------+----------------------+

### Anmerkungen {#anmerkungen-10 .unnumbered}

1.  Hat man zwei Goals (nennen wir sie `⊢1`{.Lean} und `⊢2`{.Lean}), und
    benötigt man im Beweis von `⊢2`{.Lean} die Aussage von `⊢1`{.Lean},
    so kann man zunächst ein drittes Goal mit `have h := ⊢1`{.Lean}
    einführen (wobei `⊢1`{.Lean} durch die Aussage zu ersetzen ist).
    Anschließend kann man `⊢1`{.Lean} mit `exact`{.Lean} beweisen, und
    hat im Beweis von `⊢2`{.Lean} die Aussage `⊢1`{.Lean} zur Verfügung.

## `induction`{.Lean} {#induction .unnumbered}

### Zusammenfassung {#zusammenfassung-12 .unnumbered}

Induktive Typen lassen die Möglichkeit zu, Aussagen über sie mittels
Induktion zu beweisen. Dies umfasst etwa den üblichen Fall der
vollständigen Induktion über natürliche Zahlen.

### Beispiele {#beispiele-12 .unnumbered}

  **Proof state**        **Kommando**                      **Neuer proof state**
  ---------------------- --------------------------------- ---------------------------------
  `n : ℕ`{.Lean}         `induction n with d hd,`{.Lean}   `⊢ 0 = 0 + 0`{.Lean}
  `⊢ n = 0 + n`{.Lean}                                     `hd : d = 0 + d`{.Lean}
                                                           `⊢ d.succ = 0 + d.succ,`{.Lean}

## `intro`{.Lean} {#intro .unnumbered}

### Zusammenfassung {#zusammenfassung-13 .unnumbered}

Ist das Goal von der Form `⊢ P → Q`{.Lean} oder `∀ (n : ℕ), P n`{.Lean},
so kann man mit `intro P`{.Lean} bzw. `intro n`{.Lean} weiterkommen.

### Beispiele {#beispiele-13 .unnumbered}

  **Proof state**             **Kommando**        **Neuer proof state**
  --------------------------- ------------------- -----------------------
  `⊢ P → Q`{.Lean}            `intro hP`{.Lean}   `hP : P`{.Lean}
                                                  `⊢ Q`{.Lean}
  `f : α → Prop`{.Lean}       `intro x,`{.Lean}   `f: α → Prop`{.Lean}
  `⊢ ∀ (x : α), f x`{.Lean}                       `x : α`{.Lean}
                                                  `⊢ f x`{.Lean}

### Anmerkungen {#anmerkungen-11 .unnumbered}

1.  Mehrere `intro`{.Lean}-Befehle hintereinander fasst man am besten
    mit `intros`{.Lean} zusammen. Weiter ist `rintro`{.Lean} eine
    flexiblere Variante.

2.  Eine Umkehrung von `intro`{.Lean} ist `revert`{.Lean}.

## `intros`{.Lean} {#intros .unnumbered}

### Zusammenfassung {#zusammenfassung-14 .unnumbered}

Dies ist genau wie bei `intro`{.Lean}, aber es können gleichzeitig
mehrere `intro`{.Lean}-Befehle zu einem einzigen zusammengefasst werden.
Etwas genauer ist `intros h1 h2 h3,`{.Lean} identisch mit
`intro h1, intro h2, intro h3`{.Lean}.

### Beispiele {#beispiele-14 .unnumbered}

+-------------------------------+------------------------+-----------------------+
| **Proof state**               | **Kommando**           | **Neuer proof state** |
+:==============================+:=======================+:======================+
| `⊢ P → Q → R`{.Lean}          | `intros hP hQ,`{.Lean} | `hP : P`{.Lean}       |
+-------------------------------+------------------------+-----------------------+
|                               |                        | `hQ : Q`{.Lean}       |
+-------------------------------+------------------------+-----------------------+
|                               |                        | `⊢ R`{.Lean}          |
+-------------------------------+------------------------+-----------------------+
| `P: ℕ → Prop`{.Lean}\         |                        |                       |
| `⊢ ∀ (n : ℕ), P n → Q`{.Lean} |                        |                       |
|                               |                        |                       |
| &                             |                        |                       |
|                               |                        |                       |
| `intros n hP`{.Lean}          |                        |                       |
|                               |                        |                       |
| &                             |                        |                       |
|                               |                        |                       |
| `P: ℕ → Prop`{.Lean}\         |                        |                       |
| `n: ℕ`{.Lean}\                |                        |                       |
| `hP: P n`{.Lean} `⊢ Q`{.Lean} |                        |                       |
+-------------------------------+------------------------+-----------------------+

### Anmerkungen {#anmerkungen-12 .unnumbered}

`rintro`{.Lean} ist eine flexiblere Variante, bei der gleichzeitig
`cases`{.Lean}-Anwendungen ausgeführt werden können.

## `left`{.Lean} {#left .unnumbered}

### Zusammenfassung {#zusammenfassung-15 .unnumbered}

Die Anwendung von `left,`{.Lean} ist identisch mit `apply h,`{.Lean} für
`h : P → P ∨ Q`{.Lean}. Hat man also eine Goal der Form
`⊢ P ∨ Q`{.Lean}, so bewirkt `left,`{.Lean}, dass man nur noch das Goal
`⊢ P`{.Lean} hat. Schließlich genügt es ja, `P`{.Lean} zu zeigen, um das
Goal zu schließen.

### Beispiele {#beispiele-15 .unnumbered}

+-------------------------+----------------+-----------------------+
| **Proof state**         | **Kommando**   | **Neuer proof state** |
+:========================+:===============+:======================+
| `⊢ P ∨ Q`{.Lean}        | `left,`{.Lean} | `⊢ P`{.Lean}          |
+-------------------------+----------------+-----------------------+
| `⊢ ℕ`{.Lean}            |                |                       |
|                         |                |                       |
| &                       |                |                       |
|                         |                |                       |
| `left,`{.Lean}          |                |                       |
|                         |                |                       |
| &                       |                |                       |
|                         |                |                       |
| **goals accomplished ** |                |                       |
+-------------------------+----------------+-----------------------+

  

Das zweite Beispiel bedarf einer kleinen Erklärung. Zunächst muss man
verstehen, dass beim Goal `⊢ ℕ`{.Lean} zu zeigen ist, dass es einen Term
vom Typ `ℕ`{.Lean} gibt, also dass es eine natürlich Zahl gibt. Nun muss
man wissen, wie `ℕ`{.Lean} in Lean implementiert ist. Dies ist

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
inductive nat
| zero : nat
| succ (n : nat) : nat
```

zusammen mit

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
notation `ℕ` := nat
```

Das bedeutet: Der Typ `ℕ`{.Lean} ist definiert dadurch, dass
`zero`{.Lean} ein Term von diesem Typ ist, und dass es eine Funktion
`succ : ℕ → ℕ`{.Lean} gibt. Mit der Eingabe von `left,`{.Lean} im
zweiten Beispiel wird das Goal also deshalb geschlossen, weil per
Definition `zero : ℕ`{.Lean} gilt, insbesondere gibt es also einen Term
vom Typ `ℕ`{.Lean}.

### Anmerkungen {#anmerkungen-13 .unnumbered}

1.  Siehe auch `right,`{.Lean} für die entsprechende Taktik, die
    äquivalent ist zu `apply h`{.Lean} für `h : Q → P ∨ Q`{.Lean}.

2.  Wie im zweiten Beispiel lässt sich `left,`{.Lean} immer dann
    anwenden, wenn man einen induktiven Typ mit zwei Konstruktoren (so
    wie `ℕ`{.Lean}) vor sich hat.

## `library_search`{.Lean} {#library_search .unnumbered}

### Zusammenfassung {#zusammenfassung-16 .unnumbered}

Es gibt ja sehr viele bereits bewiesene Aussage in `mathlib`{.Lean}. Bei
der Verwendung von `library_search`{.Lean} wird die `mathlib`{.Lean} auf
Aussagen hin durchsucht, deren Typen denen der zu beweisenden Aussage
entsprechen. Führt dies nicht zum Erfolg, meldet `Lean`{.Lean} einen
`timeout`{.Lean}. Im Fall eines Erfolges wird außerdem berichtet,
welches Kommando gefunden wurde. Clickt man darauf, so wird dies an
Stelle von `library_search`{.Lean} eingesetzt.

### Beispiele {#beispiele-16 .unnumbered}

  **Proof state**       **Kommando**               **Neuer proof state**
  --------------------- -------------------------- -------------------------------
  `h1 : a < b`{.Lean}   `library_search,`{.Lean}   **goals accomplished **
  `h2 : b < c`{.Lean}                              `Try this: `{.Lean}
  `⊢ a < c`{.Lean}                                 `exact lt_trans h1 h2`{.Lean}

### Anmerkungen {#anmerkungen-14 .unnumbered}

Die Taktik `suggest`{.Lean} ist ähnlich und funktioniert auch dann, wenn
das Goal nicht geschlossen werden kann.

## `linarith`{.Lean} {#linarith .unnumbered}

### Zusammenfassung {#zusammenfassung-17 .unnumbered}

Diese Taktik kann unter Zuhilfenahme der Hypothesen Gleichungen und
Ungleichungen beweisen. Wichtig ist, dass die verwendeten Hypothesen
ebenfalls nur Gleichungen und Ungleichungen sind. Hier wird also vor
allem mit Transitivität von `<`{.Lean} zusammen mit Rechenregeln
gearbeitet.

### Beispiele {#beispiele-17 .unnumbered}

  **Proof state**        **Kommando**         **Neuer proof state**
  ---------------------- -------------------- -------------------------
  `h1 : a < b`{.Lean}    `linarith,`{.Lean}   **goals accomplished **
  `h2 : b ≤ c`{.Lean}                         
  `⊢ a < c`{.Lean}[^9]                        

## `norm_num`{.Lean} {#norm_num .unnumbered}

### Zusammenfassung {#zusammenfassung-18 .unnumbered}

Solange keine Variablen involviert sind, kann `norm_num`{.Lean}
Rechnungen durchführen, die ein `=`{.Lean}, `<`{.Lean}, `≤`{.Lean}, oder
`≠`{.Lean} beinhalten.

### Beispiele {#beispiele-18 .unnumbered}

+----------------------------+--------------------+-------------------------+
| **Proof state**            | **Kommando**       | **Neuer proof state**   |
+:===========================+:===================+:========================+
| `⊢ 2 + 2 < 5`{.Lean}[^10]  | `norm_num,`{.Lean} | **goals accomplished ** |
+----------------------------+--------------------+-------------------------+
| `⊢ | (1 : ℝ) | = 1`{.Lean} |                    |                         |
|                            |                    |                         |
| &                          |                    |                         |
|                            |                    |                         |
| `norm_num,`{.Lean}         |                    |                         |
|                            |                    |                         |
| &                          |                    |                         |
|                            |                    |                         |
| **goals accomplished **    |                    |                         |
+----------------------------+--------------------+-------------------------+

### Anmerkungen {#anmerkungen-15 .unnumbered}

`norm_num`{.Lean} kennt noch ein paar andere Rechenoperationen, etwa die
Betragsfunktion, siehe das zweite Beispiel.

## `nth_rewrite`{.Lean} {#nth_rewrite .unnumbered}

  **Proof state**             **Kommando**         **Neuer proof state**
  --------------------------- -------------------- -------------------------
  `⊢ 2 + 2 < 5`{.Lean}[^11]   `norm_num,`{.Lean}   **goals accomplished **

### Zusammenfassung {#zusammenfassung-19 .unnumbered}

Diese Taktik ist verwandt zu `rw`{.Lean}. Der Unterschied ist, dass man
angeben kann, auf das wievielte Vorkommen des zu ersetzenden Terms das
`rw`{.Lean} angewendet werden soll. Die genaue Syntax ist
`nth_rewrite k h`{.Lean}, wobei `k`{.Lean} die Nummer (beginnend mit
$0$) des zu ersetzenden Terms ist und `h`{.Lean} die zu ersetzende
Hypothese. Wie bei `rw`{.Lean} muss diese von der Form `h : x=y`{.Lean}
oder `h : A↔B`{.Lean} sein.

### Beispiele {#beispiele-19 .unnumbered}

+----------------------------------+--------------+-----------------------+
| **Proof state**                  | **Kommando** | **Neuer proof state** |
+:=================================+:=============+:======================+
| `n : ℕ`{.Lean}\                  |              |                       |
| `⊢ 0 + n = 0 + 0 + n`{.Lean}     |              |                       |
|                                  |              |                       |
| &                                |              |                       |
|                                  |              |                       |
| `nth_rewrite 0 zero_add,`{.Lean} |              |                       |
|                                  |              |                       |
| &                                |              |                       |
|                                  |              |                       |
| `n: ℕ`{.Lean}\                   |              |                       |
| `⊢ n = 0 + 0 + n`{.Lean}         |              |                       |
+----------------------------------+--------------+-----------------------+

  

Lean sieht in obigem Beispiel dreimal ein Term der Form `0 + _`{.Lean}:
Nummer 0 ist auf der linken Seite, für Nummer 1 und 2 wird auf der
rechten Seite (wegen der Klammerung `0 + 0 + n = (0 + 0) + n`{.Lean})
zunächst das zweite `=`{.Lean} gecheckt. Links davon steht
`0 + 0`{.Lean}, was definitorisch identisch ist zu `0`{.Lean}. Wendet
man das `rw zero_add`{.Lean} also hier an, wird der Term zu `n`{.Lean}
umgewandelt. Für Nummer 2 sieht man das `0 + 0`{.Lean} an, stellt fest,
dass es von der gewünschten Form ist und wandelt es in `0`{.Lean} um.

## `obtain`{.Lean} {#obtain .unnumbered}

### Zusammenfassung {#zusammenfassung-20 .unnumbered}

Die `obtain`{.Lean}-Taktik kann man verwenden, um `have`{.Lean} und
`cases`{.Lean} in einem Kommando zusammenzuführen.

### Beispiele {#beispiele-20 .unnumbered}

  **Proof state**                            **Kommando**                **Neuer proof state**
  ------------------------------------------ --------------------------- -------------------------------------
  `f : ℕ → ℕ → Prop`{.Lean}                  `obtain ⟨ m, hm ⟩`{.Lean}   `f: ℕ → ℕ → Prop`{.Lean}
  `h : ∀ (n : ℕ), ∃ (m : ℕ), f n m`{.Lean}   `    := h 27,`{.Lean}       `h : ∀ (n : ℕ), ∃ (m : ℕ), `{.Lean}
                                                                         `           f n m`{.Lean}
                                                                         `m : ℕ`{.Lean}
                                                                         `hm : f 27 m`{.Lean}

## `push_neg`{.Lean} {#push_neg .unnumbered}

### Zusammenfassung {#zusammenfassung-21 .unnumbered}

In vielen Beweisschritten muss eine Negation durchgeführt werden. Um die
entsprechenden Quantoren etc. ebenfalls zu verarbeiten und das Ergebnis
besser weiterverwenden zu können, gibt es die Taktik `push_neg`{.Lean}.

### Beispiele {#beispiele-21 .unnumbered}

+---------------------+--------------+-----------------------+
| **Proof state**     | **Kommando** | **Neuer proof state** |
+:====================+:=============+:======================+
| `⊢ ¬(P ∨ Q)`{.Lean} |              |                       |
|                     |              |                       |
| &                   |              |                       |
|                     |              |                       |
| `push_neg,`{.Lean}  |              |                       |
|                     |              |                       |
| &                   |              |                       |
|                     |              |                       |
| `⊢ ¬P ∧ ¬Q`{.Lean}  |              |                       |
+---------------------+--------------+-----------------------+

### Anmerkungen {#anmerkungen-16 .unnumbered}

Diese Taktik funktioniert auch bei anderen Objekten, etwa Mengen.

## `rcases`{.Lean} {#rcases .unnumbered}

+-------------------------------+--------------+-----------------------+
| **Proof state**               | **Kommando** | **Neuer proof state** |
+:==============================+:=============+:======================+
| `h : P ∧ Q ∨ P ∧ R`{.Lean}\   |              |                       |
| `⊢ P`{.Lean}                  |              |                       |
|                               |              |                       |
| &                             |              |                       |
|                               |              |                       |
| `rcases h with`{.Lean}\       |              |                       |
| `(⟨hP1,hQ⟩|⟨hP2,hR⟩),`{.Lean} |              |                       |
|                               |              |                       |
| &                             |              |                       |
|                               |              |                       |
| `hP1 : P`{.Lean}\             |              |                       |
| `hQ : Q`{.Lean}\              |              |                       |
| `⊢ P`{.Lean}\                 |              |                       |
| `hP2 : P `{.Lean}\            |              |                       |
| `hR : R`{.Lean}\              |              |                       |
| `⊢ P`{.Lean}                  |              |                       |
+-------------------------------+--------------+-----------------------+

### Zusammenfassung {#zusammenfassung-22 .unnumbered}

`rcases`{.Lean} ist eine flexiblere Version von `cases`{.Lean}. Etwas
genauer ist es hier erlaubt, mittels `⟨ hP, hQ ⟩`{.Lean}
(bzw. `(hP | hQ)`{.Lean}) die durch `∧`{.Lean} (bzw. `∨`{.Lean})
verknüpfte Hypothesen `hP`{.Lean} und `hQ`{.Lean} in ihre Fälle
aufzuteilen. Wie man im obigen Beispiel sieht, ist dabei auch eine
Schachtelung von `⟨.,.⟩`{.Lean} und `(.|.)`{.Lean} möglich.

### Beispiele {#beispiele-22 .unnumbered}

+----------------------------+--------------+-----------------------+
| **Proof state**            | **Kommando** | **Neuer proof state** |
+:===========================+:=============+:======================+
| `h : P ∧ Q`{.Lean}\        |              |                       |
| `⊢ R`{.Lean}               |              |                       |
|                            |              |                       |
| &                          |              |                       |
|                            |              |                       |
| `rcases h with`{.Lean}\    |              |                       |
| `       ⟨ hP, hQ ⟩`{.Lean} |              |                       |
|                            |              |                       |
| &                          |              |                       |
|                            |              |                       |
| `hP : P`{.Lean}\           |              |                       |
| `hQ : Q`{.Lean}\           |              |                       |
| `⊢ R`{.Lean}               |              |                       |
+----------------------------+--------------+-----------------------+

 

### Anmerkungen {#anmerkungen-17 .unnumbered}

Im letzten Beispiel sieht man, wie man mit `rcases`{.Lean} einen
`∃`{.Lean}-Quantor in einer Hypothese, der mehr als eine Einschränkung
hat (hier: `0 ≤ m)`{.Lean} und `m < n`{.Lean} direkt auflösen kann.

## `refine`{.Lean} {#refine .unnumbered}

### Zusammenfassung {#zusammenfassung-23 .unnumbered}

Die `refine`{.Lean}-Taktik ist wie `exact`{.Lean} mit Löchern. Etwas
genauer: Wenn das Goal darin besteht, eine Kombination aus Hypothesen
anzuwenden, so kann man das mittels `refine`{.Lean} machen und für jeden
offene Term `_`{.Lean} schreiben. Dann erhält man jeden `_`{.Lean} als
neues Ziel zurück (wobei solche mit definitorischer Gleichheit sofort
gelöst werden).

### Beispiele {#beispiele-23 .unnumbered}

+----------------------+----------------------+----------------------+
| **Proof state**      | **Kommando**         | **Neuer proof        |
|                      |                      | state**              |
+:=====================+:=====================+:=====================+
| `hQ : Q`{.Lean}      | `refin               | `hQ : Q`{.Lean}      |
|                      | e ⟨ _, hQ ⟩,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `⊢ P ∧ Q`{.Lean}     |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `⊢ ∃ (n : ℕ) (h      |                      |                      |
|  : n > 0), `{.Lean}\ |                      |                      |
| `                    |                      |                      |
|    n ^ 2 = 9`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `refine `{.Lean}\    |                      |                      |
| `⟨3, _, b            |                      |                      |
| y norm_num⟩,`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `⊢ 3 > 0`{.Lean}     |                      |                      |
+----------------------+----------------------+----------------------+

## `refl`{.Lean} {#refl .unnumbered}

### Zusammenfassung {#zusammenfassung-24 .unnumbered}

Diese Taktik beweist die Gleichheit (oder Äquivalenz) zweier
definitorisch gleicher Terme.

### Beispiele {#beispiele-24 .unnumbered}

+-------------------------+----------------+-------------------------+
| **Proof state**         | **Kommando**   | **Neuer proof state**   |
+:========================+:===============+:========================+
| `⊢ P ↔ P`{.Lean} oder   | `refl,`{.Lean} | **goals accomplished ** |
+-------------------------+----------------+-------------------------+
| `⊢ P = P`{.Lean}        |                |                         |
+-------------------------+----------------+-------------------------+
| `⊢ 1 + 2 = 3`{.Lean}    |                |                         |
|                         |                |                         |
| &                       |                |                         |
|                         |                |                         |
| `refl,`{.Lean}          |                |                         |
|                         |                |                         |
| &                       |                |                         |
|                         |                |                         |
| **goals accomplished ** |                |                         |
+-------------------------+----------------+-------------------------+

### Anmerkungen {#anmerkungen-18 .unnumbered}

Das zweite Beispiel funktioniert deswegen, weil beide Seiten
definitorisch gleich `succ succ succ 0`{.Lean} sind.

## `revert`{.Lean} {#revert .unnumbered}

### Zusammenfassung {#zusammenfassung-25 .unnumbered}

`revert`{.Lean} ist das Gegenteil von `intro`{.Lean}: Es wird eine
Hypothese des lokalen Kontextes genommen, und als Voraussetzung in das
Goal eingefügt.

### Beispiele {#beispiele-25 .unnumbered}

+--------------------+--------------+-----------------------+
| **Proof state**    | **Kommando** | **Neuer proof state** |
+:===================+:=============+:======================+
| `hP : P`{.Lean}\   |              |                       |
| `⊢ Q`{.Lean}       |              |                       |
|                    |              |                       |
| &                  |              |                       |
|                    |              |                       |
| `revert hP`{.Lean} |              |                       |
|                    |              |                       |
| &                  |              |                       |
|                    |              |                       |
| `⊢ P → Q`{.Lean}   |              |                       |
+--------------------+--------------+-----------------------+

### Anmerkungen {#anmerkungen-19 .unnumbered}

`revert`{.Lean} wird selten benötigt; eigentlich nur dann, wenn man ein
bereits bewiesenes Resultat exakt anwenden möchte und erst die richtige
Form des Goals herstellen will.

## `right`{.Lean} {#right .unnumbered}

### Zusammenfassung {#zusammenfassung-26 .unnumbered}

Siehe `left`{.Lean}, wobei die Anpassungen offensichtlich sind.

### Beispiele {#beispiele-26 .unnumbered}

  **Proof state**    **Kommando**      **Neuer proof state**
  ------------------ ----------------- -----------------------
  `⊢ P ∨ Q`{.Lean}   `right,`{.Lean}   `⊢ Q`{.Lean}

## `ring`{.Lean} {#ring .unnumbered}

### Zusammenfassung {#zusammenfassung-27 .unnumbered}

Durch `ring`{.Lean} werden Rechenregeln wie Assoziatovotät,
Kommutativität, Distributivität angewandt, um das Goal zu erreichen.

### Beispiele {#beispiele-27 .unnumbered}

+------------------------------------+----------------+-------------------------+
| **Proof state**                    | **Kommando**   | **Neuer proof state**   |
+:===================================+:===============+:========================+
| `x y : ℝ`{.Lean}                   | `ring,`{.Lean} | **goals accomplished ** |
+------------------------------------+----------------+-------------------------+
| `⊢ x + y = y + x`{.Lean}[^12]      |                |                         |
+------------------------------------+----------------+-------------------------+
| `n : ℕ`{.Lean}\                    |                |                         |
| `⊢ (n+1)^2 = n^2 + 2*n + 1`{.Lean} |                |                         |
|                                    |                |                         |
| &                                  |                |                         |
|                                    |                |                         |
| `ring,`{.Lean}                     |                |                         |
|                                    |                |                         |
| &                                  |                |                         |
|                                    |                |                         |
| **goals accomplished **            |                |                         |
+------------------------------------+----------------+-------------------------+

### Anmerkungen {#anmerkungen-20 .unnumbered}

1.  Das zweite Beispiel funktioniert, obwohl `ℕ`{.Lean} kein Ring
    (sondern nur ein Halbring) ist. Es würde auch mit `n : ℝ`{.Lean}
    funktionieren (da in `ℝ`{.Lean} ja noch mehr Rechenregeln gelten als
    in `ℕ`{.Lean}.

2.  `ring`{.Lean} wird nur verwendet, um das Goal zu schließen.

## `rintro`{.Lean} {#rintro .unnumbered}

### Zusammenfassung {#zusammenfassung-28 .unnumbered}

Die `rintro`{.Lean}-Taktik wird dazu verwendet, mehrere `intro`{.Lean}-
und `cases`{.Lean}-Taktiken in einer Zeile zu verarbeiten.

### Beispiele {#beispiele-28 .unnumbered}

  **Proof state**        **Kommando**                   **Neuer proof state**
  ---------------------- ------------------------------ -----------------------
  `⊢ P ∨ Q → R`{.Lean}   `rintro ( hP | hQ ),`{.Lean}   `hP : P`{.Lean}
                         $=$                            `⊢ P`{.Lean}
                         `intro h,`{.Lean}              `hQ : Q`{.Lean}
                         `cases h with hP hQ,`{.Lean}   `⊢ Q`{.Lean}
  `⊢ P ∧ Q → R`{.Lean}   `rintro ⟨ hP , hQ ⟩,`{.Lean}   `hP : P`{.Lean}
                         $=$                            `hQ : Q`{.Lean}
                         `intro h,`{.Lean}              `⊢ Q`{.Lean}
                         `cases h with h1 h2,`{.Lean}   

### Anmerkungen {#anmerkungen-21 .unnumbered}

Hier können auch mehr als zwei `∨`{.Lean} in einem Schritt in Fälle
aufgeteilt werden: Bei `A ∨ B ∨ C`{.Lean} werden mit
`rintro (A | B | C)`{.Lean} drei Goals eingeführt.

## `rw`{.Lean} {#rw .unnumbered}

### Zusammenfassung {#zusammenfassung-29 .unnumbered}

`rw`{.Lean} steht für *rewrite*. Für `rw h`{.Lean} muss `h`{.Lean} eine
Aussage vom Typ `h : x=y`{.Lean} oder `h : A↔B`{.Lean} sein. In diesem
Fall wird durch `rw h`{.Lean} jeder Term, der syntaktisch identisch zu
`x`{.Lean} (bzw. `A`{.Lean}) ist durch `y`{.Lean} (bzw. `B`{.Lean})
ersetzt. Dies funktioniert auch, wenn `h`{.Lean} ein bereits bewiesenes
Ergebnis (also ein `lemma`{.Lean} oder `theorem`{.Lean}) ist. Mit
`rw ← h`{.Lean} wird `rw`{.Lean} von rechts nach links angewendet. (In
obigem Beispiel wird also `y`{.Lean} durch `x`{.Lean} bzw. `B`{.Lean}
durch `A`{.Lean} ersetzt.)

### Beispiele {#beispiele-29 .unnumbered}

+----------------------+----------------------+----------------------+
| **Proof state**      | **Kommando**         | **Neuer proof        |
|                      |                      | state**              |
+:=====================+:=====================+:=====================+
| `h : P ↔ Q`{.Lean}   | `rw h,`{.Lean}       | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `⊢ P`{.Lean}         |                      | `⊢ Q`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `rw ← h,`{.Lean}     | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `⊢ Q`{.Lean}         |                      | `⊢ P`{.Lean}         |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `rw h at hP,`{.Lean} | `h : P ↔ Q`{.Lean}   |
+----------------------+----------------------+----------------------+
| `hP : P`{.Lean}      |                      | `hP : Q`{.Lean}      |
+----------------------+----------------------+----------------------+
| `h : P ↔ Q`{.Lean}   | `r                   | `h : P ↔ Q`{.Lean}   |
|                      | w ← h at hQ,`{.Lean} |                      |
+----------------------+----------------------+----------------------+
| `hQ : Q`{.Lean}      |                      | `hQ : P`{.Lean}      |
+----------------------+----------------------+----------------------+
| `k m: ℕ`{.Lean}\     |                      |                      |
| `⊢ k + m + 0         |                      |                      |
|  = m + k + 0`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `                    |                      |                      |
| rw add_comm,`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `k m: ℕ`{.Lean}\     |                      |                      |
| `⊢                   |                      |                      |
| 0 + (k + m)`{.Lean}\ |                      |                      |
| `                    |                      |                      |
|  = m + k + 0`{.Lean} |                      |                      |
+----------------------+----------------------+----------------------+

  

Für die letzten vier Beispiele muss man erstmal wissen, dass
`add_comm`{.Lean} und `add_zero`{.Lean} die Aussagen

``` {.Lean mathescape="" numbersep="5pt" framesep="5mm" bgcolor="mygray"}
  add_comm : ∀ {G : Type} [_inst_1 : add_comm_semigroup G] (a b : G),
                                                               a + b = b + a
  add_zero : ∀ {M : Type} [_inst_1 : add_zero_class M] (a : M), a + 0 = a
```

sind. Im ersten der vier Beispiele wendet `rw`{.Lean} auf das erste
Vorkommen eines Terms vom Typ `a + b`{.Lean} an. Durch die interne
Klammerung steht auf der linken Seite `(k + m) + 0`{.Lean}, so dass das
`rw`{.Lean} zu einem `0 + k + m`{.Lean} führt. Will man stattdessen die
Kommutativität im Term `k + m`{.Lean} ausnutzen, so benötigt man das
zweite (bzw. dritte) Beispiel, bei dem `rw add_comm k m`{.Lean} zum
gewünschten Fortschritt führt. Im letzten Beispiel werden zunächst die
beiden `+ 0`{.Lean}-Terme durch `rw add_zero`{.Lean} beseitigt.

### Anmerkungen {#anmerkungen-22 .unnumbered}

1.  `rw`{.Lean} wird in der Praxis sehr oft verwendet, um Aussagen der
    `mathlib`{.Lean} anzuwenden (zumindest wenn Sie vom Typ `=`{.Lean}
    oder `↔`{.Lean} sind).

2.  Will man mehrere `rw`{.Lean}-Kommandos kombinieren, so kann man das
    in eckigen Klammern machen, etwa `rw [h1, h2]`{.Lean} oder
    `rw [h1, ←h2, h3]`{.Lean}.

3.  `rw`{.Lean} führt nach seiner Anwendung sofort ein `refl`{.Lean}
    durch. Das führt im zweiten und dritten Beispiel der Anwendungen von
    `add_comm`{.Lean} und `add_zero`{.Lean} dazu, dass der neue Proof
    state nicht wie angegeben ist, sondern **goals accomplished**

4.  Will man nicht der Reihe nach ein `rw`{.Lean} durchführen (wie etwa
    bei der doppelten Beseitigung des `+0`{.Lean} oben), so kann man
    mittels `nth_rewrite`{.Lean} gezielt das zweite Vorkommen eines
    Terms umschreiben.

5.  Die `rw`{.Lean}-Taktik funktioniert nicht, wenn sie nach einem
    *Binder* steht, was etwa ein `∀ ∃ ∑`{.Lean} sein kann. In diesem
    Fall hilft hoffentlich `simp_rw`{.Lean} weiter.

## `simp`{.Lean} {#simp .unnumbered}

### Zusammenfassung {#zusammenfassung-30 .unnumbered}

In `mathlib`{.Lean} gibt es viele Lemmas mit `=`{.Lean} oder
`↔`{.Lean}-Aussagen, die mit `rw`{.Lean} angewendet werden können und
mit `@[simp]`{.Lean} gekennzeichnet sind. Diese gekennzeichneten Lemmas
haben die Eigenschaft, dass auf der rechten Seite eine vereinfachte Form
der linken Seite steht. Bei `simp`{.Lean} sucht `lean`{.Lean} nach
passenden Lemmas und versucht sie anzuwenden.

### Beispiele {#beispiele-30 .unnumbered}

+----------------------------+--------------+-----------------------+
| **Proof state**            | **Kommando** | **Neuer proof state** |
+:===========================+:=============+:======================+
| `⊢ n + 0 = n`{.Lean} [^13] |              |                       |
|                            |              |                       |
| &                          |              |                       |
|                            |              |                       |
| `simp,`{.Lean}             |              |                       |
|                            |              |                       |
| &                          |              |                       |
|                            |              |                       |
| **goals accomplished **    |              |                       |
+----------------------------+--------------+-----------------------+

### Anmerkungen {#anmerkungen-23 .unnumbered}

Will man wissen welche Lemmas genau angewendet wurden, so versucht man
es mit `simp?`{.Lean} oder `squeeze_simp`{.Lean}. Dies liefert Hinweise.

+---------------------------------+--------------+-----------------------+
| **Proof state**                 | **Kommando** | **Neuer proof state** |
+:================================+:=============+:======================+
| `⊢ n + 0 = n`{.Lean}            |              |                       |
|                                 |              |                       |
| &                               |              |                       |
|                                 |              |                       |
| `simp?,`{.Lean}                 |              |                       |
|                                 |              |                       |
| &                               |              |                       |
|                                 |              |                       |
| **goals accomplished **\        |              |                       |
| Try this:\                      |              |                       |
| `simp only [add_zero, `{.Lean}\ |              |                       |
| `     eq_self_iff_true]`{.Lean} |              |                       |
+---------------------------------+--------------+-----------------------+

## `specialize`{.Lean} {#specialize .unnumbered}

  **Proof state**               **Kommando**                **Neuer proof state**
  ----------------------------- --------------------------- -----------------------
  `f : ℕ → Prop`{.Lean}         `specialize h 13,`{.Lean}   `f: ℕ → Prop`{.Lean}
  `h : ∀ (n : ℕ), f n`{.Lean}                               `h : f 13`{.Lean}
  `⊢ P`{.Lean}                                              `⊢ P`{.Lean}

### Zusammenfassung {#zusammenfassung-31 .unnumbered}

Bei einer Hypothese `h : ∀ n, ...`{.Lean} gilt `...`{.Lean} für alle
`n`{.Lean}, aber für den Beweis des Goals benötigt man eventuell ja nur
ein bestimmtes `n`{.Lean}. Gibt man `specialize h`{.Lean} gefolgt von
dem Wert an, für den `h`{.Lean} benötit wird, ändert sich die Hypothese
entsprechend.

### Beispiele {#beispiele-31 .unnumbered}

+-----------------------------------+--------------+-----------------------+
| **Proof state**                   | **Kommando** | **Neuer proof state** |
+:==================================+:=============+:======================+
| `h: ∀ (n : ℕ), 0 < n + 1`{.Lean}\ |              |                       |
| `⊢ 0 < 1`{.Lean}                  |              |                       |
|                                   |              |                       |
| &                                 |              |                       |
|                                   |              |                       |
| `specialize h 0,`{.Lean}          |              |                       |
|                                   |              |                       |
| &                                 |              |                       |
|                                   |              |                       |
| `m : ℕ`{.Lean}\                   |              |                       |
| `h: 0 < 0 + 1`{.Lean}\            |              |                       |
| `⊢ 0 < 1`{.Lean}                  |              |                       |
+-----------------------------------+--------------+-----------------------+

### Anmerkungen {#anmerkungen-24 .unnumbered}

1.  Genau wie bei `use`{.Lean} muss man aufpassen, dass das Goal
    beweisbar bleibt.

2.  Will man zwei Werte der Hypothese `h`{.Lean} verwendet, so liefert
    `let h' := h`{.Lean} zunächst eine Verdopplung der Hypothese, so
    dass man anschließend `specialize`{.Lean} auf `h`{.Lean} und
    `h'`{.Lean} anwenden kann.

## `split`{.Lean} {#split .unnumbered}

### Zusammenfassung {#zusammenfassung-32 .unnumbered}

Ist das Goal vom Typ `⊢ P ∧ Q`{.Lean}, so wird es durch `split`{.Lean}
in zwei Goals `⊢ P`{.Lean} und `⊢ Q`{.Lean} ersetzt.

### Beispiele {#beispiele-32 .unnumbered}

  **Proof state**    **Kommando**      **Neuer proof state**
  ------------------ ----------------- -----------------------
  `⊢ P ∧ Q`{.Lean}   `split,`{.Lean}   `⊢ P`{.Lean}
                                       `⊢ Q`{.Lean}
  `⊢ P ↔ Q`{.Lean}   `split,`{.Lean}   `⊢ P → Q`{.Lean}
                                       `⊢ Q → P`{.Lean}

### Anmerkungen {#anmerkungen-25 .unnumbered}

Man beachte, dass `⊢ P ↔ Q`{.Lean} identisch ist zu
`⊢ (P → Q) ∧ (Q → P)`{.Lean} ist.

## `tauto`{.Lean} {#tauto .unnumbered}

### Zusammenfassung {#zusammenfassung-33 .unnumbered}

`tauto`{.Lean} löst alle Goals, die mit einer Wahrheitstabelle lösbar
sind.

### Beispiele {#beispiele-33 .unnumbered}

+----------------------+----------------------+----------------------+
| **Proof state**      | **Kommando**         | **Neuer proof        |
|                      |                      | state**              |
+:=====================+:=====================+:=====================+
| `⊢ P                 | `tauto,`{.Lean} oder | **goals accomplished |
| ∧ Q → P`{.Lean}[^15] | `tauto!,`{.Lean}     | **                   |
+----------------------+----------------------+----------------------+
| `⊢ ((P →             |                      |                      |
|  Q) → P) → P`{.Lean} |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| `tauto!, `{.Lean}    |                      |                      |
|                      |                      |                      |
| &                    |                      |                      |
|                      |                      |                      |
| **goals accomplished |                      |                      |
| **                   |                      |                      |
+----------------------+----------------------+----------------------+

Die Wahrheitstabellen für `¬P`{.Lean}, `P ∧ Q`{.Lean}
bzw. `P ∨ Q`{.Lean} sehen wiefolgt aus; sind mehr Terme vom Typ
`Prop`{.Lean} involviert, gibt es mehr Zeilen.

::: center
  `P`{.Lean}       `¬P`{.Lean}
  ---------------- ----------------
  `true`{.Lean}    `false`{.Lean}
  `false`{.Lean}   `true`{.Lean}

  `P`{.Lean}       `Q`{.Lean}       `(P ∧ Q)`{.Lean}
  ---------------- ---------------- ------------------
  `true`{.Lean}    `true`{.Lean}    `true`{.Lean}
  `false`{.Lean}   `true`{.Lean}    `false`{.Lean}
  `true`{.Lean}    `false`{.Lean}   `false`{.Lean}
  `false`{.Lean}   `false`{.Lean}   `false`{.Lean}

  `P`{.Lean}       `Q`{.Lean}       `(P ∨ Q)`{.Lean}
  ---------------- ---------------- ------------------
  `true`{.Lean}    `true`{.Lean}    `true`{.Lean}
  `false`{.Lean}   `true`{.Lean}    `true`{.Lean}
  `true`{.Lean}    `false`{.Lean}   `true`{.Lean}
  `false`{.Lean}   `false`{.Lean}   `false`{.Lean}
:::

### Anmerkungen {#anmerkungen-26 .unnumbered}

Der Unterschied zwischen `tauto`{.Lean} und `tauto!`{.Lean} ist, dass
bei letzterer Taktik die Regel des ausgeschlossenen Dritten zugelassen
ist. Das zweite Beispiel ist deshalb nur mit `tauto!`{.Lean}, aber nicht
mit `tauto`{.Lean} lösbar.

## `triv`{.Lean} {#triv .unnumbered}

### Zusammenfassung {#zusammenfassung-34 .unnumbered}

`triv`{.Lean} löst ein Ziel, das definitorisch identisch zu
`true`{.Lean} ist. Es löst ebenfalls Ziele, die mit `refl`{.Lean} lösbar
sind.

### Beispiele {#beispiele-34 .unnumbered}

+-------------------------+----------------+-------------------------+
| **Proof state**         | **Kommando**   | **Neuer proof state**   |
+:========================+:===============+:========================+
| `⊢ true`{.Lean}         | `triv,`{.Lean} | **goals accomplished ** |
+-------------------------+----------------+-------------------------+
| `⊢ x=x`{.Lean}          |                |                         |
|                         |                |                         |
| &                       |                |                         |
|                         |                |                         |
| `triv,`{.Lean}          |                |                         |
|                         |                |                         |
| &                       |                |                         |
|                         |                |                         |
| **goals accomplished ** |                |                         |
+-------------------------+----------------+-------------------------+

## `use`{.Lean} {#use .unnumbered}

  **Proof state**             **Kommando**      **Neuer proof state**
  --------------------------- ----------------- -----------------------
  `f : α → Prop`{.Lean}       `use y,`{.Lean}   `f : α → Prop`{.Lean}
  `y : α`{.Lean}                                `y : α`{.Lean}
  `⊢ ∃ (x : α), f x`{.Lean}                     `⊢ f y`{.Lean}

### Zusammenfassung {#zusammenfassung-35 .unnumbered}

Die `use`{.Lean}-Taktik kommt bei Goals zum Einsatz, die mit ∃ beginnen.
Hier wird durch Paramtere gesagt, welches durch ∃ quantifizierte Objekt
denn im Beweis weiter verwendet werden soll.

### Beispiele {#beispiele-35 .unnumbered}

+----------------------------------+--------------+-----------------------+
| **Proof state**                  | **Kommando** | **Neuer proof state** |
+:=================================+:=============+:======================+
| `⊢ ∃ (k : ℕ), k * k = 16`{.Lean} |              |                       |
|                                  |              |                       |
| &                                |              |                       |
|                                  |              |                       |
| `use 4, `{.Lean}                 |              |                       |
|                                  |              |                       |
| &                                |              |                       |
|                                  |              |                       |
| `⊢ 4 * 4 = 16`{.Lean}            |              |                       |
+----------------------------------+--------------+-----------------------+

### Anmerkungen {#anmerkungen-27 .unnumbered}

1.  Man muss aufpassen, dass das Goal durch die Verwendung von
    `use`{.Lean} beweisbar (insbesondere wahr) bleibt. Im ersten Fall
    unter Beispiele hätten wir ja auch `use 3`{.Lean} schreiben können,
    und `3 * 3 = 16`{.Lean} ist nicht beweisbar.

2.  Man kann gleichzeitig mehr als eine Variable durch `use`{.Lean}
    angeben. Dies geschieht in eckigen Klammern; siehe das letzte
    Beispiel.

[^1]: \...oder ein anderes Statement, das mit Wahrheitstabellen lösbar
    ist.

[^2]: \...oder ein anderes Statement, das nur Rechnungen mit numerischen
    Werte beinhaltet.

[^3]: \...oder ein anderes Statement, das nur Rechenregeln von
    kommutativen Ringen verwendet. `ring`{.Lean} zieht Hypothesen nicht
    in Betracht.

[^4]: \...oder eine Aussage, die nur `<`{.Lean}, `≤`{.Lean}, `≠`{.Lean}
    oder `=`{.Lean} verwendet. `linarith`{.Lean} zieht Hypothesen in
    Betracht.

[^5]: \...oder ein anderes Statement, das mit Wahrheitstabellen lösbar
    ist.

[^6]: \...oder ein anderes Statement, das nur Rechnungen mit numerischen
    Werte beinhaltet.

[^7]: \...oder ein anderes Statement, das nur Rechenregeln von
    kommutativen Ringen verwendet. `ring`{.Lean} zieht Hypothesen nicht
    in Betracht.

[^8]: \...oder eine Aussage, die nur `<`{.Lean}, `≤`{.Lean}, `≠`{.Lean}
    oder `=`{.Lean} verwendet. `linarith`{.Lean} zieht Hypothesen in
    Betracht.

[^9]: \...oder eine Aussage, die nur `<`{.Lean}, `≤`{.Lean}, `≠`{.Lean}
    oder `=`{.Lean} verwendet. `linarith`{.Lean} zieht Hypothesen in
    Betracht.

[^10]: \...oder ein anderes Statement, das nur Rechnungen mit
    numerischen Werte beinhaltet.

[^11]: \...oder ein anderes Statement, das nur Rechnungen mit
    numerischen Werte beinhaltet.

[^12]: \...oder ein anderes Statement, das nur Rechenregeln von
    kommutativen Ringen verwendet. `ring`{.Lean} zieht Hypothesen nicht
    in Betracht.

[^13]: \...[]{#foot:simp label="foot:simp"}oder ein anderes Statement,
    das sich durch Äquivalenz-Aussagen der Bibliothek vereinfachen
    lassen.

[^14]: \...oder ein anderes Statement, das mit Wahrheitstabellen lösbar
    ist.

[^15]: \...oder ein anderes Statement, das mit Wahrheitstabellen lösbar
    ist.
