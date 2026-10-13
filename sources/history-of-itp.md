# The history in Chapter 0

What the three history sections of
[`Leancourse/Coursenotes/00-Introduction.lean`](../Leancourse/Coursenotes/00-Introduction.lean)
rest on: *Before there were machines*, *1936: what a machine cannot do*
and *The first proof assistants*.

`free` means a PDF is one click away. `library` means it is behind a
paywall or only on paper. A filename in `code` is a copy lying in this
folder (not committed -- see [README.md](README.md)).

## In this folder

    debruijn-1968-automath-th-report.pdf
    geuvers-2009-proof-assistants.pdf
    harrison-urban-wiedijk-2014-history-of-itp.pdf
    kamareddine-2022-automath-proof-checker.pdf
    milner-1972-lcf-stanford-aim-169.pdf
    paulson-nipkow-wenzel-2019-lcf-to-isabelle.pdf
    turing-1936-computable-numbers.pdf
    wiedijk-2006-seventeen-provers.pdf
    waseda-sils-turing-foundations-slides.pdf

## Start here

* **John Harrison, Josef Urban, Freek Wiedijk, "History of Interactive
  Theorem Proving".** In Jörg Siekmann (ed.), *Handbook of the History
  of Logic*, vol. 9: *Computational Logic*, Elsevier 2014, pp. 135-214.
  `free`, <https://www.cl.cam.ac.uk/~jrh13/papers/joerg.pdf>
  `harrison-urban-wiedijk-2014-history-of-itp.pdf`
  The standard reference, ~80 pages, written by three people who built
  the systems. Covers everything below in order.
* **Lawrence C. Paulson, "50 years of proof assistants".** Blog post,
  5 December 2025.
  `free`, <https://lawrencecpaulson.github.io//2025/12/05/History_of_Proof_Assistants.html>
  First-hand on the LCF line: Stanford LCF 1972, Edinburgh 1975,
  Cambridge 1982, HOL, Isabelle. The dates in the *first proof
  assistants* section come from here.
* **Herman Geuvers, "Proof assistants: history, ideas and future".**
  *Sadhana* 34 (2009), no. 1, 3-25.
  `free`, <https://www.ias.ac.in/public/Volumes/sadh/034/01/0003-0025.pdf>
  `geuvers-2009-proof-assistants.pdf`
  Shorter, and organized by idea rather than by year.

## The formalization programme

* **"Alan Turing and the Foundations of Computer Science".** Lecture
  slides, course MI314, History of Mathematics, SILS, Waseda
  University; 38 pages, no author named on the file.
  `local copy only` -- teaching slides, not a citable source, and not
  cited in the notes.
  The first half is the model for the shape of *Where the ideas come
  from*: the four metamathematical properties (independent,
  consistent, complete, decidable), 1900 and the *ignorabimus*, the
  1929 completeness theorem before the 1931 incompleteness theorems,
  and the diagonal argument as the thread from Cantor through Gödel to
  Turing. The second half (Shannon, Boolean circuits, wartime
  machines) is about computers and is not used.
  **One error in it, not copied:** slide 10 is headed "Hilbert's
  Problem 10 (the Entscheidungsproblem)". Hilbert's tenth problem of
  1900 is the solvability of Diophantine equations, settled by
  Matiyasevich in 1970. The Entscheidungsproblem is a different
  question, posed in Hilbert-Ackermann 1928.
* **Giuseppe Peano, *Arithmetices principia, nova methodo exposita*.**
  Bocca, Turin 1889. Public domain. Used for: zero, successor and
  induction, the shape Lean's `Nat` still has.
* **Gottlob Frege, *Begriffsschrift*.** Nebert, Halle 1879. Public
  domain. Used for: proofs as objects one can calculate with.
* **Bertrand Russell, letter to Frege, 16 June 1902.** Printed in Jean
  van Heijenoort (ed.), *From Frege to Gödel*, Harvard UP 1967,
  pp. 124-125. `library`
* **A. N. Whitehead, B. Russell, *Principia Mathematica*.** 3 vols.,
  Cambridge UP 1910-1913. `free` (vol. I, University of Michigan
  Historical Math Collection).
  `1 + 1 = 2` is ✱110.643 in **volume II**, and "The above proposition
  is occasionally useful" is the remark under it -- checked, because
  the line is often mis-attributed to ✱54.43 in volume I, which says
  something else.
* **David Hilbert, Wilhelm Ackermann, *Grundzüge der theoretischen
  Logik*.** Springer 1928. `library`
  Where the *Entscheidungsproblem* is posed. Worth having in the
  original if the exact wording is ever quoted; the notes only
  paraphrase it.
* **Kurt Gödel, "Über formal unentscheidbare Sätze der Principia
  Mathematica und verwandter Systeme I".** *Monatshefte für Mathematik
  und Physik* 38 (1931), 173-198. `free` via GDZ / Springer.
* **Kurt Gödel, "Über die Vollständigkeit des Logikkalküls".**
  Dissertation, Vienna 1929; published as "Die Vollständigkeit der
  Axiome des logischen Funktionenkalküls", *Monatshefte für Mathematik
  und Physik* 37 (1930), 349-360. `library`
  The completeness theorem, which is what makes proof search
  semi-decidable. Not downloaded; the notes only state it.
* **David Hilbert, "Axiomatisches Denken".** Lecture, Zurich,
  11 September 1917; *Mathematische Annalen* 78 (1918), 405-415.
  `library`
  Also the 1900 Paris address, for "denn in der Mathematik gibt es
  kein Ignorabimus".

## 1936

* **Alonzo Church, "An Unsolvable Problem of Elementary Number
  Theory".** *American Journal of Mathematics* 58 (1936), 345-363.
  `library` (JSTOR). Submitted 15 April 1936.
* **Alonzo Church, "A Note on the Entscheidungsproblem".** *Journal of
  Symbolic Logic* 1 (1936), 40-41, with a correction at 101-102.
  `library`
* **Alan M. Turing, "On Computable Numbers, with an Application to the
  Entscheidungsproblem".** *Proceedings of the London Mathematical
  Society* (2) 42 (1936-37), 230-265; correction 43 (1937), 544-546.
  `free`, <https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf>
  `turing-1936-computable-numbers.pdf`
  The appendix proves that his machines and Church's lambda terms
  compute the same functions -- that is the sentence in the notes.
* **"Alonzo Church", Stanford Encyclopedia of Philosophy**, supplement
  on the Entscheidungsproblem. `free`,
  <https://plato.stanford.edu/entries/church/supplementA.html>
  Useful for the chronology of who knew what in 1936.

## Curry-Howard and Automath

* **N. G. de Bruijn, "AUTOMATH, a language for mathematics".**
  TH-Report 68-WSK-05, Technological University Eindhoven, November
  1968.
  `free`, <https://pure.tue.nl/ws/portalfiles/portal/2039924/256169.pdf>
  `debruijn-1968-automath-th-report.pdf`
  De Bruijn began in 1967 and published in 1968; the notes say both,
  because sources differ on which year to name.
* **L. S. van Benthem Jutting, "Checking Landau's *Grundlagen* in the
  AUTOMATH system".** Thesis, Eindhoven 1977. `library`
  Not found as a single PDF; the machine verification was finished in
  September 1975, the thesis defended on 1 March 1977.
* **Fairouz Kamareddine et al., "Characteristics of de Bruijn's early
  proof checker Automath".** *Fundamenta Informaticae* 185 (2022),
  313-336, arXiv:2203.01173. `free`
  `kamareddine-2022-automath-proof-checker.pdf`
  What Automath actually did, read back from the sources.
* **H. B. Curry, R. Feys, *Combinatory Logic I*.** North-Holland 1958.
  `library` Where the correspondence is stated for implication.
* **W. A. Howard, "The formulae-as-types notion of construction".**
  Written 1969, printed in *To H. B. Curry*, Academic Press 1980,
  pp. 479-490. `free` in circulation.

## Type theory

For *Where types come from* in `01-Lean/02-Types.lean`. None of
these is downloaded; the section only states the dates.

* **Bertrand Russell, "Mathematical Logic as Based on the Theory of
  Types".** *American Journal of Mathematics* 30 (1908), 222-262.
  `free` (JSTOR / public domain). Where types are invented, as a
  repair of the paradox of 1902. Sketched already in Appendix B of
  *The Principles of Mathematics*, 1903.
* **Frank Ramsey, "The Foundations of Mathematics".** *Proc. LMS* 25
  (1926), 338-384, and Leon Chwistek, *The Theory of Constructive
  Types*, 1921-1923. The simple theory of types, without Russell's
  ramification.
* **Alonzo Church, "A Formulation of the Simple Theory of Types".**
  *Journal of Symbolic Logic* 5 (1940), 56-68. `library`
  The simply typed lambda calculus; the foundation Isabelle/HOL still
  uses. Prompted by S. C. Kleene and J. B. Rosser, "The Inconsistency
  of Certain Formal Logics", *Annals of Mathematics* 36 (1935),
  630-636, which broke Church's untyped system of 1932.
* **Per Martin-Löf, *Intuitionistic Type Theory*.** Bibliopolis 1984,
  after preprints from 1971. `free` (several scans circulate).
  Dependent types. The 1971 version had `Type : Type` and was
  inconsistent by Girard's paradox; the universe hierarchy is the
  repair.
* **Thierry Coquand, Gérard Huet, "The Calculus of Constructions".**
  *Information and Computation* 76 (1988), 95-120; presented 1985.
  `free` via INRIA. With Thierry Coquand and Christine Paulin-Mohring,
  "Inductively defined types", COLOG-88, LNCS 417 (1990), 50-66, this
  is what Lean's type theory is a variant of.

## The systems

* **Robin Milner, "Logic for Computable Functions: description of a
  machine implementation".** Stanford AI Memo AIM-169, 1972.
  `free`, but only over plain HTTP; the host has no HTTPS at all, so the
  notes link the Wayback copy
  <https://web.archive.org/web/20240703134244/http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf>
  `milner-1972-lcf-stanford-aim-169.pdf`
* **M. Gordon, R. Milner, C. Wadsworth, *Edinburgh LCF*.** LNCS 78,
  Springer 1979. `library`
* **Lawrence C. Paulson, Tobias Nipkow, Makarius Wenzel, "From LCF to
  Isabelle/HOL".** arXiv:1907.02836. `free`
  `paulson-nipkow-wenzel-2019-lcf-to-isabelle.pdf`
  Where `thm` as an abstract data type is explained, and why it makes
  the rest of the system untrusted code.
* **Freek Wiedijk, "The Seventeen Provers of the World".** LNAI 3600,
  Springer 2006.
  `free`, <https://www.cs.ru.nl/~freek/comparison/comparison.pdf>
  `wiedijk-2006-seventeen-provers.pdf`
  The same theorem in seventeen systems, and the source usually given
  for the *de Bruijn criterion*.

## Still missing

Two things the notes mention in passing and nothing here covers:

* John Harrison's 1996 thesis *Theorem Proving with the Real Numbers*,
  which is what made Flyspeck possible.
* The Mizar library, for which Trybulec 1973 is the usual citation but
  the readable account is in the Harrison-Urban-Wiedijk chapter above.

## Cited in the notes

The *Sources* section at the end of
[`00-Introduction.lean`](../Leancourse/Coursenotes/00-Introduction.lean)
lists the three surveys and the six originals, and says which four
items are only paraphrased because they are not freely available.
