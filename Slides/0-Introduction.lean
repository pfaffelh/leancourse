import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the first lecture (week 1, Monday).  It follows the
Introduction of the course notes section by section, so the two can be
shown together: what formalizing means, where things stand in 2026, how
it got there, the landmark projects, and what the course asks of you.
-/

#doc (Slides) "Why formalize?" =>

```css
img.portrait {
  width: 16vh; height: 16vh; object-fit: cover; object-position: 50% 20%;
  border-radius: 50%; margin: 0 0.35rem; vertical-align: middle;
  box-shadow: 0 1px 5px rgba(0, 0, 0, 0.2);
}
/* These two have to outrank `.reveal section p` below, which is why
   they are written out this long. */
.reveal section p.names, .reveal section .names p {
  font-size: 0.45em; color: #52514e; letter-spacing: 0.02em;
  margin: 0.1em 0; }
/* caption under a chart, saying what is plotted */
.reveal section p.caption, .reveal section .caption p {
  font-size: 0.42em; color: #52514e; margin: 0.2em 0 0;
  line-height: 1.35; }
.reveal section img { margin: 0.4rem 0; }
/* reveal's default body size overflows a slide with four or five
   lines under a picture; this is the single knob for that */
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
/* picture and faces share one horizontal band, directly under the
   heading, so the slide does not grow downwards */
.reveal .r-hstack { align-items: center; justify-content: center;
                    gap: 1.6rem; margin-bottom: 0.3rem; }
.reveal .r-hstack > * { margin: 0; }
/* a portrait keeps its name directly underneath, inside the band */
.reveal .r-hstack .r-vstack { gap: 0; }
.reveal .r-vstack > * { margin: 0; }
/* the punch line of a slide, in blue. The deck has no fragments:
   every slide is complete when it appears, one key press per slide. */
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section img.logo { height: 9vh; width: auto; margin: 0 1.2rem; }
/* the seven goals, copied from the notes: they only fit at this size */
.reveal section .goals li { font-size: 0.56em; line-height: 1.3;
                            margin: 0.35em 0; text-align: left; }
.reveal section .goals ul { width: 92%; margin: 0.2em auto; }
/* Picture heights in slide pixels, never in `vh`: reveal.js scales the
   slide with a CSS transform, while `vh` is measured against the browser
   window and escapes that scaling, so a `vh` height changes size relative
   to the slide whenever the projector's aspect ratio does. */
.reveal section img.chart { height: 280px; width: auto; }
.reveal section img.chart-arxiv { height: 240px; }
.reveal section img.lineage { height: 336px; width: auto; }
.reveal section img.inlinepic { height: 140px; width: auto; }
.reveal section img.kepler { height: 154px; }
/* a comparison table has to leave room for the lines under it */
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
```

# Why formalize?

Interactive theorem proving with Lean — first lecture.

:::notes
Title slide. The question in the heading is the one the next twenty
minutes answer.
:::

# What formalizing means

Write the proof in a language precise enough for a machine to check every step.

*Autoformalizing* runs the other way — informal mathematics in, formal text out.

:::notes
That is the definition. The machine does not *find* the proof; it reads
yours and checks it, and anything left out is refused.

Both directions end in the same place: a text the kernel accepts. The
program that writes a proof may be unreliable in any way it likes; the
program that checks it is small and fixed. That asymmetry is why any of
this works, and it comes back later as the de Bruijn criterion.

This course is about the first direction. They write the proofs.
:::

# 2026

:::hstack
{image "../static/figures/logos/claude.png" (class := "logo")}[Claude] {image "../static/figures/logos/chatgpt.png" (class := "logo")}[ChatGPT]
:::

*Feb* — sphere packing, dimension 8: a machine finishes it in five days.

*4 Sep* — Fermat's Last Theorem, checked. 11 days, 13 M lines of Lean.

*8 Sep* — Navier-Stokes with a force: a singularity in finite time.

*6 Oct* — 719 manuscripts, 42 % with a Lean proof.

:::notes
FLT: Anthropic, Claude, building on Mathlib, following a simplified
Wiles. Buzzard confirmed it assumes nothing but the axioms.

Navier-Stokes: the *forced* equation. Not the Millennium problem.
The prize is unclaimed. Say this plainly.

February first, and it is the cleanest case: the statement was
settled mathematics, only the formalizing was left. The autoformalizer
is Gauss, from Math Inc.; the human project it joined had been running
since 2024.

One day after that catalogue, three of its manuscripts were withdrawn
over a sign error, and fourteen more were revised. None of the
withdrawn ones had a Lean proof. Say it; do not put it on the slide.

Machines now produce mathematics faster than mathematicians can
referee it, and the only check that keeps up is a formal one. Do not
oversell it — the next slide takes it back a step.
:::

# But be precise

A Lean proof certifies that *a formal statement* follows from the axioms.

Whether that statement is the theorem in the paper is a *human* question.

:::class "key"
Reading a formal statement and judging what it says is most of what
this course teaches.
:::

:::notes
OpenAI's repository documents, per paper, which checks cover a main
theorem and which only a supporting result.
:::

# Where people are going

{image "../static/figures/itp_github_repos_per_million.png" (class := "chart")}[New GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle, 2018 to 2026]

:::class "caption"
New GitHub repositories per quarter for the three large proof
assistants, counted per million new repositories overall.
:::

:::notes
Per million, because GitHub itself grew steeply in 2026. One
distortion is left in: the Justin Sun Prize pays only against a
machine-verified proof, and about a fifth of September's new Lean
repositories carry a prize identifier.

Until about 2023 the three were comparable, and Coq was the larger.

Not evidence that Lean is better. Isabelle's automation is still
ahead in places; Rocq has decades of verified software behind it.
Evidence about where people are going.
:::

# Papers checked in Lean

{image "../static/figures/arxiv_lean_formalized_share.png" (class := "chart chart-arxiv")}[Share of arXiv mathematics papers with a Lean-checked result during 2026, per 100 submissions]

:::class "caption"
Papers on the mathematics arXiv whose results are checked in Lean,
per 100 submissions, by week of submission in 2026.
:::

:::class "key"
The denominator doubled too: about 1 000 submissions a week in January, about 2 500 in October.
:::

:::notes
A share, not a count: a rising count would partly be that growth in
submissions, which is itself worth a sentence.

The highest bar so far: 62 of 2 567 papers in the first week of
October, 2.4 per 100; the week after, 48 of 2 366, 2.0 per 100.
One week, so not a trend by itself.

Within a few years, reading and writing a formal proof will be
ordinary equipment. This is the answer to "why spend a semester on
this".
:::

# How we got here

*1879-1936* — the mathematics. A proof becomes a finite string, and checking one becomes a decidable question.

*1967-2013* — the machines: from Automath to Lean.

*1976-2025* — what was done with them.

:::class "key"
The idea is 150 years old; the tool is 13.
:::

:::notes
The order is chronological. First the mathematics, which needed from
Frege to Turing to turn a proof into a finite object a machine can
inspect. Then the machines.

Not chronology for its own sake: each episode adds a different
reason. What a computer proof is worth, where peer review stops,
whether an author can trust himself, who is asking for this now.

If the hour is short, the mathematics block is the part to cut.
:::

# Frege and Russell

::::::hstack
::::vstack
{image "../static/figures/portraits/frege.jpg" (class := "portrait")}[Gottlob Frege]

:::class "names"
Gottlob Frege
:::
::::

::::vstack
{image "../static/figures/portraits/russell.jpg" (class := "portrait")}[Bertrand Russell]

:::class "names"
Bertrand Russell
:::
::::
::::::

*1879* — Frege makes proofs into objects you can calculate with.

*1902* — Russell's letter: the set of all sets that are not members of themselves.

*1910-13* — *Principia Mathematica* rebuilds. `1 + 1 = 2` arrives in volume two.

:::notes
The mathematics block. Where the `fun` in `fun x => x + 1` comes
from, and why the machine checks instead of searching.

Frege's *Begriffsschrift*, 1879: the first system in which a proof is
itself an object you can manipulate. His two-dimensional notation was
never adopted; Peano's linear one was, and Russell took it from him.
That logic is not what breaks.

What Russell's letter of 1902 breaks is the later *Grundgesetze der
Arithmetik*, where Frege derived arithmetic from that logic using one
further axiom: concepts with the same instances have the same
extension.

Peano's axioms are deliberately not on this slide; they belong where
`Nat` is introduced. Whitehead and Russell then spend
*Principia Mathematica* rebuilding, and the proof that `1 + 1 = 2`
comes with the note that "the above proposition is occasionally
useful".

Done by hand, formalization is unbearable. For most of a century
little came of it.
:::

# Two repairs, 1908

*Impredicative:* an object is defined by quantifying over a collection that contains it. $`R = \{x : x \notin x\}` is such a definition — the condition ranges over all sets, and $`R` would be one of them.

:::table +colHeaders +rowSeps
*
  * 1908
  * forbids it by restricting
  * so you may form
  * `x ∈ x` is
*
  * Zermelo
  * what *exists*
  * $`\{x \in A : x \notin x\}`, never $`\{x : x \notin x\}`
  * well-formed, and false
*
  * Russell
  * what may be *said*
  * neither: $`x \notin x` is not a formula
  * no statement at all
:::

Zermelo's set is harmless: $`R = \{x \in A : x \notin x\}` gives $`R \notin R`, hence $`R \notin A`. No set contains all sets.

:::class "key"
Mathematics went with Zermelo, proof assistants with Russell.
:::

:::notes
The whole reason this course is about types.

Zermelo replaces unrestricted comprehension by separation, so the
paradoxical set is never formed. The language is untouched: `x in x`
stays a well-formed formula, and that it is false for every set is
the axiom of foundation, added by von Neumann in 1925 and Zermelo in
1930 — later, and not the repair.

Russell stratifies the grammar. `x in x` is not a false statement but
no statement at all, so well-formedness is a question about syntax
and is decidable. That is what a type checker decides, and it is why
Lean has `Type 0 : Type 1 : ...` and no type of all types.

Both hierarchies exist; the difference is who enforces them. In set
theory the cumulative hierarchy is a theorem about which sets there
are, and you may write the bad expression and then prove it denotes
nothing. In type theory you do not get that far.

The word comes back. In Lean it is a property of a *sort*: `Prop` is
impredicative because `∀ x : A, B x` is again a `Prop` for every
domain `A`, however large — `A := Prop` included. `Type u` is
predicative: the same shape climbs to the next universe. So Lean
neither follows Zermelo nor Russell wholesale. It grants the circle
for propositions and refuses it for data, which is why the supremum
of a set of reals is unproblematic and `Type : Type` is not. That is
the Types chapter; here just say that the third answer exists.
:::

# Hilbert's programme, 1917

::::vstack
{image "../static/figures/portraits/hilbert.jpg" (class := "portrait")}[David Hilbert]

:::class "names"
David Hilbert
:::
::::

Fix the language, fix the rules. A proof becomes a finite string, and checking it is a question about symbols.

*Consistent?* — no contradiction follows from the axioms.

*Complete?* — for every statement, it or its negation follows.

*Decidable?* — a procedure settles which of the two.

:::class "key"
Hilbert wants all three.
:::

:::notes
Hilbert pushes this from a lecture of 1917, *Axiomatisches Denken*, on
through the 1920s. The conviction is older: Paris 1900, "denn in der
Mathematik gibt es kein Ignorabimus" — no question we are condemned
never to settle.

The formalization half is exactly what a proof assistant does. A proof
is a finite object, and whether it follows the rules can be decided
without knowing what the symbols mean.

The consistency proof was to use finitary means only — no appeal to
the infinite objects whose consistency was in question.
:::

# Gödel, 1929 and 1931

::::vstack
{image "../static/figures/portraits/godel.jpg" (class := "portrait")}[Kurt Gödel]

:::class "names"
Kurt Gödel
:::
::::

*First-order:* quantifiers range over the *elements* of one domain, never over its subsets — so "every bounded set of reals has a supremum" is not first-order.

:::table +colHeaders +rowSeps
*
  * Gödel
  * about
  * result
*
  * 1929
  * first-order logic
  * complete: valid in every model is derivable
*
  * 1931
  * any theory containing arithmetic
  * incomplete: some truth about ℕ is neither proved nor refuted
:::

:::class "key"
Lean quantifies over types and propositions. 1929 does not apply.
:::

:::notes
Two theorems, opposite directions, by the same person.

A *model* of a set of axioms is a structure in which all of them
hold: the integers under addition are a model of the group axioms.

1929, his thesis: first-order logic is complete. What holds in every
model is derivable. Logic itself is not the obstacle.

The definition is on the slide. The point of the second example is
that "every bounded *set* of reals" quantifies over subsets of the
domain, not over its elements — that is exactly the step out of
first order. Completeness of the reals is therefore not a first-order
statement, and the reals have nonstandard models.

Why the restriction buys anything: for first-order logic the proofs
can be enumerated, so a search that will succeed does succeed. That
is the second row of the table two slides on, and the reason `exact?`
and `grind` terminate when there is something to find.

Lean is not first-order — it quantifies over types and over
propositions — so the completeness theorem does not apply to it. Say
that; it matters again when the Types chapter builds a model by hand.

Watch the word *complete*, which does two jobs. A *logic* is complete
when everything valid is derivable; a *theory* is complete when it
decides every statement. 1929 is the first, Hilbert's second question
and 1931 are the second. No conflict: the axioms of arithmetic also have
nonstandard models, with elements beyond 0, 1, 2, .... Gödel's
sentence, "no number codes a proof of me", is true in ℕ and false in
some such model. So it is not valid, and 1929 says nothing about it.

1931: the incompleteness theorems. Any consistent system containing
arithmetic, with axioms a machine can list, misses true statements
about the naturals, and cannot prove its own consistency. The
programme fails; the formalization stays.

Gödel's proof is itself the first serious piece of formalization: he
encodes formulas and proofs as numbers and computes with them. Proofs
as data. It is Cantor's diagonal argument, moved from the reals to
proofs — say that if the room has seen diagonalization.
:::

# 1936: the Entscheidungsproblem

::::::hstack
::::vstack
{image "../static/figures/portraits/placeholder_church.png" (class := "portrait")}[Alonzo Church]

:::class "names"
Alonzo Church
:::
::::

::::vstack
{image "../static/figures/portraits/turing.jpg" (class := "portrait")}[Alan Turing]

:::class "names"
Alan Turing
:::
::::
::::::

*1928* — Hilbert and Ackermann: is there a procedure deciding whether a formula is provable? The *Entscheidungsproblem*.

*1936* — Church and Turing, independently: there is none.

First they had to say what a procedure is. Turing: a tape, a head, a finite table of instructions. Church: the $`\lambda`-calculus.

:::notes
Hilbert and Ackermann, *Grundzüge der theoretischen Logik*, 1928.

Church's paper was submitted in April 1936, Turing's a few months
later. Neither knew of the other at the start. Turing went to
Princeton the year after and took his doctorate under Church.

Turing's machine is not a design. Nothing in the paper says how one
would be built; it exists to be reasoned about.

The two definitions compute the same functions — that is a theorem,
in an appendix to Turing's paper. That either captures what we
informally call "computable" cannot be a theorem, since the informal
notion has no definition. That claim is the Church-Turing thesis.

There is no photograph of Church that is free to use; hence the
silhouette.
:::

# The lambda calculus

A *calculus*: a formal language with rules for calculating. Here: terms for functions, and one rule.

$`\lambda x.\, x + 1` is the function adding one. The rule is substitution, *β-reduction*: $`(\lambda x.\, x + 1)\, 3` becomes $`3 + 1`.

Numbers, pairs and recursion are not built in. They are written as $`\lambda`-terms, and that is enough for everything Turing's machines compute.

Lean is this calculus with types on top:

```lean -panel -stretch
example : (fun x : Nat => x + 1) 3 = 3 + 1 := rfl
```

:::notes
This is ninety years old and you will type it all semester. `fun x =>`
is `λx.`, and Lean accepts `λ` too.

The kernel computes by substituting. β is one of the reduction rules
of the next chapter.

How a calculus can be a *machine*, if anyone asks. Nothing here needs
hardware: what a machine needs is a finite description, a purely
syntactic step rule, and no point at which insight is required. β is
search-and-replace, and a clerk can run it without knowing what the
symbols mean.

Numbers are encoded as terms. A number is the function that applies
something n times: `0 = λf.λx. x`, `2 = λf.λx. f (f x)`,
`succ = λn.λf.λx. f (n f x)`, and `add = λm.λn.λf.λx. m f (n f x)`.
Computing 2 + 3 *is*: write `add 2 3`, reduce until no redex is left,
read off `5`. The reduction is the computation, the normal form is the
output. Booleans likewise: `true = λx.λy.x`, `false = λx.λy.y`, and
`if b then m else n` is just `b m n`.

Recursion comes from the fixed-point combinator
`Y = λf. (λx. f (x x)) (λx. f (x x))`: `Y g` reduces to `g (Y g)`, so a
function calls itself without having a name. The same trick gives the
endless loop `(λx. x x)(λx. x x)` -- and without non-termination there
would be nothing undecidable to find.

Why it counts as a model: λ-definable, general recursive and
Turing-computable are the same class, three formalisms that grew up
apart. That convergence is the evidence for the Church-Turing thesis.

Curry-Howard, the step from functions to proofs: a proposition is a
type, a proof is a term of that type, and checking a proof is
type-checking a program. Curry saw it for implication in the 1930s; de
Bruijn, Howard and Läuchli extended it to the quantifiers in the
1960s. It is why `theorem` and `def` are the same thing in Lean.
:::

# Checking is not finding

::::table +colHeaders +rowSeps
*
  * Question about a statement $`\varphi`
  * what the procedure must do
  * verdict
*
  * Does *this text* prove $`\varphi`?
  * always halt, with yes or no
  * decidable
*
  * Does *some* text prove $`\varphi`?
  * halt with yes whenever one exists
  * semi-decidable
*
  * Does *some* text prove $`\varphi`?
  * always halt, with yes or no
  * **undecidable**
::::

Rows 2 and 3 ask the *same* question. Only the demand differs — and that is where it breaks.

:::class "key"
You prove. The machine checks. That split is a theorem, not a gap in today's software.
:::

:::notes
Row one is the kernel, and the whole trust of the system sits there.

Row two is the automation: `exact?`, `apply?`, `grind`. Proofs can be
enumerated, so a search terminates when there is something to find. If
there is nothing, it runs forever — hence the time limit on every one
of these tactics.

Row three is the Entscheidungsproblem itself.

Rows two and three look contradictory and are not. **Read the table
down the second column, not across.** Row 3 has row 1's demand and
row 2's question, and that one combination is impossible. Every yes
is eventually found; the noes are not. Nothing reliably reports that
a statement has no proof.

The gap is one-sided, and it is exactly what you see when `grind`
hangs. It cannot say there is nothing there, only that it has not
found anything yet.

Do not confuse row 3 with a different question: *is $`\varphi` either
provable or refutable?* That is whether the theory decides $`\varphi`,
and Gödel 1931 says arithmetic does not decide everything. Related,
undecidable too, but not the Entscheidungsproblem, which is about
provability alone.

This is the answer to "why doesn't the computer just do it".
:::

# 1967: Automath

::::vstack
{image "../static/figures/portraits/debruijn.jpg" (class := "portrait")}[Nicolaas Govert de Bruijn]

:::class "names"
Nicolaas Govert de Bruijn
:::
::::

*Automath* — a typed $`\lambda`-calculus with dependent types, not set theory. The first machine-checked proofs.

*1977* — Landau's *Grundlagen der Analysis* through it, end to end.

:::class "key"
Everything before this slide is mathematics. From here on there are machines.
:::

:::notes
Say what he turned away from. Since 1954 the attempt had been to make
the machine *find* proofs. By 1959 a program did all the propositional
logic of *Principia* in minutes; for mathematics it did not scale. De
Bruijn retreats to the cheap question — the human proves, the
machine checks. That is the
split between *automated* and *interactive* theorem proving, and the
title of this course sits on one side of it.

De Bruijn starts Automath at Eindhoven in 1967 and publishes in 1968.
He arrives at the Curry-Howard correspondence himself, not knowing
Howard's work, and is the first to use it in a running system. Van
Benthem Jutting's 1977 thesis pushes Landau's book through it: the
first mathematics book verified end to end.

:::

# The systems

{image "../static/figures/itp_lineage.png" (class := "lineage")}[Timeline of the proof assistants from 1967 to today, one bar each, coloured by tradition]

:::class "key"
Five of the seven still run. A library cannot be moved.
:::

:::notes
The point of the picture: this is not a succession. Only Automath
and LCF stopped, and both handed their architecture on. Everything
from Mizar in 1973 onwards is still maintained.

Colour is the tradition, not the system. Blue is the de Bruijn line
— the proof is written down as a term and rechecked afterwards:
Automath, Coq/Rocq, Lean. Green is the LCF line — no proof object
at all, soundness comes from `thm` being an abstract type: LCF, HOL,
Isabelle. Orange is Mizar, declarative proofs over set theory.

Read the lower labels as the answer to "why build another one".
Automath: no help from the machine, unreadable. Mizar: readable, over
set theory. LCF: automation without trusting it. HOL: a logic for
mathematics, simple type theory. Coq: dependent types plus tactics,
then inductive types (CIC), the foundation of Lean.

A proof assistant is a large program with bugs. Which part must be
correct? LCF: `thm` is an abstract type and only the inference rules
produce one, so only they must be correct. Automath: a proof term is
written down and a small checker rereads it, so only the checker must
be correct — the de Bruijn criterion. Lean is in that line.

Why nothing dies: seL4 stays in Isabelle, the four colour theorem
stays in Rocq. Nobody will redo those. The library is the system.

Lean's own entry is worth a remark: "tactics in the language, one
library" is not a type-theoretic feature at all. It is an
organisational decision, and it is the one that mattered.
:::

# 2013: Lean

::::vstack
{image "../static/figures/portraits/demoura.jpg" (class := "portrait")}[Leonardo de Moura]

:::class "names"
Leonardo de Moura
:::
::::

*2013* — Leonardo de Moura starts Lean at Microsoft Research.

*2021* — Lean 4, a redesign rather than a new version.

Foundation: the Calculus of Inductive Constructions, the Automath line.

:::notes
Lean 1 to 3 were research prototypes; Lean 4 is the one that stuck,
and it is written in itself.

Kevin Buzzard has argued for Lean among mathematicians since 2018.
That is roughly when Mathlib started to look like a library of real
mathematics rather than a collection of exercises.

De Moura is still chief architect, now at the Lean FRO.
:::

# Three systems

:::table +colHeaders +rowSeps
*
  * System
  * Logic
  * Library
*
  * *Lean 4*
  * dependent types
  * one: *Mathlib*
*
  * *Rocq* (Coq until 2025)
  * dependent types
  * many packages
*
  * *Isabelle/HOL*
  * simple type theory
  * the *AFP*
:::

Only Isabelle has no dependent types. Its automation is the strongest of the three.

:::class "key"
We use Lean because *Mathlib* exists.
:::

:::notes
Lean and Rocq: both CIC, both an impredicative `Prop` under a
predicative hierarchy. Isabelle: simple type theory, weak enough to
automate well; Sledgehammer.

What matters more day to day is the library: one repository, many
packages, or a refereed archive.
:::

# 1976: the four colour theorem

::::::hstack
{image "../static/figures/four_colour.png" (class := "inlinepic")}[A map of thirty-four regions coloured with four colours]
::::::

Appel and Haken reduce the problem to a list of configurations, and an ordinary program checks it — no proof assistant.

*No human has ever read that part.*

:::class "key"
2005: Gonthier redoes all of it in *Coq*, case analysis included.
:::

:::notes
Two decades of argument about whether this counted as a proof.
Gonthier did not settle it; he made it unnecessary.

The 1976 program was Fortran and assembler on an IBM 370: a program
you had to trust. Coq is the opposite arrangement — a kernel of a few
thousand lines, and everything else checked against it.
:::

# 1998: the Kepler conjecture

::::::hstack
{image "../static/figures/kepler_packing.png" (class := "inlinepic kepler")}[A pyramid of equal spheres, the face-centred cubic packing]

::::vstack
{image "../static/figures/portraits/hales.jpg" (class := "portrait")}[Thomas Hales]

:::class "names"
Thomas Hales
:::
::::
::::::

Hales announces a proof of Kepler's conjecture of 1611. Twelve referees, four years.

Verdict: *ninety-nine percent certain* — and no better was possible. The *Annals* published it with the caveat attached.

:::class "key"
Hales started Flyspeck. Complete formal proof in HOL Light and Isabelle, 2014.
:::

:::notes
Not about computers. Peer review met a proof it could not certify,
and more effort would not have helped.

Sixteen years from announcement to a proof anyone could check.
:::

# 2013: Voevodsky

::::vstack
{image "../static/figures/portraits/voevodsky.jpg" (class := "portrait")}[Vladimir Voevodsky]

:::class "names"
Vladimir Voevodsky
:::
::::

*1989* — Voevodsky and Kapranov identify $`\infty`-groupoids with homotopy types.

*Oct 1998* — Simpson argues that it cannot be true, but cannot say *which step*.

*Autumn 2013* — Voevodsky accepts it and finds his own error.

:::class "key"
Mathematics runs on *a complex system of mutual trust based on reputations*.
:::

:::notes
Note the dates: the paper is from 1989, but the episode only ends in
2013, which is why it sits here and not before Kepler. **Fifteen years
in limbo** — say the number, it is no longer on the slide.

Fifteen years, and not an obscure corner: both authors were well
known, and Voevodsky received the Fields Medal in between, in 2002. Everyone makes mistakes. What matters here is how long it took
to resolve, and why: nobody could point at the faulty step, so it was
unclear who had erred, and nobody challenged them.

How it ended: the theorem is false. Their strict, rigidly
associative higher groupoids cannot produce the two-sphere, and Ara
showed in 2012 that among simply connected spaces they produce only
products of Eilenberg-MacLane spaces.

The quoted line is Voevodsky's own, from his 2014 IAS lecture.

Second story, same lesson: in 1999 he found an error in a paper of
his own from seven years earlier. He salvaged the result, but by his
account the experience frightened him.

His conclusion: a hard technical argument by a trusted author is
*hardly ever checked in detail*.

**Mind the order, it is the point of the slide.** None of this was
settled by a machine. Simpson argued by hand in 1998, Ara proved the
theorem false by hand in 2012, and Voevodsky recognised his own error
by hand in 2013. And his turn to formalization came *before* that
resolution, not after it: the homotopy-lambda-calculus note is from
2006, the Coq library from February 2010, the first public lectures
2010 and 2011. **What drove him was the dispute staying open for
fifteen years, not its ending.**

He spent the rest of his career on foundations built so that a
machine could check such arguments — not the ones Mathlib uses, and
not our subject. We take the diagnosis, not the cure. He died in
2017.
:::

# Perfectoid spaces, 2019

::::::hstack
::::vstack
{image "../static/figures/portraits/buzzard.jpg" (class := "portrait")}[Kevin Buzzard]

:::class "names"
Kevin Buzzard
:::
::::

::::vstack
{image "../static/figures/portraits/commelin.jpg" (class := "portrait")}[Johan Commelin]

:::class "names"
Johan Commelin
:::
::::

::::vstack
{image "../static/figures/portraits/massot.jpg" (class := "portrait")}[Patrick Massot]

:::class "names"
Patrick Massot
:::
::::
::::::

*The problem:* could an object as complicated as Scholze's perfectoid space be *stated* at all in a proof assistant?

:::class "key"
They formalized a *definition*, not a theorem. Stating is a different problem from proving.
:::

:::notes
Scholze's perfectoid spaces, 2012.

Lean's reputation among mathematicians dates from this project.
:::

# 2020: the Liquid Tensor Experiment

::::::hstack
::::vstack
{image "../static/figures/portraits/scholze.jpg" (class := "portrait")}[Peter Scholze]

:::class "names"
Peter Scholze
:::
::::

::::vstack
{image "../static/figures/portraits/commelin.jpg" (class := "portrait")}[Johan Commelin]

:::class "names"
Johan Commelin
:::
::::
::::::

Scholze posts a challenge on Buzzard's blog: a theorem in condensed mathematics he is not certain of.

Liquid Tensor Experiment, led by Commelin. Finished July 2022.

:::class "key"
The request came from a working mathematician, not from logicians. That is what had changed.
:::

:::notes
Buzzard's ICM plenary in 2022 is a fair marker for the moment this
stopped being a curiosity.

Not combinatorics with a thousand cases, either — condensed
mathematics, at the research frontier.
:::

# Sphere eversion, 2022

::::::hstack
::::vstack
{image "../static/figures/portraits/massot.jpg" (class := "portrait")}[Patrick Massot]

:::class "names"
Patrick Massot
:::
::::

::::vstack
{image "../static/figures/portraits/vandoorn.jpg" (class := "portrait")}[Floris van Doorn]

:::class "names"
Floris van Doorn
:::
::::

::::vstack
{image "../static/figures/portraits/nash.jpg" (class := "portrait")}[Oliver Nash]

:::class "names"
Oliver Nash
:::
::::
::::::

*The problem:* Mathlib had no differential geometry, and Gromov's h-principle needs it.

:::class "key"
So they built the API first and proved the theorem afterwards. That order is the ordinary shape of the work.
:::

:::notes
A sphere can be turned inside out without tearing or creasing. In the
plane the turning number blocks the analogue: $`+1` cannot become
$`-1`. In three dimensions that obstruction is gone.

This is why Mathlib matters more than any single theorem in it.
:::

# Freiman-Ruzsa, 2023

::::::hstack
::::vstack
{image "../static/figures/portraits/gowers.jpg" (class := "portrait")}[Timothy Gowers]

:::class "names"
Timothy Gowers
:::
::::

::::vstack
{image "../static/figures/portraits/green.jpg" (class := "portrait")}[Ben Green]

:::class "names"
Ben Green
:::
::::

::::vstack
{image "../static/figures/portraits/tao.jpg" (class := "portrait")}[Terence Tao]

:::class "names"
Terence Tao
:::
::::
::::::

:::class "caption"
Gowers, Green, Manners and Tao. There is no freely licensed photograph of Freddie Manners.
:::

*The problem:* a formalization took one team years, so it always came long after the paper.

:::class "key"
A *blueprint* cuts the work into pieces with stated interfaces. Strangers in parallel, three weeks, before refereeing.
:::

:::notes
A set whose sumset is barely larger than itself must be structured.
Four authors; three faces, because Manners has no free photograph.

Gowers is not just a name on the list. He used Freiman's theorem --
in Ruzsa's 1994 form -- in his proof of Szemeredi's theorem, and its
poor bounds went straight into his own. That is what turned the
question of *polynomial* bounds into the central one, and it is the
"polynomial" in the name. Twenty-five years later he is one of the
four who answer it. The version proved is the one over $`\mathbb{F}_2`, known as
Marton's conjecture, which is why the paper is called "On a
conjecture of Marton".

The method carried further than the theorem: this is the step between
"LTE, two years" and "Fermat, eleven days".
:::

# Equational Theories, 2024-25

*The problem:* 22 028 942 implications between 4 694 laws on magmas. Not deep — but beyond any human team.

```lean -panel -stretch
abbrev Equation3 (a : Type) [Mul a] :=
  ∀ x : a, x = x * x

abbrev Equation4 (a : Type) [Mul a] :=
  ∀ x y : a, x = x * y

-- Equation 4 implies Equation 3: take y := x.
example (a : Type) [Mul a] (h : Equation4 a) :
    Equation3 a :=
  fun x => h x x
```

:::notes
Led by Terence Tao. All implications settled, with new constructions
found on the way.

That is one entry of twenty-two million. Proving an implication can be
a single substitution; refuting one means building a magma, and the
machine checks that too, by `decide`.
:::

# Lean today

A new Lean every month. `v4.34.0` on 14 September 2026, `v4.35.0` on 12 October.

Nothing updates by itself. `lean-toolchain` names one version, `elan` fetches it, `lake` builds against it.

:::class "key"
This course is pinned to `v4.34.0` all semester.
:::

[*Lean FRO*](https://lean-lang.org/fro/) — a non-profit since July 2023, nineteen people, living on donations.

:::notes
Monthly releases, with a release candidate about four weeks ahead.
Patch releases in between.

The pin is why the notes and their machines agree. Tell them not to
run `elan update` and wonder why the exercises stop compiling.

Lean FRO: founded July 2023 under Convergent Research. De Moura chief
architect, Sebastian Ullrich head of engineering. Funders: Simons
Foundation International, Sloan, Richard Merkin, Amazon, and five
million dollars from Alex Gerko in July 2025. No vendor, and no longer
a spare-time project.
:::

# Mathlib

One library, one repository, one version. Everything in this course imports it.

2.33 million lines, about 189 000 theorems, 1 031 contributors. 27 commits a day.

No stable releases. *Mathlib* follows Lean, your project follows *Mathlib*.

[*The Mathlib Initiative*](https://mathlib-initiative.org/) — since September 2025, maintainers are paid to maintain it.

:::class "key"
[The interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) — the whole of *Mathlib* as a graph of its modules.
:::

:::notes
Measured on the pinned version of 15 September 2026: 8 529 files,
2.33 M lines, ~189 000 theorems, ~64 000 definitions, 1 031
contributors, 34 768 commits. 820 commits in the preceding thirty
days. The library changes while they use it.

`lake exe cache get` fetches what CI already compiled. Building from
source takes hours. Say this before the lab session.

Mathlib Initiative: a programme of Renaissance Philanthropy, the other
five million of Gerko's gift. Targets: review within a week for nine
of ten pull requests, keep the downstream ecosystem building,
documentation. Johan Commelin, who led the Liquid Tensor Experiment,
works there.

Open the import map live: one connected library, not a pile of
packages. Point at a node, follow an edge, show how analysis sits on
order sits on algebra.
:::

# Goals

The course is for mathematics students.

:::class "goals"
* *Reading formal statements.* Judging whether a formal statement says what the informal one claims.
* *Interactive theorem proving.* A small kernel checks every logical step of a proof, and the editor reports what remains to be proved as you write. This is not the older use of computers in mathematics, which was to work through many cases.
* *Mathematical content.* The mathematics in the first half is deliberately easy, because explaining a proof to a computer requires understanding it first, and a proof of more than a few lines has to be planned so that the commands — *tactics* — fit together. The second half goes deeper into the mathematics.
* *Functional programming.* Inductive types, structures, typeclasses and monads, needed both to use Lean and to read *Mathlib*.
* *Type theory.* Lean rests on dependent type theory: the Curry-Howard correspondence, dependent types, the universe hierarchy, and Lean's axioms.
* *Mathematics in Mathlib.* How the library organizes order theory, the algebraic hierarchy, filters (a single framework for limits), topology, measure theory and discrete probability. Textbooks rarely treat these from the point of view of formalization.
* *Proof engineering.* Automation tactics, searching *Mathlib*, and the common pitfalls of a large formal library.
:::

:::notes
Word for word the goals from the notes, so nobody has to reconcile two
versions. Read the first three out, point at the rest.

The exercises carry the course. In addition to the sheets, everyone
works on a project, mostly self-chosen.
:::

# What your machine needs

Every sheet begins with `import Mathlib`, so a two-line sheet needs as much memory as the hardest one.

:::table +colHeaders +rowSeps
*
  * Resource
  * Minimum
  * Comfortable
*
  * RAM
  * 16 GB
  * 32 GB
*
  * Free disk
  * 20 GB
  * 20 GB
*
  * Disk
  * SSD
  * NVMe SSD
:::

:::class "key"
Below the minimum? Talk to us — there is a server with 128 GB.
:::

:::notes
Compiling one sheet peaks at about 6.6 GB resident; the language
server sits at roughly 9 GB with one file open. Most of that is
memory-mapped library data the system can drop and read back, so less
memory slows everything down rather than breaking it. On a mechanical
hard disk you cannot work at all.
:::

# Wednesday

:::fitText
Bring a laptop. With administrator rights.
:::

Follow the [installation instructions](https://pfaffelh.github.io/leancourse/Introduction/#practical) in the course notes beforehand.

:::class "key"
Then run `lake exe cache get` *before* you come.
:::

:::notes
Installation session. VS Code, the Lean extension, git clone,
`lake exe cache get`. Ask them to try it at home first, so that
Wednesday is for the ones it did not work for.

Say the last point twice. `lake exe cache get` downloads the compiled
Mathlib; without it every machine in the room compiles Mathlib from
source at once, which takes hours and kills the session.
:::

# Where to start

[The Incredible Proof Machine in Lean](https://pfaffelh.github.io/ipm) — proofs as pictures, nine worlds from conjunction to induction. Ours. Start here.

[Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — the same idea for the tactics, on $`ℕ`.

[Formalising Mathematics](https://b-mehta.github.io/formalising-mathematics-notes/) — Bhavik Mehta, after Kevin Buzzard.

[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — Avigad and Massot. The closest thing to an official course.

:::notes
Both games run in a browser, keep their progress there, and need
nothing installed. If they do one thing before Wednesday, make it one
of these.

Our own one teaches the *shape* of a proof -- natural deduction drawn
as a diagram, conjunction through quantifiers and induction, with a
tactic trainer at the end. English and German. It is after Joachim
Breitner's Incredible Proof Machine; Breitner also wrote Con-Leche,
from the bugs section, so his name turns up twice in this lecture.

The Natural Number Game teaches the tactics instead, proving things
about `ℕ`. An evening each.

The last two are references for the semester, not homework.
:::
