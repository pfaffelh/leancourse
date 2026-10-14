import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
number := false
tag := "introduction"
%%%

What formalizing means, why anyone does it, how the field got here,
where Lean stands today, and how this course is run.

# What formalizing means
%%%
number := false
tag := "what-formalizing"
%%%

To formalize a proof is to write it in a language precise enough that a computer can check every step. The machine does not look for the proof. It reads the one you give it and confirms that each step follows from the axioms and from what came before. Anything left out is refused.

*Finding a proof is not checking one.* In 1976 a computer checked a long list of cases in the four colour theorem. The argument around that list was ordinary mathematics on paper, and nothing checked it.

*Autoformalizing goes the other way.* Formalizing starts from a proof and ends in a formal text. Autoformalizing starts from informal mathematics -- a statement, a paper -- and has a machine produce that text. Both end at the same place, a text the kernel accepts. The program that writes a proof may be unreliable in any way it likes; the program that checks it is small and fixed.

This course is about the first direction. You will write the proofs.

# Why formalize?
%%%
number := false
tag := "why-formalize"
%%%

Until recently, formalizing a serious theorem took a team and several years. That is no longer so, and the change is recent enough to date precisely.

* *February 2026.* The [sphere packing](https://en.wikipedia.org/wiki/Sphere_packing) theorem in dimension 8 was finished in five days by *Gauss*, an [autoformalizer from Math Inc.](https://math.inc/sphere-packing) The [human project](https://github.com/math-inc/Sphere-Packing-Lean) it joined had been working on the proof since 2024. It is the first of these results and the clearest: the mathematics was settled, so only the formalizing was left. [Maryna Viazovska](https://en.wikipedia.org/wiki/Maryna_Viazovska) proved the dimension-8 case in 2016 and received the Fields Medal for it, which closes a thread that opens with Kepler four hundred years earlier.
* *4 September 2026.* Anthropic [announced](https://www.anthropic.com/news/formalizing-fermats-last-theorem) the first complete computer-checked proof of [Fermat's Last Theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem), produced by Claude over eleven days: roughly 13 million lines of Lean and some 29 500 intermediate theorems, following a simplified version of Wiles's 1995 proof and building on *Mathlib*. Kevin Buzzard, who has led the community formalization effort since 2024 on a five-year grant, reviewed it and confirmed that it *proves Fermat's Last Theorem with no assumptions other than the axioms of mathematics*. That confirmation is itself machine-checkable, by `#print axioms` (Appendix).
* *8 September 2026.* OpenAI [announced](https://openai.com/index/navier-stokes-solution/) a proof, with a Lean formalization, that a smooth three-dimensional fluid obeying the [Navier-Stokes equations](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_existence_and_smoothness) *under a smooth external force* can develop a singularity in finite time. This is not the Millennium Prize problem, which concerns the unforced equation, and the prize is unclaimed. It was followed by a public argument about credit, and about treating open problems as benchmarks.
* *6 October 2026.* OpenAI [published](https://openai.com/index/sharing-ai-progress-in-mathematics/) a catalogue of results from an unreleased internal model -- at the time of writing 719 manuscripts grouped into 372 families, of which about 42 % of the top-line results carry a Lean formalization. Each result took, on average, about three hours of the model's thinking time; roughly 4 000 problems were posed in all.
* *7 October 2026.* One day later, three of those manuscripts were withdrawn: a sign error invalidated an argument in one, and two further papers depended on it. Fourteen more were revised. None of the withdrawn papers had a Lean proof.

:::figure "The two systems behind the September 2026 announcements. Both delivered Lean files with their proofs" (tag := "ai-labs")
![Claude](/static/figures/logos/claude.png)
![ChatGPT](/static/figures/logos/chatgpt.png)
:::

Those last two dates belong together. Machines now produce mathematics faster than mathematicians can referee it, and the only check that keeps up is a formal one.

A Lean proof shows that the formal statement follows from the axioms. It does not show that the statement says what the paper claims; that is a separate, human question. OpenAI's [repository](https://github.com/openai/math) documents, per paper, which checks cover a main theorem and which only a supporting result. Reading a formal statement and judging what it says is most of what this course teaches.

# Where the field stands
%%%
number := false
tag := "field-stands"
%%%

Two pictures from public data. They compare Lean with [Rocq](https://rocq-prover.org/) (*Coq* until 2025) and [Isabelle/HOL](https://isabelle.in.tum.de/), the two other large proof assistants; how they differ is a question of foundations, taken up under {ref "other-provers"}[Other theorem provers].

:::figure "New GitHub repositories per quarter, per million new repositories overall" (tag := "itp-repos")
![Line chart: new GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle from 2018 to 2026, each per million new repositories overall; Lean rises from under ten to about two hundred while the others stay near ten](/static/figures/itp_github_repos_per_million.png)
:::

Counting per million corrects for GitHub's own growth, which was steep in 2026. One distortion is left in: the Justin Sun Prize, announced in September 2026, pays for solved problems only against a machine-verified proof, and about a fifth of that month's new Lean repositories carry a prize identifier.

Until about 2023 the three were comparable, with Coq the largest. The rise is recent, and it is not evidence that Lean is better: Isabelle's automation is still ahead in places, and Rocq has decades of verified-software work behind it. It is evidence about where people are going.

:::figure "Papers on the mathematics arXiv whose results are checked in Lean, per 100 submissions" (tag := "arxiv-lean")
![Bar chart: weekly share of arXiv mathematics papers with a Lean-checked result during 2026, rising from about 0.3 per 100 in January to about 2.4 per 100 in the first week of October](/static/figures/arxiv_lean_formalized_share.png)
:::

The share rises through 2026. The highest week so far is the first of October, with 60 of 2 546 papers, 2.4 per 100. It is a share rather than a count because the denominator moved too: the mathematics arXiv received about a thousand submissions a week in January and about two and a half thousand in early October. Within a few years, reading and writing a formal proof will be ordinary equipment.

# How we got here
%%%
number := false
tag := "how-we-got-here"
%%%

It took mathematics from 1879 to 1936 to turn a proof into a finite object a machine can inspect. Then the machines that inspect it, from 1967 on. Lean is at the end of that line.

## The mathematics
%%%
number := false
tag := "the-mathematics"
%%%

### 1879 to 1913: Frege, Peano, Russell
%%%
number := false
tag := "prehistory"
%%%

Gottlob Frege's *Begriffsschrift* of 1879 gave the first system in which proofs themselves were objects to be manipulated. Giuseppe Peano axiomatized arithmetic in 1889, with a zero, a successor and induction; that is still the shape of {ref "nat"}[Lean's `Nat`]. Bertrand Russell's letter of 1902 showed that Frege's system was inconsistent. The set $`R = \{x : x \notin x\}` is a member of itself exactly if it is not.

Two answers appeared in 1908, and both are still in use. They differ in what they restrict.

:::table (align := left) +header
* + 1908
  + restricts
  + `x ∈ x` is
  + the stratification is
* + Ernst Zermelo
  + which sets *exist*
  + well-formed, and false
  + the cumulative hierarchy $`V_0 \subseteq V_1 \subseteq \dots`, a theorem about the sets
* + Bertrand Russell
  + what can be *said*
  + no statement at all
  + the type hierarchy `Type 0 : Type 1 : ...`, a rule of the grammar
:::

Zermelo replaced unrestricted comprehension, which forms $`\{x : \varphi(x)\}` for any property, by separation, which forms only $`\{x \in A : \varphi(x)\}` out of a set $`A` already given. Then $`R` is never formed, and Russell's argument turns into a theorem instead of a contradiction: there is no set of all sets. That `x ∈ x` holds for no set is a later and separate axiom, foundation.

Russell stratified the language itself, so that `x ∈ x` is not false but ungrammatical. Well-formedness is then a question about syntax, settled before any question of truth arises, and a machine can decide it.

His ban was wider than the paradox. It forbids *every* definition that quantifies over a totality containing the object being defined, and ordinary mathematics is full of those. The supremum of a bounded set of reals is defined by quantifying over reals, so under the ban it is not itself a real number, and analysis stops. Russell recovered it by adding an axiom, reducibility, which grants that every forbidden definition agrees with a permitted one — an axiom that returns most of what the ban had taken. Lean draws the line in a different place, and in two: see {ref "prop-special"}[Why `Prop` is special].

Mathematics went with Zermelo, proof assistants with Russell ({ref "types-history"}[Where types come from]).

Whitehead and Russell spent *Principia Mathematica* rebuilding the rest; their proof that `1 + 1 = 2` arrives in the second volume with the note that *the above proposition is occasionally useful*. Done by hand, formalization is unbearable, and for most of a century little came of it.

### 1917 to 1931: Hilbert's programme, and Gödel
%%%
number := false
tag := "hilbert-programme"
%%%

David Hilbert turned formalization into a programme, pressing for it from a lecture of 1917, *Axiomatisches Denken*, onwards. The conviction behind it is older. At the Paris congress of 1900 he had said that in mathematics there is *no ignorabimus*: no question we are condemned never to settle.

Write mathematics in a fixed formal language, fix the rules of inference, and a proof becomes a finite string of symbols. Whether it follows the rules is then a question about symbols, answerable without knowing what they mean. Three questions about a set of axioms can then be asked precisely, and Hilbert wanted all three answered yes.

* *Consistent.* No contradiction follows from the axioms. Hilbert wanted this proved by finitary means.
* *Complete.* For every statement, either it or its negation follows.
* *Decidable.* A procedure settles, for every statement, which of the two it is.

:::figure "David Hilbert and Kurt Gödel" (tag := "hilbert-godel")
![David Hilbert](/static/figures/portraits/hilbert.jpg)
![Kurt Gödel](/static/figures/portraits/godel.jpg)
:::

Kurt Gödel settled the first two, in opposite directions. His thesis of 1929 proved first-order logic *complete*: a formula that holds in every model is derivable from the axioms. *First-order* is the restriction that quantifiers range over the elements of a domain, never over its subsets, relations or functions. $`\forall x\, \exists y\, (x \cdot y = e)` is first-order; *every bounded set of reals has a supremum* is not, because it quantifies over sets of reals. Logic itself is therefore not the obstacle, and this is why searching for a proof can be made to terminate whenever one exists.

The incompleteness theorems of 1931 end the programme. No consistent system that contains arithmetic and whose axioms a machine can list proves every true statement about the natural numbers, and none proves its own consistency. The formalization itself survived, and it is what proof assistants rest on. Gödel's proof takes it literally: he encodes formulas and proofs as natural numbers and computes with them, the first use of proofs as data. The argument is Cantor's diagonal argument, carried over from the reals to proofs. Turing used it again five years later.

The word *complete* does two jobs here. A *logic* is complete when every formula that holds in all models is derivable; a *theory* is complete when it decides every statement, which is the sense of Hilbert's list above. The two theorems are about the two different things.

:::table (align := left) +header
* + Gödel
  + about
  + result
* + 1929
  + first-order logic
  + complete: valid in every model implies derivable
* + 1931
  + any theory that contains arithmetic
  + incomplete: some statement about $`\mathbb{N}` is neither proved nor refuted
:::

They do not conflict. The sentence Gödel builds in 1931 is true of the natural numbers but false in other models of the same axioms. It therefore does not hold in every model, and the theorem of 1929 promises nothing for it.

### 1936: the Entscheidungsproblem
%%%
number := false
tag := "entscheidungsproblem"
%%%

The third question was left. Hilbert and Wilhelm Ackermann put it in print in 1928, in *Grundzüge der theoretischen Logik*: is there a procedure that decides, for an arbitrary formula of first-order logic, whether it is provable? This is the *Entscheidungsproblem*. Alonzo Church and Alan Turing answered it in 1936, independently and negatively. There is no such procedure.

:::figure "Alonzo Church and Alan Turing" (tag := "church-turing")
![Alonzo Church (no freely licensed photograph available)](/static/figures/portraits/placeholder_church.png)
![Alan Turing](/static/figures/portraits/turing.jpg)
:::

Both had to say first what a procedure is, and each built a model of computation to do it. Turing's is the machine that carries his name: a tape divided into cells, a head that reads one cell, writes and moves one step, and a finite table of instructions. The paper does not say how such a machine would be built; it is there to be reasoned about, not constructed. Church's model is the *lambda calculus*, and it is the one this course uses every day.

The lambda calculus is a notation for functions, and nothing else. The term $`\lambda x.\, x + 1` denotes the function sending $`x` to $`x + 1`, the term $`f\, a` denotes $`f` applied to $`a`, and the only rule of computation is substitution:
$$`(\lambda x.\, x + 1)\, 3 \;\rightsquigarrow\; 3 + 1.`
Numbers, pairs and recursion are not built in; they are written as lambda terms. That is what makes the calculus a model of computation and not just a notation. Turing proved in an appendix to [his paper](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf) that his machines and Church's terms compute the same functions. He went to Princeton the following year and took his doctorate under Church. That the two models agree is a theorem. That either of them is what *computable* means is not; that is the *Church-Turing thesis*, a claim about the word.

Lean is this notation with types on top. The Lean spelling of $`\lambda x.\, x+1` is `fun x => x + 1`, and the kernel computes by substituting:

```lean
#check fun x : Nat => x + 1

example : (fun x : Nat => x + 1) 3 = 3 + 1 := rfl
```

The step from a calculus of functions to a calculus of proofs is the *Curry-Howard correspondence*: a proposition is a type, a proof is a term of that type, and checking a proof is type-checking a program. Haskell Curry saw the pattern for implication in the 1930s; de Bruijn, William Howard and Hans Läuchli extended it to the quantifiers in the 1960s. It is the reason `theorem` and `def` are the same construct in Lean.

Three questions about proofs have three different answers, and a proof assistant is built on the difference.

1. *Does this text prove that statement?* Decidable, and cheap. This is what Lean's kernel does, and the whole trust of the system rests on it.
2. *Find a proof of this statement.* Semi-decidable. Proofs can be enumerated one after another, and by Gödel's completeness theorem every valid statement has one, so a search ends when a proof exists. When none exists it runs forever, which is why `exact?` and `grind` come with a time limit.
3. *Decide whether this statement is provable.* Undecidable, by Church and Turing. No procedure answers yes or no, in finite time, for every formula.

So the human writes the proof and the machine checks it. That division of labour is a theorem of 1936, not a property of today's software.

## The proof assistants
%%%
number := false
tag := "the-assistants"
%%%

### 1967: Automath
%%%
number := false
tag := "first-assistants"
%%%

Nicolaas Govert de Bruijn started *[Automath](https://en.wikipedia.org/wiki/Automath)* at Eindhoven in 1967 and published it in 1968, the first language in which a machine checked proofs. Its foundation is a typed lambda calculus with dependent types, that is, types that may mention terms, as `Vec α n` mentions `n`. It was the first system in which a proof is a term and checking it is type-checking, the {ref "entscheidungsproblem"}[Curry-Howard correspondence]; de Bruijn found that correspondence himself, not knowing Howard's work. In 1977 L. S. van Benthem Jutting pushed Landau's *Grundlagen der Analysis* through it, the first mathematics book verified end to end.

:::figure "Nicolaas Govert de Bruijn, who built Automath" (tag := "debruijn")
![Nicolaas Govert de Bruijn](/static/figures/portraits/debruijn.jpg)
:::

### 1972 to 1991: Mizar, LCF, HOL, Isabelle, Coq
%%%
number := false
tag := "lcf-line"
%%%

Four lines come out of the following twenty years, and the systems of today are on them.

* *[Mizar](https://mizar.uwb.edu.pl/)*, Andrzej Trybulec, 1973. A formal language meant to be read like mathematical prose, over set theory. Its library has been growing for fifty years.
* *[LCF](https://web.archive.org/web/20240703134244/http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf)*, Robin Milner, Stanford 1972 and Edinburgh 1975. The idea there is architectural: `thm` is an abstract data type, and the only functions that produce a value of that type are the inference rules. Anything may then be built on top without being trusted. The language ML was invented to write it.
* *[HOL](https://hol-theorem-prover.org/)*, Mike Gordon, from the mid-1980s: LCF with simple higher-order logic in place of the original logic, used first for hardware verification. *[Isabelle](https://isabelle.in.tum.de/)* follows in 1986 (Lawrence Paulson), *Isabelle/HOL* in 1991 (Tobias Nipkow).
* *[Coq](https://rocq-prover.org/)*, from 1989, on the Calculus of Constructions and from the mid-1990s on the Calculus of Inductive Constructions. That is the foundation Lean also uses, and the system was renamed *Rocq* in 2025.

The two architectures answer the same question differently. In the LCF line nothing is kept but the theorem, and one trusts the kernel because no other code can make one. In the Automath line the system writes down a proof term, which a small, separate checker reads afterwards; a system meeting that condition is said to satisfy the *[de Bruijn criterion](https://www.cs.ru.nl/~freek/comparison/comparison.pdf)*. Lean is in the second line: a Lean proof is a term, and the kernel rechecks it no matter which tactic produced it.

### 1976: the four colour theorem
%%%
number := false
tag := "four-colour-episode"
%%%

Kenneth Appel and Wolfgang Haken proved the [four colour theorem](https://en.wikipedia.org/wiki/Four_color_theorem). Their argument reduced the problem to a long list of configurations and then checked that list by computer. No human has ever read that part, and for two decades the community argued about whether it counted as a proof at all.

:::figure "Four colours suffice for any map in the plane. Georges Gonthier, who formalized the proof" (tag := "four-colour")
![A map of thirty-four regions, coloured with four colours so that no two neighbours share one](/static/figures/four_colour.png)
![Georges Gonthier (no photograph available)](/static/figures/portraits/placeholder_gonthier.png)
:::

In 2005 Georges Gonthier formalized the whole thing in Coq, case analysis included. The two events separate the distinction this course rests on: *a proof found by computer is not a proof checked by computer.*

### 1998: the Kepler conjecture
%%%
number := false
tag := "kepler-episode"
%%%

Thomas Hales announced a proof of the [Kepler conjecture](https://en.wikipedia.org/wiki/Kepler_conjecture): no packing of equal spheres in space is denser than the way a greengrocer stacks oranges.

:::figure "The packing Kepler conjectured to be optimal in 1611, and Thomas Hales, who proved it" (tag := "kepler")
![A pyramid of equal spheres, the face-centred cubic packing, with density pi over root 18](/static/figures/kepler_packing.png)
![Thomas Hales](/static/figures/portraits/hales.jpg)
:::

Twelve referees worked on it for four years and reported that they were ninety-nine percent certain, and could do no better. The *Annals of Mathematics* published it with that caveat. Hales started the [Flyspeck project](https://en.wikipedia.org/wiki/Flyspeck), which delivered a complete formal proof in HOL Light and Isabelle in 2014. This episode is not about computers: peer review had met a proof it could not certify, and more effort would not have helped.

### 2013: Voevodsky
%%%
number := false
tag := "voevodsky-episode"
%%%

In 1989 Vladimir Voevodsky and Mikhail Kapranov published a theorem identifying [higher groupoids](https://en.wikipedia.org/wiki/Infinity-groupoid) with homotopy types. In October 1998 Carlos Simpson posted an argument implying that it could not be true. Voevodsky went on believing his own theorem until the autumn of 2013.

:::figure "Vladimir Voevodsky at Oberwolfach in 2011, during a workshop on the homotopy interpretation of type theory" (tag := "voevodsky")
![Vladimir Voevodsky](/static/figures/portraits/voevodsky.jpg)
:::

His account is about people, not machines. Simpson had a counterexample but could not say which step was wrong, so it stayed unclear who had erred. Mathematics runs, in Voevodsky's words, on *a complex system of mutual trust based on reputations*, and both authors had one. The doubt made the theorem unused without settling it, for fifteen years. A second mistake, in a lemma of his own from 1992, stood in print until a listener checking his lectures found it in 1999; several seminars had read the paper by then. A hard technical argument by a trusted author, he concluded, is *hardly ever checked in detail*.

Voevodsky received the Fields Medal in 2002. He then looked for a proof assistant he could use, found none that suited his mathematics, and built the foundations for one: [univalent foundations](https://en.wikipedia.org/wiki/Univalent_foundations), a special year at the Institute for Advanced Study in 2012-13, and the book two dozen people wrote there in under six months. He formalized in Coq, and his foundations are not the ones *Mathlib* rests on: Lean 2 carried a mode for them, Lean 3 dropped it. This course takes the diagnosis, not the cure. His [own account](https://www.ias.edu/ideas/2014/voevodsky-origins) is short. He died in 2017.

### 2020: the Liquid Tensor Experiment
%%%
number := false
tag := "lte-episode"
%%%

In December 2020 Peter Scholze posed a challenge on Kevin Buzzard's blog: a theorem in condensed mathematics whose proof he was not sure of. A Fields medallist, publicly unsure of his own argument, asking a machine to check it. The *[Liquid Tensor Experiment](https://leanprover-community.github.io/liquid/)*, led by Johan Commelin, finished in July 2022. *[Condensed mathematics](https://en.wikipedia.org/wiki/Condensed_mathematics)* rebuilds topology on profinite sets rather than on open covers. The request came from a working mathematician at the centre of his subject, not from logicians or computer scientists. That is what had changed.

:::figure "Peter Scholze, who posed the challenge, and Johan Commelin, who led the project" (tag := "lte-people")
![Peter Scholze](/static/figures/portraits/scholze.jpg)
![Johan Commelin (no photograph available)](/static/figures/portraits/placeholder_commelin.png)
:::

Buzzard's plenary lecture at the ICM in 2022 marks the point where formalization stopped being a curiosity.

## 2013: Lean
%%%
number := false
tag := "lean-origin"
%%%

:::figure "Leonardo de Moura, who started Lean in 2013" (tag := "demoura")
![Leonardo de Moura](/static/figures/portraits/demoura.jpg)
:::

Leonardo de Moura started Lean at Microsoft Research in 2013. Lean 4, a redesign rather than a new version, arrived in 2021, and is written in Lean itself. Its foundation is the Calculus of Inductive Constructions, which puts it in the Automath line: a proof is a term, and the kernel rechecks it whatever tactic produced it. Kevin Buzzard has argued for Lean among mathematicians since 2018. Where development sits now is the next section.

# Current state of Lean
%%%
number := false
tag := "lean-today"
%%%

*Releases.* Lean 4 appears once a month, with a release candidate about four weeks ahead: `v4.33.0` on 10 August 2026, `v4.34.0` on 14 September, `v4.35.0` on 12 October. Nothing updates by itself. A file `lean-toolchain` in the root of a project names one exact version, `elan` fetches that version, and `lake` builds against it. This course is pinned to `leanprover/lean4:v4.34.0`, so the notes and your machine agree all semester.

*Who builds Lean.* The [Lean FRO](https://lean-lang.org/fro/), a non-profit founded in July 2023 under Convergent Research, with twenty-one people at the time of writing. Leonardo de Moura is chief architect, Sebastian Ullrich head of engineering. It runs on donations: the Simons Foundation International, the Alfred P. Sloan Foundation, the Richard Merkin Foundation, Amazon, and five million dollars from Alex Gerko of XTX Markets in July 2025. Lean has no vendor behind it, and it is no longer a spare-time project either.

*Mathlib.* [*Mathlib*](https://github.com/leanprover-community/mathlib4) is one repository holding essentially all of the mathematics, compiled as a unit. Maintainers review every change, and CI keeps the whole library building against the current Lean. There are no stable releases: *Mathlib* follows Lean, and your project follows *Mathlib*. Every file in this course starts with `import Mathlib`, so we make no distinction between the two. Compiling it from source takes hours, which is why `lake exe cache get` downloads what the CI already built.

Measured on the version pinned for this course (15 September 2026): 8 529 files, 2.33 million lines, about 189 000 theorems and lemmas, about 64 000 definitions, instances and structures, by 1 031 contributors in 34 768 commits. In the thirty days before that date it received 820 commits, 27 per day. The library changes while you use it.

*Who maintains Mathlib.* For fifteen years, nobody was paid to. The [Mathlib Initiative](https://mathlib-initiative.org/), a programme of Renaissance Philanthropy begun in September 2025, now employs maintainers; it received the other five million dollars of Gerko's gift. Its stated targets are review within a week for nine out of ten pull requests, keeping the downstream ecosystem building, and documentation. Johan Commelin, who led the {ref "lte-episode"}[Liquid Tensor Experiment], works there.

*Reading the library.* The [interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) draws *Mathlib* as a graph of its modules: which file may use which, and therefore in what order the library is built. The same site serves the [API documentation](https://leanprover-community.github.io/mathlib4_docs/) for every declaration. Both are worth half an hour before you need them.

*Lean is also a programming language.* `lake`, the compiler's own front end and much of Lean itself are written in Lean; see [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).

# Landmark formalizations
%%%
number := false
tag := "landmarks"
%%%

Between Flyspeck and 2026, each of these projects showed that something new was possible. The course material is built out of the libraries they left behind.

## Perfectoid spaces, 2019
%%%
number := false
tag := "perfectoid-landmark"
%%%

By Buzzard, Commelin and Massot ([project page](https://leanprover-community.github.io/lean-perfectoid-spaces/)). They formalized a *definition* rather than a theorem: Scholze's [perfectoid spaces](https://en.wikipedia.org/wiki/Perfectoid_space) of 2012. Whether an object of that complexity could be stated at all in a proof assistant was open, and stating is a different problem from proving. Lean's reputation among mathematicians dates from this project.

:::figure "Kevin Buzzard, Johan Commelin and Patrick Massot" (tag := "perfectoid-people")
![Kevin Buzzard](/static/figures/portraits/buzzard.jpg)
![Johan Commelin (no photograph available)](/static/figures/portraits/placeholder_commelin.png)
![Patrick Massot (no photograph available)](/static/figures/portraits/placeholder_massot.png)
:::

## Sphere eversion, 2022
%%%
number := false
tag := "eversion-landmark"
%%%

By Massot, van Doorn and Nash ([project page](https://leanprover-community.github.io/sphere-eversion/)): Gromov's [h-principle](https://en.wikipedia.org/wiki/Homotopy_principle), and with it the fact that a [sphere can be turned inside out](https://en.wikipedia.org/wiki/Sphere_eversion) without tearing or creasing. For closed curves in the plane no such thing is possible: a regular homotopy cannot change the turning number, and everting a circle would send $`+1` to $`-1`. In three dimensions that obstruction vanishes. Formalizing this meant differential topology rather than algebra, so the project built a usable differential-geometry API first and proved the theorem afterwards. That order is the ordinary shape of formalization work, and it is why *Mathlib* matters more than any single theorem in it.

:::figure "Patrick Massot, Floris van Doorn and Oliver Nash" (tag := "eversion-people")
![Patrick Massot (no photograph available)](/static/figures/portraits/placeholder_massot.png)
![Floris van Doorn (no photograph available)](/static/figures/portraits/placeholder_vandoorn.png)
![Oliver Nash (no photograph available)](/static/figures/portraits/placeholder_nash.png)
:::

## The polynomial Freiman-Ruzsa conjecture, 2023
%%%
number := false
tag := "pfr-landmark"
%%%

By Gowers, Green, Manners and Tao ([project page](https://teorth.github.io/pfr/)), formalized under Tao's direction in about three weeks -- before the paper had been refereed. It says that a set whose sumset is barely larger than itself must be structured.

:::figure "Timothy Gowers, Ben Green, Terence Tao and Freddie Manners" (tag := "pfr-people")
![Timothy Gowers](/static/figures/portraits/gowers.jpg)
![Ben Green](/static/figures/portraits/green.jpg)
![Terence Tao](/static/figures/portraits/tao.jpg)
![Freddie Manners (no photograph available)](/static/figures/portraits/placeholder_manners.png)
:::

The method carried further than the theorem. A *blueprint* cuts a formalization into independent pieces with stated interfaces, so volunteers can work in parallel without talking to each other. Formalization stopped being a job for one team over years.

## The Equational Theories Project, 2024 to 2025
%%%
number := false
tag := "equational-landmark"
%%%

Led by Tao ([project page](https://teorth.github.io/equational_theories/)): all 22 028 942 implications between 4 694 equational laws on magmas settled, with new constructions found on the way. The difficulty is not depth but bookkeeping, on a scale that needs a machine.

The laws are numbered. Equation 3 is $`x = x \diamond x`, Equation 4 is $`x = x \diamond y`. Proving an implication can be a single substitution; refuting one means building a magma.

```lean
abbrev Equation3 (a : Type) [Mul a] :=
  ∀ x : a, x = x * x

abbrev Equation4 (a : Type) [Mul a] :=
  ∀ x y : a, x = x * y

-- Equation 4 implies Equation 3: take y := x.
example (a : Type) [Mul a] (h : Equation4 a) :
    Equation3 a :=
  fun x => h x x

-- The converse fails: `and` on `Bool` is a
-- counterexample, and the machine checks it.
local instance : Mul Bool := ⟨(· && ·)⟩

example : Equation3 Bool := by decide
example : ¬ Equation4 Bool := by decide
```

That is one entry. The project settled 22 028 942 of them.

# Other theorem provers
%%%
number := false
tag := "other-provers"
%%%

The two systems Lean is usually compared with differ from it in their foundations, not in style.

:::table (align := left) +header
* + System
  + Foundation
  + Dependent types
  + Library
* + Lean 4
  + a variant of the Calculus of Inductive Constructions
  + yes
  + *Mathlib*, one repository
* + [Rocq](https://rocq-prover.org/) (until 2025 *Coq*)
  + the predicative Calculus of Cumulative Inductive Constructions
  + yes
  + many separate packages
* + [Isabelle/HOL](https://isabelle.in.tum.de/)
  + simply typed higher-order logic
  + no
  + the *Archive of Formal Proofs*
:::

*Lean and Rocq* are close relatives. Both rest on a dependent type theory in which a proof is a *term* and checking a proof is type-checking; both have an impredicative, proof-irrelevant universe `Prop` of propositions sitting under a predicative hierarchy of data types. Lean differs in four points that return later in these notes: proof irrelevance holds *definitionally*, quotient types are primitive rather than built from setoids, there is no universe cumulativity, and classical reasoning enters through an axiom (`Classical.choice`). Rocq's roots are in program verification -- the CompCert C compiler and the Feit-Thompson theorem are Rocq developments -- and it extracts verified programs to OCaml or Haskell.

*Isabelle/HOL* uses simple type theory: types are built from base types and arrows, types do not depend on terms, and one cannot write `Vec α n` for *lists of length `n`*. That logic is weak enough to automate well, and Isabelle's automation is the strongest of the three. *Sledgehammer* hands a goal to several external provers at once and reconstructs what they find as a proof Isabelle can check; much of what Lean's `grind` does, Isabelle has done for twenty years. Isabelle is also a framework: HOL is one object logic among several over the intuitionistic meta-logic Isabelle/Pure. Its largest development is *seL4*, an operating-system microkernel verified down to its C implementation.

*How the libraries are organized* matters more day to day than the foundations.

* *Mathlib* is one repository, compiled as a unit. Maintainers review every change, and CI keeps it building against the current Lean. There are no stable releases: *Mathlib* follows Lean, and your project follows *Mathlib*. Results combine without extra work, because all structures live in one hierarchy, built from `class` and `instance` (see the chapters on typeclasses and the algebraic hierarchy).
* *Rocq* has no such centre. Its standard library is small, and the mathematics lives in independent packages -- *MathComp*, out of the Feit-Thompson formalization, *Coquelicot* and *MathComp-Analysis* for analysis, and others -- distributed through `opam`, with the *Rocq Platform* bundling a tested combination. Packages evolve at their own pace, which is comfortable with one dependency and awkward with two that disagree.
* *Isabelle* sits in between. The *Archive of Formal Proofs* holds refereed, self-contained entries, released in lockstep with Isabelle. Entries may depend on one another but are never merged into one library; the archive is cited like a journal.

We use Lean because *Mathlib* exists: the exercises start with `import Mathlib` and have the real numbers, measure theory and topology already there.

# Other courses
%%%
number := false
tag := "other-courses"
%%%

* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): proofs about `ℕ` in the browser, nothing to install. The usual first contact with Lean, and a good use of an evening before the course starts.
* [_Formalising Mathematics_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, after notes by Kevin Buzzard: the format of the present course follows these.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: the closest thing to an official course, organized by area of mathematics.

# Practical matters
%%%
number := false
tag := "practical"
%%%

The rest of this chapter is about running the course.

*Goals.* The course is for mathematics students.

* *Interactive theorem proving.* A small kernel checks every logical step of a proof, and the editor reports what remains to be proved as you write. This is not the older use of computers in mathematics, which was to work through many cases.
* *Mathematical content.* The mathematics in the first half is deliberately easy, because explaining a proof to a computer requires understanding it first, and a proof of more than a few lines has to be planned so that the commands -- *tactics* -- fit together. The second half goes deeper into the mathematics.
* *Functional programming.* Inductive types, structures, typeclasses and monads, needed both to use Lean and to read *Mathlib*. These are spread across the Lean and Mathematics parts rather than collected in one chapter.
* *Type theory.* Lean rests on dependent type theory: the Curry-Howard correspondence, dependent types, the universe hierarchy, and Lean's axioms.
* *Mathematics in Mathlib.* How the library organizes order theory, the algebraic hierarchy, filters (a single framework for limits), topology, measure theory and discrete probability. Textbooks rarely treat these from the point of view of formalization.
* *Proof engineering.* Automation tactics, searching *Mathlib*, and the common pitfalls of a large formal library.

*How the course is organized.* Tactics and theory are interleaved rather than separated.

* The first part, *Lean and its type theory*, introduces writing proofs and the dependent type theory underneath at the same time.
* Tactics are documented alphabetically in a glossary in the *Appendix*. You will usually meet a tactic in a working example before reading its entry; a table at the start of *Proofs in Lean* lists the ones needed first.
* Read in order, but on a first pass you can skip the tactics chapter and consult it when you hit a `sorry`.

*How to use this course.* The notes have six parts.

* *Lean and its type theory*: first the language, writing proofs, the functional-programming side (pure functions, pattern matching, recursion, higher-order functions) and navigating *Mathlib*; then the theory -- Curry-Howard, dependent types, universes, Lean's three axioms and what the kernel adds to them, the `structure` / `class` machinery, well-foundedness and the avoidance of paradoxes.
* *Mathematics*: propositions, proofs and sets, then how *Mathlib* organizes order theory, the algebraic hierarchy, filters, topology, measure theory and monadic discrete probability (`PMF`). Pointers into the API, not full formalizations.
* *Appendix*: common pitfalls, the diagnostic commands (`#print axioms`, `#find_home`, `#lint`), a keyword reference and the glossary of tactics (a longer list is [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)).
* *Projects*: five topics for the individual formalization projects in the second half, each with a description, a sketch of an implementation and references.
* *Bibliography*: the works cited throughout, with links.
* *Slides*: the decks used in the lecture, readable on their own.

The exercises carry the course (the _Exercises_ folder within `Leancourse`). Feedback is immediate: error messages from the elaborator, and a *proof-state* panel showing what remains to be proved at every cursor position. Start with the first sheet; the sheets explain as they go.

The sheets cover the first half of the semester. In the second half you work on an individual project, mostly self-chosen -- an exercise from your first year, or a part of `Mathlib` you want to know; the {ref "projects"}[Projects chapter] has five worked-out suggestions.

Before the first exercise session, get Lean running on your own machine.

*Hardware.* Lean memory-maps all of *Mathlib* while it works, and every exercise sheet begins with `import Mathlib`. A two-line sheet therefore needs as much memory as the hardest one in the course.

:::table (align := left) +header
* + Resource
  + Minimum
  + Comfortable
* + RAM
  + 16 GB
  + 32 GB
* + Free disk space
  + 20 GB
  + 20 GB
* + Disk
  + SSD
  + NVMe SSD
:::

Measured on the version of *Mathlib* used here: compiling one sheet peaks at about 6.6 GB of resident memory, and the language server behind *vscode* sits at roughly 9 GB with one file open. Most of that is memory-mapped library data, which the system can drop and read back from disk, so less memory does not break anything, it only slows everything down. With 8 GB you can work with a single file open and little else running. On a mechanical hard disk you cannot.

*If your machine is below the minimum, talk to the teachers at the start of the course.* A server with 128 GB of RAM is available and we can give you an account on it.

Run the `git clone` and `lake exe cache get` below at home, before the first lab session: `lake exe cache get` downloads several gigabytes, and twenty people doing that at once on one network is slow for all of them.

* Installation of [vscode](https://code.visualstudio.com/).
* Open `vscode`, hit the _extensions_ icon (fifth from the top) on the left, and install the _Lean 4 language extension_.
* Install `git`, if you do not have it: open `vscode`, hit the _git_ icon (third from the top on the left), and follow the instructions.
* The exercises repository. Go to where you want the course materials and run
```
git clone https://github.com/pfaffelh/leancourse_exercises
cd leancourse_exercises
lake exe cache get
code .
```
_vscode_ opens with the course materials. (These notes are generated from a second repository, [pfaffelh/leancourse](https://github.com/pfaffelh/leancourse), which you do not need to clone.)

:::paragraph
Another description of the installation is [here](https://leanprover-community.github.io/get_started.html#regular-install).
:::


After `code .` in the `leancourse_exercises` folder, open `Exercises/01-Logic/01-a-Propositions.lean`. It works once the orange and red bars disappear and moving the cursor on the left changes the infoview on the right.
* Copy the `Exercises` directory to `MyExercises` and work there. `MyExercises` is ignored by git, so an update never overwrites your files.
* To update, run `git pull` in `leancourse_exercises`.

If the installation gives you trouble, talk to the teachers rather than spending evenings on it.

# Sources
%%%
number := false
tag := "sources"
%%%

The history follows three surveys, all freely available:

* John Harrison, Josef Urban and Freek Wiedijk, [*History of Interactive Theorem Proving*](https://www.cl.cam.ac.uk/~jrh13/papers/joerg.html), in *Handbook of the History of Logic* 9, Elsevier 2014, 135-214. The standard account, written by three people who built the systems.
* Herman Geuvers, [*Proof assistants: history, ideas and future*](https://www.ias.ac.in/article/fulltext/sadh/034/01/0003-0025), *Sadhana* 34 (2009), 3-25. Organized by idea rather than by year.
* Lawrence Paulson, [*50 years of proof assistants*](https://lawrencecpaulson.github.io//2025/12/05/History_of_Proof_Assistants.html), 2025. The LCF line from the inside.

Where a date or a formulation above comes from one text in particular:

* Alan Turing, [*On Computable Numbers, with an Application to the Entscheidungsproblem*](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf), *Proceedings of the London Mathematical Society* (2) 42 (1936-37), 230-265.
* N. G. de Bruijn, [*Automath, a language for mathematics*](https://pure.tue.nl/ws/portalfiles/portal/2039924/256169.pdf), TH-Report 68-WSK-05, Eindhoven 1968.
* Robin Milner, [*Logic for Computable Functions*](https://web.archive.org/web/20240703134244/http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf), Stanford AIM-169, 1972.
* Lawrence Paulson, Tobias Nipkow and Makarius Wenzel, [*From LCF to Isabelle/HOL*](https://arxiv.org/abs/1907.02836), 2019.
* Freek Wiedijk, [*The Seventeen Provers of the World*](https://www.cs.ru.nl/~freek/comparison/comparison.pdf), Springer LNAI 3600, 2006.
* Fairouz Kamareddine, Joe Wells, Christoph Zengler and Henk Barendregt, [*Characteristics of de Bruijn's early proof checker Automath*](https://arxiv.org/abs/2203.01173), *Fundamenta Informaticae* 185 (2022), 313-336.

* Rob Nederpelt and Herman Geuvers, *Type Theory and Formal Proof: An Introduction*, Cambridge University Press 2014. Section 13.8 sets Zermelo's answer of 1908 against Russell's. Behind a paywall.

Four further sources are on paper or behind a paywall and are only paraphrased here: Hilbert and Ackermann's *Grundzüge der theoretischen Logik* (1928), Church's two papers of 1936, Russell's letter of 1902 in van Heijenoort's *From Frege to Gödel*, and Curry and Feys' *Combinatory Logic* (1958). `sources/history-of-itp.md` in the repository lists all of them.

# Picture credits
%%%
number := false
tag := "credits"
%%%

The mathematical figures were generated by the scripts in `scripts/` and may be reused freely. The photographs, here and in the {ref "slides"}[slide decks], come from Wikimedia Commons and are reproduced under their own licences, unchanged except where noted:

* Thomas Hales -- Slawekb, CC BY-SA 3.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Halescropped.jpg)
* Peter Scholze -- George Bergman, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Peter_Scholze_2014_cropped.jpg)
* Kevin Buzzard -- George Bergman, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Kevin_Buzzard_1996_(headshot).jpg)
* Leonardo de Moura -- David Monniaux, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Leo_de_Moura_P1210629.jpg)
* Maryna Viazovska -- Petra Lein, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Maryna_Vazovska_MFO_2013_crop.jpg)
* Timothy Gowers -- Gert-Martin Greuel, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:William_Timothy_Gowers_Oslo_2012.jpg)
* Ben Green -- Renate Schmid, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Ben_Green.jpg)
* Vladimir Voevodsky -- Renate Schmid, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:VladimirVoevodsky.jpg)
* Terence Tao -- Institute for Pure and Applied Mathematics, CC BY 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Terence_Tao_at_IPAM%27s_Fireside_Chat_2026_%2850m16s%29_%28cropped%29.jpg)
* Gottlob Frege, around 1879 -- photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Young_frege.jpg)
* Bertrand Russell in 1907 -- photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Bertrand_Russell_in_1907.jpg)
* David Hilbert -- photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Hilbert.jpg)
* Kurt Gödel -- photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Kurt_g%C3%B6del.jpg)
* Alan Turing in 1951 -- Elliott and Fry, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Alan_Turing_%281951%29_%28crop%29.jpg)
* Nicolaas Govert de Bruijn -- Konrad Jacobs, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, cropped to head and shoulders, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Nicolaas_de_Bruijn.jpg)

The two product marks in this chapter -- Claude and ChatGPT -- are also from Wikimedia Commons, under CC0 and in the public domain respectively. They remain trademarks of their owners and are used here only to say which system produced which proof.

The icon in the browser tab is the `L` of the Lean wordmark, redrawn as a single stroke on a square in the Freiburg identity blue (`#34499a`). The source is `static/favicon.svg`.

Several people named in this chapter have no freely licensed photograph, and the pattern is not an accident: Georges Gonthier, who formalized both the four colour theorem and the [Feit-Thompson theorem](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem), Johan Commelin, who led the Liquid Tensor Experiment, Patrick Massot, Floris van Doorn and Oliver Nash, who formalized sphere eversion, and Freddie Manners, one of the four authors of the polynomial Freiman-Ruzsa theorem. Alonzo Church is in the same position, for the opposite reason: the photographs of him are recent enough to be under copyright. They appear above as grey silhouettes with their initials. The photographs are therefore a fair sample of who is *famous*, not of who did this work, and the silhouettes are left visible rather than quietly omitted for that reason.
