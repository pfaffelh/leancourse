import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Leancourse.Refs

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

To formalize a proof is to write it in a language precise enough that a computer can check every step. The machine reads the proof and confirms that each step follows from the axioms and from what came before.

There is a second direction. While formalizing starts from a proof and ends in a formal text, autoformalizing starts from informal mathematics and has a machine produce the formal proof.

Both end at a text (the formal proof) the computer accepts. Most importantly, the program that checks the proof (often called the kernel) is small and fixed. Small and fixed is not the same as infallible ({ref "soundness-bugs"}[2026]).

This course is about the first direction. You will write the formal proofs.

# Why formalize?
%%%
number := false
tag := "why-formalize"
%%%

Until recently, every formal proof of a serious theorem was written by people. That is no longer so:

* *September 2025.* Math Inc.'s autoformalizer *Gauss* produced a formal proof of the [prime number theorem](https://en.wikipedia.org/wiki/Prime_number_theorem). People had to step in whenever it got stuck, so Hales calls it a quasi-autoformalization{citep hales2026}[].
* *February 2026.* The [sphere packing](https://en.wikipedia.org/wiki/Sphere_packing) theorem in dimension 8 was finished in five days by *Gauss*, an [autoformalizer from Math Inc.](https://math.inc/sphere-packing) The [human project](https://github.com/math-inc/Sphere-Packing-Lean) it joined had been working on the proof since 2024. Unlike the later entries, this was no new mathematics: the proof was known, and only the formalizing was left. [Maryna Viazovska](https://en.wikipedia.org/wiki/Maryna_Viazovska) proved the dimension-8 case in 2016 and received the Fields Medal for it, which closes a thread that opens with Kepler four hundred years earlier.
* *March 2026.* A week after dimension 8, Math Inc. announced an autoformalization of sphere packing in dimension 24, following Viazovska and her collaborators: about 500 000 lines, pruned afterwards to about 200 000. In May a group at Meta autoformalized large parts of 26 mathematics textbooks, in a project called *ATLAS*. None of this is confined to Lean — in January, Josef Urban posted 130 000 lines of formal topology from Munkres, produced in two weeks in a set-theoretic assistant.
* *4 September 2026.* Anthropic [announced](https://www.anthropic.com/news/formalizing-fermats-last-theorem) the first complete computer-checked proof of [Fermat's Last Theorem](https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem), produced by Claude over eleven days: roughly 13 million lines of Lean and some 29 500 intermediate theorems, following a simplified version of Wiles's 1995 proof and building on *Mathlib*.
* *8 September 2026.* OpenAI [announced](https://openai.com/index/navier-stokes-solution/) a proof, with a Lean formalization, that a smooth three-dimensional fluid obeying the [Navier-Stokes equations](https://en.wikipedia.org/wiki/Navier%E2%80%93Stokes_existence_and_smoothness) *under a smooth external force* can develop a singularity in finite time. (This is not the Millennium Prize problem.) It was followed by a public argument about credit, and about treating open problems as benchmarks.
* *6 October 2026.* OpenAI [published](https://openai.com/index/sharing-ai-progress-in-mathematics/) a catalogue of results from an unreleased internal model — at the time of writing 719 manuscripts grouped into 372 families, of which about 42 % of the top-line results carry a Lean formalization. Each result took, on average, about three hours of the model's thinking time; roughly 4 000 problems were posed in all. (One day later, three of those manuscripts were withdrawn due to errors.)

:::figure "The two systems behind the September 2026 announcements. Both delivered Lean files with their proofs" (tag := "ai-labs")
![Claude](/static/figures/logos/claude.png)
![ChatGPT](/static/figures/logos/chatgpt.png)
:::

The last entry shows the problem. Machines now produce mathematics faster than mathematicians can referee it, and three manuscripts were withdrawn within a day. The only check that keeps up is a formal one.

A Lean proof shows that the formal statement follows from the axioms. It does not show that the statement says what the paper claims; that is a separate, human question. OpenAI's [repository](https://github.com/openai/math) documents, per paper, which checks cover a main theorem and which only a supporting result. One goal of the present course is to learn to read a formal statement and judge what it says.

# Where the field stands
%%%
number := false
tag := "field-stands"
%%%

Two pictures from public data. They compare Lean with [Rocq](https://rocq-prover.org/) (*Coq* until 2025) and [Isabelle/HOL](https://isabelle.in.tum.de/), the two other large proof assistants; how they differ is a question of foundations, taken up under {ref "other-provers"}[The three systems today].

:::figure "New GitHub repositories per quarter, per million new repositories overall" (tag := "itp-repos")
![Line chart: new GitHub repositories per quarter for Lean, Coq/Rocq and Isabelle from 2018 to 2026, each per million new repositories overall; Lean rises from under ten to about two hundred while the others stay near ten](/static/figures/itp_github_repos_per_million.png)
:::

Counting per million corrects for GitHub's own growth, which was steep in 2026. One distortion is left in: the Justin Sun Prize, announced in September 2026, pays for solved problems only against a machine-verified proof, and about a fifth of that month's new Lean repositories carry a prize identifier.

Until about 2023 the three were comparable, with Coq the largest. The rise is recent, and it is not evidence that Lean is better: Isabelle's automation is still ahead in places, and Rocq has decades of verified-software work behind it. It is evidence about where people are going.

:::figure "Papers on the mathematics arXiv whose results are checked in Lean, per 100 submissions" (tag := "arxiv-lean")
![Bar chart: weekly share of arXiv mathematics papers with a Lean-checked result during 2026, rising from about 0.3 per 100 in January to about 2.4 per 100 in early October](/static/figures/arxiv_lean_formalized_share.png)
:::

The share rises through 2026. The highest week so far is the first of October, with 62 of 2 567 papers, 2.4 per 100. It is a share rather than a count because the denominator moved too: the mathematics arXiv received about a thousand submissions a week in January and about two and a half thousand in early October. Maybe, within a few years, reading and writing a formal proof will be ordinary equipment.

# How we got here
%%%
number := false
tag := "how-we-got-here"
%%%

It took mathematics from 1879 to 1936 to turn a proof into a finite object a machine can inspect. Then the machines that inspect it, from 1967 to Lean. Then, from 1976, what has been done with them.

## The mathematics
%%%
number := false
tag := "the-mathematics"
%%%

### 1879 to 1913: Frege and Russell
%%%
number := false
tag := "prehistory"
%%%

Gottlob Frege's *Begriffsschrift* of 1879 gave the first system in which proofs themselves were objects to be manipulated. That work is pure logic, and it survives. Frege then derived arithmetic from it in the *Grundgesetze der Arithmetik* (1893, 1903), using one further axiom: concepts with the same instances have the same extension. Bertrand Russell's letter of 1902 showed that this axiom is inconsistent. The set $`R = \{x : x \notin x\}` is a member of itself exactly if it is not. The letter reached Frege while the second volume was in press.

Russell's set is *impredicative*: it is defined by quantifying over a collection that contains it. The condition ranges over all sets, and $`R` would be one of them. Both repairs below attack that, and the word returns in {ref "prop-special"}[Why `Prop` is special].

Two answers appeared in 1908, and both are still in use. They differ in what they restrict.

:::table (align := left) +header
* + 1908
  + restricts
  + `x ∈ x` is
  + the hierarchy is
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

Russell restricted the language itself, so that `x ∈ x` is not false but ungrammatical. Well-formedness is then a question about syntax, settled before any question of truth arises.

However, Russell's ban was wider than the paradox. It forbids *every* definition that quantifies over a totality containing the object being defined, and ordinary mathematics is full of those. The supremum of a bounded set of reals is defined by quantifying over reals, so under the ban it is not itself a real number, and analysis stops. Russell recovered it by adding an axiom, reducibility, which grants that every forbidden definition agrees with a permitted one — an axiom that returns most of what the ban had taken. Lean draws the line differently for propositions and for data: definitions that quantify over all propositions are allowed in `Prop`, but not over all types in `Type`; see {ref "prop-special"}[Why `Prop` is special].

Mathematics went with Zermelo, proof assistants with Russell ({ref "type-rules"}[The rules of Lean's type theory]).

Whitehead and Russell spent *Principia Mathematica* rebuilding the rest; their proof that `1 + 1 = 2` arrives in the second volume with the note that *the above proposition is occasionally useful*. Done by hand, formalization is unbearable, and for most of a century little came of it.

### 1917 to 1931: Hilbert's programme, and Gödel
%%%
number := false
tag := "hilbert-programme"
%%%

David Hilbert turned formalization into a programme, pressing for it from a lecture of 1917, *Axiomatisches Denken*, onwards. The conviction behind it is older. At the Paris congress of 1900 he had said that in mathematics there is *no ignorabimus* (we shall not know): Every well-posed mathematical question can in principle be settled.

Write mathematics in a fixed formal language, fix the rules of inference, and a proof becomes a finite string of symbols. Whether it follows the rules is then a question about symbols, answerable without knowing what they mean. Three questions about a set of axioms can then be asked precisely, and Hilbert wanted all three answered yes.

* *Consistent.* No contradiction follows from the axioms. Hilbert wanted this proved by finitary means.
* *Complete.* For every statement, either it or its negation follows.
* *Decidable.* A procedure settles, for every statement, which of the two it is.

:::figure "David Hilbert and Kurt Gödel" (tag := "hilbert-godel")
![David Hilbert](/static/figures/portraits/hilbert.jpg)
![Kurt Gödel](/static/figures/portraits/godel.jpg)
:::

Gödel's two theorems need one more word. A *model* of a set of axioms is a concrete structure in which all of them hold. The group axioms have many models: the integers under addition, the invertible $`2 \times 2` matrices, the symmetries of a square. A statement that follows from the axioms holds in every model. Commutativity $`x \cdot y = y \cdot x` holds in the first model and fails in the other two, so it does not follow from the group axioms.

Kurt Gödel settled the first two questions, in opposite directions. His thesis of 1929 proved first-order logic *complete*: a formula that holds in every model is derivable from the axioms. *First-order* is the restriction that quantifiers range over the elements of a domain, never over its subsets, relations or functions. $`\forall x\, \exists y\, (x \cdot y = e)` is first-order; *every bounded set of reals has a supremum* is not, because it quantifies over sets of reals. Logic itself is therefore not the obstacle.

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

They do not conflict. The axioms of arithmetic have models other than $`\mathbb{N}`. These *nonstandard models* contain a copy of $`0, 1, 2, \dots` and, beyond it, further elements larger than every one of these. Recall that Gödel numbers proofs: every proof is a finite string of symbols, and he assigns to each such string a natural number, its *code*. The sentence he builds in 1931 says, in effect, *I am not provable*. As a statement about numbers it reads: *no natural number is the code of a proof of this sentence*. In $`\mathbb{N}` it is true. In some nonstandard model it is false: there, one of the extra elements satisfies the formula *is the code of a proof of this sentence*, although no actual proof has it as its code. So the sentence does not hold in every model, and the theorem of 1929 promises nothing for it. Such a model must exist, by the theorem of 1929: since the sentence is not provable, adding its negation to the axioms is consistent, and a consistent first-order theory has a model.

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

Both had to say first what a procedure is, and each built a formal definition of computation to do it. Turing's is the machine that carries his name: a tape divided into cells, a head that reads one cell, writes and moves one step, and a finite table of instructions. The paper does not say how such a machine would be built; it is there to be reasoned about, not constructed. Church's is the *lambda calculus*, which we will use in this course.

A *calculus* is a formal language together with rules for calculating with its expressions. The lambda calculus has terms for functions and a single rule. The term $`\lambda x.\, x + 1` denotes the function sending $`x` to $`x + 1`, the term $`f\, a` denotes $`f` applied to $`a`, and the rule is substitution:
$$`(\lambda x.\, x + 1)\, 3 \;\rightsquigarrow\; 3 + 1.`
This step is called *β-reduction*; it is one of the {ref "reduction-rules"}[reduction rules] of Lean in the next chapter.
Numbers, pairs and recursion are not built in; they are written as lambda terms. This is why the calculus can serve as a definition of computation, and not only as a way of writing functions. Turing proved in an appendix to [his paper](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf) that his machines and Church's terms compute the same functions. He went to Princeton the following year and took his doctorate under Church. That the two definitions agree is a theorem. That either of them captures what we informally call *computable* cannot be a theorem, because the informal notion has no definition to prove anything from. This claim is the *Church-Turing thesis*. It is supported by evidence: every other definition proposed since has turned out to compute the same functions.

Lean is this calculus with types on top. The Lean spelling of $`\lambda x.\, x+1` is `fun x => x + 1`, and the kernel computes by substituting. The proof {ref "rfl"}[`rfl`] below asks it to check that both sides reduce to the same term:

```lean
#check fun x : Nat => x + 1

example : (fun x : Nat => x + 1) 3 = 3 + 1 := rfl
```

The step from a calculus of functions to a calculus of proofs is the *Curry-Howard correspondence*: a proposition is a type, a proof is a term of that type, and checking a proof is type-checking a program. Haskell Curry saw the pattern for implication in the 1930s; de Bruijn, William Howard and Hans Läuchli extended it to the quantifiers in the 1960s. It is the reason `theorem` and `def` are the same construct in Lean.

Three questions about proofs have three different answers, and a proof assistant is built on the difference.

1. *Does this text prove that statement?* Decidable, and cheap. This is what Lean's kernel does, and the whole trust of the system rests on it.
2. *Find a proof of this statement.* Semi-decidable, and question 1 is the whole reason: proof texts are finite objects, so one can enumerate them and check each. The search ends when a proof exists and runs forever when none does, which is why {ref "exact-qm"}[`exact?`] and {ref "grind"}[`grind`] come with a time limit. Gödel's completeness theorem is not what makes this work, and here it would not be available. It says that *derivable* and *true in every model* coincide for {ref "hilbert-programme"}[first-order logic]; Lean's logic is higher-order, and by the theorem of 1931 it leaves true statements about $`\mathbb{N}` unproved. The search looks for proofs, not for truths.
3. *Decide whether this statement is provable* — always, and with yes or no. Undecidable, by Church and Turing.

:::table (align := left) +header
* + Is there a procedure that
  + confirms it when true
  + refutes it when false
  + verdict
* + 1. *this text* proves the statement
  + yes, and it always stops
  + yes, and it always stops
  + decidable
* + 2. *some text* proves it — find one
  + yes, whenever a proof exists
  + not asked
  + semi-decidable
* + 3. *some text* proves it — answer either way
  + yes, whenever a proof exists
  + no such procedure
  + undecidable
:::

Rows 2 and 3 ask the same question and differ only in what is demanded, which is the whole of the third column. *Semi-decidable* says the second column is filled; *undecidable* says the third is not. The two words do not conflict. The gap is one-sided, and it is what you see when `grind` hangs. It cannot tell you that there is nothing to find, only that it has not found anything yet. The second row is also where automated proof search, begun in the 1950s ({ref "the-assistants"}[below]), comes back: `omega`, `grind` and `bv_decide` search, and in the last case an external SAT solver does, but the result is handed to the kernel as something to check. The search may be unreliable in any way it likes; the check is small and fixed.

So the human writes the proof and the machine checks it. That division of labour is a theorem of 1936, not a property of today's software.

## The proof assistants
%%%
number := false
tag := "the-assistants"
%%%

From 1954 on, computers were set to *find* proofs. By 1959 a program proved all the propositional logic of *Principia Mathematica* in minutes. For mathematics as mathematicians write it, none of this scaled. That line is *automated* theorem proving; this section follows the other one.

### 1967: Automath
%%%
number := false
tag := "first-assistants"
%%%

Nicolaas Govert de Bruijn started *[Automath](https://en.wikipedia.org/wiki/Automath)* at Eindhoven in 1967 and published it in 1968, the first language in which a machine checked proofs. The move is a retreat from the second question to the first. The field that follows is named after what the human keeps doing, *interactive* theorem proving. Its foundation is a typed lambda calculus with dependent types, that is, types that may mention terms, as `Vec α n` ({ref "vectors-indexed"}[lists of length `n`]) mentions `n`. It was the first system in which a proof is a term and checking it is type-checking, the {ref "entscheidungsproblem"}[Curry-Howard correspondence]; de Bruijn found that correspondence himself, not knowing Howard's work. In 1977 L. S. van Benthem Jutting pushed Landau's *Grundlagen der Analysis* through it, the first mathematics book verified end to end.

:::figure "Nicolaas Govert de Bruijn, who built Automath" (tag := "debruijn")
![Nicolaas Govert de Bruijn](/static/figures/portraits/debruijn.jpg)
:::

### 1972 to 1991: Mizar, LCF, HOL, Isabelle, Coq
%%%
number := false
tag := "lcf-line"
%%%

Automath left two problems open. Its proofs were written step by step, with no help from the machine, and they were unreadable to mathematicians. Four lines come out of the following twenty years, and each one starts from a problem the earlier systems had.

:::figure "The proof assistants, and what each one added. Colour is the tradition: the de Bruijn line writes the proof down as a term, the LCF line keeps only the theorem, Mizar is declarative over set theory." (tag := "itp-lineage")
![Timeline from 1967 to 2026, one bar per system. Automath 1967 and LCF 1972 stop; Mizar 1973, Isabelle 1986, HOL 1988, Coq/Rocq 1989 and Lean 2013 all run to the present day](/static/figures/itp_lineage.png)
:::

* *[Mizar](https://mizar.uwb.edu.pl/)*, Andrzej Trybulec, 1973. *Problem:* Automath texts are unreadable. *Answer:* a formal language meant to be read like mathematical prose, over the foundation mathematicians already use, set theory in first-order logic. Its library has been growing for fifty years. *Still missing:* the user cannot add automation of their own; the checker is fixed.
* *[LCF](https://web.archive.org/web/20240703134244/http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf)*, Robin Milner, Stanford 1972 and Edinburgh 1975. *Problem:* automation is a large program, and a bug in it could produce false theorems. *Answer:* `thm` is an abstract data type, and the only functions that produce a value of that type are the inference rules. Tactics may then be written by anyone, in the language ML that was invented for this, without being trusted. *Still missing:* the logic of LCF was made for reasoning about programs, not for mathematics in general.
* *[HOL](https://hol-theorem-prover.org/)*, Mike Gordon, from the mid-1980s. *Problem:* the logic. *Answer:* LCF with simple type theory, Church's higher-order logic of 1940. It quantifies over functions and sets, which is enough for most of mathematics. *[Isabelle](https://isabelle.in.tum.de/)* follows in 1986 (Lawrence Paulson), *Isabelle/HOL* in 1991 (Tobias Nipkow). *Still missing:* types cannot depend on terms, so `Vec α n` cannot be written.
* *[Coq](https://rocq-prover.org/)*, from 1989. *Problem:* dependent types and tactics had not yet met. *Answer:* the *Calculus of Constructions* (Thierry Coquand and Gérard Huet), a dependent type theory in the Automath line, with LCF-style tactics on top. Propositions, proofs and programs are written in one language. *Still missing:* `ℕ` is not built in. It must be encoded by functions, and for that encoding induction cannot be proved. *Answer, from the early 1990s:* the *Calculus of Inductive Constructions* (Coquand and Christine Paulin-Mohring), where inductive types such as `ℕ` are primitive and come with their {ref "nat-intro"}[recursor]. That is the foundation Lean also uses.


A proof assistant is a large program, and large programs have bugs. So the question is which part of it must be correct for an accepted theorem to be actually proved. The LCF and the Automath line answer it differently. In the LCF line only the theorem is kept, not the proof. A bug in a tactic still cannot produce a false theorem, because only the inference rules can produce a value of type `thm`. So only the inference rules must be correct. In the Automath line the system writes down a proof term, which a small, separate checker reads afterwards. Then only the checker must be correct; a system meeting that condition is said to satisfy the *[de Bruijn criterion](https://www.cs.ru.nl/~freek/comparison/comparison.pdf)*. Lean is in the second line: a Lean proof is a term, and the kernel rechecks it no matter which tactic produced it.

Almost nothing here died. *Mizar* has run for fifty years, and *Isabelle*, *Rocq* and the *HOL* family are maintained today; only *Automath* and *LCF* stopped, and each left its architecture to its successors. The field accumulates rather than replaces, and the reason is that a library cannot be moved: *seL4* stays in *Isabelle*, the {ref "four-colour-episode"}[four colour theorem] stays in *Rocq*, and nobody will do either again.

### 2013: Lean
%%%
number := false
tag := "lean-origin"
%%%

:::figure "Leonardo de Moura, who started Lean in 2013" (tag := "demoura")
![Leonardo de Moura](/static/figures/portraits/demoura.jpg)
:::

Leonardo de Moura started Lean at Microsoft Research in 2013. Lean 4, a redesign rather than a new version, arrived in 2021, and is written in Lean itself. Its foundation is the Calculus of Inductive Constructions, which puts it in the Automath line. Kevin Buzzard has argued for Lean among mathematicians since 2018. Where development sits now is {ref "lean-today"}[Current state of Lean], after the record.

### The three systems today
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
* + [Rocq](https://rocq-prover.org/)
  + the predicative Calculus of Cumulative Inductive Constructions
  + yes
  + many separate packages
* + [Isabelle/HOL](https://isabelle.in.tum.de/)
  + simply typed higher-order logic
  + no
  + the *Archive of Formal Proofs*
:::

*Lean and Rocq* are close relatives. Both rest on a dependent type theory in which a proof is a *term* and checking a proof is type-checking; both have an {ref "prop-special"}[impredicative], proof-irrelevant universe `Prop` of propositions sitting under a {ref "universe-determined"}[predicative] hierarchy of data types. Lean differs in four points that return later in these notes: proof irrelevance holds *definitionally*, quotient types are primitive rather than built from setoids, there is no universe cumulativity, and classical reasoning enters through an axiom (`Classical.choice`). Rocq's roots are in program verification — the CompCert C compiler and the Feit-Thompson theorem are Rocq developments — and it extracts verified programs to OCaml or Haskell.

*Isabelle/HOL* uses simple type theory: types are built from base types and arrows, and there are no dependent types. That logic is weak enough to automate well, and Isabelle's automation is the strongest of the three. *Sledgehammer* hands a goal to several external provers at once and reconstructs what they find as a proof Isabelle can check; much of what Lean's `grind` does, Isabelle has done for twenty years. Isabelle is also a framework: HOL is one object logic among several over the intuitionistic meta-logic Isabelle/Pure. Its largest development is *seL4*, an operating-system microkernel verified down to its C implementation.

*How the libraries are organized* matters more day to day than the foundations.

* *Mathlib* is one repository, compiled as a unit. Maintainers review every change, and CI keeps it building against the current Lean. There are no stable releases: *Mathlib* follows Lean, and your project follows *Mathlib*. Results combine without extra work, because all structures live in one hierarchy, built from `class` and `instance` (see the chapters on {ref "typeclasses"}[typeclasses] and the {ref "algebraic-hierarchy-mathlib"}[algebraic hierarchy]).
* *Rocq* has no such centre. Its standard library is small, and the mathematics lives in independent packages — *MathComp*, out of the Feit-Thompson formalization, *Coquelicot* and *MathComp-Analysis* for analysis, and others — distributed through `opam`, with the *Rocq Platform* bundling a tested combination. Packages evolve at their own pace, which is comfortable with one dependency and awkward with two that disagree.
* *Isabelle* sits in between. The *Archive of Formal Proofs* holds refereed, self-contained entries, released in lockstep with Isabelle. Entries may depend on one another but are never merged into one library; the archive is cited like a journal.

We use Lean because *Mathlib* exists: the exercises start with `import Mathlib` and have the real numbers, measure theory and topology already there.

## What came of it
%%%
number := false
tag := "landmarks"
%%%

### 1976: the four colour theorem
%%%
number := false
tag := "four-colour-episode"
%%%

Kenneth Appel and Wolfgang Haken proved the [four colour theorem](https://en.wikipedia.org/wiki/Four_color_theorem). Their argument reduced the problem to a long list of configurations and then checked that list by computer. No human has ever read that part, and for two decades the community argued about whether it counted as a proof at all.

:::figure "Four colours suffice for any map in the plane" (tag := "four-colour")
![A map of thirty-four regions, coloured with four colours so that no two neighbours share one](/static/figures/four_colour.png)
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

Twelve referees worked on it for four years and reported that they were ninety-nine percent certain, and could do no better. The *Annals of Mathematics* published it with that caveat. Hales started the [Flyspeck project](https://en.wikipedia.org/wiki/Flyspeck), which delivered a complete formal proof in HOL Light and Isabelle in 2014: about twenty human work-years and some 500 000 lines of proof script{citep hales2026}[]. This episode is not about computers: peer review had met a proof it could not certify, and more effort would not have helped.

### 2013: Voevodsky
%%%
number := false
tag := "voevodsky-episode"
%%%

In 1989 Vladimir Voevodsky and Mikhail Kapranov published a theorem identifying [higher groupoids](https://en.wikipedia.org/wiki/Infinity-groupoid) with homotopy types. In October 1998 Carlos Simpson posted an argument implying that it could not be true. Voevodsky went on believing his own theorem until the autumn of 2013, when he accepted Simpson's argument and found the error in his own. The theorem is false. The rigid, strictly associative kind of higher groupoid it uses cannot produce the two-sphere, and Dimitri Ara showed in 2012 that among simply connected spaces it produces exactly the products of Eilenberg-MacLane spaces — a thin slice of what had been claimed.

:::figure "Vladimir Voevodsky at Oberwolfach in 2011, during a workshop on the homotopy interpretation of type theory" (tag := "voevodsky")
![Vladimir Voevodsky](/static/figures/portraits/voevodsky.jpg)
:::

His account is about people, not machines. Simpson had a counterexample but could not say which step was wrong, so it stayed unclear who had erred. Mathematics runs, in Voevodsky's words, on *a complex system of mutual trust based on reputations*, and both authors had one. The doubt made the theorem unused without settling it, for fifteen years. A second mistake, in a lemma of his own from 1992, stood in print until a listener checking his lectures found it in 1999; several seminars had read the paper by then. A hard technical argument by a trusted author, he concluded, is *hardly ever checked in detail*.

Voevodsky received the Fields Medal in 2002, and spent the rest of his career on foundations designed so that a machine could check such arguments — not the ones *Mathlib* rests on, and not this course's subject ({ref "other-type-theories"}[other type theories]). This course takes the diagnosis, not the cure. His [own account](https://www.ias.edu/ideas/2014/voevodsky-origins) is short. He died in 2017.

### 2019: perfectoid spaces
%%%
number := false
tag := "perfectoid-landmark"
%%%

By Buzzard, Commelin and Massot ([project page](https://leanprover-community.github.io/lean-perfectoid-spaces/)). They formalized a *definition* rather than a theorem: Scholze's [perfectoid spaces](https://en.wikipedia.org/wiki/Perfectoid_space) of 2012. Whether an object of that complexity could be stated at all in a proof assistant was open, and stating is a different problem from proving. Lean's reputation among mathematicians dates from this project.

:::figure "Kevin Buzzard, Johan Commelin and Patrick Massot" (tag := "perfectoid-people")
![Kevin Buzzard](/static/figures/portraits/buzzard.jpg)
![Johan Commelin](/static/figures/portraits/commelin.jpg)
![Patrick Massot](/static/figures/portraits/massot.jpg)
:::

### 2020: the Liquid Tensor Experiment
%%%
number := false
tag := "lte-episode"
%%%

In December 2020 Peter Scholze posed a challenge on Kevin Buzzard's blog: a theorem in condensed mathematics whose proof he was not sure of. A Fields medallist, publicly unsure of his own argument, asking a machine to check it. The *[Liquid Tensor Experiment](https://leanprover-community.github.io/liquid/)*, led by Johan Commelin, finished in July 2022. *[Condensed mathematics](https://en.wikipedia.org/wiki/Condensed_mathematics)* rebuilds topology on profinite sets rather than on open covers. The request came from a working mathematician at the centre of his subject, not from logicians or computer scientists. That is what had changed.

:::figure "Peter Scholze, who posed the challenge, and Johan Commelin, who led the project" (tag := "lte-people")
![Peter Scholze](/static/figures/portraits/scholze.jpg)
![Johan Commelin](/static/figures/portraits/commelin.jpg)
:::

Buzzard's plenary lecture at the ICM in 2022 marks the point where formalization stopped being a curiosity.

### 2022: sphere eversion
%%%
number := false
tag := "eversion-landmark"
%%%

By Massot, van Doorn and Nash ([project page](https://leanprover-community.github.io/sphere-eversion/)): Gromov's [h-principle](https://en.wikipedia.org/wiki/Homotopy_principle), and with it the fact that a [sphere can be turned inside out](https://en.wikipedia.org/wiki/Sphere_eversion) without tearing or creasing. For closed curves in the plane no such thing is possible: a regular homotopy cannot change the turning number, and everting a circle would send $`+1` to $`-1`. In three dimensions that obstruction vanishes. Formalizing this meant differential topology rather than algebra, so the project built a usable differential-geometry API first and proved the theorem afterwards. That order is the ordinary shape of formalization work, and it is why *Mathlib* matters more than any single theorem in it.

:::figure "Patrick Massot, Floris van Doorn and Oliver Nash" (tag := "eversion-people")
![Patrick Massot](/static/figures/portraits/massot.jpg)
![Floris van Doorn](/static/figures/portraits/vandoorn.jpg)
![Oliver Nash](/static/figures/portraits/nash.jpg)
:::

### 2023: the polynomial Freiman-Ruzsa conjecture
%%%
number := false
tag := "pfr-landmark"
%%%

By Gowers, Green, Manners and Tao ([project page](https://teorth.github.io/pfr/)), formalized under Tao's direction in about three weeks — before the paper had been refereed. It says that a set whose sumset is barely larger than itself must be structured.

:::figure "Three of the four authors: Timothy Gowers, Ben Green and Terence Tao. Freddie Manners has no freely licensed photograph" (tag := "pfr-people")
![Timothy Gowers](/static/figures/portraits/gowers.jpg)
![Ben Green](/static/figures/portraits/green.jpg)
![Terence Tao](/static/figures/portraits/tao.jpg)
:::

The method carried further than the theorem. A *blueprint* cuts a formalization into independent pieces with stated interfaces, so volunteers can work in parallel without talking to each other. Formalization stopped being a job for one team over years.

### 2024 to 2025: the Equational Theories Project
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

The tactic {ref "decide"}[`decide`] checks both statements by trying every element of `Bool`. That is one entry. The project settled 22 028 942 of them.

### 2026: the summer of soundness bugs
%%%
number := false
tag := "soundness-bugs"
%%%

In July and August 2026, several bugs were found in the Lean kernel itself, each of
which allowed a proof of `False`. From `False`, everything follows. All were repaired
within days, and *Mathlib* was rechecked with the repaired kernel.

:::example "Bugs in Lean"

The three that were found and closed:

* [#14484](https://github.com/leanprover/lean4/issues/14484), 22 July: a missing check,
  reachable by an adversarial metaprogram.
* [#14576](https://github.com/leanprover/lean4/issues/14576), 28 July: the kernel accepted
  projections of the wrong structure. The resulting proof of `False` used no axioms at all.
* [#14875](https://github.com/leanprover/lean4/issues/14875), 21 August: the recursor of a
  class inductive could leak a private import.

What they produced was concrete. One gave an illicit disproof of the Collatz conjecture,
another a short illicit proof of the Kepler conjecture — which is how Thomas Hales
({ref "kepler-episode"}[1998]) learned of it.

Two things follow. First, `#print axioms` does not cover this. It reports which axioms a
proof uses, and the proof of `False` from #14576 used none. Second, the remedy is
redundancy rather than trust: about 25 independent Lean kernels exist, so a proof can be
rechecked by a program sharing no code with the one that accepted it. Joachim Breitner's
[*Con-Leche*](https://github.com/leanprover/con-leche) goes further: an external checker,
written in Lean, with a proof in Lean that it never accepts a proof of `False`. That is a
statement about the checker, not about Lean's type theory, whose consistency it assumes
({ref "prop-special"}[the chapter on types]).

This account follows {citet hales2026}[].
:::

# Current state of Lean
%%%
number := false
tag := "lean-today"
%%%

*Releases.* Lean 4 appears once a month, with a release candidate about four weeks ahead. A file `lean-toolchain` in the root of a project names the exact version, `elan` fetches that version, and `lake` builds against it. This course is pinned to `leanprover/lean4:v4.34.0`, so the notes and your machine agree all semester.

*Who builds Lean.* The [Lean FRO](https://lean-lang.org/fro/), a non-profit [founded in July 2023](https://lean-lang.org/fro/about/) under [Convergent Research](https://www.convergentresearch.org/), with [nineteen people](https://lean-lang.org/fro/team/) at the time of writing. [Leonardo de Moura](https://leodemoura.github.io/) is chief architect, [Sebastian Ullrich](https://sebasti.a.nullri.ch/) head of engineering. It runs on donations: the Simons Foundation International, the Alfred P. Sloan Foundation, the Richard Merkin Foundation, [Amazon](https://www.amazon.science/news/amazon-is-investing-in-the-lean-focused-research-organization), and [five million dollars](https://www.renaissancephilanthropy.org/news-and-insights/lean-fro-and-mathlib-receive-10m-from-xtx-markets-founder-alex-gerko-to-further-advance-the-use-of-ai-for-mathematical-research) from Alex Gerko of XTX Markets in July 2025. Lean has no vendor behind it, and it is no longer a spare-time project either.

*Mathlib.* [*Mathlib*](https://github.com/leanprover-community/mathlib4) is organized as described {ref "other-provers"}[above]. Every file in this course starts with `import Mathlib`, so we make no distinction between Lean and *Mathlib*. Compiling it from source takes hours, which is why `lake exe cache get` downloads what the CI already built.

Measured on the version pinned for this course (15 September 2026): 8 529 files, 2.33 million lines, about 189 000 theorems and lemmas, about 64 000 definitions, instances and structures, by 1 031 contributors in 34 768 commits. In the thirty days before that date it received 820 commits, 27 per day. The library changes while you use it.

*Who maintains Mathlib.* For fifteen years, nobody was paid to. The [Mathlib Initiative](https://mathlib-initiative.org/), a programme of Renaissance Philanthropy begun in September 2025, now employs maintainers; it received the other five million dollars of Gerko's gift. Its stated targets are review within a week for nine out of ten pull requests, keeping the downstream ecosystem building, and documentation. Johan Commelin, who led the {ref "lte-episode"}[Liquid Tensor Experiment], works there.

*Reading the library.* The [interactive import map](https://leanprover-community.github.io/mathlib4_docs/mathlib.html) draws *Mathlib* as a graph of its modules: which file may use which, and therefore in what order the library is built. The same site serves the [API documentation](https://leanprover-community.github.io/mathlib4_docs/) for every declaration.

*Lean is also a programming language*; see [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/).

*Will this last?* Unknown, and the record reads both ways. Against: *Rocq* had the most new repositories until about 2023 and was overtaken within three years ({ref "field-stands"}[the first figure]), so size settles nothing. For: in sixty years no proof assistant has been replaced by another, only joined. What does get replaced is a system by its own successor — Lean 1 to Lean 4 each broke the one before, and moving *Mathlib* from Lean 3 to Lean 4 occupied the community for more than a year. Either way most of this course survives it. Dependent types, the difference between a tactic and a term, how a hierarchy of structures is organized, and reading a formal statement are not Lean-specific.

# Running the course
%%%
number := false
tag := "practical-pointer"
%%%

Goals, the week-by-week plan, the short tests, what a machine needs
and how to install Lean are in the {ref "organization"}[Organization
chapter].

# Other courses
%%%
number := false
tag := "other-courses"
%%%

* [_The Incredible Proof Machine in Lean_](https://pfaffelh.github.io/ipm): proofs as pictures, in the browser, in English or German. Nine worlds, from conjunction through the quantifiers to induction, and a tactic trainer. It teaches the shape of a proof before any Lean syntax, and it belongs to this course. After Joachim Breitner's Incredible Proof Machine.
* [_Natural Number Game_](https://adam.math.hhu.de/#/g/leanprover-community/nng4): proofs about `ℕ` in the browser, nothing to install. The usual first contact with Lean's tactics, and a good use of an evening before the course starts.
* [_Formalising Mathematics_](https://b-mehta.github.io/formalising-mathematics-notes/) by Bhavik Mehta, after notes by Kevin Buzzard: the format of the present course follows these.
* [_Mathematics in Lean_](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot: the closest thing to an official course, organized by area of mathematics.

# Sources
%%%
number := false
tag := "sources"
%%%

* John Harrison, Josef Urban, Freek Wiedijk, [*History of Interactive Theorem Proving*](https://www.cl.cam.ac.uk/~jrh13/papers/joerg.html), Handbook of the History of Logic 9, 2014.
* Herman Geuvers, [*Proof assistants: history, ideas and future*](https://www.ias.ac.in/article/fulltext/sadh/034/01/0003-0025), Sadhana 34, 2009.
* Lawrence Paulson, [*50 years of proof assistants*](https://lawrencecpaulson.github.io//2025/12/05/History_of_Proof_Assistants.html), 2025.
* Lawrence Paulson, Tobias Nipkow, Makarius Wenzel, [*From LCF to Isabelle/HOL*](https://arxiv.org/abs/1907.02836), 2019.
* Freek Wiedijk, [*The Seventeen Provers of the World*](https://www.cs.ru.nl/~freek/comparison/comparison.pdf), LNAI 3600, 2006.
* Alan Turing, [*On Computable Numbers, with an Application to the Entscheidungsproblem*](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf), 1936.
* N. G. de Bruijn, [*Automath, a language for mathematics*](https://pure.tue.nl/ws/portalfiles/portal/2039924/256169.pdf), 1968.
* Fairouz Kamareddine, Joe Wells, Christoph Zengler, Henk Barendregt, [*Characteristics of de Bruijn's early proof checker Automath*](https://arxiv.org/abs/2203.01173), 2022.
* Robin Milner, [*Logic for Computable Functions*](https://web.archive.org/web/20240703134244/http://i.stanford.edu/pub/cstr/reports/cs/tr/72/288/CS-TR-72-288.pdf), 1972.
* Rob Nederpelt, Herman Geuvers, *Type Theory and Formal Proof*, Cambridge University Press 2014.

# Picture credits
%%%
number := false
tag := "credits"
%%%

* Mathematical figures — generated by the scripts in `scripts/`, free to reuse
* Thomas Hales — Slawekb, CC BY-SA 3.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Halescropped.jpg)
* Peter Scholze — George Bergman, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Peter_Scholze_2014_cropped.jpg)
* Leonardo de Moura — David Monniaux, CC BY-SA 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Leo_de_Moura_P1210629.jpg)
* Timothy Gowers — Gert-Martin Greuel, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:William_Timothy_Gowers_Oslo_2012.jpg)
* Ben Green — Renate Schmid, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Ben_Green.jpg)
* Vladimir Voevodsky — Renate Schmid, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:VladimirVoevodsky.jpg)
* Terence Tao — Institute for Pure and Applied Mathematics, CC BY 4.0, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Terence_Tao_at_IPAM%27s_Fireside_Chat_2026_%2850m16s%29_%28cropped%29.jpg)
* Gottlob Frege, around 1879 — photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Young_frege.jpg)
* Bertrand Russell in 1907 — photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Bertrand_Russell_in_1907.jpg)
* David Hilbert — photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Hilbert.jpg)
* Kurt Gödel — photographer unknown, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Kurt_g%C3%B6del.jpg)
* Alan Turing in 1951 — Elliott and Fry, public domain, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Alan_Turing_%281951%29_%28crop%29.jpg)
* Nicolaas Govert de Bruijn — Konrad Jacobs, Archives of the Mathematisches Forschungsinstitut Oberwolfach, CC BY-SA 2.0 de, cropped to head and shoulders, [via Wikimedia Commons](https://commons.wikimedia.org/wiki/File:Nicolaas_de_Bruijn.jpg)
* Johan Commelin — used by permission, from the [Mathlib Initiative team page](https://mathlib-initiative.org/team/)
* Patrick Massot — used by permission, from [his homepage](https://www.imo.universite-paris-saclay.fr/~patrick.massot/en/)
* Oliver Nash — used by permission, from the [Mathlib Initiative team page](https://mathlib-initiative.org/team/)
* Kevin Buzzard — Thomas Angus, Imperial College London, used by permission
* Floris van Doorn — used by permission
* Claude and ChatGPT logos — CC0 and public domain, via Wikimedia Commons; trademarks of their owners
* Browser-tab icon — the `L` of the Lean wordmark, redrawn (`static/favicon.svg`)
* Alonzo Church — no freely licensed photograph; grey placeholder
