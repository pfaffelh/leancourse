# Speaker notes — Introduction deck (week 1, Monday)

33 slides. Roughly 75 minutes if every background item is used; the
history block (slides 7–18) is the part to compress if time runs short.

**Navigation: one key press is one slide.** The deck has no step-by-step
reveals — every slide is complete the moment it appears, so nothing is
hidden while you talk. Lines that used to turn blue on a click are blue
from the start; they are the punchline of their slide.

Each section below is one slide, in deck order. Bullets marked
**[Hintergrund]** are background that is *not* in the course notes —
use what fits, skip the rest.

---

## 1. Why formalize?

- Say who you are, that the notes are online, that Wednesday is the
  first toutorial session.
- One sentence of framing: *this is a course about writing proofs that
  a machine accepts, not about a machine finding proofs.*

---

## 2. What formalizing means


- Definition: write the proof in a language precise enough that a machine
  checks every step. 
- The machine does **not** find the proof. It reads yours.
- Autoformalizing runs the other way: informal mathematics in, formal text out.
- Both end in the same place — a text the kernel accepts.
- **The asymmetry.** The program that writes a proof may be unreliable in
  any way it likes; the program that checks it is small and fixed. This
  is the single idea the whole lecture rests on. It returns as the
  *de Bruijn criterion* (slide 15) and as the decidability table (slide 14).
- This course is direction one. They write the proofs.
- **[Hintergrund]** Lean's kernel is **8 071 lines of C++** — 37 files in
  `src/kernel/`, measured on the version this course is pinned to
  (v4.34.0). Everything else — elaborator, tactics, `match`, instance
  search, Mathlib — sits outside the trusted base and is re-checked.
  That ratio is the design.
  - **Expect the objection "but Lean is written in Lean".** It is: the
    repository is about 43 MB of Lean against 1.5 MB of C++, roughly
    97 % Lean. The elaborator, the tactic framework, the compiler front
    end and `lake` are all Lean. **The exception is precisely the part
    you have to trust** — `src/kernel/` and `src/runtime/` are C++, and
    so is the bootstrapping compiler. Good line: *Lean is written in
    Lean, except for the part you are not allowed to doubt.*
  - If pressed on why: the kernel predates self-hosting and is
    deliberately frozen. And there is a Lean answer anyway —
    **Lean4Lean**, a kernel written and formally verified in Lean, plus
    about 25 further independent kernels (see the extra section).

---

## 3. 2026


Five dates, all on screen at once. Take them in order; the slide's order
is not chronological, so say February first.

- **Feb 2026 — sphere packing, dim. 8.** The cleanest case: mathematics
  settled since 2016, only the formalizing left. Autoformalizer *Gauss*,
  from Math Inc. Five days.
  - **[Hintergrund]** The human project it joined started early 2024, when
    Sidharth Hariharan — an Imperial exchange student at EPFL — went to see
    Viazovska. Chris Birkbeck and Seewoo Lee joined over the summer; it
    became Hariharan's master's thesis under Bhavik Mehta. Two years of
    human work, then five days. That contrast is the whole slide.
  - **[Hintergrund]** Two weeks later Gauss did dimension 24 as well,
    over 200 000 lines.
  - **[Hintergrund]** Viazovska proved dimension 8 in March 2016 in a
    23-page paper; dimension 24 followed about a week later with Cohn,
    Kumar, Miller and Radchenko. The method — "magic functions" built
    from modular forms — came out of nowhere. Fields Medal 2022, the
    second woman after Mirzakhani. She is from Kyiv. The optimal packing
    in dimension 8 is the E₈ lattice, in dimension 24 the Leech lattice;
    **dimensions 4 to 7 are open**, which students never expect.
  - **This closes the thread that opened with Kepler**, four hundred
    years earlier. Point back to it when slide 20 comes.
- **4 Sep 2026 — Fermat's Last Theorem.** Anthropic, Claude, eleven days,
  ~13 M lines of Lean, ~29 500 intermediate theorems. Built on Mathlib,
  following a simplified Wiles.
  - Buzzard reviewed it and confirmed it assumes nothing but the axioms.
  - **[Hintergrund]** The irony worth saying out loud: Buzzard holds a
    five-year EPSRC grant (Oct 2024 – Sep 2029, EP/Y022904/1) to formalize
    FLT by hand, full time. He is the person paid to do it slowly, and he
    is the one who certified that a machine did it in eleven days.
- **8 Sep 2026 — Navier-Stokes.** The *forced* equation. **Not** the
  Millennium problem; the prize is unclaimed. Say this plainly — the press
  did not.
- **6 Oct 2026 — the catalogue.** 719 manuscripts, 372 families, ~42 % with
  a Lean formalization. About three hours of model thinking time each,
  ~4 000 problems posed.
- **7 Oct 2026 — one day later.** Three manuscripts withdrawn (a sign error,
  plus two that depended on it), fourteen revised. **None of the withdrawn
  ones had a Lean proof.** Do not put it on the slide; say it.
- Closing line: machines now produce mathematics faster than mathematicians
  can referee it, and the only check that keeps up is a formal one.
- Do not oversell — the next slide takes it back a step.

---

## 4. But be precise


- A Lean proof certifies that *a formal statement* follows from the axioms.
- Whether that statement is the theorem in the paper is a human question,
  and no machine answers it.
- OpenAI's repository documents, per paper, which checks cover a main
  theorem and which only a supporting result. That distinction is the
  honest part of the release.
- Reading a formal statement and judging what it says is most of what
  this course teaches. Say it slowly; it is the course's actual claim.
- **[Hintergrund]** The classic failure mode is a vacuous hypothesis: a
  theorem about an empty class is trivially true and perfectly checked.
  Nothing in the kernel notices.

---

## 5. Where people are going


- Chart: new GitHub repositories per quarter, Lean vs. Coq/Rocq vs.
  Isabelle, per million new repositories overall.
- Why per million: GitHub itself grew steeply in 2026.
- One distortion left in: the Justin Sun Prize (Sept 2026) pays only
  against a machine-verified proof; about a fifth of that month's new Lean
  repositories carry a prize identifier.
- Until about 2023 the three were comparable, and Coq was the larger.
- **Not** evidence that Lean is better. Isabelle's automation is still
  ahead in places; Rocq has decades of verified-software work behind it.
  Evidence about where people are going, nothing more.

---

## 6. Papers checked in Lean


- Share, not count — the denominator moved: ~1 000 arXiv math submissions
  a week in January, ~2 500 in early October.
- Highest week so far: first week of October, 60 of 2 546 papers, 2.4 per 100.
  One week, so not a trend by itself.
- Within a few years, reading and writing a formal proof will be ordinary
  equipment. **This is the answer to "why spend a semester on this".**

---

## 7. How we got here


- Roadmap slide. Four lines, chronological, all visible at once.
- 1879–1936: the mathematics. Turning a proof into a finite object a
  machine can inspect took from Frege to Turing.
- 1967–1991: the first checkers.
- 1976, 1998, 2013, 2020: four episodes, each adding a *different* reason —
  what a computer proof is worth; where peer review stops; whether the
  author can trust himself; who is asking for this now.
- 2013: Lean. The idea is 150 years old, the tool is 13.
- If the hour is short, the mathematics block is what to cut.

---

## 8. Frege and Russell


- **1879, Frege, *Begriffsschrift*.** The first system in which a proof is
  itself an object you can manipulate. Quantifiers, variables, inference
  rules — all of it invented at once.
  - **[Hintergrund]** His notation was two-dimensional, drawn with
    branching lines, and nobody adopted it. Peano's linear notation won;
    Russell took Peano's. Frege was read by almost no one in his lifetime.
  - **Peano's axioms are deliberately not on this slide.** They belong to
    the chapter where `Nat` is introduced, not to the story of the
    paradox. If someone asks: 1889, zero, successor, induction, credited
    by Peano himself to Dedekind (*Was sind und was sollen die Zahlen*,
    1888) — and literally the shape of Lean's `Nat`. Promise it for
    week two rather than telling it here.
- **1902, Russell's letter.** The set of all sets that are not members of
  themselves.
  - **Say which book, the two get confused.** The *Begriffsschrift* (1879)
    is the logic and survives untouched. What the paradox destroys is
    Frege's **Grundgesetze der Arithmetik** (vol. I 1893, vol. II 1903),
    where he derives arithmetic from that logic using one extra axiom —
    **Basic Law V**, that concepts with the same instances have the same
    extension. That axiom, and only that axiom, is the casualty.
  - The letter arrived in June 1902, while volume II was in press. Frege
    added an appendix: a scientist can hardly meet with anything more
    undesirable than to have the foundation give way as the work is finished.
  - **[Hintergrund]** Zermelo had found the same paradox independently and
    earlier — around 1899, told Hilbert, never published. Recorded in a
    note of Husserl's.
- **1910–13, *Principia Mathematica*.** Whitehead and Russell rebuild.
  `1 + 1 = 2` is proved in volume II (*110.643) with the remark that
  the proposition "is occasionally useful".
  - **[Hintergrund]** By Russell's own account the book lost money: the
    Royal Society gave £200, Cambridge University Press covered part, and
    the two authors paid £50 each. They earned minus fifty pounds for ten
    years' work.
- The moral: done by hand, formalization is unbearable. For most of a
  century almost nothing came of it.
- No machines in this block yet — those start on slide 15.

---

## 9. Two repairs, 1908


- **This is the whole reason the course is about types.** Take the time.
- **Zermelo** restricts which sets *exist*: unrestricted comprehension —
  `{x : φ(x)}` for any property — is replaced by **separation**, which
  forms only `{x ∈ A : φ(x)}` out of a set `A` you already have. The
  language is untouched: `x ∈ x` stays a well-formed formula that happens
  to be false for every set.
  - **Walk the derivation on the slide, it is three lines.** Put
    `R = {x ∈ A : x ∉ x}`. Then `R ∈ R` iff (`R ∈ A` and `R ∉ R`). If
    `R ∈ R` the right side gives `R ∉ R`, so `R ∉ R`. Substituting that
    back, `R ∈ R` iff `R ∈ A`, and since `R ∉ R` we get `R ∉ A`.
  - **The payoff is the point:** `A` was arbitrary, so every set omits
    some set. The contradiction has turned into a theorem — there is no
    set of all sets. Nothing was forbidden; something was proved.
  - Foundation came later (von Neumann 1925, Zermelo 1930) and is *not*
    the repair.
- **Russell** restricts what may be *said*: he stratifies the grammar, so
  `x ∈ x` is not a false statement but no statement at all.
  - Well-formedness becomes a question about syntax — and therefore
    decidable. **That is exactly what a type checker decides.**
- Both produce a hierarchy; the difference is who enforces it. In set
  theory the cumulative hierarchy is a *theorem*: you may write the bad
  expression and then prove it denotes nothing. In type theory you do not
  get that far — it is a *rule*.
- Mathematics went with Zermelo. Proof assistants went with Russell.
- This is why Lean has `Type 0 : Type 1 : …` and no type of all types.
### Russell overshot, and it cost him analysis

Worth three or four minutes: it is the cleanest motivation for how Lean
draws the line, and it comes back in the *Types* chapter.

- **The ban is much wider than the paradox needs.** Russell did not just
  forbid `x ∈ x`. He adopted the **vicious circle principle**: no object
  may be defined by quantifying over a totality that contains it. A
  definition that does is called **impredicative**. Russell's set is one
  such; the trouble is that ordinary mathematics is full of them and
  almost none of them are paradoxical.
- **The supremum is the standard casualty. Spell it out:**
  - Let `S ⊆ ℝ` be non-empty and bounded above. `sup S` is *defined* as
    the least upper bound: the `b` with (i) `x ≤ b` for all `x ∈ S`, and
    (ii) `b ≤ c` **for every upper bound `c`**.
  - Clause (ii) quantifies over *all* real numbers. And `sup S` is itself
    meant to be a real number. So the definition ranges over a totality
    that contains the thing being defined — impredicative, and banned.
  - In Russell's ramified system the damage is precise. Reals are built
    from propositional functions, and those carry an *order*: the order
    of a function is above the order of everything it quantifies over.
    So if `S` is a set of reals of order `n`, then `sup S` comes out at
    order `n + 1`. **It is a real number of a higher order, not one of
    the reals you started with.**
  - Consequence: the least upper bound property fails *within* any one
    order. You cannot iterate, you cannot take a sup of sups, and
    essentially all of analysis stops. Not a corner case — Dedekind cuts,
    completeness, limits, the whole construction of `ℝ`.
- **His rescue, and why nobody liked it.** Russell added the **axiom of
  reducibility**: every propositional function is coextensional with a
  predicative one — one of the lowest order. That collapses the orders
  and gives the supremum back.
  - It is pure assertion. It hands back exactly what the ban had taken,
    with no independent reason to believe it. The tower is built and then
    declared harmless.
  - **[Hintergrund]** Russell conceded the point himself in the second
    edition of *Principia* (1925), calling reducibility a defect. Weyl
    took the other road in *Das Kontinuum* (1918): accept the loss and
    rebuild what analysis you can predicatively. Ramsey's diagnosis
    (1926) was sharpest — the paradoxes split in two. The *logical* ones
    (Russell's) need types; the *semantic* ones (Berry's "the least
    integer not nameable in under eleven words", Richard's) are about
    language, not mathematics. Only the semantic ones motivated the
    orders. Drop them and simple type theory suffices, no reducibility
    needed. That is the ancestor of what Lean does.
- **How Lean draws the line instead, and this is the payoff:** not one
  rule for everything. Impredicativity is **granted in `Prop`** and
  **refused for data**. A proposition may be defined by quantifying over
  all propositions; a type may not be defined by quantifying over all
  types.
  - So the supremum is unproblematic. The property defining the cut
    ranges over all reals, but that property is a `Prop`, and a `∀` into
    `Prop` does not climb a universe. What it carves out is an ordinary
    `Set ℚ`, at the same level as any other.
  - One level up the same move is fatal: `Type : Type` is inconsistent by
    Girard's paradox. Hence `Type 0 : Type 1 : …` and no type of all
    types.
  - Full treatment in the *Types* chapter, section *Why `Prop` is
    special*. Promise it; do not prove it here.

---

## 10. Hilbert's programme, 1917


- Fix the language, fix the rules. A proof becomes a finite string, and
  checking it becomes a question about symbols — no meaning needed.
- Three questions: **consistent?** **complete?** **decidable?** Hilbert
  wants all three.
- The consistency proof was to use finitary means only — no appeal to the
  infinite objects whose consistency was in question.
- The formalization half is exactly what a proof assistant does. Hilbert
  got that part.
- **The year on the slide is the starting gun, not the whole story.**
  *Axiomatisches Denken*, 1917: Hilbert returns to foundations after a
  gap and sets the task. The programme in its mature form is the 1920s,
  and the three questions get their sharpest statement in Hilbert and
  Ackermann, 1928 — which is where the next slide but one picks up. The conviction is older: Paris 1900, "denn in
  der Mathematik gibt es kein Ignorabimus".
- **[Hintergrund]** Königsberg, September 1930: Hilbert gives the radio
  address ending "Wir müssen wissen, wir werden wissen". At the same
  meeting, the day before, a 24-year-old Gödel announced incompleteness in
  a round-table discussion. Almost nobody in the room understood what had
  happened; von Neumann did. Hilbert probably never heard the talk.
  **This is the best anecdote in the lecture — do not rush it.**

---

## 11. Gödel, 1929 and 1931


- Two theorems, opposite directions, same person, two years apart.
- **1929** (his dissertation, Vienna, under Hans Hahn): first-order logic
  is **complete**. Valid in every model ⇒ derivable. Logic itself is not
  the obstacle. This is what makes proof *search* terminate when a proof
  exists — row two of the table on slide 14.
- **The definition is now on the slide.** The job of the second example
  is to show the step out of first order: "every bounded *set* of reals"
  quantifies over subsets of the domain, not over its elements.
  - **Lean is not first-order** — it quantifies over types and over
    propositions. So 1929 does not apply to Lean. Flag this; it matters
    again when the *Types* chapter discusses consistency.
- **Watch the word *complete*, it does two jobs.** A *logic* is complete
  when everything valid is derivable (1929). A *theory* is complete when
  it decides every statement (1931, and Hilbert's second question). No
  conflict: the Gödel sentence is true of ℕ but false in other models of
  the axioms, so it is not *valid*, and 1929 says nothing about it.
- **1931:** any consistent system containing arithmetic, with axioms a
  machine can list, misses true statements about ℕ — and cannot prove its
  own consistency. The programme fails. The formalization survives.
- **Gödel's proof is itself the first serious piece of formalization:**
  he encodes formulas and proofs as numbers and computes with them.
  Proofs as data. That is the course's subject, in 1931.
- **[Hintergrund]** Later: consistency of AC and CH with ZF (1938),
  the constructible universe. He became increasingly paranoid, ate only
  what his wife prepared, and starved to death in Princeton in 1978 when
  she was hospitalized.
- **[Hintergrund]** At his US citizenship hearing on 5 December 1947 he
  announced he had found a flaw in the Constitution by which the republic
  could be turned into a dictatorship by lawful means. Einstein and
  Morgenstern, his witnesses, steered him off it. The judge had asked what
  the government of Austria was; Gödel answered that it was a republic
  "but the constitution was such that it finally was changed into a
  dictatorship" — he had lived through that in 1933/34.
  - **If someone asks which flaw: nobody knows.** Gödel never wrote the
    argument down and Morgenstern's memorandum does not record it. The
    usual reconstruction (Suber 1990, Guerra-Pujol 2013) is Article V,
    the amendment procedure, whose limits are purely procedural: it says
    *how* to amend, not *what* may be amended, so the amendment power can
    be turned on Article V itself. On that reading the loophole is still
    open, because Article V is unchanged. But that is a reconstruction,
    not Gödel's documented claim — say so rather than asserting it.

---

## 12. 1936: the Entscheidungsproblem


- **1928**, Hilbert and Ackermann, *Grundzüge der theoretischen Logik*:
  is there a procedure deciding whether a formula is provable?
- **1936**, Church and Turing, independently: there is none.
- Before they could answer it they had to say what a *procedure is*.
  Turing: a tape, a head, a finite table of instructions. Church: the
  λ-calculus.
- Church's paper was submitted in April 1936, Turing's a few months later.
  Neither knew of the other at the start. Turing went to Princeton the
  following year and took his doctorate under Church.
- Turing's machine is **not a design**. Nothing in the paper says how one
  would be built. It exists to be reasoned about.
- The two models compute the same functions — that is a *theorem*, in an
  appendix to Turing's paper. That either of them is what "computable"
  *means* is **not** a theorem: that is the Church-Turing thesis, a claim
  about a word.
- There is no freely licensed photograph of Church, so this slide shows
  Turing alone. Worth one sentence if anyone asks.
- **[Hintergrund]** Church's first λ-calculus was *inconsistent*
  (Kleene-Rosser, 1935). He kept the consistent untyped fragment, and the
  repair — types — is what Lean inherits.
- **[Hintergrund]** Church's doctoral students: Turing, Kleene, Rosser,
  Dana Scott, Smullyan, Hartley Rogers. Few supervisors have had that run.
- **[Hintergrund]** Turing, 1949, "Checking a large routine": the first
  paper on *proving a program correct*, twenty years before Floyd and
  Hoare. Two pages. Almost nobody noticed.

---

## 13. The lambda calculus


- A notation for functions, and nothing else.
- `λx. x + 1` is the function adding one. The only rule is substitution:
  `(λx. x + 1) 3` becomes `3 + 1`.
- Numbers, pairs, recursion are not built in — they are written as
  λ-terms, and that suffices for everything Turing machines compute.
- Lean is this notation with types on top. `fun x =>` is `λx.`, and Lean
  accepts `λ` too. **They will type this all semester.** Ninety years old.
- The kernel computes by substituting. That is the rule above and nothing more.

### How can a calculus be a "machine"?

The question comes every year. Nothing here needs hardware.

- **What a "machine" has to be** for the 1936 argument: a finite
  description, a purely syntactic step rule, and no point at which
  insight is required. Turing's tape and head satisfy that. So does one
  rewriting rule.
- **β is search-and-replace.** Find a `(λx. M) N`, copy `N` into every
  place where `x` stands in `M`. A clerk can run it without knowing what
  the symbols mean. That is the whole mechanism.
- **The data are encoded as terms.** A number is the function that
  applies something `n` times:
  - `0 = λf. λx. x`, `1 = λf. λx. f x`, `2 = λf. λx. f (f x)`
  - `succ = λn. λf. λx. f (n f x)`
  - `add  = λm. λn. λf. λx. m f (n f x)`
  - So computing `2 + 3` **is**: write `add 2 3`, β-reduce until no redex
    is left, read off `5`. **The reduction is the computation; the normal
    form is the output.** Nothing else happens.
  - Booleans the same way: `true = λx. λy. x`, `false = λx. λy. y`, and
    `if b then m else n` is just `b m n`. Pairs and lists likewise.
- **Recursion is the part that matters**, because without unbounded loops
  you stay inside primitive recursion and — more to the point — nothing
  fails to terminate, so there is nothing undecidable to find.
  - `Y = λf. (λx. f (x x)) (λx. f (x x))` reduces `Y g` to `g (Y g)`. The
    term reproduces itself: a function calls itself without having a name.
  - The same trick gives the endless loop `(λx. x x)(λx. x x)`, which
    reduces to itself forever.
- **Why it counts as a model of computation.** Not by decree. Three
  formalisms that grew up apart define the same class of functions:
  λ-definable (Church), general recursive (Gödel, Herbrand, Kleene) and
  Turing-computable (Turing, in the appendix of his 1936 paper). That
  convergence is the evidence for the Church-Turing thesis — which is a
  claim about the word "computable", not a theorem.
- **[Hintergrund]** Church's undecidability proof stays inside this
  frame: he first shows it is undecidable whether two λ-terms have the
  same normal form, and derives from that that no λ-definable function
  decides provability in first-order logic.
- **The line to use:** Turing asks what a clerk with paper can do; Church
  asks what can be written as a function and substituted. Same answer.
- **And it is the Church side the course lives on.** Lean's kernel has no
  tape head; it reduces terms. The line on the slide,
  `(fun x : Nat => x + 1) 3 = 3 + 1`, is exactly the rule above.
- **Curry-Howard**, the step from functions to proofs: a proposition is a
  type, a proof is a term of that type, checking a proof is type-checking
  a program. Curry saw it for implication in the 1930s; de Bruijn, Howard
  and Läuchli extended it to quantifiers in the 1960s.
  - It is why `theorem` and `def` are the same thing in Lean. Say it now,
    prove it in week three.

---

## 14. Checking is not finding


- **Read the table down the second column, not across.** Rows 2 and 3 ask
  the *same* question; row 3 simply adds row 1's demand. That one
  combination — the open question with the always-halt demand — is the
  impossible one.
- **Row 1 — "does *this text* prove φ?": decidable.** Always stops, either
  way. This is the kernel, and the entire trust of the system sits here.
- **Row 2 — "*some text* proves it, find one": semi-decidable.** Proofs can
  be enumerated, so a search terminates when there is something to find.
  If there is nothing, it runs forever. **Hence the time limit on every
  automation tactic:** `exact?`, `apply?`, `grind`, `omega`.
- **Row 3 — the same question, now answered either way: undecidable.**
  The Entscheidungsproblem itself.
- Rows 2 and 3 look contradictory and are not. Same set of statements.
  Semi-decidable: every yes is eventually found. Undecidable: the noes
  are not — nothing reliably reports that a statement has no proof.
- **One confusion to head off**, because it is the natural misreading of
  row 3: it is *not* "is φ either provable or refutable?". That is a
  different question — whether the theory *decides* φ — and Gödel 1931
  answers it with no for arithmetic. Also undecidable, also worth
  knowing, but not what Hilbert and Ackermann asked. The
  Entscheidungsproblem is about provability alone.
- **The gap is one-sided, and it is exactly what they see when `grind`
  hangs.** It cannot say there is nothing there, only that it has not
  found anything yet. Students hit this in week two; name it now.
- "You prove, the machine checks" is a theorem, not a gap in today's
  software. **This is the answer to "why doesn't the computer just do it".**

---

## 15. 1967: Automath


- **Say what de Bruijn turned away from.** Since 1954 the attempt had been
  to make the machine *find* proofs: Davis on the JOHNNIAC (1954), the
  Logic Theory Machine (Newell/Simon/Shaw, 1956), Wang (1959), Robinson's
  resolution (1965). It works for logic calculi and does not scale to
  mathematics.
- De Bruijn retreats to the cheap question: the human proves, the machine
  checks. **That is the split between *automated* and *interactive*
  theorem proving — and the title of this course sits on one side of it.**
- Automath: Eindhoven, 1967, published 1968. A typed λ-calculus with
  dependent types, not set theory. The first machine-checked proofs.
- He arrived at the Curry-Howard correspondence himself, not knowing
  Howard's work, and was the first to use it in a running system.
- **1977:** van Benthem Jutting's thesis pushes Landau's *Grundlagen der
  Analysis* through Automath, end to end. The first mathematics book
  verified completely.
- **Two architectures come out of the next twenty years:**
  - **LCF** (Milner, 1972/75): `thm` is an abstract data type and only the
    inference rules can produce one, so nothing above the kernel needs
    trusting. **ML was invented to write it.**
  - **Automath's line:** write the proof down as a *term*, and let a small
    separate checker read it afterwards. **The de Bruijn criterion.**
    Lean is in this line: a Lean proof is a term, and the kernel rechecks
    it whatever tactic produced it.
- **[Hintergrund]** De Bruijn is also why Lean's internals work at all:
  *de Bruijn indices*, variables named by how far away their binder is, so
  α-equivalent terms are literally equal. Every proof assistant uses them.
  He also did de Bruijn sequences, the de Bruijn-Erdős theorem, and the
  pentagrid construction of Penrose tilings.
- **[Hintergrund]** Milner: Turing Award 1991, also CCS and the π-calculus.
  ML — built as the *meta language* of LCF — is the ancestor of OCaml,
  Standard ML and F#, and shaped Haskell's type system. A proof assistant
  gave the world a programming-language family.

---

## 16. The systems


- The point of the picture: **this is not a succession.** Only Automath and
  LCF stopped, and both handed their architecture on. Everything from
  Mizar (1973) onwards is still maintained.
- Colour is the *tradition*, not the system:
  - **Blue, the de Bruijn line** — proof written down as a term, rechecked
    afterwards: Automath, Coq/Rocq, Lean.
  - **Green, the LCF line** — no proof object at all; soundness comes from
    `thm` being an abstract type: LCF, HOL, Isabelle.
  - **Orange, Mizar** — declarative proofs over set theory.
- Lower labels answer "why build another one". Each system does something
  its predecessors could not.
- **Why nothing dies: the library is the system.** seL4 stays in Isabelle,
  the four colour theorem stays in Rocq. Nobody will redo those.
- Lean's own entry: "tactics in the language, one library" is not a
  type-theoretic feature at all. It is an *organisational* decision — and
  it is the one that mattered.
- **[Hintergrund]** Mizar: Andrzej Trybulec, Białystok, 1973. Its library
  is still one of the largest, and its declarative style is the ancestor
  of Isabelle's Isar.
- **[Hintergrund]** Coq: Coquand and Huet, INRIA. Named after Coquand, and
  *coq* is the French rooster. Renamed **Rocq** in 2025, largely because
  the old name travelled badly in English.
- **[Hintergrund]** Isabelle: Larry Paulson, Cambridge, 1986. By Paulson's
  own account he named it after Gérard Huet's daughter Isabelle — so that
  one day he could announce that Coq was a subsystem of Isabelle.
- **[Hintergrund]** What the LCF line bought: seL4, a verified OS
  microkernel (Isabelle, ~200 000 lines of proof for ~10 000 lines of C),
  now flying in aircraft. And CompCert, a verified C compiler in Coq —
  when Csmith fuzzed every C compiler it could find, it found bugs in all
  of them except CompCert's verified core.

---

## 17. 2013: Lean


- De Moura starts Lean at Microsoft Research in 2013.
- Lean 1 to 3 were research prototypes. **Lean 4 (2021) is a redesign, not
  a new version — and it is written in itself.**
  - Caveat, if the slide-2 question did not already come up: *written in
    itself* means the elaborator, tactics, compiler front end and `lake`.
    The kernel and the runtime are C++. See slide 2.
- Foundation: the Calculus of Inductive Constructions, the Automath line.
  A proof is a term; the kernel rechecks it.
- Buzzard has argued for Lean among mathematicians since about 2018 —
  roughly when Mathlib started to look like a library of real mathematics
  rather than a collection of exercises.
- De Moura is still chief architect, now at the Lean FRO (slide 28).
- **[Hintergrund]** Before Lean, de Moura built **Z3** (with Nikolaj
  Bjørner) at Microsoft Research — probably the most widely used SMT
  solver in the world, inside compilers, verifiers and security tools
  everywhere. He came to proof assistants from the *automation* side, and
  built one in the de Bruijn line anyway. That tells you something.
- **[Hintergrund]** The Lean 3 → Lean 4 port of Mathlib ran from 2022 to
  mid-2023 and occupied the community for over a year. Partly automated
  ("mathport"), mostly not. It is the cautionary tale about what a library
  costs — and it happened recently enough that people still flinch.

---

## 18. Three systems


- Lean 4: dependent types, **one** library (Mathlib).
- Rocq: dependent types, many packages.
- Isabelle/HOL: simple type theory, the AFP. **No dependent types, and the
  strongest automation of the three.**
- Three answers to "what is a proof": a *term* (Lean, Rocq, Agda), a
  *derivation* in a calculus (Isabelle, HOL Light), a *text in set theory*
  (Mizar, Metamath).
- All of them share the de Bruijn criterion: a tiny kernel you must trust,
  arbitrarily unreliable automation above it. **That is why `grind` is
  allowed to be as clever as it likes.**
- **We use Lean because Mathlib exists.** Not because of the logic.
- **[Hintergrund]** The AFP (Archive of Formal Proofs) is a refereed
  journal of Isabelle developments — several hundred entries. Different
  model from Mathlib: many independent articles rather than one library,
  and things do not automatically compose. That trade-off is worth one
  sentence, because it explains why Mathlib is monolithic on purpose.

---

## 19. 1976: the four colour theorem


- Appel and Haken reduce the problem to a list of configurations; an
  ordinary program checks it. No proof assistant.
- **No human has ever read that part.** Pause here.
- Two decades of argument about whether this counted as a proof.
- **2005: Gonthier redoes all of it in Coq**, case analysis included. He
  did not settle the argument — he made it unnecessary.
- The 1976 program was Fortran and assembler on an IBM 370: a program you
  had to trust. Coq is the opposite arrangement — a kernel of a few
  thousand lines, and everything else checked against it.
- **[Hintergrund]** Appel and Haken, Illinois, 1976: about 1 200 hours of
  computer time, 1 476 configurations. The department franked its mail
  "FOUR COLORS SUFFICE". Errors in the case list were found and fixed for
  years afterwards; Robertson, Sanders, Seymour and Thomas simplified it
  to 633 configurations in 1996.
- **[Hintergrund]** Gonthier went on to lead the formalization of the
  **Feit-Thompson odd order theorem** (2012) — six years, ~170 000 lines,
  one of the longest proofs in mathematics. The tooling he built for it,
  *SSReflect*, became `mathcomp`, Rocq's main mathematical library.

---

## 20. 1998: the Kepler conjecture


- Hales announces a proof of Kepler's conjecture of 1611 (with his student
  Samuel Ferguson). Twelve referees, four years.
- Verdict: **ninety-nine percent certain — and no better was possible.**
  The *Annals* published it with the caveat attached. That had never
  happened before.
- **Not about computers.** Peer review met a proof it could not certify,
  and more effort would not have helped. That is the point of the slide.
- Hales started **Flyspeck** (F-P-K: Formal Proof of Kepler). Complete
  formal proof in HOL Light and Isabelle, finished 10 August 2014.
- **The cost: about twenty human work-years and some 500 000 lines of
  proof script.** Sixteen years from announcement to a proof anyone could
  check. Hold that number — it is the yardstick for slides 26 and 27.
- **[Hintergrund]** The referee panel was led by Gábor Fejes Tóth. His
  father, László Fejes Tóth, had proposed in 1953 that the Kepler problem
  could one day be settled by computer. The son refereed the proof that
  did it.
- **[Hintergrund]** Hales also proved the honeycomb conjecture (1999) —
  the hexagonal grid is the most efficient way to tile the plane, conjectured
  around 36 BC by Marcus Terentius Varro.
- **[Hintergrund]** Hales is still in this story: in July 2026 a Lean
  kernel bug produced a short *illicit* proof of the Kepler conjecture,
  which is how he learned of the bug (see the extra section at the end).

---

## 21. 2013: Voevodsky


- Note the dates. The paper is 1989; the episode only ends in 2013, which
  is why it sits after Kepler.
- 1989: Voevodsky and Kapranov identify ∞-groupoids with homotopy types.
- Oct 1998: Carlos Simpson argues it cannot be true — but cannot say
  *which step* is wrong.
- Autumn 2013: Voevodsky accepts it and finds his own error. **Fifteen
  years in limbo.**
- Not an obscure corner: both authors well known, and Voevodsky received
  the **Fields Medal in between, in 2002**.
- Everyone makes mistakes. What matters is how long it took, and why:
  nobody could point at the faulty step, so it was unclear who had erred,
  and nobody pressed.
- How it ended: **the theorem is false.** Strict, rigidly associative
  higher groupoids cannot produce the 2-sphere; Ara showed in 2012 that
  among simply connected spaces they give only products of
  Eilenberg-MacLane spaces.
- **Second story, same lesson:** in 1999 he found an error in a paper of
  his own from seven years earlier. He salvaged the result, but by his
  own account the experience frightened him — that is the documented
  trigger for everything that followed.
- His conclusion: a hard technical argument by a trusted author is
  *hardly ever checked in detail*.
- The quoted line — mathematics runs on "a complex system of mutual trust
  based on reputations" — is his own, from the 2014 IAS lecture.
- **Mind the order — it is the point of the slide.** Nothing here was
  settled by a machine. Simpson argued by hand in 1998, Ara proved the
  theorem false by hand in 2012, Voevodsky recognised his own error by
  hand in 2013.
  - And his turn to formalization came **before** that resolution, not
    after it: the "homotopy lambda calculus" note is from September 2006,
    the Coq library from February 2010, the first public lectures 2010
    (CMU) and 2011 (Oberwolfach). **What drove him was the dispute
    staying open for fifteen years, not its ending.**
  - Worth saying out loud: the man who built formal foundations settled
    his own fifteen-year dispute without them.
- He spent the rest of his career on foundations built so a machine could
  check such arguments. **Not** the ones Mathlib uses, and not our subject:
  we take the diagnosis, not the cure. He died in 2017, aged 51.
- **[Hintergrund]** Biography worth thirty seconds: expelled from Moscow
  State for not attending classes, published anyway, admitted to Harvard
  for a PhD without a master's degree, Fields Medal at 36. Then he turned
  to foundations because he no longer trusted his own papers.

---

## 22. Perfectoid spaces, 2019


- The problem was **not** proving anything. It was: can an object as
  complicated as Scholze's perfectoid space be *stated* at all in a proof
  assistant?
- They formalized a **definition**, not a theorem. Stating is a different
  problem from proving — and for research-level objects it is the harder one.
- Scholze introduced perfectoid spaces in 2012; Fields Medal 2018.
- Buzzard, Commelin and Massot, 2019. **Lean's reputation among
  mathematicians dates from this project.**
- **[Hintergrund]** The definition unfolds through a tower of prerequisites —
  valuations, adic spaces, Huber rings, completions. Formalizing it meant
  building that whole tower in Mathlib first. The by-product (the tower)
  outlived the headline (the definition). Same pattern as slide 24.
- **[Hintergrund]** Buzzard is a number theorist (p-adic modular forms,
  the eigencurve, Buzzard-Taylor). He came to Lean around 2017 and ran the
  *Xena Project* at Imperial, named after Xena: Warrior Princess, getting
  undergraduates to formalize their problem sheets.
- **[Hintergrund, lokal]** **Johan Commelin was a postdoc here in Freiburg**,
  in Stephan Kebekus's group, through exactly these years. He is now an
  assistant professor in Utrecht and **director of the Mathlib Initiative**
  (slide 29). Worth saying to a Freiburg audience.

---

## 23. 2020: the Liquid Tensor Experiment


- December 2020: Scholze posts a challenge on Buzzard's blog — a theorem
  in condensed mathematics (with Dustin Clausen) that he is **not certain of**.
- A Fields medallist publicly asking a machine to check his own proof,
  because he could not convince himself.
- Liquid Tensor Experiment, led by Commelin with Adam Topaz. Main result
  mid-2021, whole project finished July 2022.
- **The request came from a working mathematician, not from logicians.
  That is what had changed.**
- Not combinatorics with a thousand cases either — condensed mathematics,
  at the research frontier.
- Buzzard's ICM plenary in 2022 is a fair marker for the moment this
  stopped being a curiosity.
- **[Hintergrund]** Scholze said afterwards that the formalization made him
  understand one key step better than he had before — the process gave
  back mathematics, not only a certificate.
- **[Hintergrund]** Scholze's reputation for speed: Fields Medal 2018, full
  professor in Bonn at 24. When *he* says he is unsure of a proof, the
  room should notice.

---

## 24. Sphere eversion, 2022


- A sphere can be turned inside out without tearing or creasing. In the
  plane the turning number blocks the analogue — `+1` cannot become `−1`.
  In three dimensions that obstruction is gone. Smale, 1957, non-constructively.
- The problem: **Mathlib had no differential geometry**, and Gromov's
  h-principle needs it.
- So they built the API first and proved the theorem afterwards. **That
  order is the ordinary shape of the work** — and it is what the second
  half of this course is about.
- **This is why Mathlib matters more than any single theorem in it.**
- Massot, van Doorn, Nash.
- **[Hintergrund]** Massot (Paris-Saclay) is a contact and symplectic
  topologist. He also wrote much of the *tooling*: the `leanblueprint`
  system that slices a formalization into independent pieces (slide 25),
  and the teaching dialect *Lean Verbose*. Co-author of
  *Mathematics in Lean* with Avigad — the book the course recommends.
- **[Hintergrund]** Van Doorn: PhD at CMU under Avigad, worked on the Lean 2
  HoTT library, now in Bonn; a Mathlib maintainer, much of the measure
  theory is his. Nash: came from quantitative finance, now at the Mathlib
  Initiative; Lie algebras in Mathlib are largely his.
- **[Hintergrund]** The photographs of Commelin, Massot, Nash and van Doorn
  in these slides are used by their permission — all four answered an email
  within a day. Mention it if anyone asks where the pictures come from.

---

## 25. Freiman-Ruzsa, 2023


- The problem being solved is **not** mathematical: a formalization took
  one team years, so it always came long after the paper.
- A **blueprint** cuts the work into pieces with stated interfaces, so
  strangers can work in parallel without talking to each other.
- Result: three weeks, about twenty contributors, **before the paper was
  refereed**.
- Gowers, Green, Manners, Tao. The theorem: a set whose sumset is barely
  larger than itself must be structured.
- **The method carried further than the theorem.** This is the step
  between "LTE, two years" and "Fermat, eleven days". If one slide in the
  history block has to survive the cut, it is this one.
- **[Hintergrund]** Tao posted the paper in November 2023 and started the
  formalization about three days later. The blueprint made the dependency
  graph public: anyone could see which lemmas were open and claim one.
- **[Hintergrund]** Gowers (Fields 1998) started the **Polymath** projects
  in 2009 — mass collaboration on a blog. Blueprints are Polymath with a
  type checker as the referee: you no longer have to trust the stranger
  who claimed lemma 4.7.
- **[Hintergrund]** Green and Tao are the Green-Tao theorem (2004):
  arbitrarily long arithmetic progressions of primes. Manners is at UCSD.

---

## 26. Equational Theories, 2024-25


- 22 028 942 implications between 4 694 equational laws on magmas.
  **Not deep — but beyond any human team.** Bookkeeping at machine scale.
- Led by Tao. All implications settled, with new constructions found on
  the way.
- The code on the slide is *one* entry of twenty-two million. Proving an
  implication can be a single substitution; refuting one means building a
  magma — and the machine checks that too, by `decide`.
- **[Hintergrund]** The project mixed everything: automated theorem provers,
  SAT solvers, hand constructions, and roughly fifty contributors. Lean was
  the common format they could all submit to. That is the real result —
  a shared interface for heterogeneous work.
- **[Hintergrund]** A good contrast to slide 25: PFR was one deep theorem
  cut into pieces; this is a flat space of twenty-two million shallow
  questions. Formalization helps with both, for different reasons.

---

## 27. Lean today


- A new Lean every month, release candidate about four weeks ahead,
  patch releases in between. `v4.34.0` on 14 Sep 2026, `v4.35.0` on 12 Oct.
- **Nothing updates by itself.** `lean-toolchain` names one exact version,
  `elan` fetches it, `lake` builds against it.
- **The course is pinned to `v4.34.0` all semester.** Tell them not to run
  `elan update` and then wonder why the exercises stop compiling. Say it twice.
- Lean FRO: non-profit since July 2023, under Convergent Research,
  twenty-one people. De Moura chief architect, Sebastian Ullrich head of
  engineering.
- Funding: Simons Foundation International, Sloan, Richard Merkin, Amazon,
  and five million dollars from Alex Gerko (XTX Markets) in July 2025.
  **No vendor behind it, and no longer a spare-time project.**
- **[Hintergrund]** Gerko's gift was ten million in total, split: five to
  the Lean FRO, five to the Mathlib Initiative (next slide). XTX Markets
  is an algorithmic trading firm; it also funds the AIMO prize for AI
  mathematical olympiad performance.
- **[Hintergrund]** "FRO" = Focused Research Organization: a fixed-term,
  non-profit vehicle for work that is too applied for academia and too
  unprofitable for a company. Convergent Research invented the format.
  Worth a sentence — it is why Lean has engineers rather than PhD students.

---

## 28. Mathlib


- One library, one repository, one version. Everything in this course
  imports it.
- Measured on the pinned version (15 Sep 2026): **8 529 files, 2.33 M
  lines, ~189 000 theorems, ~64 000 definitions, 1 031 contributors,
  34 768 commits.** 820 commits in the preceding thirty days — 27 a day.
  **The library changes while they use it.**
- No stable releases. Mathlib follows Lean; your project follows Mathlib.
- `lake exe cache get` fetches what CI already compiled. Building from
  source takes hours. **Say this before the lab session.**
- Mathlib Initiative: since September 2025, a programme of Renaissance
  Philanthropy, the other five million of Gerko's gift. Targets: review
  within a week for nine of ten pull requests, keep the downstream
  ecosystem building, documentation.
  - **Johan Commelin directs it** — the same person as slides 22 and 23,
    and a former Freiburg postdoc.
- **Open the import map live.** One connected library, not a pile of
  packages. Point at a node, follow an edge, show analysis sitting on
  order sitting on algebra.
- **[Hintergrund]** For fifteen years nobody was paid to maintain Mathlib.
  It started in 2017 for Lean 3; Johannes Hölzl, who had come from
  Isabelle, brought the filter-based treatment of limits with him — which
  is why the *Filters* chapter later in this course looks the way it does.
- **[Hintergrund]** The monolith is a deliberate choice. One hierarchy of
  structures means a theorem about topological groups applies to the reals
  without anyone arranging it. The cost is that nothing is ever stable.
  Students will feel both sides within three weeks.

---

## 29. Goals


- Word for word the goals from the notes, so nobody has to reconcile two
  versions. **Read the first three out, point at the last three.**
- Emphasise: the mathematics in the first half is deliberately easy,
  because explaining a proof to a computer requires understanding it first.
- The exercises carry the course. Sheets cover the first half of the
  semester; in the second half they work on a project, mostly self-chosen.
- **[Hintergrund]** Say what this course is *not*: not a logic course, not
  a programming course, and not a course in which the computer finds
  proofs. All three misconceptions show up in week one.

---

## 30. What your machine needs


- Every sheet begins with `import Mathlib`, so **a two-line sheet needs as
  much memory as the hardest one**.
- 16 GB RAM minimum, 32 GB comfortable. 20 GB free disk. SSD required.
- Compiling one sheet peaks around 6.6 GB resident; the language server
  sits at roughly 9 GB with one file open.
- Most of that is memory-mapped library data the system can drop and read
  back, so **less memory slows everything down rather than breaking it**.
  On a mechanical hard disk you cannot work at all.
- Below the minimum: talk to us, there is a server with 128 GB.

---

## 31. Wednesday


- Bring a laptop. **With administrator rights.**
- Follow the installation instructions in the course notes beforehand.
- **Then run `lake exe cache get` before you come.** Say this twice:
  without it, every machine in the room compiles Mathlib from source at
  once, which takes hours and kills the session.
- Wednesday is VS Code, the Lean extension, `git clone`, `cache get`. Ask
  them to try at home first, so Wednesday is for the ones it did not work for.

## 32. Where to start


- **Two games, both in the browser, nothing to install, progress kept
  locally. If they do one thing before Wednesday, make it one of these.**
- **The Incredible Proof Machine in Lean** — ours,
  <https://pfaffelh.github.io/ipm>. It teaches the *shape* of a proof
  before any Lean syntax: natural deduction drawn as a diagram, dragged
  together by hand. Nine worlds — conjunction, implication, disjunction,
  falsity and negation, classical logic, equivalence and truth,
  quantifiers, two puzzles, induction — and a tactic trainer at the end.
  English and German.
  - Say that it is yours and that it is built for this course. It is the
    one place in the first week where they produce a proof themselves.
  - **[Hintergrund]** It follows Joachim Breitner's *Incredible Proof
    Machine*. Breitner also wrote **Con-Leche**, the verified checker
    from the soundness-bug section — his name turns up twice in this
    lecture, once for a game and once for a consistency proof. Worth a
    sentence if the bugs slide went well.
- **Natural Number Game** — the same idea for the *tactics*, proving
  things about `ℕ`. An evening.
  - **[Hintergrund]** It came out of Buzzard's Xena Project; the platform
    it runs on was built in Düsseldorf. It makes students reprove
    `1 + 1 = 2` from the axioms — *Principia* (slide 8) in an evening, in
    a browser.
  - The two games divide the work: ours is the logic, this one is Lean.
- *Formalising Mathematics* (Bhavik Mehta, after Buzzard) and
  *Mathematics in Lean* (Avigad and Massot) are references for the
  semester, not homework.

---

---

# Extra: a slide that does not exist yet

The notes now carry a section *2026: the summer of soundness bugs*
(chapter tag `soundness-bugs`), added on 16 October 2026. The deck has no
slide for it. If you want to say it anyway, it fits after slide 27,
before *Lean today*:

- In July and August 2026 several bugs were found **in the Lean kernel
  itself**, each allowing a proof of `False`. From `False`, everything follows.
  The episode is called the *Summer of Soundness Bugs*.
- The three that were found and closed:
  - **#14484**, 22 July — a missing check, reachable by an adversarial
    metaprogram.
  - **#14576**, 28 July — the kernel accepted projections of the wrong
    structure. The resulting proof of `False` used **no axioms at all**.
  - **#14875**, 21 August — the recursor of a class inductive could leak a
    private import.
- Concrete consequences: one bug gave an illicit *disproof* of the Collatz
  conjecture, another a short illicit *proof* of the Kepler conjecture —
  **which is how Hales found out** (slide 20).
- All repaired within days. Mathlib was rechecked with the repaired kernel.
- **This qualifies slide 2.** "Small and fixed" is not the same as
  "infallible". Say it here rather than hedging on slide 2.
- **And it qualifies slide 3.** `#print axioms` reports which axioms a
  proof uses — it says nothing about the kernel that read them. The #14576
  proof of `False` used none.
- **The remedy is redundancy, not trust.** About 25 independent Lean
  kernels exist, so a proof can be rechecked by a program sharing no code
  with the one that accepted it.
- **Con-Leche** — the name is *café con leche*, and also a
  **CON**sistent **LE**an **CHE**cker. By Joachim Breitner at the Lean FRO.
  - **Not** a replacement kernel: an *external* checker that re-reads
    Lean's export files. Written in Lean, with a proof in Lean that it
    never accepts a proof of `False`. Repo `leanprover/con-leche`; there
    is a Rust port, `con-ron`.
  - Assumptions: ZF without infinity or choice, plus an ω-chain of
    Grothendieck universes, instantiated on Mathlib's `ZFSet` under ω many
    inaccessibles. `Nat` arithmetic is trusted to the Lean runtime.
  - **Say the limit, it is the interesting part.** The proof runs *inside*
    Mario Carneiro's set-theoretic framework — the same framework in which
    an error was found and which has no complete relative-consistency
    proof. So Con-Leche shows the checker is faithful to the model; it does
    not show the model is there.
  - Speed: usually faster than the official kernel, ~0.69× the
    instructions on Mathlib.
  - **[Hintergrund]** Built in his spare time after the soundness issue,
    in under a month, with code and proofs generated by Claude under his
    supervision. Hales calls it one of the most important milestones in
    Lean's history. The recursion is worth a sentence: AI found some of
    the bugs, and AI wrote the proof that the repaired thing is sound.
- Source for all of this: Thomas Hales, *What Mathematicians Should Know
  About the Lean Theorem Prover*, guest post on Tao's blog, 9 October 2026.
  Now reference `hales2026` in the notes.

---

# Two things in the script that this document goes past

1. **Slide 29 / notes.** The chapter says Commelin "works there" at the
   Mathlib Initiative. He **directs** it, and is an assistant professor at
   Utrecht. Worth correcting in `00-Introduction.lean`.
2. **Slide 22.** The Freiburg connection (Commelin as a postdoc in
   Kebekus's group) is not in the notes at all. It is the best local hook
   in the lecture; consider adding one clause.
