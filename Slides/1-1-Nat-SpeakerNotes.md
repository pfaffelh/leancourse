# Speaker notes — 1.1 deck: the natural numbers and reduction rules (week 2, Monday)

19 slides. About 75 minutes with the live demos; slides 13 (*How far
reduction goes*) and 15 (*Pattern matching*) are the ones to cut if
time runs short.

**Navigation: one key press is one slide.** Every slide is complete the
moment it appears. Blue lines are the punchline of their slide.

Each section below is one slide, in deck order. Bullets marked
**[Hintergrund]** are background that is *not* in the course notes —
use what fits, skip the rest.

**Have open before you start:** VS Code with an empty `.lean` file
importing nothing (no Mathlib — everything today is core Lean, and the
file then checks instantly). Most demos below are one line to type.

---

## 1. The natural numbers and reduction rules

- Goal of the hour, in one sentence: *why does `rfl` close some goals
  and get stuck on others?* Everything today serves that question.
- Last week was the "why"; from today on it is Lean itself.
- Sheets that hang on this hour:
  - `1.1-a` (this week): functions only via `Nat.rec`, proofs only by
    `rfl`, `show`, `induction`. No Mathlib.
  - `1.1-b` (next week): `Bool`, `cases`, `True`/`False` as types.
  - `1.1-c` (week 4): arithmetic with Mathlib lemmas.
- Also this week: `L-b`, `L-c` (logic block), independent of today.

---

## 2. The natural numbers

- Two constructors, nothing else. Write on the board:
  `Nat.succ (Nat.succ Nat.zero)` and let them count it out — *2*.
- *Inductive* means: every term of type `Nat` is built by finitely many
  constructor applications. There is no third way to get a `Nat`.
- Numerals are notation. `2` is elaborated into a term the kernel
  understands as that tower.
- **Live:** `#print Nat`. Output is short: type `Nat : Type`, zero
  parameters, the two constructors. Twenty seconds.
- Do **not** open the general `inductive` keyword — that is chapter 1.2.
- **[Hintergrund]** The unary tower is the *meaning*, not the storage.
  The kernel has special support for number literals and computes
  `+`, `*`, `%`, … on them with big-integer arithmetic (GMP).
  `example : 2^200 + 1 = 1606938044258990275541962092341162602522202993782792835301377 := rfl`
  checks instantly. Otherwise `rfl` on any realistic number would never
  finish. If someone asks "isn't this horribly slow?" — that is the
  answer.

---

## 3. Peano, 1889

- Peano's axioms: a zero, a successor, induction. (Plus: successor is
  injective, zero is no successor.)
- **The blue line is the point:** what was a list of axioms in 1889 is
  a type declaration here. Nothing is postulated.
  - Injectivity and `zero ≠ succ n` are *theorems* in Lean
    (`Nat.succ.inj`, `Nat.noConfusion`) — they follow from the
    declaration.
  - Induction is not a third constructor. It comes out of the type as
    the recursor — next slide.
- Dedekind gave the same analysis in 1888.
- **[Hintergrund]**
  - Dedekind, *Was sind und was sollen die Zahlen?* (1888). Peano,
    *Arithmetices principia, nova methodo exposita* (1889), in Latin;
    Peano acknowledges Dedekind. Peano started at 1, not 0.
  - Hermann Grassmann (1861, *Lehrbuch der Arithmetik*) had already
    defined `+` and `·` by recursion and proved their laws by
    induction.
  - Dedekind's real contribution is the *recursion theorem*: definition
    by recursion is legitimate, i.e. there is exactly one function with
    `f(0) = a`, `f(n+1) = g(n, f(n))`. He had to *prove* it. In Lean it
    is not a theorem but a primitive — the recursor. That is the next
    slide.

---

## 4. The recursor `Nat.rec`

- Constructors *build*, the recursor *consumes*.
- **Read the type left to right:** `Nat.rec : C → (Nat → C → C) → Nat → C`
  takes a value for zero (`base : C`), a rule for the successor
  (`step : Nat → C → C`), and then the number. Board:
  - `f 0 := base`
  - `f (n + 1) := step n (f n)`
- Same shape as `Bool.rec : C → C → Bool → C` on slide 14 — one
  argument per constructor, then the value. Worth pointing back to
  then.
- Stress: `step` gets **both** the predecessor `n` **and** the value
  already computed for it. Most students expect only the second.
- **Currying, if it has not come up yet.** `step : Nat → C → C` is a
  function of two arguments.
  - `α → β → γ` means `α → (β → γ)` — arrows bracket to the right.
  - `g a b` means `(g a) b` — application brackets to the left.
  - The two fit: `g a : β → γ`, then `(g a) b : γ`.
  - Brackets only where an argument is itself an application:
    `step n (f n)`.
  - The appendix *Different parentheses* has the same, for reference.
- Pattern matching, `cases`, `induction` all compile down to `Nat.rec`.
- The general form lets the result *type* depend on `n`
  (`motive : Nat → Sort u`) — that is what makes it the induction
  principle. Needs universes, comes in 1.3. Today: fixed `C`.
- **[Hintergrund]** The full signature, if someone runs `#check @Nat.rec`:
  `{motive : Nat → Sort u} → motive zero → ((n : Nat) → motive n → motive (n+1)) → (t : Nat) → motive t`.
  With `motive := fun _ => C` this is the slide's version; with
  `motive := P : Nat → Prop` it is exactly induction: `P 0`, step
  `P n → P (n+1)`, conclusion `P t`. **Recursion and induction are one
  constant.** Say this sentence even if you skip the signature.

---

## 5. `Nat.rec` computes

- A recursor applied to a constructor picks the matching case. Two
  lines, one per constructor.
- **Do not name the rule yet.** It gets its letter, ι, with the others
  on slide 8. No Greek letters before that slide.
- Numerals are put into constructor form first (`2 ⟶ succ 1`), which is
  why the rule applies to `2` at all.
- Important for later: the rule needs a **constructor** in that
  position. A variable is not enough. Hold this thought until slide 11.

---

## 6. Example: `myDouble`

- `step` ignores the predecessor (`_`) and adds 2 to the value so far.
- **Walk through the chain on the slide, line by line.** Every step is
  one of two kinds:
  - *unfold a definition* — `myDouble`, then `step`;
  - *the recursor picks its case* — because the argument is a
    constructor: `2 = succ 1`, `1 = succ 0`, finally `zero`.
- Those two kinds get their names, δ and ι, on slide 8. Say "two kinds
  of step" now, not the letters.
- `Nat.rec 0 step 1 + 2` means `(Nat.rec 0 step 1) + 2` — application
  binds tighter than `+`. Same bracket rule as on slide 4.
- Then run it in the editor.
- `example : myDouble 2 = 4 := rfl` — no proof needed, because both
  sides compute to the same thing. That is the bridge to the next slide.
- Variation if time: `#eval myDouble 10`, then `myDouble 1000`.

---

## 7. Definitional equality and `rfl`

- Three notions of equality. Only the last two today:
  - *syntactic*: literally the same term,
  - *definitional* `a ≡ b`: both reduce to a common form — a
    *judgement* of the kernel, not a statement,
  - *propositional* `a = b`: a `Prop`, may need a real proof.
- The kernel treats definitionally equal terms as interchangeable,
  in particular when it compares types (*conversion*).
- **Blue line:** `rfl` proves exactly a definitional equality.
- Two parts of Lean, named here for the first time: the *elaborator*
  turns what we write (notation, omitted arguments, tactics) into an
  explicit term; the *kernel* checks that term against fixed rules.
  Only the kernel has to be trusted. Details in chapter 1.5.
- `#eval` computes the value too, but by running compiled code, not by
  reduction. For the terms of this chapter both agree.
- The appendix *Equality* has the full three-way comparison.
- **[Hintergrund]** Why it matters beyond `rfl`: if `h : P (2 + 2)`,
  then `h` *is* a proof of `P 4` — no rewriting needed, because the two
  types are definitionally equal. Students meet this as "Lean accepted
  it although the goal looks different".

---

## 8. The reduction rules

- **Do not read the table out.** Point at δ and ι: those two do the
  work in practice, and those two will cost them time on the sheets.
- α and η almost never come up by hand.
- Rough grouping:
  - α, β, η: the lambda calculus proper — functions.
  - δ: definitions.
  - ι: inductive types — recursor meets constructor.
  - ζ: local `let`.
- **[Hintergrund]** On the names. α and β (and δ, for built-in
  constants) go back to Church's lambda calculus of the 1930s; η to
  the same tradition. ι and ζ are later, from the type-theory /
  Coq tradition, where inductive types and `let` arrived. The chapter
  says "most of the names" for that reason.

---

## 9. What `rfl` sees: `α β η`

- Run all three live.
- α: the two functions are not merely equal — for the kernel they are
  the **same term**, because it stores bound variables by position
  (de Bruijn indices), not by name. The name `x` is only for display.
- β: substitution. `(fun x => x + 1) 4` becomes `4 + 1`, then arithmetic
  does the rest (δ, ι).
- η: the one people doubt. **Ask before showing:** should
  `fun x => f x` and `f` be equal? Opinions split. Lean says yes, by
  definition — and `funext` (chapter 1.5, *Axioms*) is the propositional
  version for functions that agree on every input.

---

## 10. What `rfl` sees: `δ ι ζ`

- The three rules Lean adds on top of the lambda calculus.
- δ: `twice 3` unfolds to `2 * 3`, then computes.
- ι: `motive` has to be given explicitly here because nothing in the
  goal determines it. Wave at it and move on — explanation in 1.3.
- ζ: `let` substitutes.
- **Blue line:** `rfl` is far stronger than "syntactically identical".
- One more worth running: `example : List.length [7, 8, 9] = 3 := rfl`.
  Several rules at once, and it makes the blue line concrete — nobody
  would call these two sides syntactically identical.

---

## 11. When `rfl` fails

- **The central slide of the hour.**
- **Ask them to predict** which of the two fails *before* you go to the
  slide (or cover the second block). Most will guess that both work, or
  that the first fails.
- Mechanism:
  - `Nat.add` recurses on its **second** argument:
    `n + 0 ⟶ n`, `n + succ m ⟶ succ (n + m)`.
  - `n + 0`: second argument is the constructor `zero`, ι fires, done.
  - `0 + n`: second argument is a variable. No constructor, ι cannot
    fire. The term is *stuck*.
- Nothing is wrong with the statement. It is **true**, just not true
  **by computation**.
- Read the error message together: Lean reports that the two sides are
  not definitionally equal.
- **[Hintergrund]**
  - Live check: `#print Nat.add` shows `Nat.brecOn … x_1` — the
    recursion really is on the second argument. Not worth the time
    unless someone asks.
  - Why the second argument? Convention, so that `n + succ m` matches
    `n + (m + 1)`. With the other choice, `0 + n` would be `rfl` and
    `n + 0` would get stuck. There is always one side that gets stuck.

---

## 12. Induction instead

- To prove `0 + n = n` you have to run the recursor yourself:
  `induction`, which is `Nat.rec` with `motive := fun n => 0 + n = n`
  (back-reference to slide 4: recursion and induction are one constant).
- Two goals: `zero` (here `rfl` works — `0 + 0` fires ι) and
  `succ k` with the hypothesis `ih : 0 + k = k`.
- **Why `rw [ih]` alone fails is worth a minute.** The goal is
  `0 + (k + 1) = k + 1`. The subterm `0 + k` does not occur yet. It
  appears only after the ι step `0 + succ k ⟶ succ (0 + k)`, and
  `Nat.add_succ` is what performs that step as a rewrite.
- Same phenomenon one level down: stuck until a constructor shows up.
- **[Hintergrund]** In practice nobody writes this. `Nat.zero_add n` is
  the library lemma, and `omega` or `simp` close the goal outright.
  Today's point is *why* such lemmas have to exist at all.

---

## 13. How far reduction goes

- Short slide. Cut it first if time runs out — nothing later depends
  on it.
- Reducibility: `@[reducible]` unfolds freely, `def` on demand,
  `@[irreducible]` never (the last one used to stop expensive
  unfolding).
- Weak head normal form: reduce only until the outermost constructor or
  binder is visible. Enough to compare two terms.
- **The blue line ("undecidable").** For Lean's type theory,
  definitional equality is **not decidable** and the kernel's check is
  not even transitive — the culprit is the interaction of impredicative
  `Prop` with subsingleton elimination (`Acc.rec`), shown in Carneiro's
  thesis (2019). Reduction is not even strongly normalizing (Abel and
  Coquand, 2020). The kernel's algorithm is sound but incomplete; in
  practice nobody hits the gap. The course notes say the same (box in
  1.1, *Conversion* in 1.5).
- **[Hintergrund]** "Terminates" is also the theory. In practice `rfl`
  and `decide` can time out (`maximum recursion depth` /
  `deterministic timeout`) on terms that are large in unary form; the
  literal arithmetic from slide 2 is what keeps everyday numbers fast.

---

## 14. Bool

- Two constructors without arguments. `Bool.rec` is if-then-else.
- **The order surprises everyone: the `false` case comes first.** Say it
  twice. Reason: `Bool` is declared with `false` before `true`
  (`#print Bool` shows it), and a recursor takes its cases in
  constructor order.
- First example: `bif true …` — a constructor, ι fires, `rfl`.
- Second example: `bif b …` with `b` a variable — stuck, exactly as
  `0 + n`. The fix is `cases b`: two goals, one per constructor, each
  closes by `rfl`. `<;>` runs `rfl` on both.
- `cases` is `induction` without the hypothesis — there is nothing to
  recurse on in `Bool`.
- This is sheet `1.1-b` (next week) in one slide.
- **[Hintergrund]**
  - `bif` is notation for `cond`, which branches with `match`. Reason:
    the code generator cannot compile a bare recursor. The chapter has
    it in a collapsible box.
  - `bif` takes a `Bool`; `if … then … else` takes a `Prop` together
    with a `Decidable` instance. Typeclasses are chapter 1.6; just say
    "two different ifs" if asked.

---

## 15. Pattern matching

- One line per constructor, introduced by `|`. Lean translates it back
  into `Bool.rec`.
- Everything they will actually write looks like this, not like a call
  to the recursor. The sheet `1.1-a` forbids it on purpose, so they see
  once what is underneath.
- Details in chapter 1.3 (*Pattern matching*).
- Can be cut if short of time; slide 14 already makes the point.

---

## 16. `True`

- First: `Prop` itself is **not** an inductive type. No declaration, no
  definition to unfold — `#print Prop` fails. It is `Sort 0`, a
  primitive of the kernel. The rules it carries (proof irrelevance and
  the rest) come in 1.5.
- `True` *is* inductive, in `Prop`: one constructor `True.intro`, no
  argument. So `True.intro` is a proof of `True`.
- Three proofs on the slide:
  - `True.intro` — the constructor,
  - `trivial` — a theorem whose value is `True.intro`,
  - `by trivial` — the tactic, which also tries `rfl` and `assumption`.
  Students confuse the term `trivial` and the tactic `trivial`. Say
  that they share a name and nothing else.
- One constructor, so one case in the recursor: `True.rec c h ⟶ c`.
  A proof of `True` carries no information.
- **[Hintergrund]** The `Type`-level twin is `Unit` (really `PUnit`),
  one constructor `()`. Same recursor shape.

---

## 17. `False`

- No constructors. No term can be built — exactly what a proposition
  without a proof should look like.
- The recursor: no case argument at all between `motive` and `t`.
  Count with them: `Bool.rec` two cases, `True.rec` one, `False.rec`
  none. With no case to check, the result may be of **any** type:
  *ex falso quodlibet*.
- **`False.rec` or `False.elim` — the same?** Same principle, two
  constants. `False.rec` is the recursor the kernel generates;
  `False.elim` is an ordinary definition on top of it, exactly the line
  on the slide (`#print False.elim`). Two differences, both
  convenience:
  - The motive of `False.rec` is explicit and must be written out.
    `False.elim` takes a plain type `C`, implicitly, so Lean fills it
    in from the goal. Plain `False.rec h` is an error: Lean reads `h`
    as the motive (checked).
  - The motive of `False.rec` may depend on the proof `t`; `False.elim`
    drops that. For `False` it costs nothing — there is no proof to
    depend on.
- `h.elim` is dot notation for `False.elim h`. In practice students
  write that, `exfalso` or `cases h`, never `False.rec`.
- Why the `motive` is explicit here and implicit for `Bool.rec`: there
  are no case values for Lean to infer it from. Background, the chapter
  has it in a box.
- **[Hintergrund]**
  - In tactic mode the same thing is `cases h` — **zero** goals, because
    there is no constructor to split into. Also `nomatch h`, and
    `exfalso` to turn any goal into `False`. All on sheet `1.1-b`.
  - Ex falso is intuitionistically valid. It is *not* the classical
    part of logic — that is the excluded middle (logic sheet `L-e`).
  - The `Type`-level twin is `Empty`, with `Empty.elim`.

---

## 18. `False` and consistency

- One proof of `False` proves every proposition (`False.elim`).
- A system in which `False` is inhabited is *contradictory*: it no
  longer tells the provable from the false. Every statement becomes a
  theorem.
- **Blue line:** `False` must stay empty. That is the whole reason the
  empty type matters.
- Link back to week 1: this is exactly what the summer-2026 soundness
  bugs were about — one of them (lean4 issue #14576) produced a term of
  `False` **without any axiom**. Fixed, but it shows what is at stake.
- Picked up again in chapter 2.3 (Lean's axioms) and in the Girard
  project (*Type : Type* makes `False` inhabited).

---

## 19. Summary

- Read the four lines, then hand over to the sheets.
- `1.1-a` uses nothing but the recursor, `rfl`, `show` and `induction`
  — no Mathlib, no library lemmas. Defining `myPred`, `myMul`, `myFact`,
  `myEven` via `Nat.rec` is the point.
- Mathlib arrives on `1.1-c` in week 4.
- The question to leave them with: *when you write `rfl` and it fails,
  look for the variable that stops the recursor.*

---

## Notes beyond the deck

- **Chapter title:** `1-Nat.lean` still has `#doc (Manual)
  "Introduction"`; the deck is titled *The natural numbers and
  reduction rules*.
