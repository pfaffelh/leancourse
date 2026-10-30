# Checks — solvability tests for the exercise sheets

**This is not teaching material.** These files used to be
`Leancourse/Exercises/Solutions/`. They are no longer maintained as
model solutions for students and are never exported to the student
repository.

## What they are for

A sheet in [../Exercises/](../Exercises/) can type-check cleanly and
still be broken: a file full of `sorry` compiles without error, so the
pre-export check in
[../../scripts/export_exercises.sh](../../scripts/export_exercises.sh)
cannot tell whether an exercise is actually solvable, whether a
hypothesis is missing, or whether a scaffold line hands the student a
goal that leads nowhere.

A file here is a worked-through witness that the corresponding sheet
*can* be finished. The only property that matters is:

> it compiles with no errors **and** no `sorry`.

Run [../../scripts/check_solvable.sh](../../scripts/check_solvable.sh)
to verify that for every file in this tree.

## What they are explicitly not

- Not pedagogical. A proof here may be ugly, may use tactics the sheet
  has not introduced yet, and may be shorter or longer than what a
  student is expected to write. Do not "improve" it for style.
- Not complete. Only some sheets have a witness; see the table below.
  An uncovered sheet is not an error, just an untested one.
- Not published. Nothing in this directory reaches
  `leancourse_exercises`.

## Who may read them

Students: no. Nothing here is exported, and the point of an exercise
is lost once a worked proof is at hand.

The course tutor: yes. A tutor circulating in the lab needs to know
what a finished proof looks like, and this tree is the only place it
is written down. Give the tutor access to this repository (the course
repo), not just to `leancourse_exercises`. The proofs here are often
not the nicest ones -- see the non-goals above -- so a tutor should
treat them as *a* solution, not *the* solution.

## Keeping them honest

The one thing that *does* have to hold: a witness must prove the same
statement as the sheet. When an exercise statement changes, the witness
has to follow, or the check is worthless. The failure mode to watch for
is silent drift — in October 2026 the witness for the old `01-h`
(now `1-Lean/5-a-Predicates`) exercises 2 and 3 had been rewritten to use
`imp_iff_or_not` and `not_imp_not` while the sheet still told
students to start with `rw [l1]`, which rewrites the *outer*
implication and leads somewhere else entirely. That mismatch
survived for months precisely because nothing compared the two.

## Coverage

The tree mirrors `../Exercises/` file for file. As of October 2026:

| Sheet | Chapter | Week | Witness |
|-------|---------|------|---------|
| `0-Logic/a-Propositions` … `g-Automation` | — | 1–5 | all 7 |
| `1-Lean/1-a-NatRec` | 1.1 | 2 | yes |
| `1-Lean/1-b-Bool` | 1.1 | 3 | yes |
| `1-Lean/1-c-Naturals` | 1.1 | 4 | yes |
| `1-Lean/2-a-Quantifiers` | 1.2 | 3 | yes |
| `1-Lean/2-b-Structures` | 1.2 | 5 | yes |
| `1-Lean/3-a-Recursion` | 1.3 | 5 | yes |
| `1-Lean/4-a-DependentTypes` | 1.4 | 6 | yes |
| `1-Lean/4-b-CurryHoward` | 1.4 | 6 | yes |
| `1-Lean/4-c-Predicates` | 1.4 | 7 | yes |
| `1-Lean/5-a-Predicates` | 1.5 | 6 | yes |
| `1-Lean/6-a-Typeclasses` | 1.6 | 7 | yes |
| `1-Lean/6-b-Coercions` | 1.6 | 8 | yes |
| `1-Lean/6-c-Monads` | 1.6 | 8 | yes |
| `1-Lean/7-a-Notation` | 1.7 | 8 | yes |
| `2-Mathematics/0-a-Search` | — | 9 | yes |
| `2-Mathematics/1-a-Numbers` | 2.1 | 9 | yes |
| `2-Mathematics/2-a-Sets` | 2.2 | 9 | yes |
| `2-Mathematics/2-b-ImagePreimage` | 2.2 | 10 | yes |
| `2-Mathematics/2-c-Functions` | 2.2 | 10 | yes |
| `2-Mathematics/3-a-Axioms` | 2.3 | 10 | yes |
| `2-Mathematics/3-b-WellFoundedness` | 2.3 | 10 | yes |
| `2-Mathematics/4-a-Orders` | 2.4 | 12 | yes |
| `2-Mathematics/5-a-Algebra` | 2.5 | 12 | yes |
| `2-Mathematics/6-a-Limits` | 2.6 | 13 | yes |
| `2-Mathematics/6-b-Filters` | 2.6 | 13 | yes |
| `2-Mathematics/7-a-Topology` | 2.7 | 14 | yes |
| `2-Mathematics/8-a-MeasureTheory` | 2.8 | extra | yes |
| `2-Mathematics/9-a-Monads` | 2.9 | 15 | yes |
| `2-Mathematics/9-b-Probability` | 2.9 | 15 | yes |
| `4-Appendix/a-ProofEngineering` | Appendix | 11 | yes |
| `4-Appendix/b-Conv` | Appendix | 11 | yes |
| `9-Extra/a-Puzzles` | — | 5 | yes |

Every sheet has a witness: 39 of 39, all sorry-free apart from the
one deliberate `sorry` on `L-a`, where finding the unprovable
statement is the exercise.

Writing the first batch turned up three faults that a type-check
alone could never have caught, because the broken lines sat in
comments or were simply false:

* `1.7-a` exercise 3 gave the template `notation "avg " a " " b => ?_`.
  A bare `" "` is not a valid atom, so no student could have followed
  it. The template is now `notation "avg(" a ", " b ")"`.
* `1.7-a` exercise 2 checked itself with `example : sq 5 = 25 := rfl`,
  which parses as `sq (5 = 25)` and fails to elaborate. The check line
  now carries the type ascription, with a note on precedence.
* `2.2-b` exercise 2 asked for `g ⁻¹' s = s` for an *arbitrary*
  `g : α → α`. That is false -- take `g` constant. It now reads
  `id ⁻¹' s = s`, which is what the surrounding text promises.

## A second check, for `0-Logic` only

Sheets `c-Or` and `d-Negation` claim every statement on them is provable
*constructively*; `e-Classical` claims every statement on it is not. Both
claims are machine-checkable with `itauto`, which is `tauto`
restricted to constructive reasoning: put the statements in a scratch
file, prove each `by itauto`, and check that they all succeed
(c, d) resp. all fail (e). Both directions held in October 2026. Re-run
it after moving an exercise between those sheets.
