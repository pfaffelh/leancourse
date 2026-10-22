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
(now `03-01-Predicates`) exercises 2 and 3 had been rewritten to use
`imp_iff_or_not` and `not_imp_not` while the sheet still told
students to start with `rw [l1]`, which rewrites the *outer*
implication and leads somewhere else entirely. That mismatch
survived for months precisely because nothing compared the two.

## Coverage

| Sheet | Witness |
|-------|---------|
| `01-Logic` (a–g) | all 7 |
| `02-Numbers` (00, a–c) | all 4 |
| `03-Functions_and_Sets` | `03-00-Quantifiers`, `03-01-Predicates` only |
| `05-TypeTheory` | `05-d-WellFoundedness` only |
| `07-ProofEngineering` | `07-b-Conv` only |
| `04-FunctionalProgramming`, `06-Mathematics` | none |

## A second check, for `01-Logic` only

Sheets `01-c` and `01-d` claim every statement on them is provable
*constructively*; `01-e` claims every statement on it is not. Both
claims are machine-checkable with `itauto`, which is `tauto`
restricted to constructive reasoning: put the statements in a scratch
file, prove each `by itauto`, and check that they all succeed
(c, d) resp. all fail (e). Both directions held in October 2026. Re-run
it after moving an exercise between those sheets.
