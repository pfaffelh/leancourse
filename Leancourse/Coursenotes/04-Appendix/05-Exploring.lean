import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Exploring definitions with `#check`, `#print` and `inferInstance`" =>
%%%
htmlSplit := .never
tag := "checkprint"
%%%

Lean provides a handful of *commands* that are invaluable for exploring
a library like Mathlib.  They all start with `#` and only print
information -- they do not contribute to a proof.

- `#check e` prints the type of the term or expression `e`.  This is
  the fastest way to learn what a lemma says, or what type a definition
  has.
- `#check @lemma` (with a leading `@`) prints the type of the lemma
  *without* hiding implicit and instance arguments.  Use `@` when you
  want to see every argument.
- `#print name` prints the *definition* of the constant `name`.  For a
  typeclass, this shows you the list of fields; for a `def`, the body;
  for a `structure`, the constructor and fields.
- `#eval e` evaluates the term `e` (when it is computable) and prints
  the result.  It works on concrete `ℕ`, `List`, etc., but not on
  abstract propositions.

```lean
#check Nat.add          -- ℕ → ℕ → ℕ
#check @List.map        -- shows all implicit arguments
#eval [1, 2, 3].sum     -- 6
```

The term `inferInstance` asks Lean to *synthesize* an instance of a
stated type -- a quick way to ask "does this type have that
structure?".  If no such instance exists the command fails with a
readable error.  See {ref "instance-resolution"}[the Typeclass chapter]
for the details and an example.

Two tactics complement these commands during an interactive proof:

- `exact?` searches Mathlib for a single lemma that closes the current
  goal and prints a `exact <lemma>` line you can copy.
- `apply?` is the same, but it suggests lemmas whose *conclusion*
  matches the goal, leaving side conditions as new subgoals.

Together, `#check`, `#print`, `inferInstance`, `exact?` and `apply?`
are the main tools for navigating an unfamiliar part of Mathlib; for
searching the library by content or name, see
{ref "navigating-mathlib"}[Navigating Mathlib].
