import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

example : 2 + 2 = 4 :=
  by rfl


#doc (Manual) "Interactive Theorem Proving using Lean, Summer 2025" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

These are some notes for the course on Lean at the University of Freiburg in Summer 2025.

# First steps using logic

```lean
variable (P Q R S T : Prop)
```

```lean
example : P → Q := by
  intro h
  sorry
```

```
Proof state   Command         New proof state

⊢ P → Q       intro hP        hP : P
                              ⊢ Q
```

Assume we have `⊢ Q`, then all makes sense!

{docstring Lean.Parser.Tactic.apply}

Documentation can take many forms:

 * References
 * Tutorials
 * Etc

```lean
example : 2 + 2 = 4 :=
  by rfl
```


{include UsersGuide.Markup}




# Genres
%%%
tag := "genres"
%%%


:::paragraph
Documentation comes in many forms, and no one system is suitable for representing all of them.
The needs of software documentation writers are not the same as the needs of textbook authors, researchers writing papers, bloggers, or poets.
Thus, Lean's documentation system supports multiple _genres_, each of which consists of:

 * A global view of a document's structure, whether it be a document with subsections, a collection of interrelated documents such as a web site, or a single file of text
 * A representation of cross-cutting state such as cross-references to figures, index entries, and named theorems
 * Additions to the structure of the document - for instance, the blog genre supports the inclusion of raw HTML, and the manual genre supports grouping multiple top-level blocks into a single logical paragraph
 * Procedures for resolving cross references and rendering the document to one or more output formats

All genres use the same markup syntax, and they can share extensions to the markup language that don't rely on incompatible document structure additions.
Mixing incompatible features results in an ordinary Lean type error.
:::

# Docstrings
%%%
tag := "docstrings"
%%%

Docstrings can be included using the `docstring` directive. For instance,

```
{docstring List.forM}
```

```
example : 2 + 2 = 4 :=
  by rfl
```

results in

{docstring List.forM}

# Index
%%%
number := false
%%%

{theIndex}
