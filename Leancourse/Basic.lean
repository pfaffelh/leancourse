import Lean
import VersoManual
import DemoTextbook
import UsersGuide.Markup
import Leancourse.Meta.Table

open Verso.Genre Manual
open DemoTextbook.Exts

set_option pp.rawOnError true

example : 2 + 2 = 4 :=
  by rfl


#doc (Manual) "Interactive Theorem Proving using Lean, Summer 2025" =>

%%%
authors := ["Peter Pfaffelhuber"]
%%%

These are the notes for a course on formal proving with the interactive theorem prover Lean4 (in the following we just write Lean) in the summer semester of 2025 at the University of Freiburg. To be able to work through the course in a meaningful way, the following technical preparations are to be made:

* Installation of [vscode](https://code.visualstudio.com/).
* Local installation of Lean and the associated tools: Please follow these [instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency).
* Installing the course repository: Navigate to a location where you would like to put the course materials and use `git clone get https://github.com/pfaffelh/leancourse`.
* After `cd leancourse` and `code .`, you should see some code which looks a bit like mathematics. On the left hand side of the `vscode` window, you can click and install an extension for `Lean`.
* The directory `Exercises` contains the material for the course. We recommend that you first copy this directory, for example to `myExercises`. Otherwise, an update of the repository may overwrite the local files.
* To update the course materials, enter `git pull` from within the `leancourse`directory.

# Introduction

The course is designed for mathematics students and has at least two goals:

* Learning the techniques for interactive formal Theorem proofing using Lean: In recent years, efforts to prove mathematical theorems with the help of computers have increased dramatically. While a few decades ago, it was more a matter of consistently processing many cases that were left to the computer, interactive theorem provers are different. Here, a very small core can be used to understand or interactively generate all the logical conclusions of a mathematical proof. The computer then reports interactively on the progress of the proof and when all the steps have been completed.
* Establishing connections to some mathematical material: On the one hand, the mathematical details needed in this course should not be the main issue of this course. On the other hand, in order to _explain_ how a proof (or calculation or other argument) to a computer, you first have to understand it very well yourself. Furthermore, you have to plan the proof well -- at least if it exceeds a few lines -- so that the commands you enter (which we will call tactics) fit together.

# First steps using logic

```lean
variable (P Q R S T : Prop)
```

```lean
example : P → Q := by
  intro h
  sorry
```

```lean
example (hP : P) : (P → Q) → Q := by
  intro hPQ
  exact hPQ hP
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
:::table (header := true)
* + Type
  + First Projection
  + Second Projection
  + Dependent?
  + Universe
* + `Prod`
  + `Type u`
  + `Type v`
  + ❌️
  + `Type (max u v)`
:::

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
