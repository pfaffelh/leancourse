-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Mathlib

import «Leancourse».Coursenotes.«00-Introduction»
import «Leancourse».Coursenotes.«01-Lean»
import «Leancourse».Coursenotes.«02-Tactics»

open Verso.Genre Manual

#doc (Manual) "Interactive Theorem Proving using Lean, Summer 2025" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

These are the notes for a course on formal proving with the interactive theorem prover Lean4 (in the following we just write Lean) in the summer semester of 2025 at the University of Freiburg. To be able to work through the course in a meaningful way, the following technical preparations are to be made:

* Installation of [vscode](https://code.visualstudio.com/).
* Open `vscode`, hit the _extensions_ icon (fifth from the top) on the left, and install the _Lean 4 language extension_.
* If you haven't done already, install `git`. For this, the best way is to open `vscode`, hit the _git_ icon (third from the top on the left), and follow the instructions.
* Installing the course repository: Navigate to a location where you would like to put the course materials and use
```
git clone https://github.com/pfaffelh/leancourse
cd leancourse
lake exe cache get
code .
```
Then, _vscode_ should open and you see the course materials.

:::paragraph
Note: Yet another description how to install _Lean_ is found [here](https://leanprover-community.github.io/get_started.html#regular-install).
:::


After having typed `code .` within the `leancourse` folder, navigate to `Leancourse/Exercises/01-Logic/01-a.lean`. Everything is fine once orange and/or red bars disapprear, and navigating in the left hand side of the windom leads to changes in the right hand side (the infoview). You should see some code which looks a bit like mathematics.
* The directory `Leancourse/Exercises` contains the material for the course. We recommend that you first copy this directory, for example to `myExercises`. Otherwise, an update of the repository may overwrite the local files.
* To update the course materials, enter `git pull` from within the `leancourse`directory.

In case you cannot install the course material locally, do the following: Visit [this page](https://https://github.com/pfaffelh/leancourse) and click on the green Code-button. Navigate to Codespaces and open the course notes there. You get a window which looks a lot like _vscode_, so please follow the instructions from above. You will have to _Restart Lean_ and _Restart File_ and wait several minutes until all is set. (If you see a red vertical bar, something is wrong. If you see an orange vertical bar, you will have to wait longer.) You will probably need a github account in order to open the coursenotes in Codespaces.

# Table of Contents

{include 0 «Leancourse».Coursenotes.«00-Introduction»}

{include 0 «Leancourse».Coursenotes.«01-Lean»}

{include 0 «Leancourse».Coursenotes.«02-Tactics»}
