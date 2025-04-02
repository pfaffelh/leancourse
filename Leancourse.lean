-- This module serves as the root of the `Leancourse` library.
-- Import modules here that should be built as part of the library.
import VersoManual
import Mathlib

import «Leancourse».Coursenotes.«Introduction»
import «Leancourse».Coursenotes.«01-Lean».«01-Notes-Lean»
import «Leancourse».Coursenotes.«01-Lean».«02-Notes-Proofs»
import «Leancourse».Coursenotes.«02-Math».«01-Logic»
import «Leancourse».Coursenotes.«02-Math».«02-NandR»
import «Leancourse».Coursenotes.«02-Math».«03-Sets»
import «Leancourse».Coursenotes.«03-Tactics»

open Verso.Genre Manual

#doc (Manual) "Interactive Theorem Proving using Lean, Summer 2025" =>
%%%
tag := "ITPFr"
authors := ["Peter Pfaffelhuber"]
%%%

These are the notes for a course on formal proving with the interactive theorem prover Lean4 (in the following we just write Lean) in the summer semester of 2025 at the University of Freiburg. To be able to work through the course in a meaningful way, the following technical preparations are to be made:

* Installation of [vscode](https://code.visualstudio.com/).
* Local installation of Lean and the associated tools: Please follow these [instructions](https://leanprover-community.github.io/get_started.html#regular-install).
* Installing the course repository: Navigate to a location where you would like to put the course materials and use
```
git clone https://github.com/pfaffelh/leancourse`
cd leancourse
lake exe cache get
```
When you type `code .` within the `leancourse` folder, navigate to `Leancourse/Exercises/01-Logic/01-a.lean`, accept to have`ELAN` installed, as well as the corresponding `Lean` version.  When all is finished. Everything is fine once orange and/or red bars disapprear, and navigating in the left hand side of the windom leads to changes in the right hand side (the infoview). You should see some code which looks a bit like mathematics.
* The directory `Leancourse/Exercises` contains the material for the course. We recommend that you first copy this directory, for example to `myExercises`. Otherwise, an update of the repository may overwrite the local files.
* To update the course materials, enter `git pull` from within the `leancourse`directory.

(In case you cannot install the course material locally, do the following: Right click [here](https://gitpod.io/#/https://github.com/pfaffelh/leancourse>) and _open link in new tab_ to access the repository using Gitpod. You will probably need a github account in order to do this.)

{include 0 «Leancourse».Coursenotes.«Introduction»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«01-Notes-Lean»}

{include 0 «Leancourse».Coursenotes.«01-Lean».«02-Notes-Proofs»}

{include 0 «Leancourse».Coursenotes.«02-Math».«01-Logic»}

{include 0 «Leancourse».Coursenotes.«02-Math».«02-NandR»}

{include 0 «Leancourse».Coursenotes.«02-Math».«03-Sets»}

{include 0 «Leancourse».Coursenotes.«03-Tactics»}
