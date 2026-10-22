import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 5: The Monty Hall problem with the PMF monad" =>
%%%
tag := "project-monty-hall"
%%%

*What it is.*  A car is hidden uniformly behind one of three doors;
you pick a door; the host opens another door, revealing a goat; you
may stay or switch.  Famously, switching wins with probability 2/3.
This project models the game in the
{ref "probability-pmf"}[probability monad `PMF`] and *proves* that
number — a complete formalization of a statement most people refuse
to believe when they first hear it.

*Implementation idea.*  Work over `Fin 3`.  The car position is
`PMF.uniformOfFintype (Fin 3)`; fix the contestant's initial pick as
door `0` (argue by symmetry in prose, or model the pick uniformly as
a stretch goal).  The host's choice is the subtle part: if the car is
behind door `0` the host opens one of the two goat doors uniformly,
otherwise his hand is forced.  Chain these with `PMF.bind` and
`PMF.pure` — or `do`-notation — into a distribution over outcomes,
and define the two strategies as functions from the observed
information to the final door.  The theorem is that the switch
strategy wins with probability 2/3 and staying wins with 1/3.  The
computation unfolds via `PMF.bind_apply` and `PMF.pure_apply` into a
finite sum over `Fin 3` (`Fin.sum_univ_three` helps); note that PMF
probabilities live in `ENNReal`, so keep the extended-real
simp lemmas nearby.  Stretch goals: `n` doors of which the host
opens `k`, or a host with a known bias — does switching still help?

*References.*  {citet mathlibDocs}[] documents the `PMF` API; the
{ref "probability-pmf"}[probability chapter] of these notes develops
`pure`, `bind`, and the monad laws that the model is built from.
