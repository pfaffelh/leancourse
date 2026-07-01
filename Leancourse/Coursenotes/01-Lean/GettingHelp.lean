import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Getting help: Loogle, LeanSearch, Moogle, and friends" =>
%%%
htmlSplit := .never
tag := "help-services"
%%%

Mathlib is enormous, and naming conventions -- however consistent
-- will only take you so far.  When you know *what* you want to say
but not *which lemma* says it, a handful of search services can
save hours of scrolling.  All of them are available both as web
pages and, more conveniently, as commands inside Lean via the
`LeanSearchClient` package (already a dependency of Mathlib).

- *Loogle* ([loogle.lean-lang.org](https://loogle.lean-lang.org/))
  searches by *type shape*.  You write a pattern (using `_` for
  holes) and Loogle returns every Mathlib lemma whose statement
  unifies with it.  Inside Lean:
  ```
  #loogle (?a + ?b) * ?c = _
  ```
  returns distributivity lemmas in all their variants.  Loogle also
  accepts a comma-separated list of *constants that must appear*,
  e.g. `#loogle Real.exp, Real.log`, or a target conclusion
  `#loogle |- tsum _ = _`.

- *LeanSearch* ([leansearch.net](https://leansearch.net/))
  searches by *natural language*.  You phrase your goal in English
  ("derivative of composition of functions") and it returns the
  most relevant Mathlib lemmas, ranked by semantic similarity.
  From inside Lean:
  ```
  #leansearch "the derivative of a product of functions"
  ```

- *Moogle* ([moogle.ai](https://www.moogle.ai/)) is another
  natural-language search, with a different ranking model.  In
  Lean:
  ```
  #moogle "bolzano-weierstrass"
  ```
  The two tools often surface different lemmas, so it is worth
  trying both.

- *Mathlib docs* (the generated API reference at
  `leanprover-community.github.io/mathlib4_docs`).  If you already know the namespace
  (`Filter`, `MeasureTheory`, `Topology.Basic`, ...), browsing the
  module is faster than any search.

- *Zulip* (`leanprover.zulipchat.com`, the `#new members` and
  `#Mathlib4` streams) is the community chat.  For questions that
  no search answers, posting a minimal `example` together with the
  goal you're stuck on almost always gets a helpful reply within
  hours.

- *AI assistants* (ChatGPT, Claude, Gemini, Copilot, and the
  Lean-focused plugins and Copilot-for-Lean projects built on top of
  them) have become surprisingly effective at suggesting lemma names,
  spotting why a tactic fails, and translating informal arguments into
  Lean.  They are fallible -- they will cheerfully invent lemmas that
  do not exist, or quote outdated Mathlib 3 syntax -- but used
  critically they are one of the fastest ways to get unstuck.  A good
  workflow is: paste your goal state and the surrounding `example`,
  ask for two or three candidate approaches, and then *verify each
  suggestion in Lean* (via `exact?`, `#loogle`, or simply by trying to
  compile it).  Treat AI output the same way you would treat a
  confident but occasionally wrong colleague -- *use it*, but always
  check.
  You are strongly encouraged to use these tools alongside `#loogle`,
  `#leansearch`, and the Mathlib docs.

As a rule of thumb: try `exact?` / `apply?` first (they know your
exact proof state), then `#loogle` (precise, fast), then
`#leansearch` / `#moogle` or an AI assistant (when you do not know
the vocabulary Mathlib uses), and finally the docs or Zulip for
open-ended questions.
