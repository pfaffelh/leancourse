import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 8: How to make Lean prove 2 + 3 = 6" =>
%%%
tag := "project-fooling-lean"
%%%

*What it is.*  A Lean proof certifies the statement as it was
elaborated, not as it reads on the screen. Between the two stand
notation, typeclass instances, the pretty printer, axioms, the
compiler and the elaborator, and each of them can be bent. The
project collects the ways to make Lean accept a statement that looks
false, explains for each one what was really proved, and finds the
tool that exposes it. All examples below were checked with the
course's Lean version (v4.34).

Six ways, from harmless to serious:

1. *An instance.* With a local instance of high priority, `+` means
   multiplication (instances: {ref "typeclasses"}[chapter 1.6]):

   ```
   section
   local instance (priority := high) : Add ℕ := ⟨Nat.mul⟩
   theorem two_add_three : (2 : ℕ) + 3 = 6 := by decide
   end
   #check two_add_three         -- two_add_three : 2 + 3 = 6
   #print axioms two_add_three  -- does not depend on any axioms
   ```

   Only `set_option pp.explicit true` shows the foreign instance.

2. *Syntax.* `local macro_rules` reads `a + b` as `a * b`
   ({ref "syntax-macro-rules"}[chapter 1.8]). The source says
   `2 + 3 = 6`; here `#check` already prints `2 * 3 = 6`.

3. *The pretty printer.* The reverse: an honest statement
   `2 * 3 = 6`, and a local `app_unexpander` for `HMul.hMul` that
   prints it as `2 + 3 = 6`. Inside the section, `#check` and the
   infoview show the false version.

4. *A name.* In a namespace, `def Irrational (_ : ℝ) : Prop := False`
   makes `¬ Irrational √2` provable by `fun h => h`. Which
   `Irrational` is meant shows only on hover or in the full name.

5. *An axiom or `sorry`.* `axiom two_eq_three : (2 : ℕ) = 3` proves
   anything; `#print axioms` lists `two_eq_three`, and a `sorry`
   appears as `sorryAx` ({ref "rules-axioms"}[chapter 1.5]).

6. *The compiler and the kernel.* `@[implemented_by]` lets the
   compiled code of a function differ from its definition, and
   `native_decide` trusts the compiled code. With a function that is
   `false` by definition and `true` when compiled, this proves
   `False`; `#print axioms` names an axiom
   `oops._native.native_decide.ax_1_1`. Worse:
   `set_option debug.skipKernelTC true` with a meta-program that adds
   a theorem `t : False` whose proof is `True.intro`. Then
   `#print axioms t` says *does not depend on any axioms*. Only
   `leanchecker`, which replays the compiled file through the kernel,
   reports `declaration type mismatch`.

*Implementation idea.*

1. *Catalogue.* Reproduce the six cases in one file per case, with a
   statement that looks false. Add cases of your own: Unicode letters
   that look alike, coercions, `autoImplicit`, `open … hiding`, or
   `attribute [simp]` on a false-looking lemma. For each, state
   precisely what was proved.
2. *Detection.* For each case, find the weakest tool that exposes it:
   reading the source, hovering, `#check`, `set_option pp.explicit
   true` or `pp.all`, `#print`, `#print axioms`, `leanchecker`.
   Present the result as a table, case against tool.
3. *Defence.* Read the Lean reference on validating proofs, and run
   `comparator` on one case: a trusted file with the statement, an
   untrusted one with the proof. Which of the six cases does it
   catch? Explain each answer.
4. *History.* Real soundness bugs are a different matter: there the
   kernel itself accepted a false proof
   ({ref "soundness-bugs"}[2026]). Explain the difference to the six
   cases above.

*Comments.*  The project needs no mathematics beyond the course, but
it needs care: every claim of the form "this tool shows it" has to be
tested. The meta-programming in case 6 is short; the project does
not ask for more of it. Keep all files in a separate directory, never
in a library others build on.

*References.*  The Lean reference, [Validating a Lean
Proof](https://lean-lang.org/doc/reference/4.36.0-rc2/ValidatingProofs/),
on the blue check marks, `#print axioms`, `lean4checker` and
`comparator`; the [comparator
repository](https://github.com/leanprover/comparator); Dan Abramov,
[The Math Is Haunted](https://overreacted.io/the-math-is-haunted/), a
first encounter with a false axiom.
