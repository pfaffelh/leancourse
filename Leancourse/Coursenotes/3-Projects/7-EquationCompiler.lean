import VersoManual
import Manual.Meta
import Leancourse.Coursenotes.References

open Verso.Genre Manual
open Leancourse.Refs

#doc (Manual) "Project 7: What Lean makes of a recursive definition" =>
%%%
tag := "project-equation-compiler"
%%%

*What it is.*  The kernel knows no pattern matching and no
recursion, only recursors ({ref "recursor"}[chapter 1.3]). A
definition such as

```
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```

is translated by the elaborator into terms built from `Nat.rec`.
Along the way it generates auxiliary definitions, all ordinary
`def`s that `#print` shows:

* `Nat.casesOn`: the recursor without the values at the recursive
  arguments, a case split on the outermost constructor;
* `fib.match_1`: the patterns `0`, `1`, `n + 2` as nested `casesOn`;
* `Nat.below`: the type of a *table* of the values at all smaller
  arguments, with `Nat.below (n + 1) = motive n ×' Nat.below n`;
* `Nat.brecOn` and `Nat.brecOn.go`: one pass of `Nat.rec` that builds
  value and table together;
* `fib._f`: `fib` with every recursive call replaced by a lookup in
  the table; `#print fib` shows `fun x => Nat.brecOn x fib._f`.

The project is to rebuild this machinery by hand, for `ℕ` and for a
type of trees, and to check each step against Lean with `rfl`.
{ref "brecon"}[Course-of-values recursion] in chapter 1.3 states
the problem that this machinery solves.

*Implementation idea.*

* *Reading.* Run `#print` on `Nat.casesOn`, `Nat.below`,
  `Nat.brecOn`, `Nat.brecOn.go`, `fib.match_1`, `fib._f` and `fib`.
  Explain each term. `×'` is `PProd`, the pair type that also accepts
  proofs as components; explain why `Prod` does not suffice.
* *By hand for `ℕ`.* Define `myCasesOn`, `myBelow`, `myBrecOn` with
  `Nat.rec` only, and prove that they agree with Lean's versions, by
  `rfl` where possible. Define `fib` once more through `myBrecOn` and
  prove that it agrees with `fib`.
* *Trees.* Take
  `inductive BinTree | leaf | node (l : BinTree) (a : ℕ) (r : BinTree)`.
  Write down `BinTree.below` and `BinTree.brecOn` by hand: the table
  now branches like the tree,
  `BinTree.below (node l a r) = (motive l ×' below l) ×' (motive r ×' below r)`.
  Check against Lean with `rfl`. Define `height` through your
  `brecOn` and compare with the definition by pattern matching.
* *The structural check.* Explain with `fib._f` why Lean accepts a
  recursive call exactly when its argument is found in the table,
  and why `loop n := loop n` and `log2 (n / 2)` are not structural.
* *Proofs.* With a `Prop`-valued motive the table holds proofs: the
  induction hypotheses for all smaller arguments. Prove
  `0 < fib (n + 1)` once by pattern matching and once through your
  `myBrecOn`, and compare the proof terms with `#print`.

*Comments and extensions.*
* *Running time.* `#eval fib 32` takes over a second, `fib 90 = … :=
  rfl` is checked at once. Explain the difference: `#eval` runs
  compiled code made from the equations as written, the kernel
  reduces the `brecOn` term, which computes every value once.
  Measure, for example with `set_option profiler true`.
* *Well-founded recursion.* Definitions that are not structural are
  translated with `WellFounded.fix`. Find out how, and why `rfl`
  then usually fails while the equation lemmas (`f.eq_1`) work.
* *Other types.* Do the same for `List`, or for the infinitely
  branching `MyTree` of chapter 1.3, whose table is a function.
* Project 6 (mutual types) asks for the recursor of a mutual type;
  the two projects combine well.

*References.*  {citet theoremProvingInLean4}[], chapter on induction
and recursion, for the translation of pattern matching and
structural recursion; the Lean Language Reference on
[recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/).
