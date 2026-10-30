import VersoManual
import Manual.Meta
import Leancourse.Markup
import Leancourse.Coursenotes.References
import Mathlib
import «Leancourse».Coursenotes.«1-Lean».«2-FunctionsInductiveStructures»

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Leancourse.Refs
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Pattern matching and recursion" =>
%%%
htmlSplit := .never
tag := "pattern-matching-and-recursion"
%%%

The [slides](slides/1-3-pattern-matching-recursion/) for this chapter follow it section by section.

A term of an inductive type is used by asking which constructor built it. This chapter is about the functions defined in this way: by pattern matching, by recursion, and by the recursor itself. {ref "nat-intro"}[Chapter 1.1] wrote such functions on `ℕ` with `Nat.rec` by hand; here Lean writes them from equations, for every inductive type of {ref "types"}[chapter 1.2], structures included.

# Pattern matching
%%%
tag := "pattern-matching"
%%%

In {ref "nat-intro"}[chapter 1.1], `myDouble` was defined with the recursor `Nat.rec`, one argument per constructor. *Pattern matching* is another way to define a function on an inductive type, and the usual one: the cases are written as equations, one branch per constructor, each prefixed by `|`. Lean translates them into the recursor ({ref "recursor"}[The recursor]). The function `myNot` on `Bool` in {ref "bool"}[chapter 1.1] was of this kind. The factorial function on `ℕ` matches on whether the input is `0` or a successor `n + 1`:

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Each branch may use the variables introduced by its pattern (here `n` on the right-hand side). Lean checks two things automatically:

1. *Exhaustiveness.* Every constructor of `ℕ` is covered (the cases `0` and `n + 1` exhaust `ℕ`). If you forget a case, Lean complains.
2. *Termination.* The recursive call `factorial n` is on a strictly smaller argument than `n + 1`, so the recursion ends.

It works just as well for the inductive types you declare yourself. For `MyNat`, doubling and the conversion to `ℕ` are defined by matching on the two constructors:

```lean
def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))

def MyNat.toNat : MyNat → ℕ
  | .zero   => 0
  | .succ n => MyNat.toNat n + 1

#eval (MyNat.double (.succ .zero)).toNat   -- 2
```

Writing plain `zero` in place of `.zero` would fail: there is no `zero` in scope, only `MyNat.zero`. As for `Point.x`, for `m : MyNat` the name `m.toNat` means `MyNat.toNat m`.

Pattern matching is translated into the recursor for the kernel and into running code for `#eval`. A definition with the recursor of your own type, as in {ref "recursor"}[The recursor], cannot be run by `#eval`. That is why functions are usually written by pattern matching.

Pattern matching works for any inductive type. A list is empty, or a first element followed by a list. In Lean's library (`u` is a universe variable, {ref "polymorphic-functions"}[Polymorphic functions]):

```
inductive List (α : Type u) where
  | nil : List α                              -- written []
  | cons (a : α) (l : List α) : List α        -- written a :: l
```

So `[1, 2, 3]` is notation for `1 :: 2 :: 3 :: []`, that is `List.cons 1 (List.cons 2 (List.cons 3 List.nil))`. A function on lists has a branch for `[]` and one for `a :: l`. The pattern `_` matches anything and names nothing.

```lean
-- A function on Option α: extract or use a default
def Option.getD' {α : Type*} (d : α) : Option α → α
  | none   => d
  | some a => a

-- A recursive function on List α
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs
```

The same syntax can be used inside a term with `match`:

```lean
def isEmpty' {α : Type*} (l : List α) : Bool :=
  match l with
  | []     => true
  | _ :: _ => false
```

# Recursion and termination
%%%
tag := "recursion"
%%%

The definitions above are *recursive*: they call themselves on smaller inputs. A classic example with two base cases is the Fibonacci sequence:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- 55
```

Lean checks that the three patterns cover every natural number. The numerals in the patterns stand for constructors: `0` is `Nat.zero`, `1` is `Nat.succ Nat.zero`, and `n + 2` is `Nat.succ (Nat.succ n)`. Lean splits the argument by its constructor, `zero` or `succ m`, and splits `m` again where a pattern requires it. For `fib` this gives two nested case splits, with `Nat.casesOn`, the recursor without recursive values:

```
fun x => Nat.casesOn x  (case 0)
  (fun m => Nat.casesOn m  (case 1)
    (fun n => (case n + 2)))
```

Every leaf of this tree must be reached by one of the patterns. With the line for `1` missing, the case `Nat.succ Nat.zero` is reached by none:

```lean +error
def fib' : ℕ → ℕ
  | 0 => 0
  | n + 2 => fib' n + fib' (n + 1)
```

The error is "Missing cases: (Nat.succ Nat.zero)". A pattern that can never be reached, because earlier patterns already cover it, is an error as well ("Redundant alternative").

Lean only accepts a recursive definition once it is convinced the recursion *terminates*. There are two ways:

* *Structural recursion.* Every recursive call is on a part of the input, that is, on an argument of the constructor that built it. Lean translates the definition into the recursor of the type (more precisely into `brecOn`, a packaging of the recursor), and there is nothing to prove.
* *Well-founded recursion.* Every recursive call makes a *measure* smaller, a natural number computed from the arguments. Lean translates the definition into `WellFounded.fix` and needs a proof that the measure decreases.

`factorial`, `length'` and `fib` are structural. In `fib (n + 2)` the calls are `fib n` and `fib (n + 1)`, both on parts of `n + 2 = succ (succ n)`. So `fib` is translated into the recursor, it computes by ι, and `rfl` checks values:

```lean
-- fib 3 ⟶ fib 1 + fib 2 ⟶ 1 + (fib 0 + fib 1) ⟶ 1 + (0 + 1)
example : fib 3 = 2 := rfl
```

The recursor `Nat.rec` of {ref "nat-intro"}[chapter 1.1] hands the step only the value at `n`, but `fib (n + 2)` needs the values at `n` and at `n + 1`. Lean therefore uses `Nat.brecOn`, which is built from `Nat.rec` and hands the step the values at *all* smaller arguments:

```lean
#print fib
-- def fib : ℕ → ℕ := fun x => Nat.brecOn x fib._f
```

By hand, with `Nat.rec` alone, one carries the pair `(fib n, fib (n + 1))` along:

```lean
def fibPair (n : ℕ) : ℕ × ℕ :=
  Nat.rec (0, 1) (fun _ p => (p.2, p.1 + p.2)) n

example : fibPair 10 = (55, 89) := rfl
```

Recursion on several parts works the same way. In a binary tree whose nodes carry a natural number, every node has two subtrees, and the height recurses on both. A tree is either empty, `leaf`, or a node `node l a r` that carries the number `a` and has a *left subtree* `l` and a *right subtree* `r`, both again trees. The example below is the tree with root `3`, an empty left subtree, and as right subtree a single node carrying `4`:

```
    3
     \
      4
```

```lean
inductive BinTree where
  | leaf : BinTree
  | node (l : BinTree) (a : ℕ) (r : BinTree) : BinTree

def BinTree.height : BinTree → ℕ
  | .leaf => 0
  | .node l _ r => max l.height r.height + 1

example : (BinTree.node .leaf 3
    (.node .leaf 4 .leaf)).height = 2 := rfl
```

A call that is not on a smaller argument is rejected:

```lean +error
def loop (n : ℕ) : ℕ := loop n + 1
```

Lean reports that the argument `n` is unchanged in the recursive call. Were the definition accepted, it would give `loop 0 = loop 0 + 1`, and subtracting `loop 0` on both sides gives `0 = 1`.

When a recursive call is not on a part of the input, Lean cannot translate the definition structurally and looks for a measure. Often it finds one on its own. In `log2` the argument shrinks from `n` to `n / 2`. This holds only for `n ≥ 1`; for `n = 0` the call would be `log2 0` again. The `if` excludes this case: the recursive call stands in the branch where `2 ≤ n`, and Lean uses this condition to prove `n / 2 < n`.

```lean
def log2 (n : Nat) : Nat :=
  if 2 ≤ n then 1 + log2 (n / 2) else 0

#eval log2 16   -- 4
```

Without the `if`, Lean is left with the goal `n / 2 < n` for an arbitrary `n`, which is false for `n = 0`, and rejects the definition:

```lean +error
def log2' (n : Nat) : Nat :=
  1 + log2' (n / 2)
```

Cantor's enumeration of `ℕ × ℕ` runs through the pairs diagonal by diagonal: `(0, 0)`; `(0, 1)`, `(1, 0)`; `(0, 2)`, `(1, 1)`, `(2, 0)`; and so on. `pairIndex m n` is the position of `(m, n)` in this list. Within a diagonal it steps back from `(m + 1, n)` to `(m, n + 1)`; from the first pair `(0, n + 1)` of a diagonal it steps back to the last pair `(n, 0)` of the previous one.

:::figure "Cantor's enumeration of ℕ × ℕ. The point (m, n) carries pairIndex m n; the arrows run along a diagonal."
![Grid of the points (m, n) with m + n at most 4, each labelled with its position in Cantor's enumeration: 0 at (0, 0); 1, 2 on the next diagonal; 3, 4, 5; 6 to 9; 10 to 14. Arrows run down each diagonal from (0, n) to (n, 0)](/static/figures/cantor_pairing.png)
:::

In Lean, read backwards from `(m, n)`:

```lean
def pairIndex : ℕ → ℕ → ℕ
  | 0, 0 => 0
  | 0, n + 1 => pairIndex n 0 + 1
  | m + 1, n => pairIndex m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals (rw [Prod.lex_def]; omega)

#eval pairIndex 2 1   -- 8
```

Here Lean needs help. No argument decreases in both recursive calls, and the sum `m + n` stays the same in the third line. Without the last two lines of the definition Lean reports "Could not find a decreasing measure". The measure is a pair: first the diagonal `m + n`, then the position `m` on it. Pairs are compared *lexicographically*: `(a, b)` is smaller than `(c, d)` if `a < c`, or if `a = c` and `b < d`. `termination_by` names the measure; `m n =>` names the two arguments, which the patterns leave unnamed. `decreasing_by` proves that the measure decreases. There is one goal for each recursive call, and `all_goals` applies the same tactics to both: `rw [Prod.lex_def]` replaces the lexicographic order by its definition, and `omega`, a tactic that proves linear arithmetic over `ℕ` and `ℤ`, finishes.

That pairs are compared lexicographically is not written in the definition. Lean takes the order from the type of the measure, by instance search for the class `WellFoundedRelation` (typeclasses are the subject of {ref "typeclasses"}[chapter 1.6]). On `ℕ` the order is `<`; on a product it is `Prod.lex`, built from the orders on the two factors:

```lean
#synth WellFoundedRelation (ℕ × ℕ)
-- Prod.instWellFoundedRelation, defined as Prod.lex
```

Sometimes Lean finds the measure but cannot prove that it decreases. Which measure it found, `termination_by?` prints; for the logarithm to base `b` below it is `termination_by n`. Lean then has to show `n / b < n`. For `b = 2` this is linear arithmetic, which Lean does by itself; for a variable `b` it is not, and Lean stops with this goal. `decreasing_by` supplies the proof, here with the library theorem `Nat.div_lt_self : 0 < n → 1 < k → n / k < n`. The proof needs the condition of the `if` by name, so the `if` is *dependent*: in `if h : c then a else b`, the proof `h : c` is available in `a`, and a proof of `¬c` in `b`. Here `h.1 : 2 ≤ b` gives `1 < b`, and `0 < n` follows from `h` by `omega`:

```lean
def logb (b n : ℕ) : ℕ :=
  if h : 2 ≤ b ∧ b ≤ n then 1 + logb b (n / b)
  else 0
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) h.1

#eval logb 10 1000   -- 3
```

The theory behind well-founded recursion, what makes a relation well-founded and why `<` on `Nat` qualifies, is in {ref "wf-acc"}[Accessibility and well-founded relations]. If `decreasing_by` is left out, Lean tries a standard tactic, `decreasing_tactic`, which handles the simple cases on its own.

Functions or types that refer to each other are declared together in a `mutual … end` block; see the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#Lean___Parser___Command___mutual).

# Proving things about recursive definitions
%%%
tag := "recursive-proofs"
%%%

A structurally recursive definition is translated into the recursor, and the recursor computes by ι. So `rfl` and `#eval` see through it, even with a variable in the argument:

```lean
example : fib 10 = 55 := rfl
example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl
```

A definition by well-founded recursion does not compute in this way. `#eval` runs it, but the kernel does not unfold `WellFounded.fix`, so `rfl` and `decide` fail even on closed terms:

```lean +error
example : log2 16 = 4 := rfl
```

Instead Lean proves an *equation lemma* for every definition, here `log2.eq_1`, which states the defining equation. Proofs use it through `rw [log2]`, `unfold log2` or `simp [log2]`:

```lean
#check log2.eq_1
-- log2.eq_1 (n : ℕ) : log2 n =
--   if 2 ≤ n then 1 + log2 (n / 2) else 0

example : log2 16 = 4 := by simp [log2]

example (n : ℕ) (h : 2 ≤ n) :
    log2 n = 1 + log2 (n / 2) := by
  rw [log2]
  simp [h]
```

Proofs by induction that follow the recursion of a function, one case per branch, are done with `fun_induction` ({ref "induction"}[induction]).

# The recursor
%%%
tag := "recursor"
%%%

{ref "nat-intro"}[Chapter 1.1] used the recursor `Nat.rec` in a *non-dependent* form, into a fixed result type. In general the result type may *depend* on the term being consumed. This dependency is recorded by a *motive* `T → Sort u`. The binary tree `BinTree` from {ref "recursion"}[Recursion and termination] shows the full form:

```lean
#check @BinTree.rec
-- {motive : BinTree → Sort u} →
--   motive .leaf →                       -- leaf case
--   ((l : BinTree) → (a : ℕ) → (r : BinTree) →
--      motive l → motive r →
--      motive (.node l a r)) →            -- node case
--   (t : BinTree) → motive t
```

The case for `node` receives the three arguments of the constructor and, for the two subtrees `l` and `r`, the values `motive l` and `motive r` already computed for them. With the constant motive `fun _ => ℕ` this is recursion, for instance the sum of all numbers in a tree:

```lean
noncomputable def BinTree.sum : BinTree → ℕ :=
  BinTree.rec 0 (fun _ a _ sl sr => sl + a + sr)

example : (BinTree.node .leaf 3
    (.node .leaf 4 .leaf)).sum = 7 := rfl
```

Lean evaluates a definition in two ways. The *compiler* translates it into a program, and `#eval` runs that program. The *kernel* reduces the term with the {ref "reduction-rules"}[reduction rules], and `rfl` uses the kernel. The keyword `noncomputable` tells Lean not to compile a definition. Nothing else changes: the definition has the same type and the same value, `rfl` and all proofs work as before, and only `#eval` is unavailable. Here the keyword is needed because the compiler does not support the recursors of your own types (for `Nat` it has special support).

With a `Prop`-valued motive the same recursor is the *induction principle* for trees: to prove a statement for every tree, prove it for `leaf`, and prove it for `node l a r` assuming it for `l` and for `r`. Those are two induction hypotheses, one for each subtree. Recursion and induction are two readings of the single primitive `BinTree.rec`, which is why the `induction` tactic and recursive definitions feel so alike. The `induction` tactic applies the recursor for you: one subgoal per constructor, with an induction hypothesis for each recursive argument.

Lean generates `T.rec` for every `inductive` declaration from its constructors, always by the same recipe:

1. The parameters of `T`, such as `α` in `MyOption α`, as implicit arguments.
2. The *motive* `motive : T → Sort u`, the type of the result, which may depend on the term.
3. One *case* per constructor, in the order of the declaration. For a constructor `c (a₁ : A₁) … (aₖ : Aₖ) : T` the case takes the arguments `a₁ … aₖ`, then, for every argument `aᵢ` of type `T` itself (a *recursive* argument), a value of `motive aᵢ`, and returns a value of `motive (c a₁ … aₖ)`.
4. The term `t : T` to be consumed; the result has type `motive t`.

With the recursor come its computation rules, one per constructor: applied to `c a₁ … aₖ`, the recursor takes the case for `c`, and passes it the arguments and, for each recursive argument `aᵢ`, the recursor applied to `aᵢ`. For `BinTree` the rule for `node` is `BinTree.rec z s (.node l a r) ⟶ s l a r (BinTree.rec z s l) (BinTree.rec z s r)`.

```lean
#check @Colour.rec
-- {motive : Colour → Sort u} →
--   motive .red → motive .green → motive .blue →
--   (t : Colour) → motive t
#check @MyOption.rec
-- {α : Type} → {motive : MyOption α → Sort u} →
--   motive .none →
--   ((a : α) → motive (.some a)) →
--   (t : MyOption α) → motive t
#check @List.rec
-- {α : Type v} → {motive : List α → Sort u} →
--   motive [] →
--   ((head : α) → (tail : List α) →
--      motive tail → motive (head :: tail)) →
--   (t : List α) → motive t
#check @Point.rec
-- {motive : Point → Sort u} →
--   ((x y : ℕ) → motive { x := x, y := y }) →
--   (t : Point) → motive t
```

The constructors of `Colour` have no arguments, so its cases are plain values and `Colour.rec` is a case distinction with three branches. `MyOption.some` has an argument `a : α` that is not recursive, so its case is a function of `a` and gets no value of the motive. `List.cons` has the recursive argument `tail`, and its case gets `motive tail`, the result for the rest of the list; read as a proof, this is the induction hypothesis. A structure has a single constructor, so `Point.rec` just unpacks the fields. For an inductive type in `Prop` with more than one constructor, such as `MyOr`, the motive may only take values in `Prop` ({ref "prop-special"}[Why `Prop` is special]).

# Strict positivity
%%%
tag := "positivity-rule"
%%%

Not every `inductive` declaration is accepted. A constructor may mention the type being defined, but only *positively*. The *arrow* here is the `→` of a function type: in `α → β` the type `α` of the inputs stands to the left of the arrow, the type `β` of the values to the right. Strictly positive means that in the type of an argument of a constructor, the type being defined never stands to the left of an arrow. The type of the constructor itself does not count: every constructor of a type `T` ends in `→ T`, and only the arguments before that last arrow are checked. An example that is accepted is a type of infinitely branching trees:

```lean
inductive MyTree where
  | leaf (a : ℕ) : MyTree
  | node (f : ℕ → MyTree) : MyTree
```

`MyTree` is a type, and each of its elements is a tree. The constructors say what stands at the root. `leaf a` is the tree that consists of a single leaf, carrying the number `a`. `node f` is the tree whose root is a node with one subtree `f n` for every `n : ℕ`. Each `f n` is again a whole tree; where it is `leaf n`, it is a leaf of the big tree. The argument `f` of `node` has type `ℕ → MyTree`, and there `MyTree` stands to the *right* of `→`, so the declaration is accepted.

```lean
example : MyTree := .leaf 7
example : MyTree := .node (fun n => .leaf n)
example : MyTree :=
  .node (fun n => if n = 0 then .node .leaf else .leaf n)
```

:::figure "One element of MyTree, the last tree above. Circles are nodes, squares are leaves; the edge to the subtree f n is labelled n."
![A root node with edges labelled 0, 1, 2, 3 and dots. Edge 0 leads to a node whose edges 0, 1, 2, 3 lead to the leaves 0, 1, 2, 3; edges 1, 2, 3 lead to the leaves 1, 2, 3.](/static/figures/mytree.png)
:::

Every tree has a root, and every path from the root downwards ends in a leaf after finitely many steps: an element of an inductive type is built by constructors, from the bottom up. A tree that goes on downwards forever is not an element of `MyTree`. This is what makes structural recursion work, for instance for the function that descends into the subtree `f 0` until it meets a leaf. Only the width is infinite. The trees can be built in stages: first all `leaf a`, then all `node f` whose subtrees are leaves, then all `node f` whose subtrees come from the first two stages, and so on. The finite stages do not exhaust `MyTree`. The depth can be unbounded: in `MyTree.unbounded` the path through the subtree `n` has length `n + 1`, so every path ends, but there is no largest depth. This tree uses subtrees from every finite stage and lies on none of them, and a height with values in `ℕ` cannot be defined.

```lean
def MyTree.leftmost : MyTree → ℕ
  | .leaf a => a
  | .node f => (f 0).leftmost

def MyTree.chain : ℕ → MyTree
  | 0 => .leaf 0
  | n + 1 => .node (fun _ => MyTree.chain n)

def MyTree.unbounded : MyTree := .node MyTree.chain
```

The `leaf` case is what gets the type off the ground. Positivity constrains only *where* `MyTree` may occur, not whether the type has any elements: drop `leaf`, and the declaration is still accepted, but no tree can ever be built, because every `node` already demands a whole family `ℕ → MyTree` of subtrees. The type is then empty, like `Empty`. A finitely branching tree would be `node (l r : MyTree) : MyTree`, where `MyTree` occurs directly rather than inside a function.

But a constructor that stores a *function out of* the type is rejected. The argument `f` of `Bad.mk` has type `Bad → False`, and there `Bad` stands to the *left* of `→`:

```
inductive Bad where
  | mk (f : Bad → False) : Bad
-- error: (kernel) arg #1 of 'Bad.mk' has a non positive
--        occurrence of the datatypes being declared
```

The rejection is not pedantry: were `Bad` allowed, one could prove `False`. Every `b : Bad` has the form `Bad.mk f`, so pattern matching gives a function `unmk` that undoes `mk`: it takes `Bad.mk f` apart and returns `f`. Such a function exists for every type with a single constructor; it is just a `match`, and `match` comes with every inductive type. So nothing can be forbidden after the fact, only the declaration itself. Apply the stored function to `b` itself:

```
def unmk : Bad → (Bad → False) | .mk f => f
def neg (b : Bad) : False := unmk b b
```

so `neg : Bad → False`. Then `Bad.mk neg : Bad`, and `neg (Bad.mk neg) : False` is a closed proof of `False`; it even loops, `neg (Bad.mk neg) ⟶ unmk (Bad.mk neg) (Bad.mk neg) ⟶ neg (Bad.mk neg)`. Read as logic: `mk` and `unmk` together say `Bad ↔ ¬Bad`, and the two definitions above are the propositional proof that `P ↔ ¬P` implies `False`. Lean checks the argument once `mk` and `unmk` are given as hypotheses instead of being declared:

```lean
example (Bad : Type) (mk : (Bad → False) → Bad)
    (unmk : Bad → (Bad → False)) : False :=
  let neg : Bad → False := fun b => unmk b b
  neg (mk neg)
```

Strict positivity outlaws exactly the negative occurrence that ties this self-applying knot, the same concern that rules out `Type : Type`.

## Why positivity is enough
%%%
tag := "positivity-sufficient"
number := false
%%%

Read in sets, a declaration is an equation for a set `X`: an element of the type is exactly one of the things the constructors build. `False` is the empty set.

:::table (align := left) +header
* + declaration
  + equation
* + `ℕ`
  + `X = {0} ⊔ X`
* + `MyTree`
  + `X = ℕ ⊔ (ℕ → X)`
* + `Bad`
  + `X = (X → ∅)`
:::

The type exists if the equation has a solution, a fixed point `X = F(X)`. Whether it has one depends on where `X` stands. `ℕ → X` grows with `X`: a function into a smaller set is also a function into a larger one. `X → ∅` shrinks when `X` grows. So if `X` occurs only to the right of `→`, the map `F` is *monotone*: `X ⊆ Y` gives `F(X) ⊆ F(Y)`.

A monotone `F` has a fixed point, reached by the stages described for `MyTree` above. Put `X₀ = ∅`, `X₁ = F(X₀)`, `X₂ = F(X₁)`, …, and take unions at limit stages. By monotonicity the sets grow, and the stages continue transfinitely until nothing new is added; for `MyTree` this happens at the first uncountable ordinal, because each node has only countably many subtrees. The result is a set with `X = F(X)`. The constructors are maps into it, and the recursor is recursion over the stage at which an element first appears. A strictly positive declaration therefore adds only something that already exists in set theory, and cannot produce a contradiction. This is the set-theoretic semantics of inductive definitions: {citet aczel1977}[] for monotone inductive definitions in general, {citet dybjer1991}[] for inductive types in Martin-Löf's type theory, and {citet werner1997}[] for the Calculus of Inductive Constructions, with a model in ZFC plus inaccessible cardinals. For the type theory Lean implements, the same construction is part of the model of {citet carneiro2019}[], with the gap described in {ref "prop-special"}[Why `Prop` is special].

For `Bad` there is no solution. `X → ∅` has one element (the empty function) if `X` is empty, and none otherwise, so `X = (X → ∅)` fails either way: this is `Bad ↔ ¬Bad`. The stages do not help, because `F` is not monotone; they alternate between `∅` and a one-element set. For a negative occurrence with values in `Bool`, `mk (f : Bad' → Bool) : Bad'`, the set `X` would contain a copy of `X → Bool`, its power set, which Cantor's theorem rules out. The self-application `unmk b b` is Cantor's diagonal.

The word *strictly* matters. In `mk (f : (X → Bool) → Bool) : X` the type `X` stands to the left of two arrows, and the two reversals cancel, so `F` is monotone. But `F(X)` is then a double power set, again too large to fit into `X`, and together with the impredicative `Prop` such a declaration yields a proof of `False` {citep coquandPaulin1990}[]. Lean therefore requires that `X` stand to the left of no arrow at all.

