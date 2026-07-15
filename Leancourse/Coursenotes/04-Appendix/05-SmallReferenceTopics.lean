import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Small reference topics" =>
%%%
htmlSplit := .never
tag := "small-reference-topics"
%%%

A handful of short, self-contained reference topics -- consult them as needed rather than reading straight through.

# Different parentheses in `Lean`
%%%
tag := "parenthesis"
%%%

There are (essentially) three different types of parentheses in `Lean` statements. The simplest is `(...)`, which, as in normal use, indicates parentheses in the sense of what belongs together. However, you have to learn how `Lean` brackets internally when no '()' are given. Operators like *and* (`∧`), *or* (`∨`), are right-associative, so e.g. `P ∧ Q ∧ R := P ∧ (Q ∧ R)`. The application of functions in sequence, such as `f : ℕ → ℝ` and `g : ℝ → ℝ `, applied to `n : ℕ` is `g (f n)`, because `g` expects an input of type `ℝ`, and this is what `f n` provides. You cannot omit (...), i.e. in this case the parenthesis is left-associative.

Beyond grouping, `Lean` uses four kinds of *binder* brackets in a declaration's signature; they differ in *who supplies the argument, and how*:

:::table (align := left) +header
* + Bracket
  + Kind
  + Who fills it in
* + `(x : α)`
  + explicit
  + you, at every call
* + `{x : α}`
  + implicit
  + Lean, by *unification* (from the other arguments), eagerly
* + `⦃x : α⦄` (or `{{x : α}}`)
  + strict implicit
  + Lean, by unification -- but only once a following *explicit* argument is supplied
* + `[C α]`
  + instance-implicit
  + Lean, by *typeclass search* ({ref "typeclasses"}[the typeclass mechanism])
:::

Here is one definition using three of them; `#check @` makes every argument visible:

```lean
def foo {α : Type} [Add α] (x : α) : α := x + x

#check @foo
-- @foo : {α : Type} → [Add α] → α → α
```

`α` sits in `{}` because Lean infers it from the type of the explicit `x`; `Add α` sits in `[]` because it is found by instance search; only `x` must be given at the call. Real Mathlib lemmas read the same way:

```lean
#check @gt_iff_lt
-- @gt_iff_lt : ∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
```

Here `{α}`, `[inst : LT α]` and `{x y}` are all supplied automatically, so you write just `gt_iff_lt` (or apply it to concrete `x`, `y`).

## `{}` versus `⦃⦄`: eager vs. strict implicit
%%%
number := false
tag := "strict-implicit"
%%%

Both `{}` and `⦃⦄` are *implicit* -- Lean fills them in -- but they differ in *when*. A regular implicit `{x}` is solved *eagerly*, the moment the function is mentioned. A strict implicit `⦃x⦄` (also written `{{x}}`) is solved *only when a following explicit argument is actually supplied*; until then the binder stays put.

```lean
def idImp    {α : Type} (x : α) : α := x
def idStrict {{α : Type}} (x : α) : α := x
```

In ordinary use the difference is invisible (`idImp 5` and `idStrict 5` both give `5`). It matters when a function is used *without* its explicit argument -- exactly the situation for `⊆`. Mathlib defines `s ⊆ t` as `∀ ⦃a⦄, a ∈ s → a ∈ t` with a *strict* implicit `a`, so that from `h : s ⊆ t` you may apply `h` directly to a membership proof:

```lean
example (s t : Set ℕ) (h : s ⊆ t) (a : ℕ) (ha : a ∈ s) : a ∈ t := h ha
```

Had `a` been an ordinary implicit, mentioning `h` alone would have eagerly forced a metavariable for `a`, making `h ha` more awkward. Strict implicits keep such "apply me later" arguments out of the way until a real argument pins them down.


# Equality
%%%
tag := "equality"
%%%

Due to the multitude of types in Lean, we have to be careful about equality. In Lean, there are three types of equality:

* Syntactic equality: If two terms are letter-for-letter equal, then they are syntactically equal. However, there are a few more situations in which two terms are syntactically equal. Namely, if one term is just an abbreviation for the other (for example, `x = y` is an abbreviation for ` Eq x y`, where `Eq` is a function which takes two terms of the same type, and assigns `True` if they are the same and `False` otherwise), then these both terms are syntactically equal. Also equal are terms in which globally quantified variables have different letters. For example, `∀ x, ∃ y, f x y` and `∀ y, ∃ x, f y x` are syntactically equal.

* Definitional equality: Some terms are equal *by computation* -- Lean reduces both to a common form. For example, for `x : ℕ`, `x + 0` reduces to `x`, whereas `0 + x` does not (an asymmetry that comes from how `Nat` addition is defined). This notion, the *reduction rules* that generate it, and the cases where `rfl` gets *stuck*, are developed in full in {ref "reduction-rules"}[the reduction-rules section] of the chapter on the natural numbers.

* Propositional equality: If there is a proof of `x = y`, then `x` and `y` are said to be *propositionally equal*; likewise `P` and `Q` are propositionally equal when you can prove `P ↔ Q`. This is the equality you state and rewrite with in everyday mathematics.

The distinction matters because *tactics differ in which equality they respect* -- some see through it, some do not. `rfl`, `exact`, and `apply` accept a term whenever it is merely *definitionally* equal to what is expected (they run the reductions for you), whereas `rw` matches *syntactically* and will not fire unless the subterm literally appears. Many otherwise-puzzling tactic failures come down to exactly this.

There is a special kind of equality to be observed with sets and functions. For example, two functions are exactly the same if they return the same value for all values in the domain. This behavior is called *extensionality* in the theory of programming languages. (If extensionality applies, then, for example, two sorting algorithms are the same if they always produce the same result).


# Exploring definitions with `#check`, `#print` and `inferInstance`
%%%
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


# Diagnostic Commands
%%%
tag := "diagnostics"
%%%

These commands *inspect* your work without changing it: they report a
theorem's logical dependencies, suggest where a definition should
live, and run the library's quality checks.  Unlike the `#`-commands
in the Lean basics chapter (`#check`, `#eval`, `#print`), these are
mostly about *engineering* a clean, well-placed, axiom-honest
development.

## `#print axioms` -- the axiom footprint
%%%
number := false
tag := "diag-print-axioms"
%%%

`#print axioms name` traces a declaration back to the axioms it
ultimately depends on.  Recall (see {ref "lean-axioms"}[Lean's three
axioms]) that Lean has exactly three: `propext`, `Quot.sound`, and
`Classical.choice`.

```lean
theorem my_classical (p : Prop) : ¬¬p → p :=
  fun h => Classical.byContradiction (fun hn => h hn)

theorem my_constructive (n : ℕ) : n + 0 = n := rfl

#print axioms my_classical
-- 'my_classical' depends on axioms:
--   [propext, Classical.choice, Quot.sound]

#print axioms my_constructive
-- 'my_constructive' does not depend on any axioms
```

The main use is a *constructivity check*: if `Classical.choice` does
not appear, the proof is constructive.  Two caveats are worth
stating:

- It is a *constructivity* detector, not an *excluded-middle*
  detector.  Because the law of excluded middle is a
  {ref "em-derived"}[theorem] derived from `Classical.choice` (and not
  an axiom in its own right), using it leaves no separate token: a
  proof
  that uses `Classical.em` and one that uses `Classical.choice`
  directly are indistinguishable -- both simply show
  `Classical.choice`.
- If a proof contains a `sorry` (even indirectly, through a lemma it
  calls), the marker `sorryAx` appears.  This makes `#print axioms` a
  reliable way to detect unfinished proofs hiding in a development.

There is no `#used_axioms` command; `#print axioms` is the tool.

## `#find_home` -- where should this live?
%%%
number := false
tag := "diag-find-home"
%%%

`#find_home name` (from the `ImportGraph` library) suggests the files
*highest* in the import hierarchy where a declaration could live,
based on which files its own dependencies come from.  It is the tool
for *upstreaming* a lemma to the right place -- e.g. when contributing
to Mathlib.  `#find_home!` additionally refuses to suggest the
current file.

```
-- best used in a file with `import Mathlib`
#find_home my_lemma
-- ⇒ a list of candidate modules where `my_lemma` could go, e.g.
--   [Mathlib.Order.Basic, Mathlib.Data.Nat.Defs]

#find_home! my_lemma   -- same, but never suggests THIS file
```

Two points to keep in mind: it works best with `import Mathlib`, and
it may legitimately return only the current file (if the lemma's
dependencies are spread across incomparable files).  A related
command, `#min_imports`, computes the minimal set of imports a
declaration needs and additionally accounts for notation and tactics.

## `#lint` -- the environment linters
%%%
number := false
tag := "diag-lint"
%%%

`#lint` runs Mathlib's *environment linters* over declarations,
flagging quality problems such as undocumented definitions
(`docBlame`), unused arguments (`unusedArguments`), non-confluent simp
lemmas (`simpNF`), and uses of deprecated names.

```
#lint                 -- lint the current file's declarations
#lint in all          -- the whole environment (slow)
#lint only docBlame   -- run a single named linter
#lint+ in Batteries   -- verbose: report each linter's result
#list_linters         -- print every available linter
```

You can also append `*` to skip slow tests (`#lint*`), `-` for a
silent run that fails on any problem (handy in CI), or extra linter
names to add to the default set.

These are *not* the same as the build-time linters that produce the
warnings you see when this manual compiles (the `*`-emphasis and
60-column warnings): those check the Verso *markup source*, whereas
`#lint` checks the *Lean environment*.


# Keyword Reference
%%%
tag := "keyword-reference"
%%%

This appendix collects Lean's keywords in one place, grouped by role,
with a one-line meaning and a minimal example for each.  It is meant
as a lookup table, not a tutorial -- the relevant chapters explain the
constructs in context.

Two things are *not* keywords and are listed elsewhere:

- Commands beginning with `#` (`#check`, `#eval`, `#print`, ...) are
  *commands*, covered in the Lean basics chapter and the "Getting
  help" section.
- Symbols such as `∀`, `∃`, `λ`, `→`, `↔`, `∧`, `∨` are *notation*,
  not keywords.

## Declarations
%%%
number := false
tag := "kw-declarations"
%%%

:::table +header
* + Keyword
  + Meaning
  + Example
* + `def`
  + Define a function or value.
  + `def double (n : ℕ) := 2 * n`
* + `theorem`
  + Declare a proof of a proposition.
  + `theorem t : 1 + 1 = 2 := rfl`
* + `lemma`
  + Synonym for `theorem` (added by Mathlib).
  + `lemma l : True := trivial`
* + `example`
  + Anonymous declaration; checked but not named.
  + `example : 2 = 2 := rfl`
* + `abbrev`
  + Reducible abbreviation (unfolds eagerly).
  + `abbrev NatAlias := ℕ`
* + `instance`
  + Register a typeclass instance.
  + `instance : Inhabited ℕ := ⟨0⟩`
* + `class`
  + Declare a typeclass.
  + `class Foo (α : Type) where x : α`
* + `structure`
  + Declare a record type with named fields.
  + `structure Pt where x : ℕ; y : ℕ`
* + `inductive`
  + Declare an inductive type by its constructors.
  + `inductive Dir | up | down`
* + `axiom`
  + Postulate a constant without proof.
  + `axiom myAx : ∃ n : ℕ, n > 0`
* + `opaque`
  + Declare an irreducible constant.
  + `opaque secret : ℕ`
:::

## Modifiers
%%%
number := false
tag := "kw-modifiers"
%%%

These precede or annotate a declaration.

:::table +header
* + Keyword
  + Meaning
  + Example
* + `noncomputable`
  + Declaration has no executable code.
  + `noncomputable def r := Real.pi`
* + `partial`
  + Allow non-terminating recursion.
  + `partial def loop (n : ℕ) := loop (n+1)`
* + `unsafe`
  + Bypass termination and typing checks.
  + `unsafe def f := f`
* + `private`
  + Restrict visibility to the current file.
  + `private def helper := 0`
* + `protected`
  + Require the full name even after `open`.
  + `protected def Foo.bar := 0`
* + `mutual`
  + Block of mutually recursive declarations.
  + `mutual def a := b; def b := a end`
* + `deriving`
  + Auto-derive instances for a type.
  + `inductive C | x deriving Repr`
* + `extends`
  + Build a structure on top of others.
  + `structure G extends Mul, One`
:::

## Terms and expressions
%%%
number := false
tag := "kw-terms"
%%%

:::table +header
* + Keyword
  + Meaning
  + Example
* + `fun`
  + Anonymous function (lambda).
  + `fun x => x + 1`
* + `let`
  + Local definition inside a term.
  + `let y := 2; y + y`
* + `have`
  + Introduce an intermediate fact or value.
  + `have h : 0 ≤ 1 := by norm_num`
* + `show`
  + Restate the expected type / current goal.
  + `show 2 = 2; rfl`
* + `from`
  + Supply a term for a stated goal.
  + `show True from trivial`
* + `match` / `with`
  + Pattern matching on a value.
  + `match n with | 0 => 1 | _ => 0`
* + `if` / `then` / `else`
  + Conditional expression.
  + `if n = 0 then 1 else n`
* + `by`
  + Enter tactic mode to build a proof.
  + `by simp`
* + `do`
  + Sequence actions in a monad.
  + `do let x ← act; pure x`
* + `return`
  + Yield a value inside a `do` block.
  + `do return 0`
* + `calc`
  + Calculational (chained) proof.
  + `calc a = b := h1 _ = c := h2`
:::

## Organizing code
%%%
number := false
tag := "kw-organizing"
%%%

:::table +header
* + Keyword
  + Meaning
  + Example
* + `variable`
  + Declare reusable binders for later decls.
  + `variable (n : ℕ)`
* + `universe`
  + Declare universe variables.
  + `universe u`
* + `namespace` / `end`
  + Scope names under a common prefix.
  + `namespace Foo ... end Foo`
* + `section` / `end`
  + Group declarations, variables, and options.
  + `section ... end`
* + `open`
  + Bring names from a namespace into scope.
  + `open Nat`
* + `import`
  + Load another module (top of file only).
  + `import Mathlib`
* + `in`
  + Limit `open`/`variable`/`set_option` to one decl.
  + `open Nat in #check succ`
* + `where`
  + Auxiliary definitions or fields after a decl.
  + `def f := g where g := 0`
* + `set_option`
  + Set an elaborator or pretty-printer option.
  + `set_option pp.all true`
* + `attribute`
  + Add or remove attributes after the fact.
  + `attribute [simp] myLemma`
:::

Most of these appear throughout the notes; see the Lean basics and
type-theory chapters for the constructs in their natural setting.

