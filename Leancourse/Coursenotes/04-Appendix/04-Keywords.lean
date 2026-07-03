import VersoManual
import Manual.Meta

open Verso.Genre Manual

#doc (Manual) "Keyword Reference" =>
%%%
htmlSplit := .never
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

# Declarations
%%%
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
  + `abbrev MyNat := ℕ`
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

# Modifiers
%%%
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

# Terms and expressions
%%%
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

# Organizing code
%%%
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
