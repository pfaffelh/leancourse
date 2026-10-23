import VersoSlides
import Verso.Doc.Concrete
import Mathlib

open VersoSlides

set_option pp.rawOnError true

/-
Deck for the chapter "Terms" (Lean and its type theory). It follows
the chapter section by section: `def`, structure values, functions,
polymorphism, `fun`, pattern matching, recursion and termination.
The structures from the Types chapter are redeclared on slide 2.
-/

namespace SlidesTerms
#doc (Slides) "Terms" =>

```css
.reveal section p { font-size: 0.8em; line-height: 1.32; margin: 0.42em 0; }
.reveal section p.key, .reveal section .key p { color: #1b91ff; }
.reveal section table { font-size: 0.62em; margin: 0.2em auto 0.4em; }
.reveal section table th,
.reveal section table td { padding: 0.18em 0.9em; }
.reveal section li { font-size: 0.8em; }
```

# Terms

Lean and its type theory — the chapter on terms.

The previous chapter formed *types*. This one defines *terms*:
named inhabitants of those types.

# From the Types chapter

```lean -panel -stretch
structure Point where
  x : ℕ
  y : ℕ
structure Point3D extends Point where
  z : ℕ
structure MyComplex where
  re : ℤ
  im : ℤ
```

# Naming terms with `def`

`def name : T := term` names a term of type `T`.

```lean -panel -stretch
def origin : Point := { x := 0, y := 0 }
def p1 : Point := ⟨1, 2⟩
def p2 : Point := Point.mk 3 4
def p3 : Point where
  x := 0
  y := 0
#check ({ x := 0, y := 0 } : Point)
```

All four call the single constructor `Point.mk`.

# Four forms, one constructor

- record form `{ x := …, y := … }`
- anonymous constructor `⟨…⟩`, typed `\<` and `\>`
- explicit `Point.mk`
- `where` form: one `field := value` line per field

`where` is the record form over several lines — unrelated to the
`|`-branches of pattern matching.

:::class "key"
If the type is not clear from context, annotate the record.
:::

# Reading and updating fields

`#eval` evaluates a term and prints the value.

```lean -panel -stretch
#eval p1.x          -- outputs 1
#eval p1.y          -- outputs 2

def p4 : Point := { p1 with y := 10 }
-- p4.x = 1, p4.y = 10
```

:::class "key"
Structures are immutable: `with` builds a new `Point`.
:::

# Defaults and extended structures

```lean -panel -stretch
structure MyConfig where
  width : ℕ := 80
  height : ℕ := 24
  title : String := "Untitled"
def myConfig : MyConfig := { title := "Win" }
def q : Point3D := { x := 1, y := 2, z := 3 }
#eval q.x    -- outputs 1 (inherited)
```

Fields with defaults may be omitted. An extended structure needs
all fields, inherited and new.

# Operations and dot notation

Operations on a structure are ordinary functions. In the type's
namespace, they can be called with dot notation.

```lean -panel -stretch
def Point.normSq (p : Point) : ℕ :=
  p.x * p.x + p.y * p.y

#eval p2.normSq    -- outputs 25
```

`p2 : Point`, so Lean looks for `Point.normSq`.

# Gaussian integers

Data and its operations together.

```lean -panel -stretch
def MyComplex.mul (a b : MyComplex) :
    MyComplex :=
  { re := a.re * b.re - a.im * b.im,
    im := a.re * b.im + a.im * b.re }

def i : MyComplex := { re := 0, im := 1 }

#eval (MyComplex.mul i i).re    -- outputs -1
```

# Defining and evaluating functions

`def name (arguments) : resultType := body`

```lean -panel -stretch
def double (n : ℕ) : ℕ := 2 * n
#eval double 5    -- outputs 10

def add (a b : ℕ) : ℕ := a + b
#eval add 3 4    -- outputs 7
```

Application is `f x`. Functions are *curried*:
`ℕ → ℕ → ℕ` is `ℕ → (ℕ → ℕ)`, and `add 3 : ℕ → ℕ`.

# Polymorphic functions

Functions may take *types* as arguments.

```lean -panel -stretch
def myId (α : Type) (a : α) : α := a
#check myId ℕ 42        -- ℕ

def myId' {α : Type} (a : α) : α := a
#check myId' 42         -- ℕ, inferred
```

:::class "key"
Braces `{α : Type}` make the type implicit; Lean infers it.
:::

# Universe variables

```lean -panel -stretch
universe u
def idOne (α : Type u) (a : α) : α := a

def idStar {α : Type*} (a : α) : α := a
```

`Type*` inserts a fresh universe variable. That is why Mathlib
signatures read `{α : Type*}`: one definition for small `ℕ` and
large `Type` alike.

# Anonymous functions

```lean -panel -stretch
#eval (fun x : ℕ ↦ x + 1) 5       -- outputs 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- outputs 12
```

- `↦` is typed `\mapsto`; math `x ↦ x^2` is `fun x ↦ x ^ 2`
- `(· + 10)` is `fun x ↦ x + 10`
- `(· + ·)` is `fun x y ↦ x + y`

# Pattern matching

One branch per constructor, each prefixed by `|`.

```lean -panel -stretch
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Lean checks automatically:

- *exhaustiveness*: every constructor is covered,
- *termination*: `factorial n` is on a smaller argument.

# Matching on your own types

```lean -panel -stretch
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))
```

`.zero` abbreviates `MyNat.zero`, since the result type is known.
Plain `zero` fails: it is not in scope.

# Any inductive type

```lean -panel -stretch
def Option.getD' {α : Type*} (d : α) :
    Option α → α
  | none   => d
  | some a => a

def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs
```

Inline, the same syntax reads `match n with | 0 => … | _ + 1 => …`.

# Recursion

```lean -panel -stretch
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- outputs 55
```

Lean accepts recursion only once it sees that it terminates.

:::class "key"
Structural recursion — calls on sub-parts of the input — is automatic.
:::

# Termination by a measure

`termination_by` names a measure, `decreasing_by` proves it drops.

```lean -panel -stretch
def euclidGcd (m n : Nat) : Nat :=
  if _h : m = 0 then n
  else euclidGcd (n % m) m
termination_by m
decreasing_by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)

#eval euclidGcd 48 36   -- 12
```

Goal: `n % m < m`. The dependent `if` puts `_h` in scope.

# Routine decrease

```lean -panel -stretch
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0
termination_by n
decreasing_by omega

#eval log2 16   -- 4
```

This compiles to *well-founded recursion* (`WellFounded.fix`).
The theory behind it comes in the Mathematics part.

# Summary

- `def` names a term; four forms build a structure value
- dot notation reads fields, `with` copies with changes
- functions are terms of function type, curried
- `{α : Type*}`: implicit, universe-polymorphic arguments
- `fun x ↦ …` and `·` for anonymous functions

:::class "key"
Pattern matching must be exhaustive; recursion must terminate.
:::
