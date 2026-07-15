import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib
-- reuse the types (`Point`, `MyNat`, `MyComplex`, ...) declared there
import «Leancourse».Coursenotes.«01-Lean».«02-Types»

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Terms" =>
%%%
htmlSplit := .never
tag := "terms"
%%%

The previous chapter showed how *types* are formed. This chapter is about the other side: how to *define terms* -- named inhabitants of those types.

# Naming terms with `def`
%%%
tag := "naming-terms"
%%%

The command `def` gives a name to a term. In its simplest form,

```
def name : T := term
```

gives the name `name` to a term of type `T`. Using the `Point` structure from the previous chapter, here are four ways to define a term of type `Point`:

```lean
def origin : Point := { x := 0, y := 0 }
def p1 : Point := ⟨1, 2⟩
def p2 : Point := Point.mk 3 4
def p3 : Point where
  x := 0
  y := 0
```

All four invoke the single constructor of `Point`: the record form `{ x := …, y := … }`, the *anonymous constructor* `⟨...⟩` (typed `\<` and `\>`), the explicit `Point.mk`, and the *block* `where` form -- one `field := value` line per field, with no braces or commas. The `where` form is just the record form spread over several lines; it is the same syntax we will use to supply {ref "typeclasses"}[typeclass instances] (`instance : Add Vec2 where …`), and it has nothing to do with the `|`-branches of pattern matching (fields are `field := value`, not `| pattern => …`).

Here the target type is fixed by the `: Point` on the left of `:=`, so Lean knows which constructor `{ … }` and `⟨…⟩` mean. When the type is *not* clear from the context, you can annotate the record itself:

```lean
#check ({ x := 0, y := 0 } : Point)
```

# Constructing and using structure values
%%%
tag := "structure-values"
%%%

We read fields back with dot notation. Here the `#eval` command evaluates a (computable) term and prints the resulting value -- the same reduction that `rfl` performs, only with the answer displayed:

```lean
#eval p1.x          -- outputs 1
#eval p1.y          -- outputs 2
```

We build a new value from an existing one, changing only some fields, with the `with` keyword:

```lean
def p4 : Point := { p1 with y := 10 }
-- p4.x = 1, p4.y = 10
```

Since structures are immutable (as everything in functional programming), this creates a new `Point` rather than modifying `p1`. You may even draw from several records at once -- `{ p, q with … }` takes each remaining field from the first of `p`, `q` that supplies it. When a structure declares field defaults, a value may omit those fields:

```lean
def myConfig : MyConfig := { title := "My Window" }
-- myConfig.width = 80, myConfig.height = 24
```

For an extended structure we supply all fields, inherited and new:

```lean
def q : Point3D := { x := 1, y := 2, z := 3 }

#eval q.x    -- outputs 1 (inherited from Point)
#eval q.z    -- outputs 3
```

Operations on a structure are ordinary functions; placing them in the type's namespace lets us call them with dot notation:

```lean
def Point.normSq (p : Point) : ℕ :=
  p.x * p.x + p.y * p.y

#eval p2.normSq    -- outputs 25
```

`p2.normSq` (the squared distance from the origin) works because Lean sees that `p2 : Point` and looks for `Point.normSq`. The Gaussian-integer type gives a fuller example -- data and its operations together:

```lean
def MyComplex.add (a b : MyComplex) : MyComplex :=
  { re := a.re + b.re, im := a.im + b.im }

def MyComplex.mul (a b : MyComplex) : MyComplex :=
  { re := a.re * b.re - a.im * b.im,
    im := a.re * b.im + a.im * b.re }

def MyComplex.norm (a : MyComplex) : ℤ :=
  a.re * a.re + a.im * a.im

def i : MyComplex := { re := 0, im := 1 }

#eval (MyComplex.mul i i).re    -- outputs -1
```

# Defining and evaluating functions
%%%
tag := "pure-functions"
%%%

A *function* is again just a term -- one whose type is a function
type.  We define one with `def`, now writing its *arguments* before
the `:=`, and evaluate it with `#eval`.  The shape is

```
def name (arguments) : resultType := body
```

so the following defines `double`, taking one argument `n : ℕ` and
returning the `ℕ` value `2 * n`:

```lean
def double (n : ℕ) : ℕ := 2 * n

#eval double 5    -- outputs 10
#eval double 0    -- outputs 0
```

Application is written `f x` (no parentheses -- `f x` is Lean's way
of writing `f(x)`).  A *pure function* returns the same result for
the same arguments, exactly as in mathematics.

Functions of several arguments are *curried*: a function of two
arguments is really a function that takes one argument and returns
another function.

```lean
def add (a b : ℕ) : ℕ := a + b

#eval add 3 4    -- outputs 7
```

The type of `add` is `ℕ → ℕ → ℕ`, which reads as `ℕ → (ℕ → ℕ)`; so
`add 3` is itself a function of type `ℕ → ℕ`.

# Polymorphic functions
%%%
tag := "polymorphic-functions"
%%%

Functions can take *types* as arguments, not just values -- this is how
you write a single definition that works for every type.  The identity
function is the basic example:

```lean
def myId (α : Type) (a : α) : α := a
#check myId ℕ 42        -- ℕ
```

Usually you do not want to pass the type explicitly every time, so you
make it an *implicit* argument with braces `{...}`; Lean then infers it
from the value:

```lean
def myId' {α : Type} (a : α) : α := a
#check myId' 42         -- ℕ, inferred
```

A definition that should also work at *any universe level* -- recall
the {ref "type-universes"}[universe hierarchy] -- uses a universe
variable.  You may introduce one with the `universe` command, or, most
commonly, write `Type*`, which inserts a fresh universe variable for
you:

```lean
universe u
def idOne (α : Type u) (a : α) : α := a

def idStar {α : Type*} (a : α) : α := a
```

This is why signatures throughout Mathlib read `{α : Type*}`: the same
definition then applies whether `α` is small like `ℕ` or large like
`Type` itself.  We use `{α : Type*}` freely in the examples below.

# Anonymous functions
%%%
tag := "anonymous-functions"
%%%

Sometimes we need a quick, throwaway function without giving it a
name.  We use `fun` (short for "function") with the `↦` arrow
(typed `\mapsto`):

```lean
#eval (fun x : ℕ ↦ x + 1) 5       -- outputs 6
#eval (fun x y : ℕ ↦ x * y) 3 4   -- outputs 12
```

In mathematics one would write `x ↦ x^2`; in Lean we write
`fun x ↦ x ^ 2`.  There is an even shorter form using the `·`
placeholder (a centered dot, typed `\cdot`): a `·` stands for an
anonymous argument, so `(· + 10)` is shorthand for `fun x ↦ x + 10`,
and several `·` become successive arguments -- `(· + ·)` means
`fun x y ↦ x + y`.

# Pattern matching
%%%
tag := "pattern-matching"
%%%

For functions on {ref "inductive"}[inductive types] (like `ℕ`, `List α`, `Option α`,
`Bool`), the most natural way to define them is by *pattern matching*
on the constructors of the input.  The syntax uses `match ... with`
and one branch per constructor, each prefixed by a `|`.

For example, the factorial function on `ℕ` matches on whether the
input is `0` or a successor `n + 1`:

```lean
def factorial : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * factorial n
```

Each branch may use the variables introduced by its pattern (here
`n` on the right-hand side).  Lean checks two things automatically:

1. *Exhaustiveness.*  Every constructor of `ℕ` is covered (the cases
   `0` and `n + 1` exhaust `ℕ`).  If you forget a case, Lean
   complains.
2. *Termination.*  The recursive call `factorial n` is on a strictly
   smaller argument than `n + 1`, so the definition is well-founded.

It works just as well for the inductive types you declare yourself. For `MyNat` from the {ref "inductive"}[previous chapter], doubling is defined by matching on the two constructors:

```lean
def MyNat.double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (MyNat.double n))
```

The leading dot in `.zero` and `.succ` is *anonymous constructor notation*: because Lean already knows the result must be a `MyNat`, we may write `.zero` in place of the full `MyNat.zero`. Writing plain `zero` would fail -- there is no `zero` in scope, only `MyNat.zero`.

Pattern matching works for any inductive type:

```lean
-- A function on Bool
def negate : Bool → Bool
  | true  => false
  | false => true

-- A function on Option α: extract or use a default
def Option.getD' {α : Type*} (d : α) : Option α → α
  | none   => d
  | some a => a

-- A recursive function on List α
def length' {α : Type*} : List α → ℕ
  | []      => 0
  | _ :: xs => 1 + length' xs
```

The same syntax can be used inline with `match`:

```lean
example (n : ℕ) : ℕ :=
  match n with
  | 0     => 42
  | _ + 1 => 0
```

# Recursion and termination
%%%
tag := "recursion"
%%%

The definitions above are *recursive*: they call themselves on
smaller inputs.  A classic example with two base cases is the
Fibonacci sequence:

```lean
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10    -- outputs 55
```

Lean only accepts a recursive definition once it is convinced the
recursion *terminates*.  For *structural* recursion -- where each
call is on a syntactic sub-part of the input, as in `factorial`,
`length'`, and `fib` -- this is automatic.

When the recursive call is *not* on a structural sub-part, you
justify termination by giving a *measure* that strictly decreases:
the `termination_by` clause names the measure, and `decreasing_by`
discharges the proof that it goes down.  Euclid's algorithm is the
classic example -- `euclidGcd m n` recurses on `n % m`, which is not
a subterm of `m`, but the first argument strictly decreases:

```lean
def euclidGcd (m n : Nat) : Nat :=
  if _h : m = 0 then n
  else euclidGcd (n % m) m
termination_by m
decreasing_by
  exact Nat.mod_lt n (Nat.pos_of_ne_zero _h)

#eval euclidGcd 48 36   -- 12
```

Reading it off: `termination_by m` declares the measure (the first
argument); for the recursive call Lean then asks you to show it
shrinks, i.e. `n % m < m`, which is exactly the goal `decreasing_by`
proves (`Nat.mod_lt` from `m ≠ 0`; the hypothesis `_h` is in scope
thanks to the dependent `if`).  When the decrease is routine,
`decreasing_by` can often close it with `omega`:

```lean
def log2 (n : Nat) : Nat :=
  if _h : 2 ≤ n then 1 + log2 (n / 2) else 0
termination_by n
decreasing_by omega

#eval log2 16   -- 4
```

Under the hood this compiles to *well-founded recursion*
(`WellFounded.fix`); that theory -- what makes a relation
well-founded, and why `<` on `Nat` qualifies -- is developed in the
*Mathematics* part.
