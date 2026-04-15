import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "Structures and Records" =>
%%%
htmlSplit := .never
tag := "structures"
%%%

While inductive types let us define types with multiple constructors, many mathematical objects are better described as a *collection of named fields*. For example, a point in the plane has an `x`-coordinate and a `y`-coordinate. In Lean, we use `structure` for this.

# Defining structures
%%%
tag := "defining-structures"
%%%

A `structure` is a special case of an inductive type with exactly one constructor and named fields. Here is a simple example:

```lean
structure Point where
  x : Float
  y : Float
```

This defines a type `Point` with two fields, `x` and `y`, both of type `Float`. We create values of type `Point` using anonymous constructor syntax or by naming the constructor explicitly:

```lean
def origin : Point := { x := 0.0, y := 0.0 }
def p1 : Point := ⟨1.0, 2.5⟩
def p2 : Point := Point.mk 3.0 4.0
```

All three syntaxes create a `Point`. The angle brackets `⟨...⟩` (typed `\<` and `\>`) are the anonymous constructor.

# Accessing fields and dot notation
%%%
tag := "dot-notation"
%%%

We access fields using dot notation:

```lean
#eval p1.x          -- outputs 1.0
#eval p1.y          -- outputs 2.5
```

We can also define functions in the `Point` namespace, and then call them with dot notation:

```lean
def Point.distToOrigin (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval p2.distToOrigin    -- outputs 5.0
```

This works because Lean sees that `p2` has type `Point`, so it looks for `Point.distToOrigin`.

# Updating structures
%%%
tag := "updating-structures"
%%%

We can create a new structure value based on an existing one, changing only some fields. This uses the `with` keyword:

```lean
def p3 : Point := { p1 with y := 10.0 }
-- p3.x = 1.0, p3.y = 10.0
```

Since structures are immutable (as everything in functional programming), this creates a new `Point` rather than modifying `p1`.

# Structures with default values
%%%
tag := "default-values"
%%%

Fields can have default values:

```lean
structure MyConfig where
  width : ℕ := 80
  height : ℕ := 24
  title : String := "Untitled"

def myConfig : MyConfig := { title := "My Window" }
-- myConfig.width = 80, myConfig.height = 24
```

# Extending structures
%%%
tag := "extending-structures"
%%%

One structure can extend another, inheriting all of its fields:

```lean
structure Point3D extends Point where
  z : Float

def q : Point3D := { x := 1.0, y := 2.0, z := 3.0 }

#eval q.x    -- outputs 1.0 (inherited from Point)
#eval q.z    -- outputs 3.0
```

This is particularly important in Mathlib, where the algebraic hierarchy uses structure extension extensively. For example, `CommRing` extends `Ring`, which extends `Semiring`, and so on.

# Mathematical examples
%%%
tag := "structures-math-examples"
%%%

Structures are natural for representing mathematical objects. Here is a complex number type:

```lean
structure MyComplex where
  re : Float
  im : Float

def MyComplex.add (a b : MyComplex) : MyComplex :=
  { re := a.re + b.re, im := a.im + b.im }

def MyComplex.mul (a b : MyComplex) : MyComplex :=
  { re := a.re * b.re - a.im * b.im,
    im := a.re * b.im + a.im * b.re }

def MyComplex.norm (a : MyComplex) : Float :=
  Float.sqrt (a.re * a.re + a.im * a.im)

def i : MyComplex := { re := 0.0, im := 1.0 }
def oneComplex : MyComplex := { re := 1.0, im := 0.0 }

#eval (MyComplex.mul i i).re    -- outputs -1.0
```

Here is a structure representing a linear map between two types that have addition and scalar multiplication:

```lean
structure MyLinearMap (α β : Type) [Add α] [Add β] [HMul ℕ α α] [HMul ℕ β β] where
  toFun : α → β
  map_add : ∀ x y : α, toFun (x + y) = toFun x + toFun y
```

Notice that the structure contains both data (the function `toFun`) and a property (`map_add`). This pattern of bundling data with properties is fundamental to how Mathlib organizes mathematics.

# Inductive types vs structures
%%%
tag := "inductive-vs-structure"
%%%

When should you use `inductive` and when `structure`?

* Use `structure` when your type has a single constructor with named fields. Examples: points, complex numbers, algebraic structures.
* Use `inductive` when your type has multiple constructors. Examples: natural numbers, lists, trees, `Option`, `Bool`.

A `structure` is syntactic sugar for an inductive type with one constructor. The definition

```
structure Point where
  x : Float
  y : Float
```

is essentially equivalent to

```
inductive Point where
  | mk : Float → Float → Point
```

but the `structure` version gives us named fields, dot notation, default values, and the `extends` mechanism.

# Using `deriving`
%%%
tag := "deriving"
%%%

When we define a new type, Lean can automatically generate certain instances for us using `deriving`:

```lean
structure Student where
  name : String
  age : ℕ
  deriving Repr

def alice : Student := { name := "Alice", age := 22 }
#eval alice    -- outputs { name := "Alice", age := 22 }
```

Without `deriving Repr`, the `#eval` command would not know how to print a `Student`. The `deriving` clause tells Lean to automatically create a `Repr` instance. Other commonly derived instances include `BEq` (Boolean equality), `Hashable`, and `Inhabited`.

```lean
structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr, BEq, Hashable
```

# Namespaces
%%%
tag := "namespaces"
%%%

Every structure automatically creates a namespace. When we defined `Point`, Lean created the namespace `Point` containing `Point.mk`, `Point.x`, and `Point.y`. We can add more definitions to this namespace:

```lean
namespace Point

def translate (p : Point) (dx dy : Float) : Point :=
  { x := p.x + dx, y := p.y + dy }

def scale (p : Point) (factor : Float) : Point :=
  { x := p.x * factor, y := p.y * factor }

end Point

#eval (p1.translate 10.0 20.0).x    -- outputs 11.0
#eval (p1.scale 3.0).y              -- outputs 7.5
```

Using namespaces keeps related functions organized and enables dot notation.
