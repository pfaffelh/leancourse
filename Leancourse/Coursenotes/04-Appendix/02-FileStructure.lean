import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true

#doc (Manual) "How a Lean file is structured" =>
%%%
htmlSplit := .never
tag := "file-structure"
%%%

A Lean file is a sequence of *commands* -- `def`, `theorem`,
`structure`, `#check`, and so on -- processed top to bottom.  It opens
with its `import`s, which pull in other files, and then a handful of
keywords organize the rest and control *where* the names they
introduce are visible: `namespace`, `open`, `section`, `variable`, and
the scope modifiers `private`, `local`, and `scoped`.  This appendix
collects them in one place.

# Imports
%%%
tag := "imports"
%%%

Every Lean file begins with its *imports*.  Writing `import Foo.Bar`
makes the contents of the module `Foo/Bar.lean` available in the
current file, and imports are *transitive* -- importing a module also
brings in everything that module itself imports.  All `import` lines
must come *first*, before any other command; an `import` after the
first `def` or `#check` is a syntax error.

The module name mirrors the file path: `import Mathlib.Order.Basic`
refers to `Mathlib/Order/Basic.lean`.  Importing the umbrella module
`Mathlib` pulls in the entire library at once -- convenient for
exploration, though slower to load -- whereas a targeted import brings
in only what you need:

```
import Mathlib.Order.Basic   -- just one module
import Mathlib                -- the whole library
```

Every chapter file in this course opens with `import Mathlib` (plus a
few Verso modules), which is why any Mathlib lemma is available in the
examples without further ceremony.

# Namespaces
%%%
tag := "namespaces"
%%%

A *namespace* groups related declarations under a common prefix.
Inside `namespace Foo ... end Foo`, every declaration `bar` is really
named `Foo.bar`.  Every `structure` and `inductive` type also opens a
namespace of its own name automatically.

```lean
namespace Geo

structure Point where
  x : Float
  y : Float

-- written inside `namespace Geo`, so its full name is
-- `Geo.translate`
def translate (p : Point) (dx dy : Float) : Point :=
  { x := p.x + dx, y := p.y + dy }

end Geo

-- outside the namespace we use the qualified names
#check Geo.Point
#eval (Geo.translate ⟨1.0, 2.0⟩ 10.0 20.0).x   -- 11.0
```

Because the first explicit argument of `translate` has type
`Geo.Point`, *dot notation* works: for `p : Geo.Point`, writing
`p.translate 10.0 20.0` resolves to `Geo.translate p 10.0 20.0`.
Namespaces are the reason dot notation is so pervasive in Mathlib.

# Opening namespaces
%%%
tag := "open-namespaces"
%%%

`open` brings the names of a namespace into scope so you can drop the
prefix:

```lean
open Geo

#check Point                              -- now unqualified
#eval (translate ⟨0.0, 0.0⟩ 1.0 1.0).y    -- 1.0
```

Three useful variants:

- `open Foo Bar` opens several namespaces at once.
- `open Foo in <command>` opens `Foo` for a *single* command only.
- `open scoped Foo` opens only the *scoped* notation and instances of
  `Foo` (see below), not its ordinary definitions.

# Sections and local variables
%%%
tag := "sections"
%%%

A `section` groups commands and, crucially, delimits the scope of
`variable` declarations.  A `variable` introduces a parameter that
several declarations share, without repeating it in each signature;
Lean adds it only to the declarations that actually use it.

```lean
section
variable (n : ℕ)

def addN (m : ℕ) : ℕ := m + n
def mulN (m : ℕ) : ℕ := m * n

end
-- outside the section `n` is gone; it became an argument
#check @addN    -- addN : ℕ → ℕ → ℕ
```

Sections may be named (`section Foo ... end Foo`) and nested; the name
is only a readability aid that must match the closing `end`.  A file
also has an implicit top-level section, so `variable`s written outside
any explicit `section` last until the end of the file.

# Scope of definitions: `private`, `local`, `scoped`
%%%
tag := "scoping"
%%%

By default a `def` is visible in every file that imports it (using its
qualified name, or unqualified after `open`).  Three modifiers narrow
that reach:

- `private def f ...` -- visible only within the current file.
- `local notation ...` / `local instance ...` -- visible only until the
  end of the current `section` or file.
- `scoped notation ...` / `scoped instance ...` -- visible only when the
  enclosing namespace is `open`ed (with `open` or `open scoped`).

The `scoped` modifier is how Mathlib ships heavy notation -- `∑`, `∏`,
the `ℝ≥0` shorthand -- without polluting global scope: you get the
notation exactly when you ask for it by opening the relevant namespace.

```
namespace BigOps
scoped notation "⟦" x "⟧" => (x, x)
end BigOps

-- `⟦·⟧` is unavailable here until we opt in:
open scoped BigOps
#check (⟦3⟧ : ℕ × ℕ)   -- (3, 3)
```

Together, these keywords let a Lean file stay organized and keep each
name visible exactly where it is wanted -- no more and no less.
