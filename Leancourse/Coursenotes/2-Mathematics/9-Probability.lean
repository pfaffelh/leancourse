import VersoManual
import Manual.Meta
import Leancourse.Markup
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MyDef

set_option pp.rawOnError true
set_option verso.docstring.allowMissing true

#doc (Manual) "Monads and Probability Mass Functions" =>
%%%
htmlSplit := .never
tag := "probability-pmf"
%%%

This section is published once the chapter has been taught.

# Monads: the general pattern
%%%
tag := "monads"
%%%

This section is published once the chapter has been taught.

## The problem: chaining computations that may fail
%%%
number := false
tag := "option-type"
%%%

This section is published once the chapter has been taught.

## The `Bind` operation
%%%
number := false
tag := "bind-operation"
%%%

This section is published once the chapter has been taught.

## The `do`-notation
%%%
number := false
tag := "do-notation"
%%%

This section is published once the chapter has been taught.

## The `Functor` typeclass
%%%
number := false
tag := "functor-typeclass"
%%%

This section is published once the chapter has been taught.

## The `Monad` typeclass
%%%
number := false
tag := "monad-typeclass"
%%%

This section is published once the chapter has been taught.

## Lists as a monad
%%%
number := false
tag := "list-monad"
%%%

This section is published once the chapter has been taught.

## The `IO` monad
%%%
number := false
tag := "io-monad"
%%%

This section is published once the chapter has been taught.

## Stateful computation with `StateM`
%%%
number := false
tag := "state-monad"
%%%

This section is published once the chapter has been taught.

## Error handling with `Except`
%%%
number := false
tag := "except-monad"
%%%

This section is published once the chapter has been taught.

## Sets as a monad
%%%
number := false
tag := "set-monad"
%%%

This section is published once the chapter has been taught.

## Filters as a monad
%%%
number := false
tag := "filter-monad"
%%%

This section is published once the chapter has been taught.

## Finite sets and `Finset`
%%%
number := false
tag := "finset-monad"
%%%

This section is published once the chapter has been taught.

## Connection to category theory
%%%
number := false
tag := "monads-category-theory"
%%%

This section is published once the chapter has been taught.

## Summary of monads seen so far
%%%
number := false
tag := "monads-summary"
%%%

This section is published once the chapter has been taught.

# Probability mass functions
%%%
tag := "pmf-intro"
%%%

This section is published once the chapter has been taught.

## Notation and naming conventions
%%%
number := false
tag := "pmf-notation"
%%%

This section is published once the chapter has been taught.

## The definition
%%%
number := false
tag := "pmf-definition"
%%%

This section is published once the chapter has been taught.

## `pure`: the Dirac distribution
%%%
number := false
tag := "pmf-pure"
%%%

This section is published once the chapter has been taught.

## `bind`: composing distributions
%%%
number := false
tag := "pmf-bind"
%%%

This section is published once the chapter has been taught.

## `map`: pushing a distribution along a function
%%%
number := false
tag := "pmf-map"
%%%

This section is published once the chapter has been taught.

## `join`: flattening distributions of distributions
%%%
number := false
tag := "pmf-join"
%%%

This section is published once the chapter has been taught.

## The `Monad PMF` instance
%%%
number := false
tag := "monad-pmf-instance"
%%%

This section is published once the chapter has been taught.

## Concrete distributions
%%%
number := false
tag := "pmf-concrete"
%%%

This section is published once the chapter has been taught.

## Beyond PMFs: measures, expectation, independence
%%%
number := false
tag := "pmf-beyond"
%%%

This section is published once the chapter has been taught.

## When do we still need measurability?
%%%
number := false
tag := "pmf-measurability"
%%%

This section is published once the chapter has been taught.
