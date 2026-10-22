import Mathlib

/-!
# (witness) 1.4-a -- Typeclasses

*Notes chapter 1.4, week 5.*

A `class` is a `structure` that Lean finds for you. You never pass an
instance by hand: you write `[Add α]` in the signature, and *instance
resolution* fills it in from the instances that are registered.

Read the chapter on typeclasses first. The two classes at the end,
`Inhabited` and `Decidable`, are the ones you will keep meeting --
`Inhabited` because `∃` needs a witness, `Decidable` because `decide`
and `if` need an algorithm.

## Introduced here

| notation               | what it does                                  |
|------------------------|-----------------------------------------------|
| `class C α where`      | declare a typeclass                           |
| `instance : C τ where` | register an instance                          |
| `[C α]`                | an argument filled in by instance resolution  |
| `#synth C τ`           | show which instance Lean finds                |
| `deriving DecidableEq` | generate the equality test for your own type  |
| `decide`               | close a goal whose proposition is `Decidable` |
| `by_cases h : P`       | split on `P`, classically                     |
-/

variable {α β : Type}

/-! ## A class is a structure

Here is `Add`, stripped to its core. The `class` keyword declares a
structure with one field; `instance` registers a term of it. -/

class MyAdd (α : Type) where
  myAdd : α → α → α

instance : MyAdd ℕ where
  myAdd := Nat.add

-- Exercise 1) Register `||` as the `MyAdd` of `Bool`.
instance : MyAdd Bool where
  myAdd a b := a || b

-- Exercise 2) Both of these hold by reduction.
example : MyAdd.myAdd (2 : ℕ) 3 = 5 := rfl

example : MyAdd.myAdd true false = true := rfl

/-! ## `Inhabited`

`Inhabited α` says that `α` has a chosen element, `default`. It is
the class behind every `[Inhabited α]` you have seen on the earlier
sheets: without it, `∃ x, P x` has no witness to offer. -/

#print Inhabited

-- Exercise 3) What is the chosen natural number, and the chosen
-- Boolean? Guess first, then prove it.
example : (default : ℕ) = 0 := rfl

example : (default : Bool) = false := rfl

structure Point where
  x : ℤ
  y : ℤ
deriving Repr, DecidableEq

-- Exercise 4) Make the origin the default point.
instance : Inhabited Point := ⟨⟨0, 0⟩⟩

example : (default : Point) = ⟨0, 0⟩ := rfl

-- Exercise 5) Apply `f` twice to the default element. The instance
-- argument `[Inhabited α]` is what makes `default` available.
def twice (f : α → α) [Inhabited α] : α :=
  f (f default)

-- `twice (fun n => n + 3) = 6`, because the default `ℕ` is `0`.
#eval twice (fun n : ℕ => n + 3)

/-! ## Instances that need other instances

An instance may itself take instance arguments. That is how Lean
builds an instance for a compound type out of instances for its
parts. We practise on a copy of `Inhabited`, so that Mathlib's own
instances do not answer the questions for us. -/

class MyPointed (α : Type) where
  pt : α

instance : MyPointed ℕ := ⟨0⟩

-- Exercise 6) A pair is pointed if both components are.
instance [MyPointed α] [MyPointed β] : MyPointed (α × β) :=
  ⟨(MyPointed.pt, MyPointed.pt)⟩

-- Exercise 7) `Option α` is pointed for *every* `α`, with no
-- hypothesis at all. Which element do you take?
instance : MyPointed (Option α) := ⟨none⟩

-- Exercise 8) A function type `α → β` is pointed as soon as `β` is.
-- Why is nothing needed about `α`?
instance [MyPointed β] : MyPointed (α → β) :=
  ⟨fun _ => MyPointed.pt⟩

-- Exercise 9) Lean now assembles three instances into one. Run
-- `#synth` and read off which ones.
#synth MyPointed (ℕ × Option ℕ)

example : (MyPointed.pt : ℕ × ℕ) = (0, 0) := rfl

/-! ## `Decidable`

`Decidable P` is an *algorithm* that decides `P`, so it lives in
`Type`, not in `Prop`. The `decide` tactic runs it and checks that
the answer is `isTrue`. -/

#check @Decidable
#check (inferInstance : Decidable (2 + 3 = 5))

-- Exercise 10)
example : (2 : ℕ) ∣ 10 := by decide

-- Exercise 11) `decide` also proves negations.
example : ¬ ((3 : ℕ) ∣ 10) := by decide

/-! A `Decidable P` instance returns one of two constructors:
`isTrue h` with a proof `h : P`, or `isFalse h` with a proof
`h : ¬P`. You can write one by hand. -/

-- Exercise 12) Decide whether a natural number is zero. Each branch
-- has to supply the proof: `rfl` in one, `Nat.succ_ne_zero` in the
-- other.
def decZero (n : ℕ) : Decidable (n = 0) :=
  match n with
  | 0     => isTrue rfl
  | m + 1 => isFalse (Nat.succ_ne_zero m)

/-! ## `DecidableEq` and `if`

`if P then _ else _` needs a `Decidable P` instance -- that is how
the program knows which branch to take. For your own type, the
`deriving DecidableEq` above generated it. -/

-- Exercise 13) Halve a number, but map `0` to `0`.
def half (n : ℕ) : ℕ :=
  if n = 0 then 0 else n / 2

-- Exercise 14) Two different points. `decide` runs the derived
-- equality test.
example : (⟨1, 2⟩ : Point) ≠ ⟨2, 1⟩ := by decide

-- Exercise 15) Why does `decide` *not* work on the next goal,
-- although it is obviously true? Prove it with one word instead.
example (n : ℕ) : n = n := rfl

/-! ## When there is no algorithm

For a `P` that is not decidable, or whose instance Lean cannot find,
`decide` is of no use. `by_cases` splits anyway -- it uses the
excluded middle and therefore proves, rather than computes. -/

-- Exercise 16)
example (n : ℕ) : n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · exact Or.inl h
  · exact Or.inr h

-- Exercise 17) The same for an arbitrary proposition. Note that no
-- `Decidable P` is in sight.
example (P : Prop) : P ∨ ¬ P := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr h
