import Mathlib

/-!
# 1.6-a -- Typeclasses

*Notes chapter 1.6, week 7.*

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
| `classical`            | make every proposition decidable in a proof   |
| `[Fact p]`             | a proposition as an instance argument         |
| `Fact.out`             | the proof inside a `Fact`                     |
| `have : C := ...`      | a local instance for the rest of the proof    |
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
  myAdd a b := sorry

-- Exercise 2) Both of these hold by reduction.
example : MyAdd.myAdd (2 : ℕ) 3 = 5 := by
  sorry

example : MyAdd.myAdd true false = true := by
  sorry

/-! ## `Inhabited`

`Inhabited α` says that `α` has a chosen element, `default`. It is
the class behind every `[Inhabited α]` you have seen on the earlier
sheets: without it, `∃ x, P x` has no witness to offer. -/

#print Inhabited

-- Exercise 3) What is the chosen natural number, and the chosen
-- Boolean? Guess first, then prove it.
example : (default : ℕ) = 0 := by
  sorry

example : (default : Bool) = false := by
  sorry

structure Point where
  x : ℤ
  y : ℤ
deriving Repr, DecidableEq

-- Exercise 4) Make the origin the default point.
instance : Inhabited Point := sorry

example : (default : Point) = ⟨0, 0⟩ := by
  sorry

-- Exercise 5) Apply `f` twice to the default element. The instance
-- argument `[Inhabited α]` is what makes `default` available.
def twice (f : α → α) [Inhabited α] : α :=
  sorry

-- Once it works, `twice (fun n => n + 3)` is `6`, because the
-- default `ℕ` is `0`.
-- #eval twice (fun n : ℕ => n + 3)

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
  sorry

-- Exercise 7) `Option α` is pointed for *every* `α`, with no
-- hypothesis at all. Which element do you take?
instance : MyPointed (Option α) := sorry

-- Exercise 8) A function type `α → β` is pointed as soon as `β` is.
-- Why is nothing needed about `α`?
instance [MyPointed β] : MyPointed (α → β) :=
  sorry

-- Exercise 9) Lean now assembles three instances into one. Run
-- `#synth` and read off which ones.
#synth MyPointed (ℕ × Option ℕ)

example : (MyPointed.pt : ℕ × ℕ) = (0, 0) := by
  sorry

/-! ## `Decidable`

`Decidable P` is an *algorithm* that decides `P`, so it lives in
`Type`, not in `Prop`. The `decide` tactic runs it and checks that
the answer is `isTrue`. -/

#check @Decidable
#check (inferInstance : Decidable (2 + 3 = 5))

-- Exercise 10)
example : (2 : ℕ) ∣ 10 := by
  sorry

-- Exercise 11) `decide` also proves negations.
example : ¬ ((3 : ℕ) ∣ 10) := by
  sorry

/-! A `Decidable P` instance returns one of two constructors:
`isTrue h` with a proof `h : P`, or `isFalse h` with a proof
`h : ¬P`. You can write one by hand. -/

-- Exercise 12) Decide whether a natural number is zero. Each branch
-- has to supply the proof: `rfl` in one, `Nat.succ_ne_zero` in the
-- other.
def decZero (n : ℕ) : Decidable (n = 0) :=
  sorry

/-! ## `DecidableEq` and `if`

`if P then _ else _` needs a `Decidable P` instance -- that is how
the program knows which branch to take. For your own type, the
`deriving DecidableEq` above generated it. -/

-- Exercise 13) Halve a number, but map `0` to `0`.
def half (n : ℕ) : ℕ :=
  sorry

-- Exercise 14) Two different points. `decide` runs the derived
-- equality test.
example : (⟨1, 2⟩ : Point) ≠ ⟨2, 1⟩ := by
  sorry

-- Exercise 15) Why does `decide` *not* work on the next goal,
-- although it is obviously true? Prove it with one word instead.
example (n : ℕ) : n = n := by
  sorry

/-! ## When there is no algorithm

For a `P` that is not decidable, or whose instance Lean cannot find,
`decide` is of no use. `by_cases` splits anyway -- it uses the
excluded middle and therefore proves, rather than computes. -/

-- Exercise 16)
example (n : ℕ) : n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · sorry
  · sorry

-- Exercise 17) The same for an arbitrary proposition. Note that no
-- `Decidable P` is in sight.
example (P : Prop) : P ∨ ¬ P := by
  sorry

/-! `Finset.filter P` keeps the elements of a finite set that satisfy
`P`, and it needs `DecidablePred P` to do so. For an arbitrary `P`
there is no such instance. The tactic `classical` provides one, by
the axiom of choice, for the rest of the proof. Instances that exist
are still found first. `Finset.filter_subset` and `Finset.mem_filter`
are the two lemmas you need. -/

-- Exercise 18) Start with `classical`, then give `s.filter P` as the
-- witness. Delete the line `classical` afterwards and read the error.
example (P : ℕ → Prop) (s : Finset ℕ) :
    ∃ t : Finset ℕ, t ⊆ s ∧ ∀ x ∈ t, P x := by
  sorry

/-! ## `Fact`

`Nat.Prime` is not a class, so instance search cannot see a hypothesis
`hp : p.Prime`. `Fact p` is a class with one field `out : p`. `ZMod p`
is a field exactly when `Fact p.Prime` is an instance. Read the section
*Propositions as instances: `Fact`* of chapter 1.6 first. -/

-- Exercise 19) Read the proof out of the instance with `Fact.out`,
-- then use `Nat.Prime.two_le`.
example (p : ℕ) [Fact p.Prime] : 2 ≤ p :=
  sorry

-- Exercise 20) Register the instance. `norm_num` proves that `7` is
-- prime.
instance : Fact (Nat.Prime 7) :=
  sorry

-- Exercise 21) With the instance of Exercise 20, `ZMod 7` is a field.
-- Find the lemma with `exact?`.
example (a : ZMod 7) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  sorry

-- Exercise 22) The same for any prime, given as a hypothesis. Turn the
-- hypothesis into a local instance with `have`. Then delete the `have`
-- and read the error: it does not mention `Fact`.
example (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  sorry

-- Exercise 23) The inverse of `3` in `ZMod 7`. Rewrite with
-- `inv_eq_of_mul_eq_one_right`; what is left, `decide` computes.
example : (3 : ZMod 7)⁻¹ = 5 := by
  sorry
