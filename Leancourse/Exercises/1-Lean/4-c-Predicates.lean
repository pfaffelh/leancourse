import Mathlib

/-!
# 1.4-c -- Inductive predicates and a quotient

*Notes chapter 1.4, week 6.*

Two type formers in practice: a predicate defined by rules, and the
integers as a quotient of `ℕ × ℕ`. Read *Indexed families and
inductive predicates* and *Quotient types* in chapter 1.4 first.
Structures are on sheet `1.2-b`.

## Introduced here

| notation / tactic          | use it when                                   |
|----------------------------|-----------------------------------------------|
| `inductive P : ℕ → Prop`   | define a predicate by rules                   |
| `cases h`, `induction h`   | use `h : P n`: one case per rule that fits    |
| `Quot.mk r a`              | the class of `a`                              |
| `Quot.sound h`             | related elements have the same class          |
| `Quot.lift f h`            | a function on classes; `h`: `f` respects `r`  |
| `induction x using Quot.ind` | prove a statement for every class           |
-/

/-! ## Part 1: Inductive predicates

`MyEven n` can be proved in exactly two ways: by `zero` for `n = 0`,
or by `add_two` from a proof for `n - 2`. -/

inductive MyEven : ℕ → Prop where
  | zero : MyEven 0
  | add_two (n : ℕ) : MyEven n → MyEven (n + 2)

example : MyEven 4 := .add_two 2 (.add_two 0 .zero)

/-! `cases h` on `h : MyEven 1` leaves one goal per rule whose index
can be `1`. There is none, so the goal is closed. -/

example : ¬ MyEven 1 := by
  intro h
  cases h

-- Exercise 1)
example : MyEven 10 := by
  sorry

-- Exercise 2) Here one rule fits, `add_two` with `n = 1`. Use
-- `cases h with | add_two _ h' => ...` and continue with `h'`.
example : ¬ MyEven 3 := by
  sorry

-- Exercise 3) A term suffices.
example (n : ℕ) (h : MyEven n) : MyEven (n + 4) := by
  sorry

/-! `induction h` works like `induction n`, with one case per rule
and an induction hypothesis for `add_two`:

    induction h with
    | zero => ...
    | add_two m hm ih => ...      -- ih : the statement for m -/

-- Exercise 4)
example (n : ℕ) (h : MyEven n) : ∃ k, n = 2 * k := by
  sorry

-- Exercise 5) The converse, by induction on `k`. In the step,
-- `show MyEven (2 * k + 2)` brings the goal into a form that
-- `add_two` fits.
example (k : ℕ) : MyEven (2 * k) := by
  sorry

/-! ## Part 2: The integers as a quotient

A pair `(a, b)` stands for `a - b`. Two pairs stand for the same
integer if `a + d = c + b`. -/

def R (p q : ℕ × ℕ) : Prop := p.1 + q.2 = q.1 + p.2

def MyInt : Type := Quot R

def MyInt.mk (a b : ℕ) : MyInt := Quot.mk R (a, b)

/-! Related pairs give the same class, by the axiom `Quot.sound`.
Here `R (3, 1) (5, 3)` is `3 + 3 = 5 + 1`, which `rfl` proves. -/

example : MyInt.mk 3 1 = MyInt.mk 5 3 :=
  Quot.sound rfl

/-! A function on `MyInt` is a function on pairs together with a
proof that related pairs have the same value. Negation swaps the
pair: -/

def MyInt.neg : MyInt → MyInt :=
  Quot.lift (fun p => MyInt.mk p.2 p.1)
    (fun p q h => Quot.sound (by simp only [R] at h ⊢; omega))

example (a b : ℕ) : (MyInt.mk a b).neg = MyInt.mk b a := rfl

/-! Every element of `MyInt` is the class of some pair. To use that,
`induction x using Quot.ind` replaces `x` by `Quot.mk R p`: -/

example (x : MyInt) : ∃ a b, x = MyInt.mk a b := by
  induction x using Quot.ind with
  | mk p => exact ⟨p.1, p.2, rfl⟩

-- Exercise 6) Prove that `toInt` is well defined. `omega` handles
-- the casts `(p.1 : ℤ)` once `h` is unfolded.
def MyInt.toInt : MyInt → ℤ :=
  Quot.lift (fun p => (p.1 : ℤ) - p.2)
    (fun p q h => sorry)

-- Exercise 7) `Quot.lift` computes on a class.
example : (MyInt.mk 2 5).toInt = -3 := by
  sorry

-- Exercise 8) After `induction x using Quot.ind`, both sides
-- compute.
example (x : MyInt) : x.neg.neg = x := by
  sorry

-- Exercise 9) Start like exercise 8. Then `show` the goal as an
-- equation in `ℤ` and use `omega`.
example (x : MyInt) : x.neg.toInt = - x.toInt := by
  sorry
