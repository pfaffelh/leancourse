import Mathlib

/-!
# (witness) 1.4-c -- Inductive predicates and a quotient

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

/-! ## Part 1: Inductive predicates -/

inductive MyEven : ℕ → Prop where
  | zero : MyEven 0
  | add_two (n : ℕ) : MyEven n → MyEven (n + 2)

example : MyEven 4 := .add_two 2 (.add_two 0 .zero)

example : ¬ MyEven 1 := by
  intro h
  cases h

example : MyEven 10 :=
  .add_two 8 (.add_two 6 (.add_two 4 (.add_two 2 (.add_two 0 .zero))))

example : ¬ MyEven 3 := by
  intro h
  cases h with
  | add_two _ h' => cases h'

example (n : ℕ) (h : MyEven n) : MyEven (n + 4) :=
  .add_two (n + 2) (.add_two n h)

example (n : ℕ) (h : MyEven n) : ∃ k, n = 2 * k := by
  induction h with
  | zero => exact ⟨0, rfl⟩
  | add_two m _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by omega⟩

example (k : ℕ) : MyEven (2 * k) := by
  induction k with
  | zero => exact .zero
  | succ k ih =>
    show MyEven (2 * k + 2)
    exact .add_two _ ih

/-! ## Part 3: A quotient -/

def R (p q : ℕ × ℕ) : Prop := p.1 + q.2 = q.1 + p.2

def MyInt : Type := Quot R

def MyInt.mk (a b : ℕ) : MyInt := Quot.mk R (a, b)

example : MyInt.mk 3 1 = MyInt.mk 5 3 :=
  Quot.sound rfl

example (x : MyInt) : ∃ a b, x = MyInt.mk a b := by
  induction x using Quot.ind with
  | mk p => exact ⟨p.1, p.2, rfl⟩

def MyInt.neg : MyInt → MyInt :=
  Quot.lift (fun p => MyInt.mk p.2 p.1)
    (fun p q h => Quot.sound (by simp only [R] at h ⊢; omega))

example (a b : ℕ) : (MyInt.mk a b).neg = MyInt.mk b a := rfl

def MyInt.toInt : MyInt → ℤ :=
  Quot.lift (fun p => (p.1 : ℤ) - p.2)
    (fun p q h => by simp only [R] at h; omega)

example : (MyInt.mk 2 5).toInt = -3 := rfl

example (x : MyInt) : x.neg.neg = x := by
  induction x using Quot.ind with
  | mk p => rfl

example (x : MyInt) : x.neg.toInt = - x.toInt := by
  induction x using Quot.ind with
  | mk p =>
    show (p.2 : ℤ) - p.1 = -((p.1 : ℤ) - p.2)
    omega
