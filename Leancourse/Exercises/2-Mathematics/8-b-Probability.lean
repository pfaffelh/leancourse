import Mathlib

/-
# 2.8-b -- Probability and the PMF monad

*Notes chapter 2.8, week 15.*

These exercises cover the monad structure of `PMF` (probability mass
functions in Mathlib): `pure`, `bind`, `map`, and `join`.  Almost no
measurability is needed -- everything works at the level of the
discrete distribution itself.  The functor laws are practised on
`2.8-a`.  For `PMF`, the monad and functor laws are the Mathlib
lemmas `PMF.pure_bind`, `PMF.bind_pure`, `PMF.bind_bind`,
`PMF.map_id`, `PMF.map_comp` and `PMF.pure_map`; use them freely.

Replace each `sorry` with a proof.

## Tactics from earlier sheets

| sheet   | tactics            |
|---------|--------------------|
| `L-a`   | `exact`            |
| `1.1-a` | `rw`               |
| `1.1-b` | `cases`, `<;>`     |
| `1.1-c` | `norm_num`, `simp` |
| `1.5-a` | `ext`              |
-/

open PMF

/- ## Part 1: Basic properties of a PMF -/

-- Exercise 1: The total mass of a PMF is 1.
example {α : Type*} (p : PMF α) : ∑' a, p a = 1 := by
  sorry

-- Exercise 2: Every value of a PMF is at most 1.
example {α : Type*} (p : PMF α) (a : α) : p a ≤ 1 := by
  sorry

-- Exercise 3: a is in the support of p iff p a ≠ 0.
example {α : Type*} (p : PMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := by
  sorry

-- Exercise 4: The support of any PMF is nonempty.
example {α : Type*} (p : PMF α) : p.support.Nonempty := by
  sorry

/- ## Part 2: The Dirac PMF (pure) -/

-- Exercise 5: pure a evaluated at a is 1.
example {α : Type*} (a : α) : (PMF.pure a : PMF α) a = 1 := by
  sorry

-- Exercise 6: pure a evaluated at a different point is 0.
example {α : Type*} (a a' : α) (h : a' ≠ a) : (PMF.pure a : PMF α) a' = 0 := by
  sorry

-- Exercise 7: The support of pure a is the singleton {a}.
example {α : Type*} (a : α) : (PMF.pure a : PMF α).support = {a} := by
  sorry

-- Exercise 8: a' is in the support of pure a iff a' = a.
example {α : Type*} (a a' : α) :
    a' ∈ (PMF.pure a : PMF α).support ↔ a' = a := by
  sorry

/- ## Part 3: Bind -/

-- Exercise 9: Bind with a constant family is the constant distribution.
example {α β : Type*} (p : PMF α) (q : PMF β) :
    (p.bind fun _ => q) = q := by
  sorry

-- Exercise 10: The probability of b under p.bind f.
example {α β : Type*} (p : PMF α) (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑' a, p a * (f a) b := by
  sorry

/- ## Part 4: Map -/

-- Exercise 11: The support of p.map f is the image of p.support.
example {α β : Type*} (p : PMF α) (f : α → β) :
    (p.map f).support = f '' p.support := by
  sorry

-- Exercise 12: bind followed by map = bind ∘ (map ∘ f).
example {α β γ : Type*} (p : PMF α) (q : α → PMF β) (f : β → γ) :
    (p.bind q).map f = p.bind (fun a => (q a).map f) := by
  sorry

-- Exercise 13: map then bind = bind through composition.
example {α β γ : Type*} (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (p.map f).bind q = p.bind (q ∘ f) := by
  sorry

-- Exercise 14: map a constant function gives a Dirac.
example {α β : Type*} (p : PMF α) (b : β) :
    p.map (Function.const α b) = PMF.pure b := by
  sorry

/- ## Part 5: Join (defined as bind id) -/

noncomputable def myJoin {α : Type*} (P : PMF (PMF α)) : PMF α :=
  P.bind id

-- Exercise 15: join of pure p is p (left identity for join).
example {α : Type*} (p : PMF α) : myJoin (PMF.pure p) = p := by
  sorry

-- Exercise 16: join of (map pure p) is p (right identity for join).
example {α : Type*} (p : PMF α) :
    myJoin (p.map (PMF.pure : α → PMF α)) = p := by
  sorry

-- Exercise 17: Naturality of join: pushing a function commutes with join.
example {α β : Type*} (P : PMF (PMF α)) (f : α → β) :
    (myJoin P).map f = myJoin (P.map (fun p => p.map f)) := by
  sorry

-- Exercise 18: Associativity of join.
example {α : Type*} (P : PMF (PMF (PMF α))) :
    myJoin (myJoin P) = myJoin (P.map myJoin) := by
  sorry

-- Exercise 19: bind is map then join.
example {α β : Type*} (p : PMF α) (f : α → PMF β) :
    p.bind f = myJoin (p.map f) := by
  sorry

/- ## Part 6: A small concrete example -/

-- A fair coin. `PMF.uniformOfFintype α` is the uniform distribution on
-- a nonempty finite type. (`PMF.bernoulli` would do the same job but is
-- deprecated.)
noncomputable def coin : PMF Bool := PMF.uniformOfFintype Bool

-- Exercise 20: The probability of true under a fair coin is 1/2.
example : coin true = 1 / 2 := by
  sorry

-- Exercise 21: Mapping `fun b => if b then 1 else 0` over a fair coin
-- gives a PMF on ℕ whose support is {0, 1}.
example : (coin.map (fun b => if b then 1 else 0 : Bool → ℕ)).support
    = {0, 1} := by
  sorry

-- Exercise 22: Tossing two independent fair coins with `bind` (the
-- `do` version is the same term) and returning the conjunction.
noncomputable def bothHeads : PMF Bool :=
  coin.bind fun x => coin.bind fun y => PMF.pure (x && y)

-- The probability of getting (true, true) is 1/4.
example : bothHeads true = 1 / 4 := by
  sorry

-- Exercise 23 (*Extra*): Turning the coin over does not change it.
-- Hint: `ext b`, `simp [coin, PMF.map_apply]`, then cases on `b`.
example : coin.map not = coin := by
  sorry
