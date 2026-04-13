import Mathlib

/-
# Exercises: Probability Mass Functions

These exercises cover the monad structure of `PMF` (probability mass
functions in Mathlib): `pure`, `bind`, `map`, and `join`.  Almost no
measurability is needed -- everything works at the level of the
discrete distribution itself.

Replace each `sorry` with a proof.
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

/- ## Part 3: Bind and the monad laws -/

-- Exercise 9: Left identity: pure a >>= f = f a.
example {α β : Type*} (a : α) (f : α → PMF β) :
    (PMF.pure a).bind f = f a := by
  sorry

-- Exercise 10: Right identity: p.bind pure = p.
example {α : Type*} (p : PMF α) : p.bind PMF.pure = p := by
  sorry

-- Exercise 11: Associativity:
-- (p.bind f).bind g = p.bind (fun a => (f a).bind g).
example {α β γ : Type*} (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (p.bind f).bind g = p.bind (fun a => (f a).bind g) := by
  sorry

-- Exercise 12: Bind with a constant family is the constant distribution.
example {α β : Type*} (p : PMF α) (q : PMF β) :
    (p.bind fun _ => q) = q := by
  sorry

-- Exercise 13: The probability of b under p.bind f.
example {α β : Type*} (p : PMF α) (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑' a, p a * (f a) b := by
  sorry

/- ## Part 4: Map and the functor laws -/

-- Exercise 14: map id is the identity on PMFs.
example {α : Type*} (p : PMF α) : p.map id = p := by
  sorry

-- Exercise 15: map respects composition.
example {α β γ : Type*} (p : PMF α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  sorry

-- Exercise 16: map of pure is pure of the value.
example {α β : Type*} (a : α) (f : α → β) :
    (PMF.pure a : PMF α).map f = PMF.pure (f a) := by
  sorry

-- Exercise 17: The support of p.map f is the image of p.support.
example {α β : Type*} (p : PMF α) (f : α → β) :
    (p.map f).support = f '' p.support := by
  sorry

-- Exercise 18: bind followed by map = bind ∘ (map ∘ f).
example {α β γ : Type*} (p : PMF α) (q : α → PMF β) (f : β → γ) :
    (p.bind q).map f = p.bind (fun a => (q a).map f) := by
  sorry

-- Exercise 19: map then bind = bind through composition.
example {α β γ : Type*} (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (p.map f).bind q = p.bind (q ∘ f) := by
  sorry

-- Exercise 20: map a constant function gives a Dirac.
example {α β : Type*} (p : PMF α) (b : β) :
    p.map (Function.const α b) = PMF.pure b := by
  sorry

/- ## Part 5: Join (defined as bind id) -/

noncomputable def myJoin {α : Type*} (P : PMF (PMF α)) : PMF α :=
  P.bind id

-- Exercise 21: join of pure p is p (left identity for join).
example {α : Type*} (p : PMF α) : myJoin (PMF.pure p) = p := by
  sorry

-- Exercise 22: join of (map pure p) is p (right identity for join).
example {α : Type*} (p : PMF α) :
    myJoin (p.map (PMF.pure : α → PMF α)) = p := by
  sorry

-- Exercise 23: Naturality of join: pushing a function commutes with join.
example {α β : Type*} (P : PMF (PMF α)) (f : α → β) :
    (myJoin P).map f = myJoin (P.map (fun p => p.map f)) := by
  sorry

-- Exercise 24: Associativity of join.
example {α : Type*} (P : PMF (PMF (PMF α))) :
    myJoin (myJoin P) = myJoin (P.map myJoin) := by
  sorry

-- Exercise 25: bind is map then join.
example {α β : Type*} (p : PMF α) (f : α → PMF β) :
    p.bind f = myJoin (p.map f) := by
  sorry

/- ## Part 6: A small concrete example -/

-- The PMF that is uniform on {0, 1} ⊆ ℕ
-- (using PMF.bernoulli specialized to ℕ via map).
noncomputable def coin : PMF Bool := PMF.bernoulli (1 / 2) (by norm_num)

-- Exercise 26: The probability of true under a fair coin is 1/2.
example : coin true = 1 / 2 := by
  sorry

-- Exercise 27: Mapping `Bool.toNat` over a fair coin gives a PMF on ℕ
-- whose support is {0, 1}.
example : (coin.map (fun b => if b then 1 else 0 : Bool → ℕ)).support
    = {0, 1} := by
  sorry

-- Exercise 28: Tossing two independent fair coins (using do-notation)
-- and returning the conjunction.
noncomputable def bothHeads : PMF Bool :=
  coin.bind fun x => coin.bind fun y => PMF.pure (x && y)

-- The probability of getting (true, true) is 1/4.
example : bothHeads true = 1 / 4 := by
  sorry
