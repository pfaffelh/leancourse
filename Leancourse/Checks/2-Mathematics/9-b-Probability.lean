import Mathlib

/-
# (witness) 2.9-b -- Probability and the PMF monad

*Notes chapter 2.9, week 15.*

These exercises cover the monad structure of `PMF` (probability mass
functions in Mathlib): `pure`, `bind`, `map`, and `join`.  Almost no
measurability is needed -- everything works at the level of the
discrete distribution itself.

One worked proof for each exercise.
-/

open PMF

/- ## Part 1: Basic properties of a PMF -/

-- Exercise 1: The total mass of a PMF is 1.
example {α : Type*} (p : PMF α) : ∑' a, p a = 1 := by
  exact p.tsum_coe

-- Exercise 2: Every value of a PMF is at most 1.
example {α : Type*} (p : PMF α) (a : α) : p a ≤ 1 := by
  exact p.coe_le_one a

-- Exercise 3: a is in the support of p iff p a ≠ 0.
example {α : Type*} (p : PMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := by
  exact PMF.mem_support_iff p a

-- Exercise 4: The support of any PMF is nonempty.
example {α : Type*} (p : PMF α) : p.support.Nonempty := by
  exact p.support_nonempty

/- ## Part 2: The Dirac PMF (pure) -/

-- Exercise 5: pure a evaluated at a is 1.
example {α : Type*} (a : α) : (PMF.pure a : PMF α) a = 1 := by
  simp

-- Exercise 6: pure a evaluated at a different point is 0.
example {α : Type*} (a a' : α) (h : a' ≠ a) : (PMF.pure a : PMF α) a' = 0 := by
  simp [h]

-- Exercise 7: The support of pure a is the singleton {a}.
example {α : Type*} (a : α) : (PMF.pure a : PMF α).support = {a} := by
  simp

-- Exercise 8: a' is in the support of pure a iff a' = a.
example {α : Type*} (a a' : α) :
    a' ∈ (PMF.pure a : PMF α).support ↔ a' = a := by
  simp

/- ## Part 3: Bind and the monad laws -/

-- Exercise 9: Left identity: pure a >>= f = f a.
example {α β : Type*} (a : α) (f : α → PMF β) :
    (PMF.pure a).bind f = f a := by
  exact PMF.pure_bind a f

-- Exercise 10: Right identity: p.bind pure = p.
example {α : Type*} (p : PMF α) : p.bind PMF.pure = p := by
  exact PMF.bind_pure p

-- Exercise 11: Associativity:
-- (p.bind f).bind g = p.bind (fun a => (f a).bind g).
example {α β γ : Type*} (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (p.bind f).bind g = p.bind (fun a => (f a).bind g) := by
  exact PMF.bind_bind p f g

-- Exercise 12: Bind with a constant family is the constant distribution.
example {α β : Type*} (p : PMF α) (q : PMF β) :
    (p.bind fun _ => q) = q := by
  exact PMF.bind_const p q

-- Exercise 13: The probability of b under p.bind f.
example {α β : Type*} (p : PMF α) (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑' a, p a * (f a) b := by
  exact PMF.bind_apply p f b

/- ## Part 4: Map and the functor laws -/

-- Exercise 14: map id is the identity on PMFs.
example {α : Type*} (p : PMF α) : p.map id = p := by
  simp [PMF.map_id]

-- Exercise 15: map respects composition.
example {α β γ : Type*} (p : PMF α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  simp [PMF.map_comp]

-- Exercise 16: map of pure is pure of the value.
example {α β : Type*} (a : α) (f : α → β) :
    (PMF.pure a : PMF α).map f = PMF.pure (f a) := by
  simp [PMF.pure_map]

-- Exercise 17: The support of p.map f is the image of p.support.
example {α β : Type*} (p : PMF α) (f : α → β) :
    (p.map f).support = f '' p.support := by
  simp [PMF.support_map]

-- Exercise 18: bind followed by map = bind ∘ (map ∘ f).
example {α β γ : Type*} (p : PMF α) (q : α → PMF β) (f : β → γ) :
    (p.bind q).map f = p.bind (fun a => (q a).map f) := by
  simp [PMF.map, PMF.bind_bind]

-- Exercise 19: map then bind = bind through composition.
example {α β γ : Type*} (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (p.map f).bind q = p.bind (q ∘ f) := by
  simp [PMF.map, PMF.bind_bind, Function.comp_def]

-- Exercise 20: map a constant function gives a Dirac.
example {α β : Type*} (p : PMF α) (b : β) :
    p.map (Function.const α b) = PMF.pure b := by
  simp [PMF.map_const]

/- ## Part 5: Join (defined as bind id) -/

noncomputable def myJoin {α : Type*} (P : PMF (PMF α)) : PMF α :=
  P.bind id

-- Exercise 21: join of pure p is p (left identity for join).
example {α : Type*} (p : PMF α) : myJoin (PMF.pure p) = p := by
  simp [myJoin]

-- Exercise 22: join of (map pure p) is p (right identity for join).
example {α : Type*} (p : PMF α) :
    myJoin (p.map (PMF.pure : α → PMF α)) = p := by
  simp [myJoin, PMF.map, PMF.bind_bind]

-- Exercise 23: Naturality of join: pushing a function commutes with join.
example {α β : Type*} (P : PMF (PMF α)) (f : α → β) :
    (myJoin P).map f = myJoin (P.map (fun p => p.map f)) := by
  simp [myJoin, PMF.map, PMF.bind_bind]

-- Exercise 24: Associativity of join.
example {α : Type*} (P : PMF (PMF (PMF α))) :
    myJoin (myJoin P) = myJoin (P.map myJoin) := by
  simp [myJoin, PMF.map, PMF.bind_bind]

-- Exercise 25: bind is map then join.
example {α β : Type*} (p : PMF α) (f : α → PMF β) :
    p.bind f = myJoin (p.map f) := by
  simp [myJoin, PMF.map, PMF.bind_bind]

/- ## Part 6: A small concrete example -/

-- A fair coin. `PMF.uniformOfFintype α` is the uniform distribution on
-- a nonempty finite type. (`PMF.bernoulli` would do the same job but is
-- deprecated.)
noncomputable def coin : PMF Bool := PMF.uniformOfFintype Bool

-- Exercise 26: The probability of true under a fair coin is 1/2.
example : coin true = 1 / 2 := by
  simp [coin, PMF.uniformOfFintype_apply]

-- Exercise 27: Mapping `Bool.toNat` over a fair coin gives a PMF on ℕ
-- whose support is {0, 1}.
example : (coin.map (fun b => if b then 1 else 0 : Bool → ℕ)).support
    = {0, 1} := by
  ext n
  simp [coin, PMF.support_map, PMF.support_uniformOfFintype]

-- Exercise 28: Tossing two independent fair coins (using do-notation)
-- and returning the conjunction.
noncomputable def bothHeads : PMF Bool :=
  coin.bind fun x => coin.bind fun y => PMF.pure (x && y)

-- The probability of getting (true, true) is 1/4.
example : bothHeads true = 1 / 4 := by
  simp [bothHeads, coin, PMF.bind_apply, PMF.uniformOfFintype_apply]
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num
