import Mathlib

/-!
# (witness) 1.7-a -- Functors and monads

*Notes chapter 1.7, week 9.*
-/

/-! ## Part 1: `map` -/

-- Exercise 1)
example : (· * 3) <$> [1, 2, 3] = [3, 6, 9] := rfl

-- Exercise 2)
example : (· + 1) <$> (none : Option ℕ) = none := rfl

-- Exercise 3)
example (xs : List ℕ) : id <$> xs = xs := id_map xs

-- Exercise 4)
example (f g : ℕ → ℕ) (x : Option ℕ) :
    (g ∘ f) <$> x = g <$> f <$> x :=
  comp_map f g x

/-! ## Part 2: `Option` as a monad -/

-- Exercise 5)
def safeHead {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: _ => some x

-- Exercise 6)
def safeGet {α : Type} (xs : List α) (n : ℕ) : Option α :=
  match xs, n with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => safeGet xs n

-- Exercise 7)
def safeDiv (a b : ℕ) : Option ℕ :=
  if b = 0 then none else some (a / b)

-- Exercise 8)
def divByElement (xs : List ℕ) (i : ℕ) : Option ℕ := do
  let x ← safeGet xs i
  safeDiv 100 x

-- Exercise 9)
def addAtIndex (xs ys : List ℕ) (i : ℕ) : Option ℕ := do
  let x ← safeGet xs i
  let y ← safeGet ys i
  return x + y

-- Exercise 10)
def nestedDivide (xss : List (List ℕ)) (i j : ℕ) :
    Option ℕ := do
  let xs ← safeGet xss i
  let x ← safeGet xs j
  safeDiv 1000 x

example : divByElement [5, 0] 0 = some 20 := rfl
example : divByElement [5, 0] 1 = none := rfl
example : addAtIndex [1, 2] [10, 20] 1 = some 22 := rfl
example : nestedDivide [[1], [3, 4]] 1 1 = some 250 := rfl

/-! ## Part 3: The laws for `Option` -/

-- Exercise 11)
example (a : ℕ) (f : ℕ → Option ℕ) :
    (pure a >>= f) = f a := rfl

-- Exercise 12)
example (x : Option ℕ) : (x >>= pure) = x := by
  cases x
  · rfl
  · rfl

-- Exercise 13)
example (x : Option ℕ) (f g : ℕ → Option ℕ) :
    (x >>= f >>= g) = (x >>= fun a => f a >>= g) := by
  cases x
  · rfl
  · rfl

-- Exercise 14)
example (f : ℕ → ℕ) (x : Option ℕ) :
    f <$> x = (x >>= fun a => pure (f a)) := by
  cases x
  · rfl
  · rfl

/-! ## Part 4: Lists as a monad -/

-- Exercise 15)
example : ([1, 2] >>= fun x => [x, x + 1]) = [1, 2, 2, 3] := rfl

-- Exercise 16)
def sumToFour : List (ℕ × ℕ) := do
  let x ← [1, 2, 3]
  let y ← [1, 2, 3]
  guard (x + y = 4)
  return (x, y)

example : sumToFour = [(1, 3), (2, 2), (3, 1)] := rfl

-- Exercise 17)
def pythagoreanTriples : List (ℕ × ℕ × ℕ) := do
  let a ← List.range' 1 20
  let b ← List.range' a (21 - a)
  let c ← List.range' b (21 - b)
  guard (a * a + b * b = c * c)
  return (a, b, c)

example : (3, 4, 5) ∈ pythagoreanTriples := by decide

/-! ## Part 5: A functor of your own -/

inductive LTree (α : Type) where
  | leaf : LTree α
  | node : LTree α → α → LTree α → LTree α

-- Exercise 18)
def LTree.map {α β : Type} (f : α → β) : LTree α → LTree β
  | .leaf => .leaf
  | .node l a r => .node (l.map f) (f a) (r.map f)

-- Exercise 19)
instance : Functor LTree where
  map := LTree.map

-- Exercise 20)
example {α : Type} (t : LTree α) : id <$> t = t := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    show LTree.node (id <$> l) (id a) (id <$> r) = _
    rw [ihl, ihr]
    rfl

-- Exercise 21) *Extra.*
example {α β γ : Type} (f : α → β) (g : β → γ) (t : LTree α) :
    (g ∘ f) <$> t = g <$> f <$> t := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr =>
    show LTree.node ((g ∘ f) <$> l) ((g ∘ f) a) ((g ∘ f) <$> r)
      = LTree.node (g <$> f <$> l) (g (f a)) (g <$> f <$> r)
    rw [ihl, ihr]
    rfl
