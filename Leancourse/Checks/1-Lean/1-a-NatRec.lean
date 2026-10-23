import Mathlib

/-!
# (witness) 1.1-a -- The recursor `Nat.rec`

*Notes chapter 1.1, week 2.*
-/

/- Solutions to 1.1-a. -/

def myDouble (n : ℕ) : ℕ := Nat.rec 0 (fun _ j => j + 2) n

-- Exercise 1)
example :
    Nat.rec (motive := fun _ => ℕ) 5 (fun _ j => j + 1) 3 = 8 := by
  rfl

-- Exercise 2) (comment only)
--   myDouble 3
-- ⟶ Nat.rec 0 (fun _ j => j + 2) 3                -- δ
-- ⟶ (fun _ j => j + 2) 2 (Nat.rec 0 _ 2)           -- ι
-- ⟶ Nat.rec 0 _ 2 + 2                              -- β
-- ⟶ (Nat.rec 0 _ 1 + 2) + 2                        -- ι, β
-- ⟶ ((Nat.rec 0 _ 0 + 2) + 2) + 2                  -- ι, β
-- ⟶ ((0 + 2) + 2) + 2  ⟶  6                        -- ι, +

-- Exercise 3)
def myPred (n : ℕ) : ℕ := Nat.rec 0 (fun k _ => k) n

example : myPred 0 = 0 := by
  rfl

example : myPred 5 = 4 := by
  rfl

def myAdd (m n : ℕ) : ℕ := Nat.rec m (fun _ k => k + 1) n

example : myAdd 2 3 = 5 := by
  rfl

-- Exercise 4)
def myMul (m n : ℕ) : ℕ := Nat.rec 0 (fun _ k => myAdd k m) n

example : myMul 3 4 = 12 := by
  rfl

-- Exercise 5)
def myFact (n : ℕ) : ℕ := Nat.rec 1 (fun k f => (k + 1) * f) n

example : myFact 4 = 24 := by
  rfl

-- Exercise 6)
def myEven (n : ℕ) : Bool := Nat.rec true (fun _ b => !b) n

example : myEven 4 = true := by
  rfl

example : myEven 7 = false := by
  rfl

-- Exercise 7)
example (m : ℕ) : myAdd m 0 = m := by
  rfl

example (m n : ℕ) : myAdd m (n + 1) = myAdd m n + 1 := by
  rfl

example (n : ℕ) : myDouble (n + 1) = myDouble n + 2 := by
  rfl

theorem myAdd_zero_left (n : ℕ) : myAdd 0 n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show myAdd 0 k + 1 = k + 1
      rw [ih]

-- Exercise 8)
theorem myAdd_succ_left (m n : ℕ) :
    myAdd (m + 1) n = myAdd m n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show myAdd (m + 1) k + 1 = myAdd m k + 1 + 1
      rw [ih]

-- Exercise 9)
theorem myAdd_comm (m n : ℕ) : myAdd m n = myAdd n m := by
  induction n with
  | zero => rw [myAdd_zero_left]; rfl
  | succ k ih =>
      show myAdd m k + 1 = myAdd (k + 1) m
      rw [myAdd_succ_left, ih]

-- Exercise 10)
example (n : ℕ) : myDouble n = myAdd n n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show myDouble k + 2 = myAdd (k + 1) k + 1
      rw [myAdd_succ_left, ih]

-- Exercise 11)
example (n : ℕ) : myEven (n + 2) = myEven n := by
  show (!!myEven n) = myEven n
  cases (myEven n) <;> rfl

-- Exercise 12)
example (m k : ℕ) : m + (k + 1) = (m + k) + 1 := by
  rfl

-- Exercise 13)
example (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show (0 + k) + 1 = k + 1
      rw [ih]
