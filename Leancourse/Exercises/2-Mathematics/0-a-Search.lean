import Mathlib

/-!
# 2.0-a -- Finding theorems

*Opens the mathematics part, week 8. No chapter of its own; the
reference is the appendix* Navigating Mathlib.

Mathlib has about 189 000 theorems. From here on most steps of a
proof are among them, and the work is to find the right one.
`exact?`, `apply?`, `#loogle` and `#leansearch` are known from
`L-g`, where the goals were propositional. Here the goals are
mathematics, and most of the sheet is about what to do when the first
search does not succeed.

## Introduced here

| tool               | use it when                                         |
|--------------------|-----------------------------------------------------|
| `rw?`              | an equation or `↔` in Mathlib rewrites the goal     |
| `rw? at h`         | the same for the hypothesis `h`                     |
| `#check name`      | you guessed a name and want to see its statement    |
| `#loogle ?a + _`   | you know the form of the statement                  |
| `#loogle A, B`     | you know constants that occur in the statement      |

`have`, `obtain`, `rw … at h` and `absurd` are known from the logic
block, `simp` and `norm_num` from `1.1-c`.

Replace every search by its result before you go on. A search left
in the file runs again each time the file is checked, and that takes
seconds per search.
-/

/-! ## Part 1: `exact?` and its answer

`exact?` prints a term that closes the goal. Read it: the name tells
you the statement, the arguments tell you which hypotheses were
used. -/

example (a b : ℝ) : |a * b| = |a| * |b| := by
  -- exact?
  exact abs_mul a b

-- Exercise 1)
example (x : ℝ) : 0 ≤ x ^ 2 := by
  sorry

-- Exercise 2) Which hypotheses does the answer use, and in which
-- order?
example (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b := by
  sorry

-- Exercise 3) `exact?` answers `Nat.Prime.two_le hp`. Since `hp` has
-- type `Nat.Prime p`, this can also be written `hp.two_le`. Do that.
example (p : ℕ) (hp : p.Prime) : 2 ≤ p := by
  sorry

-- Exercise 4)
example (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g) :
    Monotone (f ∘ g) := by
  sorry

-- Exercise 5) The answer does not use `hn`. Delete `hn` from the
-- statement and check that the proof still works. What does that
-- say about the statement?
example (n : ℕ) (hn : 2 ≤ n) : n < 2 ^ n := by
  sorry

/-! ## Part 2: When `exact?` fails

`exact?` looks for *one* theorem, applied to the hypotheses. It
fails when the goal needs two steps, and when the statement is false
as it stands. -/

-- Exercise 6) `exact?` fails here. Prove `0 < x ^ 2` first, with
-- `have` and `exact?`; then `exact?` closes the goal.
example (x : ℝ) (hx : 0 < x) : 0 < x + x ^ 2 := by
  sorry

-- Exercise 7) `exact?` fails, because the statement is false: in
-- Mathlib, `Real.sqrt x = 0` for `x < 0`. Replace `True` by the
-- missing hypothesis, then `exact?` succeeds.
example (x : ℝ) (hx : True) : Real.sqrt x ^ 2 = x := by
  sorry

/-! ## Part 3: `rw?`

`rw?` lists the rewrites that apply to the goal, each with the goal
it leaves, and then performs the first. The first is often not the
one you want. Read the list, choose, and write the `rw` yourself. -/

example (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y := by
  -- rw?
  rw [Real.exp_add]

-- Exercise 8) Three rewrites. `rw?` suggests `Real.exp_mul` first;
-- it does not help. Find `two_mul` in the list, then call `rw?`
-- again.
example (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  sorry

-- Exercise 9) After the rewrite, a `↑2` is left: the natural number
-- `2`, cast to `ℝ`. `norm_num` removes it. Why does this hold without
-- `0 < x`? (`#check Real.log_neg_eq_log` and `#check Real.log_zero`.)
example (x : ℝ) : Real.log (x ^ 2) = 2 * Real.log x := by
  sorry

/-! `∑ i ∈ Finset.range m, f i` is `f 0 + f 1 + ... + f (m - 1)`. -/

-- Exercise 10) `exact?` fails: Mathlib states Gauss's formula in a
-- different form. Find it with `rw?`, then `simp [mul_comm]`.
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  sorry

-- Exercise 11) `rw? at h` rewrites `h`. Find the rewrite that turns
-- `h` into `a = 0 ∨ b = 0`, then finish with `obtain` and `absurd`.
-- Afterwards try `exact?` on the original goal.
example (a b : ℝ) (h : a * b = 0) (ha : a ≠ 0) : b = 0 := by
  sorry

/-! ## Part 4: Guessing names

Names in Mathlib describe the statement, read from left to right.
The conclusion comes first, the hypotheses after `_of_`:

* `mul_comm : a * b = b * a`
* `add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d`
* `le_of_lt : a < b → a ≤ b`
* `lt_of_lt_of_le : a < b → b ≤ c → a < c`
* `Set.mem_union`, `Set.inter_subset_left`: theorems about sets
  start with `Set.`, about natural numbers with `Nat.`.

`#check name` shows the statement of a guess. In the editor, typing
the start of a name lists the completions. The rule set is in the
appendix *Navigating Mathlib*, under *Naming conventions*. -/

#check add_le_add

-- Exercises 12 to 16) Guess the name, check it with `#check`, and
-- use it without a search.

-- Exercise 12)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  sorry

-- Exercise 13)
example (a b : ℝ) (h : a < b) : a ≤ b := by
  sorry

-- Exercise 14)
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  sorry

-- Exercise 15)
example (α : Type) (s t : Set α) : s ⊆ s ∪ t := by
  sorry

-- Exercise 16) The triangle inequality. The old name `abs_add` no
-- longer exists; the new one ends in `_le`. Chat models still
-- suggest the old one.
example (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  sorry

/-! ## Part 5: `apply?`

`apply?` lists theorems whose conclusion fits the goal, together
with the goals they leave. The list is long and ordered by no rule
you can use. On the goal of exercise 17, `mul_pos` comes about
twentieth. Often it is faster to guess the first step and search
for the rest. -/

-- Exercise 17) `apply mul_pos`, then one goal each. `exact?` does the
-- first; the second it does not. There, guess the step:
-- `0 ≤ x ^ 2` and `0 < 1` give `0 < x ^ 2 + 1`.
example (x : ℝ) : 0 < Real.exp x * (x ^ 2 + 1) := by
  sorry

/-! ## Part 6: Searching outside Lean

`#loogle` and `#leansearch` send the query to a server, so they need
an internet connection; both sites can also be used in the browser.
`#loogle` takes a pattern, with `?a` for a variable that must occur
the same way each time and `_` for anything:

    #loogle (?a + ?b) ^ 2 = _
    #loogle Real.sqrt, Real.exp

`#leansearch` takes a sentence in English:

    #leansearch "a continuous function takes every value in between"

Uncomment the searches below one at a time. -/

-- Exercise 18) Find the binomial formula with `#loogle`. There are
-- several hits; which two are for real numbers?
-- #loogle (?a + ?b) ^ 2 = _
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

-- Exercise 19) Find the theorem of exercise 7 with `#loogle`, and
-- compare its hypothesis with yours.
-- #loogle Real.sqrt ?x ^ 2 = ?x

-- Exercise 20) The intermediate value theorem. `exact?` fails. Find
-- `intermediate_value_Icc` with `#leansearch`, read its statement
-- with `#check`, and use it. It wants `ContinuousOn f (Set.Icc 0 1)`;
-- `hf.continuousOn` gives that. Its conclusion is about an image
-- `f '' s`, as in chapter 2.2.
-- #leansearch "a continuous function takes every value in between"
example (f : ℝ → ℝ) (hf : Continuous f) (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ x, f x = 0 := by
  sorry
