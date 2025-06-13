import VersoManual
import Manual.Meta
import Leancourse.Misc.Defs
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Projects" =>
%%%
htmlSplit := .never
tag := "projects"
%%%

**Summary:** In the second phase of this course, students can assign themselves projects. For this, they were asked to look for simple exercises, e.g. from their first year courses. Here comes a list of exercises they used.

# Induction (Luis Jaschke und Felicitas Kissel)

Prove the following equalities using induction:

```lean
example (n : ℕ) :
    ∑ k ≤ n, k * k = n * (n + 1) * (2*n + 1) / 6 := by
  sorry
```

```lean
example (n : ℕ) :
    ∑ k ≤ n, k * k * k = n * n * (n + 1) * (n + 1) / 4 := by
  sorry
```

Compute the following sums and products, and show your result by induction.

```lean
example (n : ℕ) : ∑ k ≤ n, 2 * k - 1 = sorry := by
  sorry
```

```lean
example (n : ℕ) : ∏ k ≤ n, (1 + 1 / (k + 1)) = sorry := by
  sorry
```

```lean
example (n : ℕ) : ∏ k ≤ n, (1 - 1 / (k + 1)) = sorry := by
  sorry
```

# Own addition on ℚ (Adrian Eckstein und Debora Ortlieb)

```lean

def own_add (a b : ℚ) : ℚ := a * b + 2 * a + 2 * b + 2

notation a " ⊕ " b:60 => own_add a b

lemma own_mul_komm (a b : ℚ) : (a ⊕ b) = b ⊕ a := by
  sorry

lemma own_mul_assoc (a b c : ℚ) :
    ((a ⊕ b) ⊕ c) = a ⊕ (b ⊕ c) := by

  sorry

lemma own_mul_right_neutral (a : ℚ) : (a ⊕ (-1)) = a := by
  sorry

lemma own_mul_left_neutral (a : ℚ) : ((-1) ⊕ a) = a := by
  sorry

```

```lean
example (n : ℕ) : ∏ k ≤ n, (1 - 1 / (k + 1)) = sorry := by
  sorry
```

# Fixed points and contractions (Jule Kiesele, Anna Vitiello)

Jede Kontraktion hat genau einen Fixpunkt

# Path-connected spaces (Jasper Ganten)

The union of path-connected spaces is path-connected, if their intersection is not empty.

# Parallel inequality (Moritz Graßnitzer, Natalie Jahnes)

Parallel inequality, or a homomorphism is injective iff its kernel is trivial.

# There is only one prime triplet (Patrick Nasdala, Max Lehr)

There is only one prime triplet, i.e. only one `n : ℕ` prime, such that `n + 2` and `n + 4` are prime as well.

```lean

example (n : ℕ) :
    Nat.Prime n ∧ Nat.Prime (n + 2) ∧
    Nat.Prime (n + 4) → n = 3 := by
  sorry
```
