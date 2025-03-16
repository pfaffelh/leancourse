import tactic -- lade lean-Taktiken
import data.nat.digits
import data.finset.basic
import data.real.basic

variable n : ℕ
#check n

#check 2 + 2 = 4
#check 2 + 2 = 5


open_locale big_operators

open finset

example (n : ℕ) :
  ∑ i in range n, (i : ℝ) = n * (n - 1) / 2 :=
begin
  induction n with d hd,
  { -- base case: sum over empty type is 0 * (0 - 1) / 2
    simp },
  { -- inductive step
    rw [sum_range_succ, hd],
    simp, -- tidies up and reduces the goal to
    -- ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
    ring, -- a more appropriate tactic to finish the job
  },
end