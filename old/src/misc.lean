
import data.real.basic -- reelle Zahlen




-- 2) 
example : (2.5 : ℝ) + 2.5 = 5 :=
begin
  norm_num,
end

example : (2 : ℝ) + 2 = 4 := 
begin
    norm_num,
end

import data.finset.basic
import data.real.basic
open_locale big_operators
open finset
example (n : N) :
2/7 i in range n, (i : R) = n * (n - 1) / 2 :=
begin
induction n with d hd,
{ -- base case: sum over empty type is 0 * (0 - 1) / 2
simp },
{ -- inductive step
rw [sum_range_succ, hd],
simp, -- tidies up and reduces the goal to
-- ⊢ ↑d * (↑d - 1) / 2 + ↑d = (↑d + 1) * ↑d / 2
ring, -- a more appropriate tactic to finish the job
}
end