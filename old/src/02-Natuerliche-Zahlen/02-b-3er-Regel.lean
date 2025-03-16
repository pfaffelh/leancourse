import data.nat.digits
open nat 

example  (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum := 
begin
  refine dvd_iff_dvd_digits_sum 3 10 _ n, 
  norm_num,
end

