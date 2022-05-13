import tactic

lemma binomial_solution (x : ℤ) : x ^ 2 - 2 * x + 1 = 0 ↔ x = 1 := 
begin
  split; intro h,
  { have : (x - 1) ^ 2 = x ^ 2 - 2 * x + 1 := by {
      rw[pow_two, pow_two, two_mul, mul_sub, mul_one, sub_mul, one_mul],
      rw[← sub_add, sub_add_eq_sub_sub]
    },
    rw[← this] at h,
    exact sub_eq_zero.mp (pow_eq_zero h)
  },
  { rw[h], refl }
end

lemma binomial_solution' (x : ℤ) : x ^ 2 - 2 * x + 1 = 0 ↔ x = 1 := 
  by { split; intro h, nlinarith, simp[h], refl }

#print binomial_solution
