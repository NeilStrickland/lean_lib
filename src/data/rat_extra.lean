import data.rat

namespace rat 

lemma mk_with_one_eq_cast (n : ℤ) : mk n 1 = n := 
 by {rw[← of_int_eq_mk n,← coe_int_eq_of_int],}
 
lemma mk_nat_with_one_eq_cast (n : ℤ) : mk_nat n 1 = n := 
 calc mk_nat n 1 = mk n (int.of_nat 1) : rfl
  ... = n : mk_with_one_eq_cast n

lemma mk_pnat_with_one_eq_cast (n : ℤ) : mk_pnat n 1 = n := 
 mk_nat_with_one_eq_cast n

lemma of_int_eq_cast (n : ℤ) : of_int n = n := 
 (coe_int_eq_of_int n).symm

lemma nat_mk_with_one_eq_cast (n : ℕ) : mk n 1 = n := 
 by {rw[mk_with_one_eq_cast,int.cast_coe_nat],} 

lemma nat_mk_nat_with_one_eq_cast (n : ℕ) : mk_nat n 1 = n := 
 by {rw[mk_nat_with_one_eq_cast,int.cast_coe_nat],} 

lemma nat_mk_pnat_with_one_eq_cast (n : ℕ) : mk_pnat n 1 = n := 
 by {rw[mk_pnat_with_one_eq_cast,int.cast_coe_nat],} 

theorem num_denom'' (q : ℚ) : q = (q.num : ℚ) / (q.denom : ℚ) := 
begin
 have dnz : (q.denom : ℚ) ≠ 0 := ne_of_gt (nat.cast_pos.mpr q.pos),
 rw[eq_div_iff_mul_eq dnz],
 have : q * q.denom = (mk q.num q.denom) * q.denom :=
  by {congr' 1,exact num_denom.symm},
 rw[mk_eq_div,int.cast_coe_nat,div_mul_cancel _ dnz] at this,
 exact this,
end

end rat