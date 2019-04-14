/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Some basic lemmas about integers.  I should check whether the
new coercion tactic makes them trivial.

-/

import data.fintype 

lemma int.lt_succ_iff {n m : ℤ} : n < m + 1 ↔ n ≤ m := 
 ⟨int.le_of_lt_add_one,int.lt_add_one_of_le⟩ 

lemma nat.square_le {n m : ℕ} : m ^ 2 ≤ n ↔ m ≤ n.sqrt := 
 ⟨λ h0, le_of_not_gt (λ h1, not_le_of_gt ((nat.pow_two m).symm.subst (nat.sqrt_lt.mp h1)) h0),
  λ h0, le_of_not_gt (λ h1,not_le_of_gt (nat.sqrt_lt.mpr ((nat.pow_two m).subst h1)) h0)⟩ 

lemma nat.square_lt {n m : ℕ} : m ^ 2 < n.succ ↔ m ≤ n.sqrt :=
 (@nat.lt_succ_iff (m ^ 2) n).trans (@nat.square_le n m)

lemma int.abs_le {n m : ℤ} : abs m ≤ n ↔ (- n ≤ m ∧ m ≤ n) := 
begin
 by_cases hm : 0 ≤ m,
 { rw[abs_of_nonneg hm],
   exact ⟨ 
     λ hmn, ⟨le_trans (neg_nonpos_of_nonneg (le_trans hm hmn)) hm,hmn⟩,
     λ hmn, hmn.right
      ⟩ 
 },{
   let hma := le_of_lt (lt_of_not_ge hm),
   let hmb := neg_nonneg_of_nonpos hma,
   rw[abs_of_nonpos hma],
   exact ⟨ 
     λ hmn, ⟨(neg_neg m) ▸ (neg_le_neg hmn),le_trans (le_trans hma hmb) hmn⟩,
     λ hmn, (neg_neg n) ▸ (neg_le_neg hmn.left), 
    ⟩
 }
end

lemma int.abs_le' {n : ℕ} {m : ℤ} : m.nat_abs ≤ n ↔ (- (n : ℤ) ≤ m ∧ m ≤ n) := 
begin
 let h := @int.abs_le n m,
 rw[int.abs_eq_nat_abs,int.coe_nat_le] at h,
 exact h,
end

lemma int.abs_square (n : ℤ) : n ^ 2 = (abs n) ^ 2 := begin
 by_cases h0 : n ≥ 0,
 {rw[abs_of_nonneg h0]},
 {rw[abs_of_neg (lt_of_not_ge h0),pow_two,pow_two,neg_mul_neg],}
end

lemma int.abs_square' (n : ℤ) : n ^ 2 = ((int.nat_abs n) ^ 2 : ℕ) :=
 calc 
   n ^ 2 = n * n : pow_two n
   ... = ↑ (n.nat_abs * n.nat_abs) : int.nat_abs_mul_self.symm
   ... = ↑ (n.nat_abs ^ 2 : ℕ) : by rw[(nat.pow_two n.nat_abs).symm]

lemma int.square_le {n : ℕ} {m : ℤ} : 
 m ^ 2 ≤ n ↔ - (n.sqrt : ℤ) ≤ m ∧ m ≤ n.sqrt := 
begin
 rw[int.abs_square',int.coe_nat_le,nat.square_le,int.abs_le'],
end

lemma int.square_lt {n : ℕ} {m : ℤ} : 
 m ^ 2 < n.succ ↔ - (n.sqrt : ℤ) ≤ m ∧ m ≤ n.sqrt := 
begin
 rw[int.abs_square',int.coe_nat_lt,nat.square_lt,int.abs_le'],
end

