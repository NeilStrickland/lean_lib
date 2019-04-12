import data.fintype 

namespace MAS114
namespace exercises_1
namespace Q05

def A : finset ℕ := [0,1,2].to_finset
def B : finset ℕ := [0,1,2,3].to_finset
def C : finset ℤ := [-2,-1,0,1,2].to_finset
def D : finset ℤ := [-3,-2,-1,0,1,2,3].to_finset

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

lemma A_spec (n : ℕ) : n ∈ A ↔ n ^ 2 < 9 := begin
 have sqrt_8 : 2 = nat.sqrt 8 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 exact calc
  n ∈ A ↔ n ∈ finset.range 3 : by rw[(dec_trivial : A = finset.range 3)]
  ... ↔ n < 3 : finset.mem_range
  ... ↔ n ≤ 2 : by rw[nat.lt_succ_iff]
  ... ↔ n ≤ nat.sqrt 8 : by rw[← sqrt_8]
  ... ↔ n ^ 2 < 9 : by rw[nat.square_lt]
end

lemma B_spec (n : ℕ) : n ∈ B ↔ n ^ 2 ≤ 9 := begin
 have sqrt_9 : 3 = nat.sqrt 9 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 exact calc
  n ∈ B ↔ n ∈ finset.range 4 : by rw[(dec_trivial : B = finset.range 4)]
  ... ↔ n < 4 : finset.mem_range
  ... ↔ n ≤ 3 : by rw[nat.lt_succ_iff]
  ... ↔ n ≤ nat.sqrt 9 : by rw[← sqrt_9]
  ... ↔ n ^ 2 ≤ 9 : by rw[nat.square_le]
end

lemma C_spec (n : ℤ) : n ∈ C ↔ n ^ 2 < 9 := begin
 have sqrt_8 : 2 = nat.sqrt 8 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 have e0 : (3 : ℤ) = ((2 : ℕ) : ℤ) + (1 : ℤ) := rfl,
 have e1 : (-2 : ℤ) = - ((2 : ℕ) : ℤ) := rfl, 
 have e2 : ((nat.succ 8) : ℤ)  = 9 := rfl,
 let e3 := @int.square_lt 8 n,
 exact calc
  n ∈ C ↔ n ∈ (int.range (-2) 3).to_finset :
   by rw[(dec_trivial : C = (int.range (-2) 3).to_finset)]
  ... ↔ n ∈ int.range (-2) 3 : by rw[list.mem_to_finset]
  ... ↔ -2 ≤ n ∧ n < 3 : int.mem_range_iff
  ... ↔ - ((2 : ℕ) : ℤ) ≤ n ∧ n < (2 : ℕ) + 1 : by rw[e0,e1]
  ... ↔ - ((2 : ℕ) : ℤ) ≤ n ∧ n ≤ (2 : ℕ) : by rw[int.lt_succ_iff]
  ... ↔ - (nat.sqrt 8 : ℤ) ≤ n ∧ n ≤ nat.sqrt 8 : by rw[← sqrt_8]
  ... ↔ n ^ 2 < nat.succ 8 : by rw[e3]
  ... ↔ n ^ 2 < 9 : by rw[e2],
end

lemma D_spec (n : ℤ) : n ∈ D ↔ n ^ 2 ≤ 9 := begin
 have sqrt_9 : 3 = nat.sqrt 9 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 have e0 : (4 : ℤ) = ((3 : ℕ) : ℤ) + (1 : ℤ) := rfl,
 have e1 : (-3 : ℤ) = - ((3 : ℕ) : ℤ) := rfl, 
 have e2 : ((9 : ℕ) : ℤ)  = 9 := rfl,
 let e3 := @int.square_le 9 n,
 exact calc
  n ∈ D ↔ n ∈ (int.range (-3) 4).to_finset :
   by rw[(dec_trivial : D = (int.range (-3) 4).to_finset)]
  ... ↔ n ∈ int.range (-3) 4 : by rw[list.mem_to_finset]
  ... ↔ -3 ≤ n ∧ n < 4 : int.mem_range_iff
  ... ↔ - ((3 : ℕ) : ℤ) ≤ n ∧ n < (3 : ℕ) + 1 : by rw[e0,e1]
  ... ↔ - ((3 : ℕ) : ℤ) ≤ n ∧ n ≤ (3 : ℕ) : by rw[int.lt_succ_iff]
  ... ↔ - (nat.sqrt 9 : ℤ) ≤ n ∧ n ≤ nat.sqrt 9 : by rw[← sqrt_9]
  ... ↔ n ^ 2 ≤ (9 : ℕ) : by rw[e3]
  ... ↔ n ^ 2 ≤ 9 : by rw[e2]
end

end Q05
end exercises_1
end MAS114