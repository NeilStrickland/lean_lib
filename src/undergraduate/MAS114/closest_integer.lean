import data.rat
import data.real.basic
import tactic.ring

lemma abs_neg_of_pos {α : Type*} [linear_ordered_add_comm_group α] (a : α) : 
 a > 0 → abs (- a) = a := 
 λ a_pos, (abs_of_neg (neg_neg_of_pos a_pos)).trans (neg_neg a)

def half_Q : ℚ := 1 / 2
def neg_half_Q : ℚ := - half_Q

lemma dist_neg_Q (n : ℤ) (h : n ≥ 0) :
 abs (neg_half_Q - ((- (1 + n)) : ℤ)) = (n : ℚ) + half_Q := 
begin
 let n_Q : ℚ := n,
 have e0 : neg_half_Q + 1 = half_Q := by { dsimp[neg_half_Q,half_Q], norm_num },
 have e1  := 
  calc 
   neg_half_Q - ((- (1 + n)) : ℤ) = n + (neg_half_Q + 1) :
    by { rw[int.cast_neg, int.cast_add, int.cast_one, sub_neg_eq_add],
         ring, }
   ... = n_Q + half_Q : by rw[e0],
 have e2 : n_Q + half_Q > 0 :=
   add_pos_of_nonneg_of_pos (int.cast_nonneg.mpr h) one_half_pos,
 rw[e1,abs_of_pos e2],
end

lemma dist_nonneg_Q (n : ℤ) (h : n ≥ 0) :
 abs (neg_half_Q - n) = (n : ℚ) + half_Q := 
begin
 let n_Q : ℚ := n,
 have e1 : neg_half_Q - n = - (n_Q + half_Q) := 
   by {dsimp[neg_half_Q,half_Q], ring_nf },
 have e2 : n_Q + half_Q > 0 :=
   add_pos_of_nonneg_of_pos (int.cast_nonneg.mpr h) one_half_pos,
 have e3 : abs (- (n_Q + half_Q)) = n_Q + half_Q := 
  @abs_neg_of_pos ℚ _ (n_Q + half_Q) e2,
 rw[e1,e3],
end

noncomputable def half_R : ℝ := half_Q
noncomputable def neg_half_R : ℝ := neg_half_Q

lemma dist_neg (n : ℤ) (h : n ≥ 0) :
 abs (neg_half_R - (-(1 + n) : ℤ)) = (n : ℝ) + half_R :=
begin
 let x_Q : ℚ := neg_half_Q - (-(1 + n) : ℤ),
 let x_R : ℝ := neg_half_R - (-(1 + n) : ℤ),
 let d_Q : ℚ := abs x_Q,
 let d_R : ℝ := abs x_R,
 have e0 : x_R = x_Q := by {
   dsimp[x_R,x_Q,neg_half_R,neg_half_Q,half_Q],
   norm_cast
   },
 have e1 : d_R = d_Q := by { dsimp[d_R,d_Q],rw[e0,rat.cast_abs] },
 have e2 : d_Q = (n : ℚ) + half_Q := dist_neg_Q n h,
 exact calc
  d_R = d_Q : e1
  ... = (n : ℚ) + half_Q : by {rw[e2,rat.cast_add]}
  ... = (n : ℝ) + half_R : by {dsimp[half_R],rw[rat.cast_coe_int]}
end

lemma dist_nonneg (n : ℤ) (h : n ≥ 0) :
 abs(neg_half_R - n) = (n : ℝ) + half_R :=
begin
 let x_Q : ℚ := neg_half_Q - n,
 let x_R : ℝ := neg_half_R - n,
 let d_Q : ℚ := abs x_Q,
 let d_R : ℝ := abs x_R,
 have e0 : x_R = x_Q := by { 
  dsimp[x_R,x_Q,neg_half_R,neg_half_Q,half_Q],
  norm_cast
 },
 have e1 : d_R = d_Q := by { dsimp[d_R,d_Q],rw[e0,rat.cast_abs] },
 have e2 : d_Q = (n : ℚ) + half_Q := dist_nonneg_Q n h,
 exact calc
  d_R = d_Q : e1
  ... = (n : ℚ) + half_Q : by {rw[e2,rat.cast_add]}
  ... = (n : ℝ) + half_R : by {dsimp[half_R],rw[rat.cast_coe_int]}
end

def is_closest_integer (n : ℤ) (x : ℝ) := 
  ∀ (m : ℤ), m ≠ n → abs(x - n) < abs (x - m) 

lemma no_closest_integer (n : ℤ) : ¬ (is_closest_integer n neg_half_R) := 
begin
 have hh : ∀ k : ℤ, k ≥ 0 → ¬ ((k : ℝ) + half_R < half_R) := begin
  intros k k_nonneg k_half_lt,
  have k_half_ge : (k : ℝ) + half_R ≥ half_R :=
    le_add_of_nonneg_left (int.cast_nonneg.mpr k_nonneg), 
  exact not_le_of_gt k_half_lt k_half_ge,
 end,
 intro h0,
 by_cases h1 : n ≥ 0,
 {let m : ℤ := -1,
  have : ¬ (m ≥ 0) := dec_trivial,
  have h2 : m ≠ n := λ e, this (e.symm.subst h1),
  let h3 := h0 (-1) h2,
  let h4 := dist_neg 0 (le_refl 0),
  rw[add_zero] at h4,
  rw[h4,dist_nonneg n h1,int.cast_zero,zero_add] at h3,
  exact hh n h1 h3,
 },{
  have h1a : n < 0 := lt_of_not_ge h1,
  let m : ℤ := 0,
  have : ¬ (m < 0) := dec_trivial,
  have h2 : m ≠ n := λ e, this (e.symm.subst h1a),
  let h3 := h0 0 h2,
  let h4 := dist_nonneg 0 (le_refl 0),
  rw[h4,int.cast_zero,zero_add] at h3,
  let k :=  - (1 + n),
  have h5 : n = - (1 + k) := by {dsimp[k],ring},
  let h6 := (neg_nonneg_of_nonpos (int.add_one_le_iff.mpr (lt_of_not_ge h1))),
  rw[add_comm n 1] at h6,
  have h6a : 0 ≤ k := h6,
  let h7 := dist_neg k h6a,
  rw[← h5] at h7,
  rw[h7] at h3,
  exact hh k h6a h3,
 }
end
