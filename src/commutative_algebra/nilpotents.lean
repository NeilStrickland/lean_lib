import algebra.ring
import algebra.group_power
import ring_theory.ideals
import data.nat.choose
import data.zmod.basic

open nat finset
universe u

section nilpotents
 variable {R : Type u}
 variable [R_comm_ring : comm_ring R]
 include R_comm_ring
 def next_pow_zero (x : R) (n : ℕ)  := (x ^ (n + 1)) = 0

 def is_nilpotent (x : R) : Prop := ∃ n : ℕ, (next_pow_zero x n)

 lemma npz_zero : next_pow_zero (0 : R) (0 : ℕ) := 
   by {simp[next_pow_zero],}

 lemma npz_shift
  {x : R} {n m : ℕ}
   (xR : (next_pow_zero x n)) (Sn_le_m : n + 1 ≤ m) : 
     x ^ m = 0 := 
 begin
  unfold next_pow_zero at xR,
  rw[← (nat.add_sub_of_le Sn_le_m),_root_.pow_add,xR,zero_mul],
 end

lemma npz_add {x y : R} {n m : ℕ}
  (xR : next_pow_zero x n) (yR : next_pow_zero y m) :
  next_pow_zero (x + y) (n + m) :=
begin
  unfold next_pow_zero at xR yR ⊢,
  let p := n + m + 1,
  suffices : ∀ (k : ℕ) (h : k ∈ (range (succ p))),
    x ^ k * y ^ (p - k) * ↑(choose p k) = 0,
  { exact calc (x + y)^p
        = (range (succ p)).sum (λ k, x ^ k * y ^ (p - k) * ↑(choose p k))
        : add_pow x y p 
    ... = (range (succ p)).sum (λ k, (0 : R))
        : finset.sum_congr rfl this 
    ... = 0 : sum_const_zero },

  intros k k_in_range,
have k_lt_Sp : k < p + 1 := mem_range.mp k_in_range,
have k_le_p : k ≤ p := le_of_lt_succ k_lt_Sp,
rcases le_or_gt (n + 1) k with Sn_le_k | Sn_gt_k,
{ have : x ^ k = 0 := npz_shift xR Sn_le_k,
simp [this],
}, { have k_le_n : k ≤ n := lt_succ_iff.mp Sn_gt_k,
let j := n - k,
have Z1 : k + j = n := add_sub_of_le k_le_n,
have Z2 : p - k = (m + 1) + j,
{ apply nat.sub_eq_of_eq_add,
simp [p, Z1.symm]
},
    have : y ^ (p - k) = 0 := 
     by { rw [Z2, _root_.pow_add, yR, zero_mul] },
    simp [this],
 }
end

lemma npz_add' {x y : R} {n m : ℕ}
  (xR : next_pow_zero x n) (yR : next_pow_zero y m) :
  next_pow_zero (x + y) (n + m) :=
begin
  unfold next_pow_zero at xR yR ⊢,
  let p := n + m + 1,
  suffices : ∀ (k : ℕ) (h : k ∈ (range (succ p))),
    x ^ k * y ^ (p - k) * ↑(choose p k) = 0,
  { exact ((add_pow x y p).trans
       (finset.sum_congr rfl this)).trans sum_const_zero,},
  intros k k_in_range,
  have k_lt_Sp : k < p + 1 := mem_range.mp k_in_range,
  have k_le_p : k ≤ p := le_of_lt_succ k_lt_Sp,
  rcases le_or_gt (n + 1) k with Sn_le_k | Sn_gt_k,
  { rw[npz_shift xR Sn_le_k,zero_mul,zero_mul],},
  { let j := n - k,
    let e0 : p = (m + n) + 1 :=
     congr_fun (congr_arg nat.add (nat.add_comm n m)) 1,
    let e1 : (m + n) + 1 = (m + 1) + n :=
       ((nat.add_assoc m n 1).trans
         (congr_arg (nat.add m) (nat.add_comm n 1))).trans
        (nat.add_assoc m 1 n).symm,
    let e2 : n = j + k :=
       (add_sub_of_le (lt_succ_iff.mp Sn_gt_k)).symm.trans
          (nat.add_comm k j),
    let e3 : (m + 1) + n = (m + 1 + j) + k :=
     (congr_arg (nat.add (m + 1)) e2).trans
       (nat.add_assoc (m + 1) j k).symm,
    let e4 : p = k + (m + 1 + j) :=
     (e0.trans (e1.trans e3)).trans (nat.add_comm (m + 1 + j) k),
    let e5 : p - k = m + 1 + j := nat.sub_eq_of_eq_add e4,
    let e6 : y ^ (p - k) = y^(m + 1) * y^j :=
     (congr_arg (pow y) e5).trans (_root_.pow_add y (m + 1) j),
    let e7 : y^(p - k) = 0 := e6.trans
     ((congr_fun (congr_arg R_comm_ring.mul yR) (y ^ j)).trans
        (zero_mul (y ^ j))),
    let e8 : x^k * y^(p - k) = 0 := 
     (congr_arg (@comm_ring.mul R R_comm_ring (x ^ k)) e7).trans
        (mul_zero (x ^ k)),
    let e9 : x^k * y^(p - k) * ↑(choose p k)  = 0 :=
     (congr_fun (congr_arg R_comm_ring.mul e8) ↑(choose p k)).trans
       (zero_mul ↑(choose p k)),
    exact e9,
 }
end

lemma npz_mul_left (x : R) {y : R} {m : ℕ} (yR : next_pow_zero y m): 
  (next_pow_zero (x * y) m) :=
begin
  unfold next_pow_zero at yR ⊢,
  rw[_root_.mul_pow,yR,mul_zero],
end

lemma npz_mul_right {x : R} {n : ℕ} (xR : next_pow_zero x n) (y : R):
  (next_pow_zero (x * y) n) := 
 calc
   (x * y) ^ (n + 1) = (y * x)^(n + 1) : by rw[mul_comm x y]
   ... = 0 : npz_mul_left y xR.

lemma npz_chain {x : R} {n m : ℕ}
   (xR : next_pow_zero (x ^ (n + 1)) m) :
      next_pow_zero x (n * m + n + m) :=
 begin
  unfold next_pow_zero at xR ⊢,
  have Z0 : x^((n + 1) * (m + 1)) = 0, by rw[pow_mul,xR],
  have Z1 : (n * m + n + m) + 1 = (n + 1) * (m + 1) := 
    by simp[add_mul,mul_add,mul_one,one_mul,add_assoc],
  by rw[Z1,Z0],
 end

lemma nilpotent_zero : is_nilpotent (0 : R) := ⟨0,npz_zero⟩

lemma nilpotent_add {x y : R} :
   is_nilpotent x → is_nilpotent y → is_nilpotent (x + y)
| ⟨n,xR⟩ ⟨m,yR⟩ := ⟨n+m,npz_add xR yR⟩

lemma nilpotent_mul_left (x : R)  {y : R} : 
  is_nilpotent y → is_nilpotent (x * y)
| ⟨m,yN⟩ := ⟨m,npz_mul_left x yN⟩ 

lemma nilpotent_mul_right : ∀ {x : R} (xN : is_nilpotent x) (y : R),
  (is_nilpotent (x * y)) 
| x ⟨m,xN⟩ y := ⟨m,npz_mul_right xN y⟩ 

lemma unit_not_nilpotent (x y : R) (e0 : x * y = 1) (e1 : (1 : R) ≠ 0) :
  ¬ is_nilpotent x := 
begin
  rintro ⟨m,e2⟩,
  apply e1,
  exact calc 
   (1 : R) = 1 ^ (m + 1) : (_root_.one_pow (m + 1)).symm
    ... = (x * y) ^ (m + 1) : by rw[← e0]
    ... = 0 : npz_mul_right e2 y,
end
  
lemma nilpotent_chain {x : R} {n : ℕ} :
   is_nilpotent (x ^ (n + 1)) →  is_nilpotent x 
| ⟨m,xN⟩ := ⟨n*m+n+m,npz_chain xN⟩  
 
def is_reduced
   (R : Type*) [R_comm_ring : comm_ring R] : Prop :=
     ∀ x : R, (is_nilpotent x) → (x = 0)

def nilradical
 (R : Type*) [R_comm_ring : comm_ring R] : ideal R :=
{
  carrier := is_nilpotent,
  zero := nilpotent_zero,
  add  := @nilpotent_add _ _ ,
  smul  := nilpotent_mul_left
}      

def reduced_quotient (R : Type*) [R_comm_ring : comm_ring R] := 
  (nilradical R).quotient 

instance reduced_quotient_ring_structure
  (R : Type*) [R_comm_ring : comm_ring R] : 
     comm_ring (reduced_quotient R) := 
      by { dsimp[reduced_quotient]; apply_instance }

def reduced_quotient_mk {R : Type*} [R_comm_ring : comm_ring R] :
   R → reduced_quotient R := ideal.quotient.mk (nilradical R)

instance reduced_quotient_mk_is_ring_hom :=
  ideal.quotient.is_ring_hom_mk (nilradical R)

lemma reduced_quotient_is_reduced : is_reduced (reduced_quotient R) :=
begin
 let π := @reduced_quotient_mk R _,
 rintros ⟨x0⟩ ⟨n,e0⟩,
  let e1 := calc 
   π (x0 ^ (n + 1)) = (π x0) ^ (n + 1) :
    by simp[π,reduced_quotient_mk,is_semiring_hom.map_pow]
    ... = 0 : e0,
  have : is_nilpotent (x0 ^ (n + 1)) :=
    ideal.quotient.eq_zero_iff_mem.mp e1,
 have : is_nilpotent x0 := nilpotent_chain this,
 exact ideal.quotient.eq_zero_iff_mem.mpr this,
end
end nilpotents 

section Z_is_reduced

lemma N_reduced (n k : ℕ) : n^(k+1) = 0 → n = 0 :=
begin
 cases n with n0,
 {intro,refl},
 {
   intro h0,
   exfalso,
   exact
    (ne_of_lt (nat.pow_pos (nat.zero_lt_succ n0) (k + 1))).symm h0,
 }
end

lemma nat_abs_pow : ∀ (n : ℤ) (k : ℕ),
      int.nat_abs (n ^ k) = (int.nat_abs n) ^ k 
| n 0 := rfl
| n (k + 1) := 
  begin
   let na := int.nat_abs n,
   exact calc
    int.nat_abs (n ^ (k + 1)) = 
          int.nat_abs (n * n^k) : rfl
    ... = na * (int.nat_abs (n ^ k)) : by rw[int.nat_abs_mul]
    ... = na * na ^ k : by rw[nat_abs_pow n k]
    ... = na ^ k * na : by rw[nat.mul_comm]
    ... = na ^ (k + 1) : rfl
  end

lemma Z_reduced : is_reduced ℤ := 
begin
 rintros x ⟨k,e⟩,
 let x0 := int.nat_abs x,
 have : (int.nat_abs x)^(k + 1) = 0
  := (nat_abs_pow x k.succ).symm.trans (congr_arg int.nat_abs e),
 have : x0 = 0 := N_reduced (int.nat_abs x) k this,
 exact int.eq_zero_of_nat_abs_eq_zero this,
end

end Z_is_reduced

section Z4_nilpotents

lemma zmod.pow_val {n : ℕ+} (a : zmod n) (m : ℕ) :
 (a ^ m).val = (a.val ^ m) % n :=
begin
 induction m with m0 ih,
 {simp[has_one.one,monoid.one,ring.one,has_mod.mod,comm_ring.one],},
 {exact calc
   (a ^ (m0 + 1)).val = (a * a^m0).val : rfl
  ... = (a.val * (a^m0).val) % n : by rw[zmod.mul_val]
  ... = (a.val * ((a.val ^ m0) % n)) % n : by rw[ih]
  ... = (a.val * a.val ^ m0) % n :
   modeq.modeq_mul (modeq.refl a.val) (mod_mod (a.val ^ m0) n)
  ... = (a.val ^ m0 * a.val) % n : by rw[mul_comm]
  ... = (a.val ^ (m0 + 1)) % n : rfl 
 }
end

lemma zmod.nilpotent_iff (n : ℕ+) (k : ℕ) (k_is_lt : k < n) :
 @is_nilpotent (zmod n) _ ⟨k,k_is_lt⟩ ↔ 
  ∃ m : ℕ, k ^ (m + 1) % n = 0 :=
begin
 split,
 {
   rintro ⟨m,h1⟩,
   use m,
   exact 
    (@zmod.pow_val n ⟨k,k_is_lt⟩ (m + 1)).symm.trans 
    (congr_arg fin.val h1),
 },{
   rintro ⟨m,h1⟩,
   use m,
   let k0 : zmod n := ⟨k,k_is_lt⟩,
   let z0 : zmod n := 0,
   let h2 : (k0 ^ (m + 1)).val = z0.val :=
    (@zmod.pow_val n ⟨k,k_is_lt⟩ (m + 1)).trans h1,
   exact fin.eq_of_veq h2,
 }
end

lemma Z4_nilpotents : (nilradical (zmod 4)).carrier = {0,2} := 
begin
 have h0 : is_nilpotent (0 : zmod 4) := ⟨0,rfl⟩,
 have h2 : is_nilpotent (2 : zmod 4) := ⟨1,rfl⟩,
 have nt : (1 : zmod 4) ≠ 0 := dec_trivial,
 have h1 : ¬ is_nilpotent (1 : zmod 4) :=
  unit_not_nilpotent 1 1 rfl nt,
 have h3 : ¬ is_nilpotent (3 : zmod 4) :=
  unit_not_nilpotent 3 3 rfl nt,
 have e1 : ∀ j0 : ℕ, ¬ (j0.succ.succ.succ.succ < 4) :=
   λ j0, dec_trivial,
 ext j,
 simp[nilradical],
 split,
 {intro j_nil,
  rcases j;
  rcases j_val with _ | _ | _ | _ | j0,
  {exact dec_trivial,},
  {exfalso,exact h1 j_nil,},
  {exact dec_trivial,},
  {exfalso,exact h3 j_nil,},
  {exfalso,exact e1 j0 j_is_lt,}
 },{
  intro j_eq, cases j_eq; rw[j_eq],
  exact h2,
  exact h0,
 }
end

end Z4_nilpotents

