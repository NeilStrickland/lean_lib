/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This is about the ideal of nilpotent elements in a commutative ring.
There is another version in nilpotents.doc.lean with voluminous 
comments aimed at Lean beginners.
-/

import algebra.ring
import algebra.group_power
import ring_theory.ideals
import data.nat.choose
import data.zmod.basic

import tactic.squeeze
open nat finset
universe u

namespace comm_ring

variables {R : Type u} [comm_ring R]

def next_pow_zero (x : R) (n : ℕ)  := (x ^ (n + 1)) = 0

def is_nilpotent (x : R) : Prop := ∃ n : ℕ, (next_pow_zero x n)

lemma npz_zero : next_pow_zero (0 : R) (0 : ℕ) := 
  by {rw[next_pow_zero,_root_.pow_one],}

lemma npz_shift {x : R} {n m : ℕ} : 
  (next_pow_zero x n) → (n + 1 ≤ m) →  x ^ m = 0 := 
by {rintros hx hn, dsimp[next_pow_zero] at hx,
rw[← (nat.add_sub_of_le hn),_root_.pow_add,hx,zero_mul]}

lemma npz_add {x y : R} {n m : ℕ} : 
  (next_pow_zero x n) → (next_pow_zero y m) → 
    next_pow_zero (x + y) (n + m) :=
λ hx hy, begin
unfold next_pow_zero at *,
let p := n + m + 1,
suffices : ∀ (k : ℕ) (h : k ∈ (range (succ p))),
    x ^ k * y ^ (p - k) * ↑(choose p k) = 0,
{rw[add_pow,sum_congr rfl this,sum_const_zero],},
intros k hk,
have k_le : k ≤ p := le_of_lt_succ (mem_range.mp hk),
rcases le_or_gt (n + 1) k with n_le | n_gt,
{rw[← congr_arg ((^) x) (add_sub_of_le n_le),
    _root_.pow_add,hx,zero_mul,zero_mul,zero_mul]},
{have : p = k + ((n - k) + (m + 1)) := 
  by {dsimp[p],
      rw[← nat.add_assoc k,add_sub_of_le (lt_succ_iff.mp n_gt),nat.add_assoc],},
  rw[nat.sub_eq_of_eq_add this,_root_.pow_add,hy,mul_zero,mul_zero,zero_mul]}
end

lemma npz_mul_left (x : R) {y : R} {m : ℕ} : 
 (next_pow_zero y m) → (next_pow_zero (x * y) m) :=
λ hy, by {unfold next_pow_zero at *,rw[_root_.mul_pow,hy,mul_zero]}

lemma npz_mul_right {x : R} {n : ℕ} : 
 (next_pow_zero x n) → ∀ y, (next_pow_zero (x * y) n) := 
λ hx y, by {unfold next_pow_zero at *,rw[_root_.mul_pow,hx,zero_mul],}

lemma npz_chain {x : R} {n m : ℕ} :
 (next_pow_zero (x ^ (n + 1)) m) → next_pow_zero x (n * m + n + m) :=
λ hx, 
begin
unfold next_pow_zero at *,
have : (n * m + n + m) + 1 = (n + 1) * (m + 1) := 
  by rw[add_mul,mul_add,nat.mul_one,nat.one_mul,nat.add_assoc],
rw[this,pow_mul,hx]
end

lemma nilpotent_zero : is_nilpotent (0 : R) := ⟨0,npz_zero⟩

lemma nilpotent_add {x y : R} :
   is_nilpotent x → is_nilpotent y → is_nilpotent (x + y)
| ⟨n,hx⟩ ⟨m,hy⟩ := ⟨n+m,npz_add hx hy⟩

lemma nilpotent_mul_left (x : R)  {y : R} : 
  is_nilpotent y → is_nilpotent (x * y)
| ⟨m,hy⟩ := ⟨m,npz_mul_left x hy⟩ 

lemma nilpotent_mul_right : ∀ {x : R} (xN : is_nilpotent x) (y : R),
  (is_nilpotent (x * y)) 
| x ⟨m,hx⟩ y := ⟨m,npz_mul_right hx y⟩ 

lemma unit_not_nilpotent (x y : R) :
 (x * y = 1) → ((1 : R) ≠ 0) →  ¬ is_nilpotent x := 
λ hxy hz ⟨m,hx⟩, hz (by {rw[← _root_.one_pow (m + 1),← hxy],exact npz_mul_right hx y})

lemma nilpotent_chain {x : R} {n : ℕ} :
   is_nilpotent (x ^ (n + 1)) →  is_nilpotent x 
| ⟨m,hx⟩ := ⟨n*m+n+m,npz_chain hx⟩  
 
variable (R)
def is_reduced: Prop := ∀ x : R, (is_nilpotent x) → (x = 0)

def nilradical : ideal R :=
{
  carrier := is_nilpotent,
  zero := nilpotent_zero,
  add  := @nilpotent_add _ _ ,
  smul  := nilpotent_mul_left
}      

def reduced_quotient := (nilradical R).quotient 

namespace reduced_quotient

instance : comm_ring (reduced_quotient R) := 
  by { dsimp[reduced_quotient]; apply_instance }

variable {R}

def mk : R → reduced_quotient R := ideal.quotient.mk (nilradical R)

instance : is_ring_hom mk :=
  ideal.quotient.is_ring_hom_mk (nilradical R)

lemma mk_eq_zero_iff {x : R} : mk x = 0 ↔ (is_nilpotent x) :=
 ideal.quotient.eq_zero_iff_mem

lemma is_reduced : is_reduced (reduced_quotient R) :=
begin
 rintros ⟨x0⟩ ⟨n,e0⟩,
 apply mk_eq_zero_iff.mpr,
 have := (is_semiring_hom.map_pow mk x0 (n + 1)).trans e0,
 have := mk_eq_zero_iff.mp this,
 exact nilpotent_chain this
end

end reduced_quotient

lemma mem_nilradical (x : R) : x ∈ nilradical R ↔ is_nilpotent x := 
 by {refl}

section Z_is_reduced

lemma N_reduced (n k : ℕ) : n^(k+1) = 0 → n = 0 :=
begin
 cases n with n0,
 {intro,refl},
 {exact λ h0,
  ((ne_of_lt (nat.pow_pos (nat.zero_lt_succ n0) (k + 1))).symm h0).elim,
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
  ... = (a.val ^ m0 * a.val) % n : by rw[nat.mul_comm]
  ... = (a.val ^ (m0 + 1)) % n : rfl 
 }
end

lemma zmod.nilpotent_iff (n : ℕ+) (k : ℕ) (k_is_lt : k < n) :
 @is_nilpotent (zmod n) _ ⟨k,k_is_lt⟩ ↔ 
  ∃ m : ℕ, k ^ (m + 1) % n = 0 :=
begin
 split,
 {exact λ ⟨m,h1⟩,⟨m,
    (@zmod.pow_val n ⟨k,k_is_lt⟩ (m + 1)).symm.trans 
    (congr_arg fin.val h1)⟩,
 },{
  exact λ ⟨m,h1⟩,⟨m,by {apply fin.eq_of_veq,rw[zmod.pow_val],exact h1,}⟩
 }
end

lemma Z4_nilpotents : (nilradical (zmod 4)).carrier = {0,2} := 
begin
 have h0 : is_nilpotent (0 : zmod 4) := ⟨0,rfl⟩,
 have h2 : is_nilpotent (2 : zmod 4) := ⟨1,rfl⟩,
 have nt : (1 : zmod 4) ≠ 0 := dec_trivial,
 have h1 : ¬ is_nilpotent (1 : zmod 4) :=
  unit_not_nilpotent 1 1 dec_trivial nt,
 have h3 : ¬ is_nilpotent (3 : zmod 4) :=
  unit_not_nilpotent 3 3 dec_trivial nt,
 have h4 : ∀ (i : zmod 4), i ∈ ({0,2} : set (zmod 4)) ↔ i = 2 ∨ i = 0 := 
  λ i, by {simp},
 have e1 : ∀ j0 : ℕ, ¬ (j0.succ.succ.succ.succ < 4) := λ j0, dec_trivial,
 ext j,rw[h4 j],dsimp[nilradical],
 split,
 {intro j_nil,
  rcases j;
  rcases j_val with _ | _ | _ | _ | j0,
  {exact dec_trivial},
  {exfalso,exact h1 j_nil},
  {exact dec_trivial},
  {exfalso,exact h3 j_nil},
  {exfalso,exact e1 j0 j_is_lt}
 },
 {rintro (j_eq | j_eq) ; rw[j_eq], exact h2,exact h0,}
end

end Z4_nilpotents

end comm_ring

