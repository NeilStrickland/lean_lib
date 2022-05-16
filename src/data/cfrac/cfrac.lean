/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file attempts to define the rationals using a variant of 
continued fractions as the primary definition.  Essentially,
the point is that any strictly positive rational p can be 
written uniquely as n + 1 or n + 1 - 1/(1 + q), where n is
a natural number and q is another strictly positive rational.
This means that there is a free monoid on two generators that
acts on ℚ⁺, and evaluation at 1 ∈ ℚ⁺ gives a bijection from 
that monoid to ℚ⁺.  The action actually extends to a group
action on ℚ ∪ {∞}, although we have not written that yet. 

The possible advantage of this approach is that the positive 
rationals become a straightforward inductive type with two 
constructors; no quotient constructions or subtypes are 
required.  The total ordering is also quite straightforward
from this point of view.
   
The disadvantage is that it becomes harder to set up the
algebraic structure.  There is an algorithm due to Gosper and
some of the material below in intended to lead towards an 
implementation, but we have not yet completed that.

This approach also fails to leverage the relative computational 
efficiency of the Lean virtual machine.  
-/

import data.nat.basic
import tactic.find tactic.ring

inductive posrat : Type 
| twist : posrat → posrat 
| one : posrat
| succ : posrat → posrat

namespace posrat
open posrat

def nat_add : ℕ → posrat → posrat 
| 0 a := a
| (nat.succ n) a := posrat.succ (nat_add n a)

def nat_succ (n : ℕ) : posrat := nat_add n one

def weight : posrat → ℕ 
| (twist a) := nat.succ (weight a)
| one := 0
| (succ a) := nat.succ (weight a)

def pred_ceil : posrat → ℕ
| (twist a) := 0
| one := 0
| (succ a) := nat.succ (pred_ceil a)

def le : posrat → posrat → Prop
| (twist a) (twist b) := le a b
| (twist _) one := true
| (twist _) (succ _) := true
| one (twist _) := false
| one one := true
| one (succ _) := true
| (succ _) one := false
| (succ a) (succ b) := le a b
| (succ _) (twist _) := false

def lt (a b : posrat) : Prop := ¬ (le b a)

lemma pred_ceil_le : ∀ (a b : posrat),
 le a b → (pred_ceil a ≤ pred_ceil b) := 
begin
 intro a,
 induction a with a1 iha1 a2 iha2;
 intros b h; rcases b with b1 | _ | b2; simp[le] at h;
 simp[pred_ceil];
 try {contradiction};
 try {apply nat.succ_le_succ, apply iha2, assumption}
end

lemma le_refl : ∀ a : posrat, le a a
| (twist a) := le_refl a
| one := true.intro
| (succ a) := le_refl a

lemma le_antisymm : ∀ a b : posrat, le a b → le b a → a = b :=
begin
 intro a,
 induction a with a1 iha a2 iha;
 intros b a_le_b b_le_a;
 rcases b with b1 | _ | b2; simp[le] at a_le_b b_le_a ⊢;
 try {contradiction};
 try {apply iha,assumption,assumption},
end

lemma le_trans : ∀ {a b c : posrat}, le a b → le b c → le a c :=
begin
 intro a,
 induction a with a1 iha a2 iha;
 intros b c a_le_b b_le_c;
 rcases b with b1 | _ | b2;
 rcases c with c1 | _ | c2;
 simp[le] at a_le_b b_le_c ⊢;
 try {contradiction};
 try {apply iha,assumption,assumption},
end

lemma le_total : ∀ a b : posrat, le a b ∨ le b a := 
begin
 intro a,
 induction a with a1 iha a1 iha;
 intro b;
 rcases b with b1 | _ | b1; simp[le]; apply iha,
end

lemma lt_iff_le_not_le (a b : posrat) :
 (lt a b) ↔ (le a b) ∧ ¬ (le b a) :=
begin
 dsimp[lt],
 rcases (le_total a b) with a_le_b | b_le_a; split,
 {intro h,split;assumption},
 {intro h,exact h.right},
 {intro h,split;contradiction},
 {intro h,exact h.right}
end

def inv : posrat → posrat 
| (twist a) := succ (inv a)
| one := one
| (succ a) := twist (inv a) 

lemma inv_inv (a : posrat) : inv (inv a) = a := 
begin
 induction a with _ ih _ ih;
 simp[inv]; apply ih,
end

lemma inv_order: ∀ (a b : posrat), le a b ↔ le (inv b) (inv a) :=
begin
 intro a,
 induction a with a1 iha a1 iha;
 intro b;
 rcases b with b1 | _ | b1; simp[le,inv]; apply iha,
end

/-
mutual def mul2, div2 
with mul2 : posrat → posrat
| (mul2 (succ a)) := succ (succ (mul2 a))
| (mul2 (twist (succ a))) := succ (twist (div2 a))
| (mul2 (twist (twist a))) := twist (mul2 a)
with div2 : posrat → posrat
| (div2 (twist a)) := twist (twist (div2 a))
| (div2 (succ (twist a))) := twist (succ (mul2 a))
| (div2 (succ (succ a))) := succ (div2 a)

def from_frac (u v : ℕ) (u_pos : u > 0) (v_pos : v > 0)
 : posrat := sorry

-/

structure mat : Type := 
(a : nat) (b : nat) (c : nat) (d : nat) 
(det_prop : a * d = c * b + 1)

namespace mat

def ab (m : mat) : ℕ := m.a + m.b
def cd (m : mat) : ℕ := m.c + m.d

lemma a_pos (m : mat) : m.a > 0 :=
begin
 rcases m with ⟨_ | a0,b,c,d,det_prop⟩;
 simp at det_prop ⊢,
 { cases det_prop, }
end

lemma d_pos (m : mat) : m.d > 0 :=
begin
 rcases m with ⟨a,b,c,_ | d0,det_prop⟩;
 simp at det_prop ⊢,
 { cases det_prop }
end

def ab_pos (m : mat) : 0 < m.ab := nat.add_pos_left m.a_pos _
def cd_pos (m : mat) : 0 < m.cd := nat.add_pos_right _ m.d_pos

def aq  (m : mat) : ℚ := (m.a  : ℚ)
def bq  (m : mat) : ℚ := (m.b  : ℚ)
def cq  (m : mat) : ℚ := (m.c  : ℚ)
def dq  (m : mat) : ℚ := (m.d  : ℚ)
def abq (m : mat) : ℚ := (m.ab : ℚ)
def cdq (m : mat) : ℚ := (m.cd : ℚ)

def aq_pos  (m : mat) : 0 < m.aq  := int.cast_lt.mpr (int.coe_nat_lt.mpr m.a_pos)
def dq_pos  (m : mat) : 0 < m.dq  := int.cast_lt.mpr (int.coe_nat_lt.mpr m.d_pos)
def abq_pos (m : mat) : 0 < m.abq := int.cast_lt.mpr (int.coe_nat_lt.mpr m.ab_pos)
def cdq_pos (m : mat) : 0 < m.cdq := int.cast_lt.mpr (int.coe_nat_lt.mpr m.cd_pos)

def aq_nz  (m : mat) : m.aq  ≠ 0 := (ne_of_lt m.aq_pos ).symm
def dq_nz  (m : mat) : m.dq  ≠ 0 := (ne_of_lt m.dq_pos ).symm
def abq_nz (m : mat) : m.abq ≠ 0 := (ne_of_lt m.abq_pos).symm
def cdq_nz (m : mat) : m.cdq ≠ 0 := (ne_of_lt m.cdq_pos).symm

def au  (m : mat) : units ℚ := units.mk0 m.aq  m.aq_nz
def du  (m : mat) : units ℚ := units.mk0 m.dq  m.dq_nz
def abu (m : mat) : units ℚ := units.mk0 m.abq m.abq_nz
def cdu (m : mat) : units ℚ := units.mk0 m.cdq m.cdq_nz

def one : mat := 
 {a := 1, b := 0, c := 0, d := 1, det_prop := rfl}

def twist (m : mat) : mat := 
begin
 rcases m with ⟨ a,b,c,d,det_prop ⟩,
 have dp := calc
  a * (b + d) = a * b + a * d : mul_add a b d
  ... = a * b + (c * b + 1) : by rw[det_prop] 
  ... = (a * b + c * b) + 1 : by rw[add_assoc]
  ... = (a + c) * b + 1 : by rw[← add_mul]
 ,
 exact ⟨ a , b, a + c, b + d, dp⟩ 
end

def succ (m : mat) : mat  := 
begin
 rcases m with ⟨ a,b,c,d,det_prop ⟩,
 have dp := calc
  (a + c) * d = a * d + c * d : add_mul a c d
  ... = c * b + 1 + c * d : by rw[det_prop]
  ... = c * b + c * d + 1 : by rw[add_assoc, add_comm 1 (c * d), ← add_assoc]
  ... = c * (b + d) + 1 : by rw[← mul_add]
 ,
 exact ⟨ a + c , b + d,  c, d, dp⟩ 
end

def inv (m : mat) : mat := 
begin
 rcases m with ⟨ a,b,c,d,det_prop ⟩,
 have dp : d * a = b * c + 1, by rw[mul_comm,det_prop,mul_comm],
 exact ⟨ d,c,b,a, dp⟩ 
end

def to_rat (m : mat) : ℚ := m.abq / m.cdq

lemma to_rat_pos (m : mat) : 0 < to_rat m := 
begin
 dsimp[to_rat],
 apply mul_pos,exact m.abq_pos,apply inv_pos.mpr,exact m.cdq_pos
end

lemma one_to_rat : to_rat mat.one = (1:ℚ) := begin
  change (0 + 1) / (0 + 1) = (1 : ℚ),
  rw[zero_add,div_one],
end

lemma succ_to_rat (m : mat) : to_rat (mat.succ m) = (to_rat m) + 1 :=
begin
 let cdnz := m.cdq_nz,
 rcases m with ⟨ a,b,c,d,det_prop ⟩,
 simp only [to_rat,mat.succ,mat.abq,mat.cdq,mat.ab,mat.cd] at cdnz ⊢,
 have : (((a + c + (b + d)) : ℕ) : ℚ) = ((a + b) : ℕ)  + ((c + d) : ℕ) := by { norm_cast, ring },
 rw[this,add_div,div_self cdnz]
end

def twist_rat (p : ℚ) : ℚ := p / (1 + p)

lemma rat_simp₀ {p q r : ℚ} (hp : p > 0) (hq : q > 0) (hr : r > 0) : p / q / r = p / (q * r) := 
begin 
  change (p * q⁻¹) * r⁻¹ = p * (q * r)⁻¹,
  rw[mul_inv_rev, mul_comm r⁻¹, mul_assoc]
end

lemma twist_to_rat (m : mat) :
 to_rat (mat.twist m) = twist_rat (to_rat m) :=
begin
 let abp  := m.abq_pos,
 let cdp  := m.cdq_pos,
 let abnz := m.abq_nz,
 let cdnz := m.cdq_nz,
 rcases m with ⟨ a,b,c,d,det_prop ⟩,
 simp only[to_rat,mat.twist,mat.abq,mat.cdq,mat.ab,mat.cd,twist_rat]
  at abp cdp abnz cdnz ⊢,
 have : (((a + c + (b + d)) : ℕ) : ℚ) = ((a + b) : ℕ)  + ((c + d) : ℕ) := by { norm_cast, ring },
 rw[this],
 let p : ℚ := (a + b : ℕ),
 let q : ℚ := (c + d : ℕ),
 change p / (p + q) = (p / q) / (1 + p / q),
 have pp : p > 0 := abp,
 have qp : q > 0 := cdp,
 have op : (1 : ℚ) > 0 := one_pos,
 have rp := add_pos (div_pos pp qp) op,
 rw[add_comm (1 : ℚ), rat_simp₀ pp qp rp],
 congr' 1, 
 rw[mul_add, mul_one, div_eq_mul_inv, ← mul_assoc, mul_comm q, mul_assoc],
 rw[mul_inv_cancel (ne_of_gt qp), mul_one]
end

lemma inv_to_rat (m : mat) : 
 to_rat (mat.inv m) = (to_rat m)⁻¹ := 
begin
 let abp  := m.abq_pos,
 let cdp  := m.cdq_pos,
 let abnz := m.abq_nz,
 let cdnz := m.cdq_nz,
 rcases m with ⟨ a,b,c,d,det_prop ⟩,
 simp[to_rat,mat.inv,mat.abq,mat.cdq,mat.ab,mat.cd],
 rw[add_comm ↑c ↑d,add_comm ↑a ↑b],
end

end mat

def to_mat : posrat → mat 
| (posrat.twist a) := mat.twist (to_mat a)
| posrat.one := mat.one
| (posrat.succ a) := mat.succ (to_mat a)

def to_rat (a : posrat) : rat := mat.to_rat (posrat.to_mat a)
def num (a : posrat) : ℕ := (posrat.to_mat a).ab
def den (a : posrat) : ℕ := (posrat.to_mat a).cd

end posrat

