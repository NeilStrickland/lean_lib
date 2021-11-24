/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file defines the monoid SL₂(ℕ) of 2 × 2 matrices over ℕ with
determinant one.  Various things about the Euclidean algorithm,
continued fractions and so on can be formulated nicely in terms 
of this monoid.  It is also closely related to the group SL₂(ℤ),
which plays a key role in the theory of modular forms.

We have chosen to do this directly rather than embedding it in
a larger framework of matrices of general size over a general 
semiring.  This might or might not be a good decision.

Some key facts are as follows:
* SL₂(ℕ) is freely generated as a monoid by the matrices 
  S = [[1,1],[0,1]] and T = [[1,0],[1,1]]

* SL₂(ℕ) acts by multiplication on ℕ+ × ℕ+.  For any 
  [a,b] in ℕ+ × ℕ+, there exists m in SL₂(ℕ) such that 
  m • [d,d] = [a,b], where d = gcd a b.  This characterizes
  the gcd.  There is a version of the extended Euclidean 
  algorithm that works solely in ℕ rather than ℤ, and 
  calculates m and d as above.

* SL₂(ℕ) acts on ℚ+ by 
   [[a,b],[c,d]] • q = (a * q + b) / (c * q + d)
  The map m ↦ m • 1 gives a bijection SL₂(ℕ) → ℚ+
  In combiation with the isomorphism SL₂(ℕ) = ⟨S,T⟩,
  this gives a verson of the theory of continued fractions.
-/

import data.pnat.basic data.rat group_theory.group_action
import tactic.ring

structure SL2N : Type := 
(a : nat) (b : nat) (c : nat) (d : nat) 
(det_prop : a * d = c * b + 1)

namespace SL2N

@[ext]
theorem ext : ∀ (m₁ m₂ : SL2N),
 m₁.a = m₂.a → m₁.b = m₂.b → m₁.c = m₂.c → m₁.d = m₂.d → m₁ = m₂ := 
λ ⟨a₁,b₁,c₁,d₁,dp₁⟩ ⟨a₂,b₂,c₂,d₂,dp₂⟩ ha hb hc hd, 
 by {cases ha, cases hb, cases hc,cases hd,rw[(rfl : dp₁ = dp₂)]}

theorem ext' {m₁ m₂ : SL2N} : 
 m₁ = m₂ ↔ (m₁.a = m₂.a ∧ m₁.b = m₂.b ∧ m₁.c = m₂.c ∧ m₁.d = m₂.d) :=
by {split,{rintro rfl,simp only[eq_self_iff_true,true_and]},
    {intro h,ext,exact h.1,exact h.2.1,exact h.2.2.1,exact h.2.2.2}}

instance : has_sizeof SL2N := ⟨λ m,m.a + m.b + m.c + m.d⟩ 

instance : has_one SL2N := ⟨⟨1,0,0,1,rfl⟩⟩ 
@[simp] theorem one_a : (1 : SL2N).a = 1 := rfl
@[simp] theorem one_b : (1 : SL2N).b = 0 := rfl
@[simp] theorem one_c : (1 : SL2N).c = 0 := rfl
@[simp] theorem one_d : (1 : SL2N).d = 1 := rfl

instance : has_mul SL2N := ⟨λ m n, 
  ⟨m.a * n.a + m.b * n.c, m.a * n.b + m.b * n.d,
   m.c * n.a + m.d * n.c, m.c * n.b + m.d * n.d,
   by {have h : forall (x y w z : ℕ), 
        (w * x) * (y * z) = (w * y) * (x * z) := 
         by {intros,
             rw[mul_assoc w,mul_assoc w,← mul_assoc x,← mul_assoc y],
             rw[mul_comm x y]},
       rw[add_mul,add_mul,mul_add,mul_add,mul_add,mul_add],
       repeat {rw[h n.a]},repeat {rw[h n.c]},
       rw[mul_comm m.a m.c,mul_comm m.b m.c,mul_comm m.c m.a],
       rw[mul_comm m.d m.a,mul_comm m.d m.b],
       rw[m.det_prop,n.det_prop],
       rw[mul_add,mul_one,mul_add,mul_one,add_mul,one_mul],
       repeat {rw[add_assoc]},congr' 2,
       rw[add_comm,add_assoc],congr' 1,
       rw[add_assoc,add_comm,add_assoc,add_assoc],congr' 1,
       rw[← add_assoc,← add_assoc,add_comm (n.c * n.b)]}⟩⟩

@[simp] theorem mul_a (m n : SL2N) : (m * n).a = m.a * n.a + m.b * n.c := rfl
@[simp] theorem mul_b (m n : SL2N) : (m * n).b = m.a * n.b + m.b * n.d := rfl
@[simp] theorem mul_c (m n : SL2N) : (m * n).c = m.c * n.a + m.d * n.c := rfl
@[simp] theorem mul_d (m n : SL2N) : (m * n).d = m.c * n.b + m.d * n.d := rfl

instance : monoid SL2N := {
 one := has_one.one,
 mul := has_mul.mul,
 mul_assoc := λ m n p, 
  by {have : ∀ w x y z : ℕ, w + (x + (y + z)) = w + (y + (x + z)) := 
      by {intros,congr' 1,rw[← add_assoc,← add_assoc,add_comm x]},
      ext; 
      simp only [mul_a,mul_b,mul_c,mul_d,add_mul,mul_add,
                 mul_assoc,add_assoc,this],},
 one_mul := λ m, by {ext; simp only[mul_a,mul_b,mul_c,mul_d,
                     one_a,one_b,one_c,one_d,one_mul,zero_mul,
                    add_zero,zero_add],},
 mul_one := λ m, by {ext; simp only[mul_a,mul_b,mul_c,mul_d,
                     one_a,one_b,one_c,one_d,mul_one,mul_zero,
                    add_zero,zero_add],},
}

def S : SL2N := ⟨1,1,0,1,rfl⟩ 
def T : SL2N := ⟨1,0,1,1,rfl⟩ 

@[simp] theorem S_a : S.a = 1 := rfl
@[simp] theorem S_b : S.b = 1 := rfl
@[simp] theorem S_c : S.c = 0 := rfl
@[simp] theorem S_d : S.d = 1 := rfl

@[simp] theorem T_a : T.a = 1 := rfl
@[simp] theorem T_b : T.b = 0 := rfl
@[simp] theorem T_c : T.c = 1 := rfl
@[simp] theorem T_d : T.d = 1 := rfl

def S_pow (n : ℕ) : SL2N := ⟨1,n,0,1,by {rw[zero_mul,zero_add,one_mul]}⟩ 
def T_pow (n : ℕ) : SL2N := ⟨1,0,n,1,by {rw[mul_zero,zero_add,one_mul]}⟩

@[simp] theorem S_pow_a (n : ℕ) : (S_pow n).a = 1 := rfl
@[simp] theorem S_pow_b (n : ℕ) : (S_pow n).b = n := rfl
@[simp] theorem S_pow_c (n : ℕ) : (S_pow n).c = 0 := rfl
@[simp] theorem S_pow_d (n : ℕ) : (S_pow n).d = 1 := rfl

@[simp] theorem T_pow_a (n : ℕ) : (T_pow n).a = 1 := rfl
@[simp] theorem T_pow_b (n : ℕ) : (T_pow n).b = 0 := rfl
@[simp] theorem T_pow_c (n : ℕ) : (T_pow n).c = n := rfl
@[simp] theorem T_pow_d (n : ℕ) : (T_pow n).d = 1 := rfl

@[simp] theorem S_pow_one : S_pow 1 = S := by {ext; refl,}
@[simp] theorem T_pow_one : T_pow 1 = T := by {ext; refl,}

theorem S_pow_eq : ∀ (n : ℕ), S_pow n = S ^ n 
| 0 := rfl
| (n + 1) := by {
    rw[pow_succ,← S_pow_eq n],ext;
    simp only[mul_a,mul_b,mul_c,mul_d,
              S_a,S_b,S_c,S_d,S_pow_a,S_pow_b,S_pow_c,S_pow_d,
              zero_mul,mul_zero,one_mul,mul_one],}

theorem T_pow_eq : ∀ (n : ℕ), T_pow n = T ^ n 
| 0 := rfl
| (n + 1) := by {
    rw[pow_succ,← T_pow_eq n],ext;
    simp only[mul_a,mul_b,mul_c,mul_d,
              T_a,T_b,T_c,T_d,T_pow_a,T_pow_b,T_pow_c,T_pow_d,
              zero_mul,mul_zero,one_mul,mul_one,add_comm 1 n],}

def ab (m : SL2N) : ℕ := m.a + m.b
def cd (m : SL2N) : ℕ := m.c + m.d

lemma a_pos (m : SL2N) : m.a > 0 :=
begin
 rcases m with ⟨_ | a0,b,c,d,det_prop⟩;
 simp at det_prop ⊢, injection det_prop
end

lemma d_pos (m : SL2N) : m.d > 0 :=
begin
 rcases m with ⟨a,b,c,_ | d0,det_prop⟩;
 simp at det_prop ⊢, injection det_prop
end

def ab_pos (m : SL2N) : 0 < m.ab := nat.add_pos_left m.a_pos _
def cd_pos (m : SL2N) : 0 < m.cd := nat.add_pos_right _ m.d_pos

def aq  (m : SL2N) : ℚ := (m.a  : ℚ)
def bq  (m : SL2N) : ℚ := (m.b  : ℚ)
def cq  (m : SL2N) : ℚ := (m.c  : ℚ)
def dq  (m : SL2N) : ℚ := (m.d  : ℚ)
def abq (m : SL2N) : ℚ := (m.ab : ℚ)
def cdq (m : SL2N) : ℚ := (m.cd : ℚ)

def aq_pos  (m : SL2N) : 0 < m.aq  := int.cast_lt.mpr (int.coe_nat_lt.mpr m.a_pos)
def dq_pos  (m : SL2N) : 0 < m.dq  := int.cast_lt.mpr (int.coe_nat_lt.mpr m.d_pos)
def abq_pos (m : SL2N) : 0 < m.abq := int.cast_lt.mpr (int.coe_nat_lt.mpr m.ab_pos)
def cdq_pos (m : SL2N) : 0 < m.cdq := int.cast_lt.mpr (int.coe_nat_lt.mpr m.cd_pos)

def aq_nz  (m : SL2N) : m.aq  ≠ 0 := (ne_of_lt m.aq_pos ).symm
def dq_nz  (m : SL2N) : m.dq  ≠ 0 := (ne_of_lt m.dq_pos ).symm
def abq_nz (m : SL2N) : m.abq ≠ 0 := (ne_of_lt m.abq_pos).symm
def cdq_nz (m : SL2N) : m.cdq ≠ 0 := (ne_of_lt m.cdq_pos).symm

def au  (m : SL2N) : units ℚ := units.mk0 m.aq  m.aq_nz
def du  (m : SL2N) : units ℚ := units.mk0 m.dq  m.dq_nz
def abu (m : SL2N) : units ℚ := units.mk0 m.abq m.abq_nz
def cdu (m : SL2N) : units ℚ := units.mk0 m.cdq m.cdq_nz

def S_pow_mul (n : ℕ) (m : SL2N) : SL2N  := 
⟨ m.a + n * m.c , m.b + n * m.d,  m.c, m.d, 
  by {rw[mul_add,add_mul,← mul_assoc,mul_comm m.c n,m.det_prop,
         add_assoc,add_assoc,add_comm 1],}⟩ 

@[simp] theorem S_pow_mul_a (n : ℕ) (m : SL2N) : (S_pow_mul n m).a = m.a + n * m.c := rfl
@[simp] theorem S_pow_mul_b (n : ℕ) (m : SL2N) : (S_pow_mul n m).b = m.b + n * m.d := rfl
@[simp] theorem S_pow_mul_c (n : ℕ) (m : SL2N) : (S_pow_mul n m).c = m.c := rfl
@[simp] theorem S_pow_mul_d (n : ℕ) (m : SL2N) : (S_pow_mul n m).d = m.d := rfl

theorem S_pow_mul_eq (n : ℕ) (m : SL2N) : S_pow_mul n m = (S_pow n) * m := 
by {ext;
    simp only[mul_a,mul_b,mul_c,mul_d,
              S_pow_a,S_pow_b,S_pow_c,S_pow_d,
              S_pow_mul_a,S_pow_mul_b,S_pow_mul_c,S_pow_mul_d,
              one_mul,zero_mul,zero_add],}

def T_pow_mul (n : ℕ) (m : SL2N) : SL2N := 
⟨ m.a , m.b, n * m.a + m.c, n * m.b + m.d, 
  by {rw[mul_add,add_mul,← mul_assoc,mul_comm m.a n,m.det_prop,
         add_assoc],}⟩ 

@[simp] theorem T_pow_mul_a (n : ℕ) (m : SL2N) : (T_pow_mul n m).a = m.a := rfl
@[simp] theorem T_pow_mul_b (n : ℕ) (m : SL2N) : (T_pow_mul n m).b = m.b := rfl
@[simp] theorem T_pow_mul_c (n : ℕ) (m : SL2N) : (T_pow_mul n m).c = n * m.a + m.c := rfl
@[simp] theorem T_pow_mul_d (n : ℕ) (m : SL2N) : (T_pow_mul n m).d = n * m.b + m.d := rfl

theorem T_pow_mul_eq (n : ℕ) (m : SL2N) : T_pow_mul n m = (T_pow n) * m := 
by {ext;
    simp only[mul_a,mul_b,mul_c,mul_d,
              T_pow_a,T_pow_b,T_pow_c,T_pow_d,
              T_pow_mul_a,T_pow_mul_b,T_pow_mul_c,T_pow_mul_d,
              one_mul,zero_mul,add_zero],}

theorem S_pow_mul_zero : ∀ (m : SL2N), S_pow_mul 0 m = m := 
 λ ⟨a,b,c,d,dp⟩, by {dsimp[S_pow_mul],ext;simp only[zero_mul,add_zero],}

theorem T_pow_mul_zero : ∀ (m : SL2N), T_pow_mul 0 m = m := 
 λ ⟨a,b,c,d,dp⟩, by {dsimp[T_pow_mul],ext;simp only[zero_mul,zero_add],}

def S_mul : SL2N → SL2N := S_pow_mul  1
def T_mul : SL2N → SL2N := T_pow_mul 1

@[simp] theorem S_mul_a (m : SL2N) : (S_mul m).a = m.a + m.c := 
 by {dsimp[S_mul,S_pow_mul],rw[one_mul]}
@[simp] theorem S_mul_b (m : SL2N) : (S_mul m).b = m.b + m.d := 
 by {dsimp[S_mul,S_pow_mul],rw[one_mul]}
@[simp] theorem S_mul_c (m : SL2N) : (S_mul m).c = m.c := rfl
@[simp] theorem S_mul_d (m : SL2N) : (S_mul m).d = m.d := rfl

@[simp] theorem T_mul_a (m : SL2N) : (T_mul m).a = m.a := rfl
@[simp] theorem T_mul_b (m : SL2N) : (T_mul m).b = m.b := rfl
@[simp] theorem T_mul_c (m : SL2N) : (T_mul m).c = m.a + m.c := 
 by {dsimp[T_mul,S_pow_mul],rw[one_mul]}
@[simp] theorem T_mul_d (m : SL2N) : (T_mul m).d = m.b + m.d := 
 by {dsimp[T_mul,S_pow_mul],rw[one_mul]}

theorem S_mul_eq (m : SL2N) : S_mul m = S * m := 
 by {dsimp[S_mul],rw[S_pow_mul_eq,S_pow_one],}

theorem T_mul_eq (m : SL2N) : T_mul m = T * m := 
 by {dsimp[T_mul],rw[T_pow_mul_eq,T_pow_one],}

theorem db_ca_ineq (m : SL2N) (h : m.d ≤ m.b) : m.c < m.a := 
begin
  let u := m.a - m.c, let v := m.b - m.d, 
  have : m.c * m.d < m.a * m.d :=
    m.det_prop.symm ▸ (lt_of_le_of_lt (nat.mul_le_mul_left m.c h) 
                        (m.c * m.b).lt_succ_self),
  exact (mul_lt_mul_right m.d_pos).mp this,
end

theorem ac_bd_ineq (m : SL2N) (h : m.a ≤ m.c) : m.b < m.d := 
begin
  let u := m.c - m.a, let v := m.d - m.b, 
  have : m.a * m.b < m.a * m.d :=
    m.det_prop.symm ▸ (lt_of_le_of_lt (nat.mul_le_mul_right m.b h) 
                       (m.c * m.b).lt_succ_self),
  exact (mul_lt_mul_left m.a_pos).mp this,
end

theorem S_mul_ineq (m : SL2N) : 
 (S_mul m).d ≤ (S_mul m).b ∧ (S_mul m).c < (S_mul m).a := 
begin
 suffices : (S_mul m).d ≤ (S_mul m).b,
 {exact ⟨this,db_ca_ineq _ this⟩},
 rw[S_mul_b,S_mul_d], exact nat.le_add_left m.d m.b
end

theorem T_mul_ineq (m : SL2N) : 
 (T_mul m).a ≤ (T_mul m).c ∧ (T_mul m).b < (T_mul m).d := 
begin
 suffices : (T_mul m).a ≤ (T_mul m).c,
 {exact ⟨this,ac_bd_ineq _ this⟩},
 rw[T_mul_a,T_mul_c], exact nat.le_add_right m.a m.c
end

def S_div (m : SL2N) (h : m.b ≥ m.d) : SL2N := 
 ⟨m.a - m.c, m.b - m.d, m.c, m.d, by {
  let u := m.a - m.c, let v := m.b - m.d, 
  change u * m.d = m.c * v + 1,
  let hm := m.det_prop,
  have h' := m.db_ca_ineq h,
  have : m.b = m.d + v := (nat.add_sub_of_le h).symm,
  rw[this] at hm,
  have : m.a = m.c + u := (nat.add_sub_of_le (le_of_lt h')).symm,
  rw[this,mul_add,add_mul,add_assoc] at hm,
  exact nat.add_left_cancel hm,
 }⟩ 

def T_div (m : SL2N) (h : m.c ≥ m.a) : SL2N := 
 ⟨m.a, m.b, m.c - m.a, m.d - m.b, by {
  let u := m.c - m.a, let v := m.d - m.b, 
  change m.a * v = u * m.b + 1,
  let hm := m.det_prop,
  have h' := m.ac_bd_ineq h,
  have : m.c = m.a + u := (nat.add_sub_of_le h).symm,
  rw[this] at hm,
  have : m.d = m.b + v := (nat.add_sub_of_le (le_of_lt h')).symm,
  rw[this,mul_add,add_mul,add_assoc] at hm,
  exact nat.add_left_cancel hm,
 }⟩ 

@[simp] theorem S_div_a (m : SL2N) (h) : (S_div m h).a = m.a - m.c := rfl
@[simp] theorem S_div_b (m : SL2N) (h) : (S_div m h).b = m.b - m.d := rfl 
@[simp] theorem S_div_c (m : SL2N) (h) : (S_div m h).c = m.c := rfl
@[simp] theorem S_div_d (m : SL2N) (h) : (S_div m h).d = m.d := rfl

@[simp] theorem T_div_a (m : SL2N) (h) : (T_div m h).a = m.a := rfl
@[simp] theorem T_div_b (m : SL2N) (h) : (T_div m h).b = m.b := rfl 
@[simp] theorem T_div_c (m : SL2N) (h) : (T_div m h).c = m.c - m.a := rfl
@[simp] theorem T_div_d (m : SL2N) (h) : (T_div m h).d = m.d - m.b := rfl

theorem S_div_mul (m : SL2N) (h) : S_div (S_mul m) h = m := 
by {
 ext; simp only[S_mul_a,S_mul_b,S_mul_c,S_mul_d,
                S_div_a,S_div_b,S_div_c,S_div_d,nat.add_sub_cancel]}

theorem T_div_mul (m : SL2N) (h) : T_div (T_mul m) h = m := 
by {
 ext; simp only[T_mul_a,T_mul_b,T_mul_c,T_mul_d,
                T_div_a,T_div_b,T_div_c,T_div_d,
                add_comm m.a,add_comm m.b,nat.add_sub_cancel]}

theorem S_mul_div {m : SL2N} (h) : S_mul (S_div m h) = m := 
by {let h' := le_of_lt (db_ca_ineq m h),
    ext; 
    simp only[S_mul_a,S_mul_b,S_mul_c,S_mul_d,
              S_div_a,S_div_b,S_div_c,S_div_d,
              add_comm,nat.add_sub_of_le h,nat.add_sub_of_le h']}

theorem T_mul_div {m : SL2N} (h) : T_mul (T_div m h) = m := 
by {let h' := le_of_lt (ac_bd_ineq m h),
    ext; 
    simp only[T_mul_a,T_mul_b,T_mul_c,T_mul_d,
              T_div_a,T_div_b,T_div_c,T_div_d,
              add_comm,nat.add_sub_of_le h,nat.add_sub_of_le h']}

theorem S_mul_sizeof (m : SL2N) : sizeof (S_mul m) > sizeof m := 
by {dsimp[sizeof,has_sizeof.sizeof],rw[S_mul_a,S_mul_b],
    apply add_lt_add_right,apply add_lt_add_right,
    rw[add_assoc],apply add_lt_add_left,rw[add_comm,add_assoc],
    exact lt_add_of_pos_right m.b (nat.add_pos_left m.d_pos m.c),}
    
theorem T_mul_sizeof (m : SL2N) : sizeof (T_mul m) > sizeof m := 
by {dsimp[sizeof,has_sizeof.sizeof],rw[T_mul_c,T_mul_d],
    rw[add_assoc (m.a + m.b),add_assoc (m.a + m.b)],
    apply add_lt_add_left,
    rw[add_comm m.a,add_assoc],apply add_lt_add_left,
    rw[← add_assoc],
    exact lt_add_of_pos_left m.d (nat.add_pos_left m.a_pos m.b)}

theorem S_div_sizeof (m : SL2N) (h) : sizeof (S_div m h) < sizeof m := 
 by { rw[← congr_arg sizeof (S_mul_div h)], apply S_mul_sizeof}

theorem T_div_sizeof (m : SL2N) (h) : sizeof (T_div m h) < sizeof m := 
 by { rw[← congr_arg sizeof (T_mul_div h)], apply T_mul_sizeof}

theorem eq_one_iff (m : SL2N) : m = 1 ↔ (m.b < m.d ∧ m.c < m.a) := 
begin
 split; intro h,
 {rw[h,one_a,one_b,one_c,one_d],exact dec_trivial},
 {let u := m.d - (m.b).succ, let v := m.a - (m.c).succ,
  have hu : m.d = m.b + 1 + u := 
   (nat.add_sub_of_le h.left).symm,
  have hv : m.a = m.c + 1 + v := 
   (nat.add_sub_of_le h.right).symm,
  have hd := m.det_prop,
  rw[hu,hv] at hd,
  repeat {rw[mul_add] at hd},repeat {rw[add_mul] at hd},
  repeat {rw[mul_one] at hd},repeat {rw[one_mul] at hd},
  repeat {rw[← add_assoc] at hd},rw[add_comm _ 1,add_comm _ 1] at hd,
  repeat {rw[add_assoc] at hd},
  replace hd := add_left_cancel hd,
  replace hd := add_left_cancel (hd.trans (add_zero _).symm),
  rcases add_eq_zero_iff.mp hd with ⟨eb,hd⟩,
  rw[eb,mul_zero,zero_add] at hd,
  rcases add_eq_zero_iff.mp hd with ⟨ec,hd⟩,
  rw[ec,zero_mul,zero_add] at hd,
  rcases add_eq_zero_iff.mp hd with ⟨ev,hd⟩,
  rw[ev,zero_mul,add_zero] at hd,
  rw[eb,hd,zero_add,add_zero] at hu,
  rw[ec,ev,zero_add,add_zero] at hv,
  ext; simp only[one_a,one_b,one_c,one_d]; assumption,
 }
end

def flip : SL2N →* SL2N := {
  to_fun := λ m, ⟨ m.d,m.c,m.b,m.a, by rw[mul_comm,det_prop,mul_comm]⟩,
  map_one' := by { ext; refl },
  map_mul' := λ m n, 
  by {ext; simp only [mul_a,mul_b,mul_c,mul_d,add_comm] }
}

@[simp] theorem flip_a (m : SL2N) : (flip m).a = m.d := rfl
@[simp] theorem flip_b (m : SL2N) : (flip m).b = m.c := rfl
@[simp] theorem flip_c (m : SL2N) : (flip m).c = m.b := rfl
@[simp] theorem flip_d (m : SL2N) : (flip m).d = m.a := rfl

lemma flip_flip : ∀ (m : SL2N), m.flip.flip = m := 
 λ ⟨a,b,c,d,dp⟩, by {constructor}

lemma flip_S : flip S = T := rfl
lemma flip_T : flip T = S := rfl
lemma flip_S_pow (n : ℕ) : flip (S_pow n) = T_pow n := rfl
lemma flip_T_pow (n : ℕ) : flip (T_pow n) = S_pow n := rfl

lemma flip_S_pow_mul  (n : ℕ) : ∀ (m : SL2N), (S_pow_mul  n m).flip = T_pow_mul n m.flip := 
 λ ⟨a,b,c,d,dp⟩,
  by {dsimp[S_pow_mul,T_pow_mul,flip],ext,
      refl,refl,
      exact add_comm b _,exact add_comm a _}

lemma flip_T_pow_mul (n : ℕ) : ∀ (m : SL2N), (T_pow_mul n m).flip = S_pow_mul n m.flip := 
 λ ⟨a,b,c,d,dp⟩,
  by {dsimp[S_pow_mul,T_pow_mul,flip],ext,
      exact (add_comm d _).symm,exact (add_comm c _).symm,
      refl,refl}

def word := list bool

instance word_monoid : monoid word := {
 one := list.nil,
 mul := list.append,
 mul_assoc := list.append_assoc,
 one_mul := list.nil_append,
 mul_one := list.append_nil
}

def word.to_string : word → string
| list.nil := ""
| (list.cons ff w) := string.append "S" (word.to_string w)
| (list.cons tt w) := string.append "T" (word.to_string w)

instance : has_repr word := ⟨word.to_string⟩

def of_word₀ : word → SL2N
| list.nil := 1
| (list.cons ff w) := S_mul (of_word₀ w) 
| (list.cons tt w) := T_mul (of_word₀ w) 

theorem of_word_append₀ : ∀ (u v : word), 
  of_word₀ (list.append u v) = (of_word₀ u) * (of_word₀ v)
| list.nil v := by {
    have h₀ : (list.append list.nil v = v) := list.nil_append v,
    have h₁ : of_word₀ list.nil = 1 := rfl,
    rw[h₀,h₁,one_mul],}
| (list.cons ff u) v := by {
    rw[list.append,of_word₀,of_word₀,of_word_append₀],
    rw[S_mul_eq,S_mul_eq,mul_assoc],}
| (list.cons tt u) v := by {
    rw[list.append,of_word₀,of_word₀,of_word_append₀],
    rw[T_mul_eq,T_mul_eq,mul_assoc],}

def of_word : word →* SL2N := {
  to_fun := of_word₀,
  map_one' := rfl,
  map_mul' := λ u v, of_word_append₀ u v
}

theorem of_word_nil : of_word list.nil = 1 := rfl
theorem of_word_one : of_word 1 = 1 := rfl

theorem of_word_ff (w : word) : of_word (list.cons ff w) = S_mul (of_word w) := rfl
theorem of_word_tt (w : word) : of_word (list.cons tt w) = T_mul (of_word w) := rfl

def to_word₀ (m : SL2N) : word := 
begin
 let r : SL2N → SL2N → Prop := has_well_founded.r,
 let wf : well_founded r := has_well_founded.wf,
 let C : ∀ (m : SL2N), Type := λ m, word,
 let F : ∀ m, ∀ f : (∀ n (h : r n m), C n), C m := 
 λ m f, by {
  by_cases hb : m.b ≥ m.d,
  {exact ff :: (f (S_div m hb) (S_div_sizeof m hb))},
  by_cases hc : m.c ≥ m.a,
  {exact tt :: (f (T_div m hc) (T_div_sizeof m hc))},
  exact 1
 },
 exact @well_founded.fix SL2N C r wf F m
end

theorem to_word_one₀₀
 {m : SL2N} (hb : ¬ (m.d ≤ m.b)) (hc : ¬ (m.a ≤ m.c)) : to_word₀ m = 1 := 
by {dsimp[to_word₀],rw[well_founded.fix_eq,dif_neg hb,dif_neg hc]}

theorem to_word_one₀ : to_word₀ 1 = 1 :=
 by {apply to_word_one₀₀,exact dec_trivial,exact dec_trivial} 

theorem to_word_S₀ {m : SL2N} (hb : m.d ≤ m.b) : 
 to_word₀ m = ff :: (to_word₀ (S_div m hb)) := 
by {dsimp[to_word₀],rw[well_founded.fix_eq,dif_pos hb]}

theorem to_word_T₀ {m : SL2N} (hc : m.a ≤ m.c) : 
 to_word₀ m = tt :: (to_word₀ (T_div m hc)) := 
by {have hb : ¬ (m.d ≤ m.b) := 
     not_le_of_gt (ac_bd_ineq m hc),
    dsimp[to_word₀],rw[well_founded.fix_eq,dif_neg hb,dif_pos hc]}

theorem to_of_word₀ (w : word) : to_word₀ (of_word w) = w := 
begin
 induction w with b w ih,
 {rw[of_word_nil], exact to_word_one₀},
 cases b,
 {rw[of_word_ff,to_word_S₀ (S_mul_ineq (of_word w)).left,S_div_mul,ih]},
 {rw[of_word_tt,to_word_T₀ (T_mul_ineq (of_word w)).left,T_div_mul,ih]},
end

theorem of_to_word₀ (m : SL2N) : of_word (to_word₀ m) = m := 
begin
 let r : SL2N → SL2N → Prop := has_well_founded.r,
 let wf : well_founded r := has_well_founded.wf,
 let C : ∀ (m : SL2N), Prop := λ m, of_word (to_word₀ m) = m,
 let F : ∀ m, ∀ f : (∀ n (h : r n m), C n), C m := 
 λ m f, by {
  by_cases hb : m.b ≥ m.d,
  {let ih : of_word (to_word₀ (S_div m hb)) = S_div m hb :=
    f (S_div m hb) (S_div_sizeof m hb),
   dsimp[C],rw[to_word_S₀ hb,of_word_ff,ih,S_mul_div hb],
  },
  by_cases hc : m.c ≥ m.a,
  {let n := T_div m hc,
   let ih : of_word (to_word₀ (T_div m hc)) = T_div m hc :=
    f (T_div m hc) (T_div_sizeof m hc),
   dsimp[C],rw[to_word_T₀ hc,of_word_tt,ih,T_mul_div hc],
   },
  {dsimp[C],rw[to_word_one₀₀ hb hc,of_word_one],
   exact ((eq_one_iff m).mpr ⟨(lt_of_not_ge hb),(lt_of_not_ge hc)⟩).symm,
  }
 },
 exact @well_founded.fix SL2N C r wf F m,
end

def to_word : SL2N →* word := {
  to_fun := to_word₀,
  map_one' := to_word_one₀,
  map_mul' := λ m n, by {
  let u := to_word₀ m,
  let v := to_word₀ n,
  change to_word₀ (m * n) = u * v,
  have hm : m = of_word u := (of_to_word₀ m).symm,
  have hn : n = of_word v := (of_to_word₀ n).symm,
  rw[hm,hn,← of_word.map_mul,to_of_word₀],
 }
}

theorem to_word_S {m : SL2N} (hb : m.d ≤ m.b) : 
 to_word m = ff :: (to_word (S_div m hb)) := to_word_S₀ hb

theorem to_word_T {m : SL2N} (hc : m.a ≤ m.c) : 
 to_word m = tt :: (to_word (T_div m hc)) := to_word_T₀ hc

def word_equiv : SL2N ≃* word := {
 to_fun := to_word, inv_fun := of_word,
 map_mul' := to_word.map_mul',
 left_inv := of_to_word₀, 
 right_inv := to_of_word₀
} 

structure P2 : Type := 
(x : nat) (y : nat) (x_pos : x > 0) (y_pos : y > 0) 

namespace P2

@[ext]
theorem ext : ∀ (u₁ u₂ : P2), u₁.x = u₂.x → u₁.y = u₂.y → u₁ = u₂ := 
λ ⟨x₁,y₁,hx₁,hy₁⟩ ⟨x₂,y₂,hx₂,hy₂⟩ hx hy, 
by {simp only [] at *,rcases hx,rcases hy,split; refl}

instance : has_sizeof P2 := ⟨λ u, u.x + u.y⟩

def xp : P2 → ℕ+ := λ u, ⟨u.x,u.x_pos⟩
def yp : P2 → ℕ+ := λ u, ⟨u.y,u.y_pos⟩

theorem xp_val (u : P2) : (u.xp).val = u.x := rfl
theorem yp_val (u : P2) : (u.yp).val = u.y := rfl

instance : has_scalar SL2N P2 := {
 smul := λ m u, 
  ⟨m.a * u.x + m.b * u.y,
   m.c * u.x + m.d * u.y,
   nat.add_pos_left (mul_pos m.a_pos u.x_pos) _,
   nat.add_pos_right _ (mul_pos m.d_pos u.y_pos)⟩
}

theorem smul_x (m : SL2N) (u : P2) : (m • u).x = m.a * u.x + m.b * u.y := rfl
theorem smul_y (m : SL2N) (u : P2) : (m • u).y = m.c * u.x + m.d * u.y := rfl

theorem S_smul_x (u : P2) : (S • u).x = u.x + u.y := 
 by {change 1 * u.x + 1 * u.y = u.x + u.y,rw[one_mul,one_mul],}
theorem S_smul_y (u : P2) : (S • u).y = u.y := 
 by {change 0 * u.x + 1 * u.y = u.y,rw[zero_mul,one_mul,zero_add],}

theorem T_smul_x (u : P2) : (T • u).x = u.x := 
 by {change 1 * u.x + 0 * u.y = u.x,rw[zero_mul,one_mul,add_zero],}
theorem T_smul_y (u : P2) : (T • u).y = u.x + u.y := 
 by {change 1 * u.x + 1 * u.y = u.x + u.y,rw[one_mul,one_mul],}

instance : mul_action SL2N P2 := {
 smul := has_scalar.smul,
 one_smul := λ u,
  by {ext; simp only [smul_x,smul_y,one_a,one_b,one_c,one_d,
                      one_mul,zero_mul,zero_add,add_zero],},
 mul_smul := λ m n u,
  by {ext,
   {rw[smul_x,smul_x,smul_x,smul_y,
       mul_a,mul_b,add_mul,add_mul,mul_add,mul_add,
       mul_assoc,mul_assoc,mul_assoc,mul_assoc,
       add_assoc,add_assoc],
    congr' 1,rw[← add_assoc,← add_assoc],
    congr' 1,rw[add_comm]},
   {rw[smul_y,smul_y,smul_y,smul_x,
       mul_c,mul_d,add_mul,add_mul,mul_add,mul_add,
       mul_assoc,mul_assoc,mul_assoc,mul_assoc,
       add_assoc,add_assoc],
    congr' 1,rw[← add_assoc,← add_assoc],
    congr' 1,rw[add_comm]},
  }
}

def S_sdiv {u : P2} (h : u.y < u.x) : P2 := 
 {x := u.x - u.y, y := u.y, x_pos := nat.sub_pos_of_lt h, y_pos := u.y_pos}

def T_sdiv {u : P2} (h : u.x < u.y) : P2 := 
 {x := u.x, y := u.y - u.x, x_pos := u.x_pos, y_pos := nat.sub_pos_of_lt h}

@[simp] theorem S_sdiv_x {u : P2} (h) : (@S_sdiv u h).x = u.x - u.y := rfl
@[simp] theorem S_sdiv_y {u : P2} (h) : (@S_sdiv u h).y = u.y := rfl
@[simp] theorem T_sdiv_x {u : P2} (h) : (@T_sdiv u h).x = u.x := rfl
@[simp] theorem T_sdiv_y {u : P2} (h) : (@T_sdiv u h).y = u.y - u.x := rfl

theorem S_sdiv_smul (u : P2) (h) : @S_sdiv (S • u) h = u := 
 by {ext, rw[S_sdiv_x,S_smul_x,S_smul_y,nat.add_sub_cancel],rw[S_sdiv_y,S_smul_y],}

theorem T_sdiv_smul (u : P2) (h) : @T_sdiv (T • u) h = u := 
 by {ext, rw[T_sdiv_x,T_smul_x],rw[T_sdiv_y,T_smul_y,T_smul_x,add_comm,nat.add_sub_cancel],}

theorem S_smul_sdiv (u : P2) (h) : S • (@S_sdiv u h) = u := 
 by {ext,rw[S_smul_x,S_sdiv_x,S_sdiv_y,nat.sub_add_cancel (le_of_lt h)],
         rw[S_smul_y,S_sdiv_y]}

theorem T_smul_sdiv (u : P2) (h) : T • (@T_sdiv u h) = u := 
 by {ext,rw[T_smul_x,T_sdiv_x],
         rw[T_smul_y,T_sdiv_x,T_sdiv_y,add_comm,nat.sub_add_cancel (le_of_lt h)]}

theorem S_sdiv_sizeof {u : P2} (h) : sizeof (@S_sdiv u h) < sizeof u := 
 by { change (u.x - u.y) + u.y < u.x + u.y, rw[nat.sub_add_cancel (le_of_lt h)],
      exact lt_add_of_pos_right u.x u.y_pos}

theorem T_sdiv_sizeof {u : P2} (h) : sizeof (@T_sdiv u h) < sizeof u := 
 by { change u.x + (u.y - u.x) < u.x + u.y, rw[add_comm,nat.sub_add_cancel (le_of_lt h)],
      exact lt_add_of_pos_left u.y u.x_pos}

def xgcd_aux (mu : SL2N × P2) : SL2N × P2 := 
begin
 let r : (SL2N × P2) → (SL2N × P2) → Prop := measure (λ mu,sizeof mu.2),
 have r_iff : ∀ nv mu, r nv mu ↔ nv.2.x + nv.2.y < mu.2.x + mu.2.y := 
  by {intros, refl}, 
 let wf : well_founded r := measure_wf _,
 let C : ∀ (mu : SL2N × P2), Type := λ mu, SL2N × P2,
 let F : ∀ mu, ∀ f : (∀ nv (h : r nv mu), C nv), C mu := 
 λ mu f, by {
  by_cases hyx : mu.2.y < mu.2.x,
  {exact f ⟨mu.1 * S,S_sdiv hyx⟩ (S_sdiv_sizeof hyx)},
  by_cases hxy : mu.2.x < mu.2.y,
  {exact f ⟨mu.1 * T,T_sdiv hxy⟩ (T_sdiv_sizeof hxy)},
  exact mu
 },
 exact @well_founded.fix (SL2N × P2) C r wf F mu
end

theorem xgcd_aux_S {mu : SL2N × P2} (h : mu.2.y < mu.2.x) : 
 xgcd_aux mu = xgcd_aux ⟨mu.1 * S,S_sdiv h⟩ := 
  by {dsimp[xgcd_aux],rw[well_founded.fix_eq,dif_pos h],}

theorem xgcd_aux_T {mu : SL2N × P2} (h : mu.2.x < mu.2.y) : 
 xgcd_aux mu = xgcd_aux ⟨mu.1 * T,T_sdiv h⟩ := 
  by {dsimp[xgcd_aux],
      rw[well_founded.fix_eq,dif_neg (not_lt_of_gt h),dif_pos h],}

theorem xgcd_aux_end {mu : SL2N × P2} (h : mu.2.x = mu.2.y) :
 xgcd_aux mu = mu :=  
  by {dsimp[xgcd_aux],rw[well_founded.fix_eq],
      have : ¬ (mu.2.y < mu.2.x) := by {rw[h],exact lt_irrefl _},
      rw[dif_neg this],
      have : ¬ (mu.2.x < mu.2.y) := by {rw[h],exact lt_irrefl _},
      rw[dif_neg this]}

def smul' (mu : SL2N × P2) : P2 := mu.1 • mu.2

theorem xgcd_aux_spec (mu : SL2N × P2) : 
 smul' (xgcd_aux mu) = smul' mu ∧ ((xgcd_aux mu).2.x = (xgcd_aux mu).2.y) := 
begin
 let r : (SL2N × P2) → (SL2N × P2) → Prop := measure (λ mu,sizeof mu.2),
 have r_iff : ∀ nv mu, r nv mu ↔ nv.2.x + nv.2.y < mu.2.x + mu.2.y := 
  by {intros, refl}, 
 let wf : well_founded r := measure_wf _,
 let C : ∀ (mu : SL2N × P2), Prop := λ mu,
  smul' (xgcd_aux mu) = smul' mu ∧ ((xgcd_aux mu).2.x = (xgcd_aux mu).2.y),
 let F : ∀ mu, ∀ f : (∀ nv (h : r nv mu), C nv), C mu := 
 λ mu f, by {
  by_cases hyx : mu.2.y < mu.2.x,
  {rcases f ⟨mu.1 * S,S_sdiv hyx⟩ (S_sdiv_sizeof hyx) with ⟨h_smul,h_u⟩,
   split; rw[xgcd_aux_S hyx],
   {rw[h_smul,smul',smul',mul_smul,S_smul_sdiv]},{rw[h_u]}},
  by_cases hxy : mu.2.x < mu.2.y,
  {rcases f ⟨mu.1 * T,T_sdiv hxy⟩ (T_sdiv_sizeof hxy) with ⟨h_smul,h_u⟩,
   split; rw[xgcd_aux_T hxy],
   {rw[h_smul,smul',smul',mul_smul,T_smul_sdiv]},{rw[h_u]}},
  have := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy),
  split; rw[xgcd_aux_end this], exact this,  
 }, 
 exact @well_founded.fix (SL2N × P2) C r wf F mu,
end

def xgcd (u : P2) := xgcd_aux ⟨1,u⟩

def gcd (u : P2) := (xgcd u).2.x
def gcd_a (u : P2) := (xgcd u).1.a
def gcd_b (u : P2) := (xgcd u).1.b
def gcd_c (u : P2) := (xgcd u).1.c
def gcd_d (u : P2) := (xgcd u).1.d

theorem gcd_pos (u : P2) : (gcd u) > 0 := (xgcd u).2.x_pos
theorem gcd_a_pos (u : P2) : (gcd_a u) > 0 := (xgcd u).1.a_pos
theorem gcd_d_pos (u : P2) : (gcd_d u) > 0 := (xgcd u).1.d_pos

/- The next two theorems show that (gcd u) is a common divisor of
   u.x and u.y
-/

theorem gcd_x_eq (u : P2) : u.x = (gcd_a u + gcd_b u) * gcd u := by {
 rcases xgcd_aux_spec ⟨1,u⟩ with ⟨h_smul,h_xy⟩,
 rw[smul',smul',one_smul] at h_smul,
 have := congr_arg P2.x h_smul,
 rw[smul_x,h_xy.symm,← add_mul] at this,exact this.symm,
}

theorem gcd_y_eq (u : P2) : u.y = (gcd_c u + gcd_d u) * gcd u := by {
 rcases xgcd_aux_spec ⟨1,u⟩ with ⟨h_smul,h_xy⟩,
 rw[smul',smul',one_smul] at h_smul,
 have := congr_arg P2.y h_smul,
 rw[smul_y,h_xy.symm,← add_mul] at this,exact this.symm,
}

def gcd_det_prop (u : P2) : (gcd_a u) * (gcd_d u) = (gcd_c u) * (gcd_b u) + 1 := 
 (xgcd u).1.det_prop

/-
 Either of the next two theorems proves that (gcd u) is an integral
 linear combination of u.x and u.y, so it really is the gcd.
-/
theorem gcd_eq (u : P2) : gcd u + (gcd_b u) * u.y = (gcd_d u) * u.x := 
 by {symmetry,
     rw[← one_mul (gcd u),add_comm,gcd_x_eq,gcd_y_eq,
        ← mul_assoc,← mul_assoc,← add_mul],congr' 1,
      rw[mul_add,mul_add,mul_comm,gcd_det_prop u,mul_comm],
      rw[add_assoc,add_assoc,add_comm 1,mul_comm (gcd_d u)],}

theorem gcd_eq' (u : P2) : gcd u + (gcd_c u) * u.x = (gcd_a u) * u.y := 
 by {symmetry,
     rw[← one_mul (gcd u),add_comm,gcd_x_eq,gcd_y_eq,
        ← mul_assoc,← mul_assoc,← add_mul],congr' 1,
      rw[mul_add,mul_add,mul_comm,gcd_det_prop u,mul_comm,add_assoc]}

theorem is_gcd (u : P2) : ∀ n : ℕ, n ∣ gcd u ↔ (n ∣ u.x ∧ n ∣ u.y) := 
begin
 intro n,split,
 {intro h,split,
  {rw[gcd_x_eq u],exact dvd_mul_of_dvd_right h _},
  {rw[gcd_y_eq u],exact dvd_mul_of_dvd_right h _}},
 {rintro ⟨hx,hy⟩,
  have h₀ : n ∣ gcd u + (gcd_b u) * u.y := 
   by {rw[gcd_eq u],exact dvd_mul_of_dvd_right hx _},
  have h₁ : n ∣ (gcd_b u) * u.y := dvd_mul_of_dvd_right hy _,
  exact (nat.dvd_add_left h₁).mp h₀,
 }
end

end P2

end SL2N
