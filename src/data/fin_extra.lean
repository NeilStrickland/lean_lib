/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

 Recall that (fin n) is the type of pairs ⟨i,h⟩, where i is a natural
 number and h is a proof that i < n.  In this file we prove some 
 additional facts about these types, which might perhaps be added 
 to the standard library at some point. 
-/

import data.list data.fintype.basic data.finset.interval data.fin.interval

namespace fin
open fin finset

def reflect : ∀ {n : ℕ} (i : fin n), fin n
| 0 i := fin.elim0 i
| (n + 1) i := ⟨n - i, nat.lt_succ_of_le (nat.sub_le n i)⟩  

@[simp] lemma coe_reflect : ∀ {n : ℕ} (i : fin n), (i.reflect : ℕ) = n - 1 - i
| 0 i := fin.elim0 i
| (n + 1) i := by { change n - i = _, simp }

@[simp] lemma reflect_val {n : ℕ} (i : fin n) : i.reflect.val = n - 1 - i := 
  coe_reflect i

lemma reflect_reflect : ∀ {n : ℕ} (i : fin n), i.reflect.reflect = i
| 0 i := fin.elim0 i
| (n + 1) ⟨i,h⟩ := 
begin
  rw [fin.ext_iff], 
  let j := n - i,
  change n - j = i,
  have : n = i + j := (nat.add_sub_of_le (nat.le_of_lt_succ h)).symm,
  rw [this, nat.add_sub_cancel]
end

lemma add_reflect : ∀ {n : ℕ} (i : fin n), (i : ℕ) + (i.reflect : ℕ) + 1 = n
| 0 i := fin.elim0 i
| (n + 1) ⟨i,h⟩ := 
begin
  let j := n - i,
  change i + j + 1 = n + 1,
  rw [(nat.add_sub_of_le (nat.le_of_lt_succ h)).symm]
end

lemma reflect_le : ∀ {n : ℕ} {i j : fin n} (h : i ≤ j), j.reflect ≤ i.reflect 
| 0 i _ _ := i.elim0
| (n + 1) ⟨i,hi⟩ ⟨j,hj⟩ hij := nat.sub_le_sub_left n hij

lemma reflect_lt {n : ℕ} {i j : fin n} (h : i < j) : j.reflect < i.reflect := 
begin
  apply lt_of_not_ge, intro hr, replace hr := reflect_le hr,
  rw [reflect_reflect, reflect_reflect] at hr,
  exact not_lt_of_ge hr h
end

def inc {n : ℕ} : fin n → fin n.succ := 
  λ i, ⟨i.val, lt_trans i.is_lt n.lt_succ_self⟩ 

@[simp] lemma coe_inc {n : ℕ} (i : fin n) : (i.inc : ℕ) = (i : ℕ) := rfl
@[simp] lemma inc_val {n : ℕ} (i : fin n) :  i.inc.val  = i.val := rfl

lemma reflect_inc {n : ℕ} (i : fin n) : i.inc.reflect = i.reflect.succ :=
begin
  cases n, exact fin.elim0 i, apply fin.eq_of_veq,
  change (n + 1) - i = (n - i) + 1, 
  exact nat.succ_sub (nat.le_of_lt_succ i.is_lt)
end

lemma reflect_succ {n : ℕ} (i : fin n) : i.succ.reflect = i.reflect.inc :=
begin
  let h := congr_arg fin.reflect (reflect_inc (i.reflect)),
  rw [reflect_reflect, reflect_reflect] at h,
  exact h.symm
end

lemma inc_lt_succ {n : ℕ} (i : fin n) : i.inc < i.succ := 
 by { cases i with i₀ hi, exact i₀.lt_succ_self }

def res {n : ℕ} {i : fin n} {j : fin n.succ} (h : (j : ℕ) ≤ (i : ℕ)) : 
  fin n := ⟨j.val, lt_of_le_of_lt h i.is_lt⟩

@[simp] lemma coe_res {n : ℕ} {i : fin n} {j : fin n.succ} (h : (j : ℕ) ≤ (i : ℕ)) : 
  (res h : ℕ) = (j : ℕ) := rfl
@[simp] lemma res_val {n : ℕ} {i : fin n} {j : fin n.succ} (h : (j : ℕ) ≤ (i : ℕ)) : 
  (res h).val = j.val := rfl

def trunc {n : ℕ} (i : fin (n + 2)) : fin (n + 1) := 
  dite ((i : ℕ) < n + 1) (λ h, fin.mk i h) (λ h, fin.mk n n.lt_succ_self)

@[simp] lemma coe_trunc {n : ℕ} (i : fin (n + 2)) : 
  (trunc i : ℕ) = if (i : ℕ)  < n + 1 then i else n := 
by { rw [trunc], split_ifs; refl }
@[simp] lemma trunc_val {n : ℕ} (i : fin (n + 2)) : 
  (trunc i).val = if (i : ℕ)  < n + 1 then i.val else n := coe_trunc _

def pred' {n : ℕ} (i : fin (n + 2)) : fin (n + 1) := 
  ⟨i.val.pred, begin have hi : i.val < n + 2 := i.is_lt, cases i.val with i₀, 
    { rw [nat.pred_zero], exact nat.zero_lt_succ n },
    { rw [nat.pred_succ], exact nat.lt_of_succ_lt_succ hi }
  end⟩ 

@[simp] lemma coe_pred' {n : ℕ} (i : fin (n + 2)) :
  (i.pred' : ℕ) = (i : ℕ).pred := rfl

lemma coe_inj {n : ℕ} {i j : fin n} (h : (i : ℕ) = (j : ℕ)) : i = j := 
fin.eq_of_veq h

def pred_alt {n : ℕ} {i : ℕ} (h : i.succ < n.succ) : fin n :=
 ⟨i,nat.lt_of_succ_lt_succ h⟩

/- Zero is not a successor -/
lemma zero_ne_succ : ∀ {n : ℕ} {i : fin n}, (0 : fin n.succ) ≠ i.succ
| n ⟨i_val,_⟩ := λ e, nat.no_confusion (congr_arg subtype.val e)

/- Zero is less than any successor -/
lemma zero_lt_succ : ∀ {n : ℕ} {i : fin n}, (0 : fin n.succ) < i.succ
| n ⟨i_val,_⟩ := nat.zero_lt_succ i_val

/- The successor map preserves order -/
lemma succ_le_succ {n : ℕ} {i j : fin n} (h : i ≤ j) : i.succ ≤ j.succ := 
 by {cases i,cases j,dsimp[has_le.le,fin.le],apply nat.succ_le_succ h,}

/- The successor map preserves strict order -/
lemma succ_lt_succ {n : ℕ} {i j : fin n} (h : i < j) : i.succ < j.succ := 
 by {cases i,cases j,dsimp[has_lt.lt,fin.lt],apply nat.succ_lt_succ h,}

/- The successor map reflects order -/
lemma le_of_succ_le_succ {n : ℕ} {i j : fin n} (h : i.succ ≤ j.succ) : i ≤ j := 
 by {cases i,cases j,dsimp[has_le.le,fin.le],apply nat.le_of_succ_le_succ h,}

/- The successor map reflects strict order -/
lemma lt_of_succ_lt_succ {n : ℕ} {i j : fin n} (h : i.succ < j.succ) : i < j := 
 by {cases i,cases j,dsimp[has_lt.lt,fin.lt],apply nat.lt_of_succ_lt_succ h,}

/- Nothing is less than zero -/
lemma not_lt_zero {n : ℕ} (i : fin n.succ) : ¬ i < 0 := 
 by {cases i,dsimp[has_lt.lt,fin.lt],exact nat.not_lt_zero i_val,}

/- This function produces a list of all the elements of (fin n) -/
def elems_list : ∀ (n : ℕ), list (fin n)
| 0 := @list.nil _
| (n + 1) := list.cons 0 ((elems_list n).map fin.succ)

/-The number of elements of (fin n) is n -/
lemma elems_list_length : ∀ (n : ℕ), (elems_list n).length = n 
| 0 := rfl
| (n + 1) := congr_arg nat.succ
             ((list.length_map fin.succ (elems_list n)).trans
              (elems_list_length n))

/- The list of elements has no duplicates -/
def elems_list_nodup : ∀ (n : ℕ), list.nodup (elems_list n)
| 0 := @list.pairwise.nil _ ne
| (n + 1) := begin
  let old_list := (elems_list n).map fin.succ,
  have h : function.injective (fin.succ : (fin n) → (fin (n + 1))) := 
   λ _ _ e, fin.succ_inj.mp e,
  have old_nodup : list.nodup old_list :=
   list.nodup_map h (elems_list_nodup n),
  have not_mem_old : ∀ k ∈ old_list, (0 : fin n.succ) ≠ k := 
  begin
   intros k k_in_old zero_eq_k,
   let h1 := (list.mem_map.mp k_in_old),
   exact exists.elim h1 (λ k0 h2,zero_ne_succ (zero_eq_k.trans h2.right.symm)),
  end,
  exact list.pairwise.cons (not_mem_old) (old_nodup)
 end

/- Every element occurs in our list of elements -/
def elems_list_complete {n : ℕ} (k : fin n) : k ∈ (elems_list n) :=
begin
 induction n with n0 ih,
 {exact fin.elim0 k,},
 {dsimp[elems_list],
  rw[list.mem_cons_eq],
  cases k with k_val k_is_lt,
  cases k_val with k0_val,
  {left,apply fin.eq_of_veq,refl,},
  {have k0_is_lt : k0_val < n0 := nat.lt_of_succ_lt_succ k_is_lt,
   let k0 : fin n0 := ⟨k0_val,k0_is_lt⟩,
   have h0 : k0.succ = ⟨k0_val.succ,k_is_lt⟩ := 
   by {apply fin.eq_of_veq,refl,},
   right,
   apply list.mem_map.mpr,
   existsi k0,
   exact ⟨ih k0,h0⟩,
  }
 }
end

/- Convert our list of elements to a set -/
def elems_finset (n : ℕ) : finset (fin n) :=
{ val := elems_list n,
  nodup := elems_list_nodup n
}

/- Every element is in our set of elements -/
def elems_finset_complete {n : ℕ} (k : fin n) : k ∈ (elems_finset n) :=
 elems_list_complete k

/- 
 This function returns the least element of (fin n) satisfying a given 
 predicate p.  For this to work, we need a decision procedure for p
 (given as an implicit typeclass argument) and also a proof that at 
 least one element of (fin n) satisfies p.  Moreover, we return the
 least element k packaged together with proofs of its properties.
 Thus, if this function returns x, then x.val is the relevant value
 of k, and x.property.left is a proof of (p k), and x.property.right
 is a proof that k is minimal with respect to this.
-/
def least_element {n : ℕ} (p : fin n → Prop) [d : decidable_pred p] (e : ∃ k, p k) :
 {k : fin n // p k ∧ ∀ j, p j → k ≤ j} :=
begin
 tactic.unfreeze_local_instances,
 induction n with n0 ih,
 {exfalso, cases e with i _,exact fin.elim0 i,},
 {
   by_cases pz : (p 0),
    {exact ⟨0, pz, λ j _,fin.zero_le j⟩}, 
    {let p0 : fin n0 → Prop := λ k0, p k0.succ,
     let d0 : decidable_pred p0 := λ k0, d k0.succ,
     have e0 : ∃ k0, p0 k0 :=
      begin
       rcases e with ⟨⟨k_val,k_is_lt⟩,p_k⟩,
       rcases k_val with _ | k0_val,
        {contradiction},
        {have k0_is_lt : k0_val < n0 := nat.lt_of_succ_lt_succ k_is_lt,
         let k0 : fin n0 := ⟨k0_val,k0_is_lt⟩,
         existsi k0,assumption
        }  
      end,
     rcases (@ih p0 d0 e0) with ⟨k0,p0_k0,k0_min⟩,
     let k := fin.succ k0,
     have p_k : p k := p0_k0, 
     have k_min : ∀ j, p j → k ≤ j := 
     begin
      intro j,
      cases j with j_val j_is_lt,rcases j_val with _ | j0_val;
       simp[has_le.le,fin.le],
      {intro pz0, exact false.elim (pz pz0),},
      {have j0_is_lt : j0_val < n0 := nat.lt_of_succ_lt_succ j_is_lt,
       let j0 : fin n0 := ⟨j0_val,j0_is_lt⟩,
       intro p0_j0,
       exact nat.succ_le_succ (k0_min j0 p0_j0),
       }
     end,
     exact ⟨k,p_k,k_min⟩ 
    }
 }
end

/-
 This is essentially the same as the previous function, but formulated
 in terms of a finite subset of (fin n) rather than a predicate.
-/
def finset_least_element {n : ℕ} (s : finset (fin n)) (e : s.nonempty) : 
 {k : fin n // k ∈ s ∧ ∀ j, j ∈ s → k ≤ j} :=
  least_element (λ k,k ∈ s) (nonempty.bex e)

/-
 We now have a similar function for finding the largest element of 
 a finite subset of (fin n).  For technical reasons we have found it
 more convenient to do this directly with finite sets rather than 
 predicates.

 I am not sure why Lean thinks this is noncomputable
-/
noncomputable def finset_largest_element {n : ℕ} (s : finset (fin n)) (e : s.nonempty) :
 {k : fin n // k ∈ s ∧ ∀ j, j ∈ s → j ≤ k} :=
begin
 tactic.unfreeze_local_instances,
 induction n with n0 ih,
 {exfalso,
  cases (nonempty.bex e) with i _,
  exact fin.elim0 i,},
 {let s0 := univ.filter (λ i0 : fin n0, i0.succ ∈ s),
  by_cases e0 : s0.nonempty,
  {rcases (ih s0 e0) with ⟨⟨k0_val,k0_is_lt⟩,⟨k0_in_s0,k0_max⟩⟩,
   let k0 : fin n0 := ⟨k0_val,k0_is_lt⟩,
   let k := k0.succ,
   let k_in_s : k ∈ s := (mem_filter.mp k0_in_s0).right,
   let k_max : ∀ j, j ∈ s → j ≤ k := begin
    intros j j_in_s,
    cases j with j_val j_is_lt, cases j_val with j0_val,
    {exact fin.zero_le k,},
    {have j0_is_lt : j0_val < n0 := nat.lt_of_succ_lt_succ j_is_lt,
     let j0 : fin n0 := ⟨j0_val,j0_is_lt⟩,
     have j0_in_s0 : j0 ∈ s0 := mem_filter.mpr ⟨mem_univ j0,j_in_s⟩,
     dsimp[has_le.le,fin.le,k,fin.succ],
     exact nat.succ_le_succ (k0_max j0 j0_in_s0),
    }
   end,
   exact ⟨k,⟨k_in_s,k_max⟩⟩,
  },{
   let z : fin n0.succ := 0,
   have zero_in_s : z ∈ s := begin 
    let h : ∀ k, k ∈ s → z ∈ s := begin
     intro k,cases k with k_val k_is_lt,cases k_val with k0_val,
     {intro z_in_s,exact z_in_s,},
     {intro k_in_s,exfalso,
      have k0_is_lt : k0_val < n0 := nat.lt_of_succ_lt_succ k_is_lt,
      let k0 : fin n0 := ⟨k0_val,k0_is_lt⟩,
      have k0_in_s0 : k0 ∈ s0 := mem_filter.mpr ⟨mem_univ k0,k_in_s⟩,
      exact e0 ⟨k0,k0_in_s0⟩,
     }
    end,
    exact exists.elim (nonempty.bex e) h,
   end,
   have zero_max : ∀ j, j ∈ s → j ≤ z := 
   begin
    intros j j_in_s,
    cases j with j_val j_is_lt, cases j_val with j0_val,
    {exact fin.zero_le z},
    {exfalso,
     have j0_is_lt : j0_val < n0 := nat.lt_of_succ_lt_succ j_is_lt,
     let j0 : fin n0 := ⟨j0_val,j0_is_lt⟩,
     have j0_in_s0 : j0 ∈ s0 := mem_filter.mpr ⟨mem_univ j0,j_in_s⟩,
     exact e0 ⟨j0,j0_in_s0⟩,
    }
   end,
   exact ⟨z,zero_in_s,zero_max⟩,
  }
 }
end

def fin.list_Ico {n : ℕ} (i : fin n) (j : fin n.succ) : 
  list (fin n) := (list.Ico i j).attach.map 
   (λ x, ⟨x.val,lt_of_lt_of_le (list.Ico.mem.mp x.property).right
                               (nat.le_of_lt_succ j.is_lt)⟩)

end fin

