/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

 If J is a finite set then the sum of (-1)^{|K|} over subsets K ⊆ J
 is usually zero, except that the sum is one if J is empty.

 We will prove two versions of this, one where J is a finset in an 
 arbitrary type I, and one where J is the universal set in a fintype I.

 A key point is as follows: if we take J' = (insert a J) = J ∪ {a},
 then the subsets of J can be split into those that contain a and those
 that do not, and these two families are in bijection.  Equivalently, 
 we have a bijection P(J') ≃ P(J) × bool (where bool is a set with 
 two elements).  We construct this bijection as 
 `finset.insert.powerset_filter`.
-/

import data.fintype.basic algebra.big_operators
import algebra.prod_equiv

namespace finset
open finset

universe u

variables {I : Type u} [decidable_eq I]

def card_sign (K : finset I) : ℤ := (-1) ^ K.card
def card_sign_sum (J : finset I) := J.powerset.sum (card_sign : finset I → ℤ)

section insert 

variables {i : I} {J : finset I} (hiJ : i ∉ J)
include hiJ

example (n : ℤ) : n * (-1) = - n := by library_search

lemma insert.card_sign :
 card_sign (insert i J) = - card_sign J := 
 by {dsimp[card_sign],
     rw[card_insert_of_not_mem hiJ,pow_add,pow_one,mul_neg_one] }

lemma subset_iff_subset_insert (K : finset I) :
 K ⊆ J ↔ K ⊆ (insert i J) ∧ i ∉ K := 
begin
 split,
 {exact λ hKJ,⟨subset.trans hKJ (subset_insert i J),λ i_in_K,hiJ (hKJ i_in_K)⟩},
 {rintros ⟨hKiJ,hi⟩ a ha,
  rcases mem_insert.mp (hKiJ ha) with a_eq_i | a_in_J,
  {exact (hi (a_eq_i ▸ ha)).elim},{exact a_in_J}
 }
end

lemma insert.powerset_filter : 
 (insert i J).powerset.filter (λ K, i ∉ K) = J.powerset := by {
  ext K,rw[mem_filter,mem_powerset,mem_powerset,subset_iff_subset_insert hiJ],
 } 

def insert.powerset_equiv : 
 { K // K ∈ (insert i J).powerset} ≃ ({K // K ∈ J.powerset} × bool) := {
 to_fun := λ K, ⟨⟨K.val ∩ J,mem_powerset.mpr (inter_subset_right K.val J)⟩,
                 if i ∈ K.val then tt else ff⟩,
 inv_fun := λ Kb, cond Kb.2
  ⟨insert i Kb.1.val,
   mem_powerset.mpr (insert_subset_insert i (mem_powerset.mp Kb.1.property))⟩ 
  ⟨Kb.1.val,
   mem_powerset.mpr (subset.trans (mem_powerset.mp Kb.1.property) (subset_insert i J))⟩,
 left_inv := λ ⟨K,hK⟩,
 begin
  let hK' := mem_powerset.mp hK,
  apply subtype.eq,ext a,simp only [],split_ifs,
  {rw[cond,mem_insert,mem_inter],
   split,
   {rintro (a_eq_i | h2),exact a_eq_i.symm.subst h,exact h2.left},
   {intro a_in_K,
    rcases mem_insert.mp (hK' a_in_K) with a_eq_i | a_in_J,
    {exact or.inl a_eq_i},
    {exact or.inr ⟨a_in_K,a_in_J⟩}
   }
  },{
   rw[cond,mem_inter],
   split,
   {exact λ h,h.1},
   {intro a_in_K,
    exact ⟨a_in_K,((subset_iff_subset_insert hiJ K).mpr ⟨hK',h⟩) a_in_K⟩,
   }
  }
 end,
 right_inv := λ ⟨⟨K,hK⟩,b⟩,
 begin
  let hK' := mem_powerset.mp hK,
  have hiK : i ∉ K := λ h, hiJ (hK' h),
  cases b; simp only[cond],
  {rw[if_neg hiK],congr,ext a,rw[mem_inter],
   exact ⟨λ h,h.1,λ h,⟨h,hK' h⟩⟩,
  },{
   rw[if_pos (mem_insert_self i K)],congr,ext a,rw[mem_inter,mem_insert],
   split,
   {rintro ⟨a_eq_i | a_in_K,a_in_J⟩,
    {exact (hiJ (a_eq_i ▸ a_in_J)).elim,},
    {exact a_in_K}
   },{
    intro a_in_K,
    exact ⟨or.inr a_in_K,hK' a_in_K⟩
   }
  }
 end
}

lemma card_sign_sum_insert : card_sign_sum (insert i J) = 0 := 
begin 
 let e := (insert.powerset_equiv hiJ).symm,
 rw[card_sign_sum,sum_eq_univ_sum],
 rw[← univ_sum_equiv e (λ K,card_sign K.val)],
 let g : {K // K ∈ J.powerset} → bool → ℤ := 
  λ K b, cond b (- (card_sign K.val)) (card_sign K.val),
 have eg : ∀ K, (@univ bool _).sum (g K) = 0 := 
  λ K, by {rw[sum_over_bool],dsimp[g],rw[add_neg_self]},
 have : (λ (K : {K // K ∈ powerset (insert i J)}), (card_sign K.val)) ∘ e.to_fun = 
        λ Kb, g Kb.1 Kb.2 := 
  by {ext Kb,rcases Kb with ⟨⟨K,hK⟩,ff | tt⟩,
   {refl},
   {have : i ∉ K := λ h, hiJ ((mem_powerset.mp hK) h),
    exact insert.card_sign this}
  },
 rw[this,sum_univ_product,sum_congr rfl (λ K _,eg K),sum_const_zero],
end

end insert

#check finset.nonempty
lemma card_sign_sum_eq (J : finset I) : card_sign_sum J = if J = ∅ then 1 else 0 := 
begin
 split_ifs with h,
 {rw[h],refl},
 { rcases (nonempty_of_ne_empty h) with ⟨a,a_in_J⟩,
  rw[← insert_erase a_in_J,card_sign_sum_insert (not_mem_erase a J)],
 }
end

end finset

namespace fintype
open finset

lemma card_sign_sum_eq (I : Type*) [decidable_eq I] [fintype I] : 
 (@univ I _).powerset.sum card_sign = if (card I = 0) then 1 else 0 := 
begin 
 change (@univ I _).card_sign_sum  = if (card I = 0) then 1 else 0,
 let h := @finset.card_eq_zero I univ,
 rw[finset.card_sign_sum_eq,← card_univ],
 by_cases hu : (@univ I _).card = 0,
 rw[if_pos hu,if_pos (h.mp hu)],
 rw[if_neg hu,if_neg (hu ∘ h.mpr)],
end

end fintype

