/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file contains various addenda to algebra/big_operators.
One issue is that I often prefer to work with fintypes and 
sums/products over all of univ, and it is helpful to have some 
lemmas specialised to that situation.

-/

import algebra.big_operators data.fintype
import tactic.squeeze

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [decidable_eq α] [decidable_eq β]
variable [comm_monoid γ]

open finset 

@[to_additive finset.sum_coe_list]
lemma finset.prod_coe_list {l : list α} (h : l.nodup) (f : α → γ) :
 l.to_finset.prod f = (l.map f).prod :=
begin
 let s := @finset.mk α l h,
 have : s = l.to_finset := (list.to_finset_eq h),
 exact calc 
  l.to_finset.prod f = s.prod f : by rw[← this]
  ... = ((l : multiset α).map f).prod : rfl
  ... = ((l.map f) : multiset γ).prod : by rw[multiset.coe_map]
  ... = (l.map f).prod : by rw[multiset.coe_prod], 
end

@[to_additive finset.sum_equiv]
lemma finset.prod_equiv {s : finset α} {t : finset β}
 (e : {a // a ∈ s} ≃ {b // b ∈ t})
  (f : α → γ) (g : β → γ) 
   (hfg : ∀ (a : α) (ha : a ∈ s), f a = g (e ⟨a,ha⟩).val) :
    s.prod f = t.prod g := 
prod_bij 
 (λ a a_in_s, (e.to_fun ⟨a,a_in_s⟩).val)
 (λ a a_in_s, (e.to_fun ⟨a,a_in_s⟩).property)
 hfg
 (λ a₁ a₂ a₁_in_s a₂_in_s h, 
  congr_arg subtype.val (e.injective (subtype.eq h)))
 (λ b b_in_t, let aa := e.inv_fun ⟨b,b_in_t⟩ in 
   exists.intro aa.val 
   begin
    have ea : aa = ⟨aa.val,aa.property⟩ := subtype.eq rfl,
    use aa.property,
    rw[← ea],
    exact congr_arg subtype.val (e.right_inv ⟨b,b_in_t⟩).symm,
   end
  )

@[to_additive finset.univ_sum_equiv]
lemma finset.univ_prod_equiv [fintype α] [fintype β] (e : α ≃ β) (g : β → γ) :
 univ.prod (g ∘ e.to_fun) = univ.prod g := 
prod_bij 
 (λ a _,e.to_fun a) (λ a _,mem_univ _) (λ a _, @rfl _ (g (e.to_fun a)))
 (λ a₁ a₂ _ _ h, e.injective h)
 (λ b _, begin use e.inv_fun b, use mem_univ _, exact (e.right_inv b).symm, end)

@[to_additive finset.sum_eq_univ_sum]
lemma finset.prod_eq_univ_prod (s : finset α) (f : α → γ) : 
 s.prod f = (@univ {a // a ∈ s} _).prod (λ a, f a.val) := 
begin
 have : @univ {a // a ∈ s} _ = s.attach := rfl,
 rw[← prod_attach,this],
end

@[to_additive finset.sum_univ_product]
lemma finset.prod_univ_product [fintype α] [fintype β] (f : α → β → γ) :
 (@univ (α × β) _).prod (λ ab, f ab.1 ab.2) = 
  (@univ α _).prod (λ a, (@univ β _).prod (f a)) := 
begin 
 have : @univ (α × β) _ = (@univ α _).product (@univ β _) := rfl,
 rw[this,finset.prod_product],
end

@[to_additive finset.sum_over_bool]
lemma finset.prod_over_bool (f : bool → γ) : 
 (@univ bool _).prod f = (f ff) * (f tt) := 
begin
 let l : list bool := [ff,tt],
 let h : l.nodup := dec_trivial,
 have : (@univ bool _) = l.to_finset := dec_trivial,
 rw[this,finset.prod_coe_list h],
 simp only [list.map,list.prod_cons,list.prod_nil,mul_one]
end

