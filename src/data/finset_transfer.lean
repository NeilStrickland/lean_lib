/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Suppose we have two types α and β with decidable equality, and 
an equivalence between them (as defined in 
mathlib/data/equiv/basic.lean).  We then get an equivalence 
between the associated types (finset α) and (finset β) of finite
subsets, and this equivalence respects membership, inclusion,
intersections and unions and various other kinds of structure.
In this file we prove a variety of facts of that type.

All this should probably be done in some more abstract and 
general framework of functors from types to types, or something
like that.  Also, the naming conventions should be changed for
greater compatibility with mathlib.
-/

import data.finset data.fintype.basic

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

namespace finset
open finset fintype equiv

universes u v
variables {α : Type u} {β : Type v}
 [decidable_eq α] [decidable_eq β] 

def finset_equiv_of_equiv (f : α ≃ β) :
 (finset α) ≃ (finset β) := {
   to_fun := (finset.image f.to_fun),
   inv_fun := (finset.image f.inv_fun),
   left_inv := begin
    unfold function.left_inverse at ⊢,
    intro x,
    rw[image_image],
    have li : f.inv_fun ∘ f.to_fun = id,
     {ext t,simp[f.left_inv t]},
    rw[li,image_id]
    end,
   right_inv := begin
    unfold function.right_inverse at ⊢,
    intro y,
    rw[image_image],
    have ri : f.to_fun ∘ f.inv_fun = id,
     {ext u,simp[f.right_inv u]},
    rw[ri,image_id]
   end
 }

 lemma finset_equiv_symm : ∀ (f : α ≃ β),
  (finset_equiv_of_equiv f).symm = finset_equiv_of_equiv (f.symm)
| ⟨ft,fi,l,r⟩  :=
 begin
  unfold equiv.symm,
  unfold finset_equiv_of_equiv
 end

 lemma mem_transfer (f : α ≃ β) (a : α) (u : finset α) :
  a ∈ u ↔ f.to_fun a ∈ (finset_equiv_of_equiv f).to_fun u :=
 begin
  split,
  exact mem_image_of_mem f.to_fun,
  intro f_a_in_f_u,
  have : (∃ a0 ∈ u, f.to_fun a0 = f.to_fun a) := (mem_image.mp f_a_in_f_u),
  cases this with a0 Z0,
  cases Z0 with a0_in_u same_image,
  have a0_eq_a : a0 = a := 
  calc a0 = f.inv_fun (f.to_fun a0) : (f.left_inv a0).symm
       ... = f.inv_fun (f.to_fun a) : congr_arg f.inv_fun same_image 
       ... = a : f.left_inv a,
  exact eq.subst a0_eq_a a0_in_u
 end

 lemma mem_transfer_inv (f : α ≃ β) (b : β) (u : finset α) :
  b ∈ (finset_equiv_of_equiv f).to_fun u ↔ f.inv_fun b ∈ u :=
 begin
  split,
  {intro b_in_f_u,
  have : (∃ a ∈ u, f.to_fun a = b) := (mem_image.mp b_in_f_u),
  cases this with a a_in_u_f_a_eq_b,
  cases a_in_u_f_a_eq_b with a_in_u f_a_eq_b,
  have f_inv_b_eq_a : f.inv_fun b = a := eq.subst f_a_eq_b (f.left_inv a),
  exact eq.subst f_inv_b_eq_a.symm a_in_u},
  {intro f_inv_b_in_u,
  exact eq.subst (f.right_inv b) (mem_image_of_mem f.to_fun f_inv_b_in_u)
  }
 end

 lemma mem_transfer_alt (f : α ≃ β) (a : α) (v : finset β) :
  a ∈ (finset_equiv_of_equiv f).inv_fun v ↔ f a ∈ v :=
 begin
  let Pf := finset_equiv_of_equiv f,
  let u := Pf.inv_fun v,
  let E := Pf.right_inv v, 
  let T := (mem_transfer f a u), 
  rw E at T,
  exact T
 end

 lemma empty_transfer (f : α ≃ β) : 
  (finset_equiv_of_equiv f) ∅ = ∅ := (image_empty f.to_fun)

 lemma subset_transfer (f : α ≃ β) {u v : finset α} :
  u ⊆ v ↔ (finset_equiv_of_equiv f) u ⊆ (finset_equiv_of_equiv f) v :=
 begin
  split,
  {intro u_sse_v,
   exact image_subset_image u_sse_v},
  {intro f_u_sse_f_v,
   apply subset_iff.mpr,
   intros a a_in_u,
   have f_a_in_f_u : f a ∈ (finset_equiv_of_equiv f) u :=
    mem_image_of_mem f a_in_u,
   have f_a_in_f_v : f a ∈ (finset_equiv_of_equiv f) v := 
    subset_iff.mp f_u_sse_f_v f_a_in_f_u,
   exact (mem_transfer f a v).mpr (f_a_in_f_v)}
 end

 lemma ssubset_transfer (f : α ≃ β ) {u v : finset α} :
  u ⊂ v ↔  (finset_equiv_of_equiv f) u ⊂ (finset_equiv_of_equiv f) v :=
 begin
  let Pf := finset_equiv_of_equiv f,
  have uu_eq_u : image f.inv_fun (Pf u) = u := Pf.left_inv u,
  have vv_eq_v : image f.inv_fun (Pf v) = v := Pf.left_inv v,
  split,
  intro u_ssubset_v,
  have u_subset_v := u_ssubset_v.left,
  have v_not_subset_u := u_ssubset_v.right,
  have f_u_subset_f_v : Pf u ⊆ Pf v := 
      (subset_transfer f).mp u_subset_v,
  have f_v_not_subset_f_u : 
    not (Pf v ⊆ Pf u) :=
   begin
    intro f_v_subset_f_u,
    let vv_subset_uu := @image_subset_image β α _ f.inv_fun _ _ f_v_subset_f_u,
    rw[uu_eq_u,vv_eq_v] at vv_subset_uu,
    exact v_not_subset_u vv_subset_uu
   end,
   exact ⟨f_u_subset_f_v,f_v_not_subset_f_u⟩,
  intro f_u_ssubset_f_v,
  have f_u_subset_f_v := f_u_ssubset_f_v.left,
  have f_v_not_subset_f_u := f_u_ssubset_f_v.right,
  have uu_subset_vv := (subset_transfer f).mpr f_u_subset_f_v,
  have not_vv_subset_uu : not (v ⊆ u) := 
   begin
    intro v_subset_u,
    have f_v_subset_f_u := (subset_transfer f).mp v_subset_u,
    exact f_v_not_subset_f_u f_v_subset_f_u,
   end,
  exact ⟨uu_subset_vv,not_vv_subset_uu⟩   
 end

 lemma union_transfer (f : α ≃ β) (u v : finset α) :
  (finset_equiv_of_equiv f).to_fun (u ∪ v) = 
   (finset_equiv_of_equiv f).to_fun (u) ∪ (finset_equiv_of_equiv f).to_fun (v) :=
    (image_union u v)

 lemma intersect_transfer (f : α ≃ β) (u v : finset α) :
  (finset_equiv_of_equiv f).to_fun (u ∩ v) = 
   (finset_equiv_of_equiv f).to_fun (u) ∩ (finset_equiv_of_equiv f).to_fun (v) :=
 begin
  apply finset.ext,
  intro b,
  let P := mem_transfer_inv f b u,
  let Q := mem_transfer_inv f b v,
  let R := mem_transfer_inv f b (u ∩ v),
  split,
  {intro H,apply finset.mem_inter.mpr,
  exact ⟨P.mpr (mem_inter.mp (R.mp H)).left,
         Q.mpr (mem_inter.mp (R.mp H)).right⟩},
  {intro H,rw[finset.mem_inter] at H,
  exact R.mpr (mem_inter.mpr ⟨P.mp H.left,Q.mp H.right⟩)}
 end

 lemma sdiff_transfer (f : α ≃ β) (u v : finset α) :
  (finset_equiv_of_equiv f).to_fun (u \ v) = 
   (finset_equiv_of_equiv f).to_fun (u) \ (finset_equiv_of_equiv f).to_fun (v) :=
 begin
  apply finset.ext,
  intro b,
  let P := mem_transfer_inv f b u,
  let Q := mem_transfer_inv f b v,
  let R := mem_transfer_inv f b (u \ v),
  split,
  {intro H,apply finset.mem_sdiff.mpr,
  exact ⟨P.mpr (mem_sdiff.mp (R.mp H)).left,
        λ U,(mem_sdiff.mp (R.mp H)).right (Q.mp U)⟩}, 
  {intro H,rw[finset.mem_sdiff] at H,
  exact R.mpr (mem_sdiff.mpr ⟨P.mp H.left,λ U,H.right (Q.mpr U)⟩)}
 end
 
 lemma singleton_transfer (f : α ≃ β) (a : α) : 
  (finset_equiv_of_equiv f) (singleton a) = singleton (f a) := rfl

 lemma insert_transfer (f : α ≃ β) (a : α) (u : finset α) : 
  (finset_equiv_of_equiv f) (insert a u) = 
    insert (f a) ((finset_equiv_of_equiv f) u) := 
    image_insert f a u
 
 lemma card_transfer (f : α ≃ β) (u : finset α) : 
  card ((finset_equiv_of_equiv f) u) = card u := 
  card_image_of_injective u (function.left_inverse.injective f.left_inv)

 lemma erase_transfer (f : α ≃ β) (u : finset α) (a : α) :
  (finset_equiv_of_equiv f) (erase u a) = erase ((finset_equiv_of_equiv f) u) (f a) := 
 begin
  let Pf := (finset_equiv_of_equiv f),
  simp[ext_iff],
  intro b,
  split,
  intro b_in_f_erase,
  have f_inv_b_in_erase := (mem_transfer_inv f b (erase u a)).mp b_in_f_erase,
  have f_inv_b_neq_a : ¬ (f.inv_fun b = a) := (mem_erase.mp f_inv_b_in_erase).left, 
  have f_inv_b_in_u : f.inv_fun b ∈ u  := (mem_erase.mp f_inv_b_in_erase).right, 
  split,
  intro b_eq_f_a,
  have f_inv_b_eq_a := eq.trans (congr_arg f.inv_fun b_eq_f_a) (f.left_inv a),
  exact f_inv_b_neq_a f_inv_b_eq_a,
  have b_in_f_u := (mem_transfer f (f.inv_fun b) u).mp f_inv_b_in_u,
  rw[f.right_inv b] at b_in_f_u,
  exact b_in_f_u,
  intro H,
  have f_inv_b_in_erase : f.inv_fun b ∈ erase u a := 
  begin
   apply mem_erase.mpr,
   split,
   intro f_inv_b_eq_a,
   exact H.left (eq.trans (f.right_inv b).symm (congr_arg f f_inv_b_eq_a)),
   have f_inv_b_in_uu := mem_image_of_mem f.inv_fun H.right,
   have uu_eq_u : image f.inv_fun (Pf u) = u := Pf.left_inv u,
   rw[uu_eq_u] at f_inv_b_in_uu,
   exact f_inv_b_in_uu
  end,
  have b_in_f_erase := mem_image_of_mem f f_inv_b_in_erase,
  have bb_eq_b : f (f.inv_fun b) = b := f.right_inv b,
  rw[bb_eq_b] at b_in_f_erase,
  exact b_in_f_erase
 end

 lemma filter_transfer
  (f : α ≃ β) (p : α → Prop) [decidable_pred p] (u : finset α) :
   (finset_equiv_of_equiv f) (filter p u) = 
    filter (p ∘ f.inv_fun) ((finset_equiv_of_equiv f) u) :=
 begin
  let Pf := (finset_equiv_of_equiv f),
  simp[ext_iff],
  intro b,
  let a := f.inv_fun b,
  split,
  intro b_in_f_filter,
  let a_in_filter : a ∈ filter p u :=
   (mem_transfer_inv f b (filter p u)).mp b_in_f_filter,
  have a_in_u : a ∈ u := (mem_filter.mp a_in_filter).left,
  let p_a : p a := (mem_filter.mp a_in_filter).right,
  {split,
  exact (mem_transfer_inv f b u).mpr a_in_u,
  exact p_a},
  intro H,
  have b_in_f_u := H.left,
  have a_in_u : a ∈ u := (mem_transfer_inv f b u).mp b_in_f_u,
  have p_a : p a := H.right,
  have a_in_filter : a ∈ filter p u := mem_filter.mpr ⟨a_in_u,p_a⟩,
  exact (mem_transfer_inv f b (filter p u)).mpr a_in_filter
 end

 lemma disjoint_transfer 
  (f : α ≃ β) (s0 s1 : finset α) : 
   (disjoint s0 s1) ↔ 
    (disjoint ((finset_equiv_of_equiv f) s0) ((finset_equiv_of_equiv f) s1)) :=
 begin
  let Pf := finset_equiv_of_equiv f,
  split,
  {intro s_disjoint,
  by calc 
   (Pf s0) ∩ (Pf s1) = Pf (s0 ∩ s1) : (intersect_transfer f s0 s1).symm
    ... ⊆ Pf ∅ : (subset_transfer f).mp s_disjoint
    ... = ∅ : empty_transfer f},
  {intro t_disjoint,
  let t0 := Pf s0,
  let t1 := Pf s1,
  let E := calc
   Pf (s0 ∩ s1) = t0 ∩ t1 : intersect_transfer f s0 s1
   ... ⊆ ∅ : t_disjoint,
  by calc
   s0 ∩ s1 = Pf.inv_fun (Pf (s0 ∩ s1)) : (Pf.left_inv _).symm 
    ... ⊆ Pf.inv_fun ∅ : (subset_transfer f.symm).mp E
    ... = ∅ : empty_transfer f.symm
  }
 end
end finset

namespace fintype

open finset fintype equiv

universes u v
variables {α : Type u} {β : Type v}
 [decidable_eq α] [decidable_eq β] 

lemma fintype_eq_of_elems_eq : ∀ {s t : fintype α}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

lemma fintype_unique (u v : fintype α) : u = v := 
begin
 apply fintype_eq_of_elems_eq,
 ext,split,
 intro a_in_u,
 exact (@fintype.complete α v a),
 intro a_in_v,
 exact (@fintype.complete α u a)
end

def fintype_equiv_of_equiv (f : α ≃ β) :
 (fintype α ≃ fintype β ) :=
begin
 let Pf := finset.finset_equiv_of_equiv f,
 exact {
  to_fun := λ u, {
   elems := Pf.to_fun u.elems,
   complete := λ b, 
    (mem_transfer_inv f b u.elems).mpr (@fintype.complete α u (f.inv_fun b))
  },
  inv_fun := λ v, {
   elems := Pf.inv_fun v.elems,
   complete := λ a,
    (mem_transfer_alt f a v.elems).mpr (@fintype.complete β v (f.to_fun a))
  },
  left_inv  := λ u,fintype_eq_of_elems_eq (Pf.left_inv  u.elems),
  right_inv := λ v,fintype_eq_of_elems_eq (Pf.right_inv v.elems)
 }
end

lemma univ_transfer [u : fintype α] [v : fintype β] (f : α ≃ β) :
 (finset_equiv_of_equiv f) (@univ α _) = (@univ β _) := 
begin
 ext b,split,
 intro,
 exact (@fintype.complete β v b),
 intro,
 exact (mem_transfer_inv f b (@univ α _)).mpr
  (@fintype.complete α u (f.inv_fun b)),
end


end fintype
