/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file defines a typeclass for types α with an ordered 
enumeration of the elements (as opposed to a `fintype` 
instance, which is an unordered enumeration).  This is 
intended to allow for explicit calculation in a wider range
of cases.
-/

-- TODO: 
-- instances for (co) products etc

import data.finset data.fintype.basic data.list.basic logic.encodable.basic

namespace combinatorics

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

class enumeration (α : Type*) :=
(elems : list α)
(nodup : list.nodup elems)
(complete : ∀ x : α, x ∈ elems)

instance enumeration_fintype [e : enumeration α] : fintype α := 
  ⟨⟨e.elems,e.nodup⟩,e.complete⟩

namespace enumeration

variable (α)
variable [enumeration α]

def univ_list : list α := (@enumeration.elems α _)
def univ_nodup : list.nodup (univ_list α) := (@enumeration.nodup α _)
def univ_complete := (@enumeration.complete α _)

lemma enum_card : fintype.card α = (@enumeration.elems α _).length := 
begin
  dsimp[fintype.card,finset.univ,fintype.elems,finset.card],refl,
end

#check function.left_inverse.injective

def of_equiv (f : α ≃ β) : enumeration β := 
{ elems := (univ_list α).map f.to_fun,
  nodup := list.nodup.map f.left_inv.injective (univ_nodup α),
  complete := 
  begin
    intro b,
    rw[← f.right_inv b],
    exact list.mem_map_of_mem f.to_fun (univ_complete α (f.inv_fun b)),
   end }

variable [decidable_eq α] 

def fin_equiv {n : ℕ} (h : (univ_list α).length = n) : α ≃ (fin n) := 
begin
  let els := univ_list α,
  let inv_fun : (fin n) → α := 
    λ i, els.nth_le i.val (@eq.subst ℕ (nat.lt i.val) _ _ h.symm i.is_lt),
  let to_fun_aux : ∀ (a : α), {i : fin n // inv_fun i = a} := 
  begin
    intro a,
    let i_val := els.index_of a,
    let i_lt_l := list.index_of_lt_length.mpr (enumeration.complete a),
    let i_lt_n : i_val < n := @eq.subst ℕ (nat.lt i_val) _ _ h i_lt_l,
    let i : fin n := ⟨i_val,i_lt_n⟩,
    have : inv_fun i = a := 
      by { cases h,exact list.index_of_nth_le i_lt_l },
    exact ⟨i,this⟩ 
  end,
  let to_fun : α → (fin n) := λ a, (to_fun_aux a).val,
  let left_inv : ∀ a : α, inv_fun (to_fun a) = a := 
    λ a, (to_fun_aux a).property,
  let right_inv : ∀ i : (fin n), to_fun (inv_fun i) = i := 
  begin
   intro i,cases i with i_val i_is_lt,
   apply fin.eq_of_veq,
   let i_lt_l : i_val < els.length := 
    @eq.subst ℕ (nat.lt i_val) _ _ h.symm i_is_lt,
   exact list.nth_le_index_of (univ_nodup α) i_val i_lt_l,
  end,
  exact ⟨to_fun,inv_fun,left_inv,right_inv⟩ 
end

instance : encodable α := 
begin
 let els := univ_list α,
 let f := fin_equiv α rfl,
 let encode : α → ℕ := λ a,(f.to_fun a).val,
 let decode : ℕ → option α := 
 begin
  intro i,
  by_cases h : i < els.length,
  {exact some (f.inv_fun ⟨i,h⟩),},
  {exact none,}
 end,
 let encodek : ∀ a, decode (encode a) = some a := 
 begin
  intro a,
  dsimp[decode,encode],
  rw[dif_pos (f a).is_lt],simp[f.left_inv a],
 end,
 exact ⟨encode,decode,encodek⟩ 
end

def subtype_enumeration {p : α → Prop} (l : list α)
 (l_nodup : list.nodup l)
 (l_mem : ∀ x : α, x ∈ l ↔ p x) : enumeration {x // p x} :=
begin
 let α1 := {x // p x},
 let elems1 : list α1 := @list.pmap α α1 p subtype.mk l (λ x, (l_mem x).mp),
 let nodup : elems1.nodup :=
  @list.nodup.pmap α α1 p subtype.mk l (λ x, (l_mem x).mp)
   (λ a _ b _,congr_arg subtype.val) l_nodup,
 let complete : ∀ a1 : α1, a1 ∈ elems1 := 
 begin
  intro a1, cases a1,
  let h0 := ((@list.mem_pmap α α1 p subtype.mk l
               (λ x, (l_mem x).mp)) ⟨a1_val,a1_property⟩).mpr,
  have h1 : a1_val ∈ l := (l_mem a1_val).mpr a1_property,
  exact h0 ⟨a1_val,h1,rfl⟩, 
 end,
 exact ⟨elems1,nodup,complete⟩ 
end

instance (p : α → Prop) [decidable_pred p] : enumeration {a // p a} :=
begin
 let l := (univ_list α).filter p,
 let l_nodup : l.nodup := list.nodup.filter p (univ_nodup α), 
 let l_mem : ∀ x : α, x ∈ l ↔ p x := 
 begin
  intro x,
  let h0 : x ∈ univ_list α := (univ_complete α) x,
  simp[list.mem_filter,h0],
 end,
 exact subtype_enumeration α l l_nodup l_mem,
end

end enumeration

end combinatorics

namespace fin

instance enum : ∀ (n : ℕ), combinatorics.enumeration (fin n) 
| 0 := { elems := [], nodup := list.nodup_nil, complete := λ x, fin.elim0 x }
| (n + 1) := {
    elems := (0 : fin n.succ) :: ((enum n).elems.map fin.succ),
    nodup := 
    begin 
      rw [list.nodup_cons], split,
      { intro h, rcases list.mem_map.mp h with ⟨i,⟨hm,he⟩⟩,
        exact fin.succ_ne_zero i he },
      { exact list.nodup.map (λ i j e, fin.succ_inj.mp e) (enum n).nodup }
    end,
    complete := 
    λ i, begin
      by_cases h : i = 0,
      { rw [h], exact list.mem_cons_self _ _ },
      { let j := fin.pred i h, 
        have : i = j.succ := (fin.succ_pred i h).symm,
        rw [this],
        let hc := (enum n).complete,
        exact list.mem_cons_of_mem _ 
         (list.mem_map_of_mem fin.succ (hc j)),
      }
    end    
  }

lemma enum_length : ∀ (n : ℕ), (fin.enum n).elems.length = n 
| 0 := rfl
| (n + 1) := 
begin
  change (list.cons (0 : fin (n + 1)) ((fin.enum n).elems.map fin.succ)).length = n + 1,
  rw [list.length, list.length_map, enum_length n]
end

end fin
