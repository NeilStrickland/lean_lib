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
import data.fin_extra

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
  nodup := list.nodup.map 
    (function.left_inverse.injective f.left_inv) (univ_nodup α),
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
  have : ((f a) : ℕ) < els.length := (f.to_fun a).is_lt,
  rw[dif_pos this], simp only [equiv.symm_apply_apply, fin.eta],
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

namespace fin

instance : ∀ (n : ℕ), enumeration (fin n)
| 0 := { elems := [], nodup := list.nodup_nil, complete := λ i, fin.elim0 i }
| (n + 1) := {
  elems := list.cons (0 : fin (n + 1)) ((enumeration n).elems.map fin.succ),
  nodup := begin
    rw [list.nodup_cons], split,
    { intro h, rcases list.mem_map.mp h with ⟨i,hi⟩,
      exact i.succ_ne_zero hi.2 },
    { exact list.nodup.map (λ a₁ a₂ ha, fin.succ_inj.mp ha) (enumeration n).nodup }
  end,
  complete := begin
    rintro ⟨i,hi⟩, cases i with i,
    { apply list.mem_cons_self },
    { let i' : fin n := ⟨i,nat.lt_of_succ_lt_succ hi⟩,
      have : (⟨i.succ,hi⟩ : fin (n + 1)) = i'.succ := fin.eq_of_veq rfl,
      rw [this],
      apply list.mem_cons_of_mem,
      apply list.mem_map_of_mem,
      apply (enumeration n).complete }
  end
} 

lemma enumeration_zero : (@enumeration.elems (fin 0) _) = [] := rfl

lemma enumeration_succ (n : ℕ) : 
  (@enumeration.elems (fin (n + 1)) _) = 
  (0 : fin (n + 1)) :: ((@enumeration.elems (fin n) _).map fin.succ) := rfl

lemma enumeration_coe (n : ℕ) :
  (@enumeration.elems (fin n) _).map (coe : (fin n) → ℕ) = list.range n :=
begin
  let f : ℕ → list ℕ := λ m,
    (@enumeration.elems (fin m) _).map (coe : (fin m) → ℕ),
  change f n = list.range n,
  have f_zero : f 0 = [] := rfl,
  have f_step : ∀ m, f (m + 1) = 0 :: ((f m).map nat.succ) := λ m,
    by { dsimp [f], 
         rw [enumeration_succ, list.map_cons, list.map_map, list.map_map],
         congr' 2, funext i, 
         rw [function.comp_app, function.comp_app, fin.coe_succ] }, 
  have map_add_add : ∀ (p q : ℕ) (l : list ℕ),
    (l.map ((+) q)).map ((+) p) = l.map ((+) (p + q)) := 
      by { intros, rw[list.map_map], congr' 1, funext i, rw [add_assoc] },
  suffices h : ∀ (p q : ℕ), f (p + q) = list.range_core p ((f q).map ((+) p)), 
  { have h₀ := h n 0,
    rw [add_zero, f_zero, list.map] at h₀, exact h₀ },
  { intro p, induction p with p ih, 
    { intro q,
      have : ((+) 0 : ℕ → ℕ) = id := by { funext i, exact zero_add i },
      rw [zero_add, list.range_core, this, list.map_id] },
    { intro q,
      have : (f (q + 1)).map ((+) p) = p :: ((f q).map ((+) (p + 1))) := 
      begin
        rw [f_step q, list.map_cons, add_zero, list.map_map],
        congr' 2,  funext i, rw [function.comp_app, add_assoc, add_comm 1] 
      end, 
      rw [list.range_core, ← this, ← ih (q + 1), add_assoc p 1 q, add_comm 1 q]
    } }
end

end fin