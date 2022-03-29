/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file is about ordered subsets of a finite type, i.e. lists
of distinct elements.  It probably has some overlap with Mario's
recent mathlib additions on lists of sublists etc.
-/

import data.nat.choose data.fintype.basic
import tactic.squeeze
import combinatorics.erase combinatorics.falling combinatorics.qualify

open nat

namespace combinatorics

variables (α : Type*) [fintype α] [decidable_eq α]

/- @latex: defn-F -/
def ordered_subset (k : ℕ) := 
 { s : list α // s.length = k ∧ s.nodup }

namespace ordered_subset

instance (k : ℕ) : has_mem α (ordered_subset α k) := 
 ⟨λ (a : α) (s : ordered_subset α k), list.mem a s.val⟩ 

instance (k : ℕ) : decidable_eq (ordered_subset α k) := 
 by {apply_instance}

variable {α}

@[ext]
lemma ext {k : ℕ} {s₁ s₂ : ordered_subset α k} : 
  s₁ = s₂ ↔ s₁.val = s₂.val := 
begin 
 split; intro e,rw[e],exact subtype.eq e,
end

section map 

/- ordered_subset α k is covariantly functorial for injective
   functions of α.
-/

variables {β : Type*} [fintype β] [decidable_eq β]
variables {γ : Type*} [fintype γ] [decidable_eq γ]
variables {f : α → β} (f_inj : function.injective f)
variables {g : β → γ} (g_inj : function.injective g)

def map {k : ℕ} : ∀ (s : ordered_subset α k), ordered_subset β k
| ⟨s,⟨s_len,s_nodup⟩⟩ :=
   ⟨s.map f,⟨(list.length_map f s).trans s_len,list.nodup_map f_inj s_nodup⟩⟩

@[simp]
lemma map_id {k : ℕ} : ∀ s : ordered_subset α k, 
 map function.injective_id s = s
| ⟨s,⟨s_len,s_nodup⟩⟩ := by {apply subtype.eq,exact list.map_id s}

lemma map_map {k : ℕ} : 
 ∀ s : ordered_subset α k, 
  map (function.injective.comp g_inj f_inj) s = 
   map g_inj (map f_inj s)
| ⟨s,⟨s_len,s_nodup⟩⟩ := 
   by { apply subtype.eq,exact (list.map_map g f s).symm }

lemma mem_map {k : ℕ} (b : β) : ∀ (s : ordered_subset α k),
 b ∈ (map f_inj s) ↔ ∃ a, a ∈ s ∧ f a = b
| ⟨s,⟨s_len,s_nodup⟩⟩ := begin
 split,{intro b_in_fs,exact (@list.mem_map _ _ f b s).mp b_in_fs,},
 {intro ex_a,exact (@list.mem_map _ _ f b s).mpr ex_a,}
end

lemma list.map_inj {f : α → β} (f_inj : function.injective f) :
 function.injective (list.map f) 
| [] [] e := rfl
| [] (a2 :: l2) e := false.elim (list.no_confusion e)
| (a1 :: l1) [] e := false.elim (list.no_confusion e)
| (a1 :: l1) (a2 :: l2) e := begin
   rw[list.map,list.map] at e,
   injection e with e_head e_tail,
   congr,exact f_inj e_head,exact list.map_inj e_tail,
  end

lemma map_inj (k : ℕ) :
 function.injective (@map α _ _ β _ _ f f_inj k)
| ⟨s1,⟨s1_len,s1_nodup⟩⟩ ⟨s2,⟨s2_len,s2_nodup⟩⟩ e := 
begin
 apply subtype.eq,
 change s1 = s2,
 rw[ext] at e, change s1.map f = s2.map f at e,
 exact list.map_inj f_inj e,
end

end map

def nil : ordered_subset α 0 := ⟨list.nil,⟨rfl,list.nodup_nil⟩⟩ 

lemma eq_nil : ∀ s : ordered_subset α 0, s = nil  
| ⟨s,⟨s_len,s_nodup⟩⟩ :=
   subtype.eq $ list.eq_nil_of_length_eq_zero s_len

variable {α}

def cons : ∀ (a : α) {n : ℕ} (s : ordered_subset α n) (h : ¬ (a ∈ s)),
 ordered_subset α (n + 1)
| a _ ⟨s,⟨s_len,s_nodup⟩⟩ h := 
   ⟨list.cons a s,⟨by {rw[← s_len],refl},list.nodup_cons.mpr ⟨h,s_nodup⟩⟩⟩ 

@[simp]
lemma val_cons : ∀ (a : α) {n : ℕ} (s : ordered_subset α n) (h : ¬ (a ∈ s)),
 (cons a s h).val = a :: s.val
| a _ ⟨s,⟨s_len,s_nodup⟩⟩ h := rfl

def head : ∀ {n : ℕ} (s : ordered_subset α (n + 1)), α 
| _ ⟨list.cons a t,⟨s_len,s_nodup⟩⟩ := a
| n ⟨list.nil,⟨s_len,s_nodup⟩⟩ := false.elim (succ_ne_zero n s_len.symm)

def tail : ∀ {n : ℕ} (s : ordered_subset α (n + 1)), 
 ordered_subset α n 
| _ ⟨list.cons a t,⟨s_len,s_nodup⟩⟩ :=
      ⟨t,⟨nat.succ_inj'.mp s_len,(list.nodup_cons.mp s_nodup).right⟩⟩ 
| n ⟨list.nil,⟨s_len,s_nodup⟩⟩ := false.elim (succ_ne_zero n s_len.symm)

@[simp]
lemma val_tail : ∀ {n : ℕ} (s : ordered_subset α (n + 1)), 
 s.tail.val = s.val.tail 
| _ ⟨list.cons a t,⟨s_len,s_nodup⟩⟩ := rfl
| n ⟨list.nil,⟨s_len,s_nodup⟩⟩ := false.elim (succ_ne_zero n s_len.symm)

@[simp]
lemma head_cons : ∀ {n : ℕ} (a : α) (s : ordered_subset α n) (h : a ∉ s), 
 head (cons a s h) = a
| n a ⟨s,⟨s_len,s_nodup⟩⟩ h := rfl

@[simp]
lemma tail_cons : ∀ {n : ℕ} (a : α) (s : ordered_subset α n) (h : a ∉ s), 
 tail (cons a s h) = s
| n a ⟨s,⟨s_len,s_nodup⟩⟩ h := by { apply subtype.eq,refl }

lemma head_not_in_tail : ∀ {n : ℕ} (s : ordered_subset α (n + 1)), 
 s.head ∉ s.tail
| _ ⟨list.cons a t,⟨s_len,s_nodup⟩⟩ :=
   (list.nodup_cons.mp s_nodup).left
| n ⟨list.nil,⟨s_len,s_nodup⟩⟩ := false.elim (succ_ne_zero n s_len.symm)

lemma head_not_in_tail' {n : ℕ} {s : ordered_subset α (n + 1)} 
 {a : α} (e : s.head = a) (b : α) :
 b ∈ s.tail → b ≠ a := 
  λ b_in_t b_eq_a, s.head_not_in_tail ((b_eq_a.trans e.symm) ▸ b_in_t)
 
lemma eq_cons : ∀ {n : ℕ} (s : ordered_subset α (n + 1)), 
 s = cons s.head s.tail s.head_not_in_tail 
| _ ⟨list.cons a t,⟨s_len,s_nodup⟩⟩ := by {apply subtype.eq,refl}
| n ⟨list.nil,⟨s_len,s_nodup⟩⟩ := false.elim (succ_ne_zero n s_len.symm)

def qualify {u : α → Prop} [decidable_pred u] {n : ℕ} : 
 ∀ (s : ordered_subset α n) (h : ∀ {a}, a ∈ s → u a),
  ordered_subset {a // u a} n
| ⟨s,⟨s_len,s_nodup⟩⟩ h :=
   ⟨list.qualify s @h,⟨(list.length_qualify s @h).trans s_len,
                       (list.nodup_qualify s @h).mpr s_nodup⟩⟩ 

@[simp]
lemma val_qualify {u : α → Prop} [decidable_pred u] {n : ℕ} : 
 ∀ (s : ordered_subset α n) (h : ∀ {a}, a ∈ s → u a),
  (qualify s @h).val = list.qualify s.val @h
| ⟨s,⟨s_len,s_nodup⟩⟩ h := rfl

def unqualify {u : set α} [decidable_pred (∈ u)] {n : ℕ} :
 ∀ (s : ordered_subset u n), ordered_subset α n
| ⟨s,⟨s_len,s_nodup⟩⟩ := 
   ⟨list.unqualify s,⟨(list.length_unqualify s).trans s_len,
                      list.nodup_unqualify.mpr s_nodup⟩⟩

@[simp]
lemma val_unqualify {u : set α} [decidable_pred (∈ u)] {n : ℕ} :
 ∀ (s : ordered_subset u n), (unqualify s).val = list.unqualify s.val
| ⟨s,⟨s_len,s_nodup⟩⟩ := rfl

lemma unqualify_eq {u : set α} [decidable_pred (∈ u)] {n : ℕ} 
 {s₁ s₂ : ordered_subset u n} :
  s₁ = s₂ ↔ (unqualify s₁) = (unqualify s₂) :=
begin
 rw[ext,ext,val_unqualify,val_unqualify],
 exact list.unqualify_eq,
end

lemma mem_unqualify {u : set α} [decidable_pred (∈ u)] {n : ℕ} :
 ∀ (s : ordered_subset u n) (a : α),
  a ∈ (unqualify s) ↔ ∃ h : u a, subtype.mk a h ∈ s
| ⟨s,⟨s_len,s_nodup⟩⟩ a := @list.mem_unqualify α u s a

lemma mem_unqualify' {u : set α} [decidable_pred (∈ u)] {n : ℕ} :
 ∀ (s : ordered_subset u n) (a : u),
  a.val ∈ (unqualify s) ↔ a ∈ s
| ⟨s,⟨s_len,s_nodup⟩⟩ a := @list.mem_unqualify' α u s a

@[simp]
lemma un_qualify  {u : set α} [decidable_pred (∈ u)] {n : ℕ} : 
 ∀ (s : ordered_subset α n) (h : ∀ {a}, a ∈ s → u a),
    unqualify (qualify s @h) = s 
| ⟨s,⟨s_len,s_nodup⟩⟩ h :=
   begin 
    rw[qualify,unqualify],
    {apply subtype.eq,simp only [],rw[list.un_qualify],},
    {exact (list.length_qualify s @h).trans s_len,},
    {exact (list.nodup_qualify s @h).mpr s_nodup,}
   end

def cons' (a : α) {n : ℕ} (s : ordered_subset (erase a) n) : 
 ordered_subset α n.succ := cons a s.unqualify 
  begin -- Need to supply proof that a ∉ s.unqualify
   intro a_in_s,
   cases (mem_unqualify s a).mp a_in_s with h,
   exact h rfl,
  end

variables P Q : Prop

def tail' {n : ℕ} (s : ordered_subset α n.succ) {a : α} (e : s.head = a) :
 ordered_subset (erase a) n :=
  (qualify s.tail) (head_not_in_tail' e)

@[simp]
lemma unqualify_tail {n : ℕ} (s : ordered_subset α n.succ)  {a : α} (e : s.head = a) :
 unqualify (tail' s e) = s.tail := un_qualify s.tail _

@[simp]
lemma head_cons' (a : α) {n : ℕ} (s : ordered_subset (erase a) n) : 
 head (cons' a s) = a := head_cons a s.unqualify _

@[simp]
lemma tail_cons' (a : α) {n : ℕ} (s : ordered_subset (erase a) n) 
 (e : head(cons' a s) = a) : 
 tail' (cons' a s) e = s := begin
 apply unqualify_eq.mpr,rw[unqualify_tail,cons',tail_cons],
end

lemma eq_cons' {n : ℕ} (s : ordered_subset α n.succ) {a : α} (e : s.head = a) :
 s = cons' a (tail' s e) := 
begin
 apply ext.mpr,rw[cons',val_cons,val_unqualify,tail',val_qualify],
 rw[list.un_qualify,val_tail],
 rcases s with ⟨s_val,⟨s_len,s_nodup⟩⟩,
 rcases s_val with _ | ⟨a0,t⟩,
 {exact false.elim (succ_ne_zero _ s_len.symm)},
 replace e : a0 = a := e,
 simp only [e],split; refl,
end

lemma sigma_eq {k : ℕ} : ∀ {x₁ x₂ : (Σ a : α, ordered_subset (erase a) k)},
 x₁ = x₂ ↔ x₁.1 = x₂.1 ∧ unqualify x₁.2 = unqualify x₂.2
| ⟨a₁,t₁⟩ ⟨a₂,t₂⟩ := 
 begin
  split,
  {intro e,rw[e],split;refl},
  {rintro ⟨ea,et⟩,replace ea : a₁ = a₂ := ea,
   rcases ea with rfl,congr,exact unqualify_eq.mpr et,
  }
 end

def base_equiv : unit ≃ ordered_subset α 0 := {
 to_fun := λ _,nil,
 inv_fun := λ _,unit.star,
 left_inv := λ s,by { cases s,refl},
 right_inv := λ s, (eq_nil s).symm,
} 

def sigma_equiv (k : ℕ) : 
 (Σ a : α, ordered_subset (erase a) k) ≃ (ordered_subset α k.succ) := {
  to_fun := λ x,cons' x.1 x.2,
  inv_fun := λ s,⟨s.head,tail' s rfl⟩,
  right_inv := λ s,(eq_cons' s rfl).symm,
  left_inv := λ x,begin 
   rcases x with ⟨a,t⟩,
   apply sigma_eq.mpr,split,simp only[head_cons'],
   simp only[tail',unqualify_tail,un_qualify,cons',tail_cons],
  end
 }

instance (n : ℕ) :  fintype (ordered_subset α n) := 
begin
 tactic.unfreeze_local_instances,
 induction n with n ih generalizing α,
 {exact fintype.of_equiv unit base_equiv},
 {exact fintype.of_equiv _ (sigma_equiv n)}
end

#check finset.sum_const

lemma card (n m : ℕ) (e : fintype.card α = m) :
 fintype.card (ordered_subset α n) = falling m n := 
begin
 tactic.unfreeze_local_instances,
 induction n with n ih generalizing α m e,
 {exact
   ((fintype.card_congr base_equiv).symm.trans fintype.card_unit).trans 
   (falling_zero m).symm,
 },
 {rcases m with _ | m,
  {rw[falling_zero_succ],
   rw[fintype.card_eq_zero_iff,is_empty_iff] at e ⊢,
   intro s, exact e s.head
  },{
  rw[falling_succ],
  let h0 := (fintype.card_congr (sigma_equiv n)).symm.trans 
            (fintype.card_sigma (λ a : α, ordered_subset (erase a) n)),
  have h1 : ∀ (a : α), fintype.card (erase a) = m := 
   λ a, nat.succ_inj'.mp ((erase.card a).trans e),
  have h2 : ∀ (a : α), fintype.card (ordered_subset (erase a) n) = falling m n :=
   λ (a : α), ih m (h1 a),
  let c0 : α → ℕ := λ a, fintype.card (ordered_subset (erase a) n),
  let c1 : α → ℕ := λ a, falling m n,
  have h3 : finset.univ.sum c0 = finset.univ.sum c1 := finset.sum_congr rfl (λ a _, h2 a),
  have : finset.univ.sum c1 = _ := finset.sum_const (falling m n),
  let h4 : finset.univ.sum c1 = m.succ * (falling m n) :=
   begin
    change finset.univ.card = m + 1 at e,
    rw[finset.sum_const (falling m n),e],refl
   end,
   exact h0.trans (h3.trans h4),
  }
 }
end

end ordered_subset

end combinatorics

