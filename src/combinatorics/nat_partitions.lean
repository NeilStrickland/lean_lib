/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

(This is part of an attempt to formalise some material from
 a basic undergraduate combinatorics course.)

 We consider the equation x₀ + ... + xₘ = n, 
 where the variables xᵢ are natural numbers.  
 The set of solutions bijects with the set of 
 (n,m) grid paths, so the number of solutions is 
 (n + m) choose n.

 There are various possible modifications, where 
 we might impose constraints xᵢ ≥ cᵢ for example. 
-/

import data.pnat.basic data.finset combinatorics.enumeration

namespace combinatorics

def inc_list (α : Type) [linear_order α] : Type := 
  { l : list α // l.pairwise has_lt.lt }

namespace inc_list

variables {α : Type} [linear_order α]

instance : has_coe (inc_list α) (list α) := ⟨λ l, l.val⟩

lemma coe_inj {l₀ l₁ : inc_list α} : 
  (l₀ : list α) = (l₁ : list α) → l₀ = l₁ := subtype.eq

instance : has_mem α (inc_list α) := ⟨λ a l, a ∈ (l : list α) ⟩ 

lemma nodup (l : inc_list α) : (l : list α).nodup := 
  list.pairwise.imp (λ a₀ a₁ h, ne_of_lt h) l.property

def to_finset (l : inc_list α) : finset α := ⟨(l : list α),l.nodup⟩ 

def of_finset (s : finset α) : inc_list α := ⟨ s.sort has_le.le, 
begin
  have hx := list.pairwise.and
   (s.sort_sorted has_le.le) (s.sort_nodup has_le.le),
  have hi : ∀ (a b : α) (h : a ≤ b ∧ a ≠ b), a < b := 
    λ a b h, lt_of_le_of_ne h.1 h.2,
  exact list.pairwise.imp hi hx,
end⟩

lemma to_of_finset (s : finset α) : 
  to_finset (of_finset s) = s := 
(list.to_finset_eq (s.sort_nodup has_le.le)).trans
 (s.sort_to_finset has_le.le)

lemma of_to_finset (l : inc_list α) : 
  of_finset (to_finset l) = l := 
coe_inj $  list.eq_of_perm_of_sorted (list.perm_merge_sort _ _) 
    (of_finset (to_finset l)).property l.property

def finset_equiv : inc_list α ≃ finset α := {
  to_fun := to_finset,
  inv_fun := of_finset,
  left_inv := of_to_finset,
  right_inv := to_of_finset
}

def nil : inc_list α := ⟨[],list.pairwise.nil⟩ 

def cons (a : α) (l : inc_list α) (h : ∀ b : α, b ∈ l → a < b) : 
  inc_list α :=
    ⟨list.cons a (l : list α),list.pairwise.cons h l.property⟩

def map {β : Type} [linear_order β] 
 (f : α → β) (hf : ∀ a₀ a₁, a₀ < a₁ → f a₀ < f a₁) 
 (l : inc_list α) : (inc_list β) := 
⟨ (l : list α).map f, 
  (list.pairwise_map f).mpr (list.pairwise.imp hf l.property) ⟩

end inc_list

def nondec_list (α : Type) [linear_order α] : Type := 
  { l : list α // l.pairwise has_le.le }

namespace nondec_list

variables {α : Type} [linear_order α]

instance : has_coe (nondec_list α) (list α) := ⟨λ l, l.val⟩

instance : has_mem α (nondec_list α) := ⟨λ a l, a ∈ (l : list α) ⟩ 

lemma coe_inj {l₀ l₁ : nondec_list α} : 
  (l₀ : list α) = (l₁ : list α) → l₀ = l₁ := subtype.eq

def to_multiset (l : nondec_list α) : multiset α := (l : list α) 

def of_multiset (s : multiset α) : nondec_list α :=
 ⟨ s.sort has_le.le, s.sort_sorted has_le.le ⟩

lemma to_of_multiset (s : multiset α) : 
  to_multiset (of_multiset s) = s := s.sort_eq has_le.le

lemma of_to_multiset (l : nondec_list α) : 
  of_multiset (to_multiset l) = l := 
coe_inj $  list.eq_of_perm_of_sorted (list.perm_merge_sort _ _) 
    (of_multiset (to_multiset l)).property l.property

def multiset_equiv : nondec_list α ≃ multiset α := {
  to_fun := to_multiset,
  inv_fun := of_multiset,
  left_inv := of_to_multiset,
  right_inv := to_of_multiset
}

def nil : nondec_list α := ⟨[],list.pairwise.nil⟩ 

def cons (a : α) (l : nondec_list α) (h : ∀ b : α, b ∈ l → a ≤ b) : 
  nondec_list α :=
    ⟨list.cons a (l : list α),list.pairwise.cons h l.property⟩

def map {β : Type} [linear_order β] 
 (f : α → β) (hf : ∀ a₀ a₁, a₀ ≤ a₁ → f a₀ ≤ f a₁) 
 (l : nondec_list α) : (nondec_list β) := 
⟨ (l : list α).map f, 
  (list.pairwise_map f).mpr (list.pairwise.imp hf l.property) ⟩

end nondec_list

def acc : list ℕ → list ℕ 
| [] := []
| (a :: bs) := a :: ((acc bs).map (has_add.add a))

namespace acc

def is_nondec : ∀ (l : list ℕ), (acc l).pairwise has_le.le
| [] := list.pairwise.nil
| (a :: l) := 
begin
  rw [acc], apply list.pairwise.cons,
  { intros x hx, 
    rcases list.mem_map.mp hx with ⟨y,⟨hm,he⟩⟩,
    rw [← he], exact nat.le_add_right a y },
  { let h₀ := λ (a₀ a₁ : ℕ) (h : a₀ ≤ a₁), add_le_add_left h a,
    let h₁ := list.pairwise.imp h₀ (is_nondec l),
    exact (list.pairwise_map (has_add.add a)).mpr h₁ }
end

def nondec (l : list ℕ) : nondec_list ℕ := 
  ⟨acc l, acc.is_nondec l⟩

end acc

def diff₀ : list ℕ → list ℕ
| [] := []
| [a] := []
| (a :: b :: l) := (b - a) :: (diff₀ (b :: l))

lemma diff₀_add (a : ℕ) : ∀ (l : list ℕ),
  diff₀ (l.map (has_add.add a)) = diff₀ l
| [] := rfl
| [b] := by { rw[list.map_singleton], refl }
| (b :: c :: l) := 
begin
  rw [list.map_cons, list.map_cons, diff₀, diff₀],
  congr' 1,
  { exact nat.add_sub_add_left a c b },
  { have h := diff₀_add (c :: l), 
    rw [list.map_cons] at h, exact h }
end

lemma diff₀_acc : ∀ (a : ℕ) (l : list ℕ), diff₀ (acc (a :: l)) = l
| a [] := rfl
| a (b :: l) := 
begin
  rw [acc, acc, list.map_cons, diff₀, add_comm a b, nat.add_sub_cancel b a],
  rw [add_comm b a],
  let h := diff₀_add a (b :: ((acc l).map (has_add.add b))),
  congr' 1,
  rw [list.map_cons] at h, rw [h],
  exact diff₀_acc b l,
end

def diff : list ℕ → list ℕ
| [] := []
| (a :: l) := a :: (diff₀ (a :: l))

lemma diff_acc : ∀ (l : list ℕ), diff (acc l) = l 
| [] := rfl
| [a] := rfl
| (a :: b :: l) := 
begin
  rw [acc, diff], congr' 1, apply diff₀_acc
end

def pnat_sols (k n : ℕ) :=
 { l : list ℕ+ // l.length = k ∧ (l.map (coe : ℕ+ → ℕ)).sum = n }

namespace pnat_sols

def nil : pnat_sols 0 0 := ⟨[],⟨rfl,rfl⟩⟩

def cons {k n m : ℕ} (i : ℕ+) (e : (i : ℕ) + n = m) (l : pnat_sols k n) :
  pnat_sols (k + 1) m := 
⟨ i :: l.val, 
  begin
   split,
   rw [list.length, l.property.left],
   rw [list.map, list.sum_cons, l.property.right, e] 
  end ⟩

lemma cons_inj {k n m : ℕ} (i : ℕ+) (e : (i : ℕ) + n = m) : 
  function.injective (cons i e : pnat_sols k n → pnat_sols (k + 1) m) := 
begin
  rintros ⟨l₀,⟨hl₀,hs₀⟩⟩ ⟨l₁,⟨hl₁,hs₁⟩⟩ el,
  apply subtype.eq, change l₀ = l₁,
  replace el := congr_arg subtype.val el,
  injection el
end

def cons' {k n : ℕ} (i : fin n) (l : pnat_sols k (n - 1 - i)) : 
    pnat_sols (k + 1) n :=
cons (nat.succ_pnat i) 
  ( by { cases n with m, { exact fin.elim0 i},
         let i0 : ℕ := i,
         change (i0 + 1) + ((m + 1) - 1 - i0) = m + 1,
         have : m + 1 - 1 = m := nat.pred_succ m,
         rw [this, add_comm, ← add_assoc],
         have : i0 ≤ m := nat.le_of_lt_succ i.is_lt,
         rw [nat.sub_add_cancel this] }) l

lemma cons'_inj {k n : ℕ} (i : fin n) : 
  function.injective (cons' i : pnat_sols k (n - 1 - i) → pnat_sols (k + 1) n) := 
λ l₀ l₁ e, cons_inj _ _ e

instance enum : ∀ (k n : ℕ), enumeration (pnat_sols k n) 
| 0 0 := 
  { elems := [nil], 
    nodup := list.nodup_singleton nil, 
    complete := λ l, list.mem_singleton.mpr $ subtype.eq $ 
                list.eq_nil_of_length_eq_zero $ l.property.left }
| 0 (n + 1) := 
  { elems := [],
    nodup := list.nodup_nil,
    complete := λ ⟨l,⟨hl,hs⟩⟩, 
      begin
        exfalso,
        rw [list.eq_nil_of_length_eq_zero hl] at hs,
        exact (nat.succ_ne_zero n).symm hs,
      end }
| (k + 1) n := 
  { elems := 
     (fin.enum n).elems.bind (λ i, (enum k (n - 1 - i)).elems.map (cons' i)),
    nodup := 
    begin
      apply list.nodup_bind.mpr; split,
      { intros i hi, 
        exact list.nodup.map (cons'_inj i) (enum k (n - 1 - i)).nodup },
      { have hd : ∀ (i₀ i₁ : fin n), i₀ ≠ i₁ → 
          list.disjoint 
            ((enum k (n - 1 - i₀)).elems.map (cons' i₀))
            ((enum k (n - 1 - i₁)).elems.map (cons' i₁)) := 
        λ i₀ i₁ hn, begin 
          intros l h₀ h₁,
          rcases list.mem_map.mp h₀ with ⟨l₀,⟨hm₀,he₀⟩⟩,
          rcases list.mem_map.mp h₁ with ⟨l₁,⟨hm₁,he₁⟩⟩,
          let he := congr_arg subtype.val (he₀.trans he₁.symm),
          injection he with hei hel,
          exact hn (fin.eq_of_veq (nat.succ_pnat_inj hei)),
        end,
        apply list.pairwise.imp hd enumeration.nodup }
    end,
    complete := λ l,
    begin
      rcases l with ⟨l,⟨hl,hs⟩⟩,
      cases l with i l,
      { rcases hl }, 
      { rw [list.length] at hl, replace hl := nat.succ_inj'.mp hl,
        let i0 := (i : ℕ).pred,
        have hi0 : i = nat.succ_pnat i0 := 
          pnat.eq (nat.succ_pred_eq_of_pos i.pos).symm,
        rw [list.map, list.sum_cons, hi0, nat.succ_pnat_coe, add_comm,
            nat.succ_eq_add_one] at hs,
        have i0_is_lt := nat.lt_of_lt_of_le (i0.lt_succ_self)
         (nat.le_add_left (i0 + 1) (l.map (coe : ℕ+ → ℕ)).sum), 
        rw [hs] at i0_is_lt,
        let i1 : fin n := ⟨i0,i0_is_lt⟩,
        have hi1 : i1 ∈ enumeration.elems := 
          enumeration.complete i1,
        apply list.mem_bind.mpr, 
        use i1, use hi1,
        rw [list.mem_map],
        rw [add_comm, add_comm i0] at hs,
        let hs1 : n - (1 + i0) = (l.map coe).sum := tsub_eq_of_eq_add_rev hs.symm,
        rw [← nat.sub_sub] at hs1,
        use ⟨l,⟨hl,hs1.symm⟩⟩,
        split,
        { apply enumeration.complete },
        { rw [cons', cons], apply subtype.eq, 
          change list.cons i0.succ_pnat l = list.cons i l,
          rw [hi0] } }
    end
  }

/-
def to_finset {n k : ℕ} : pnat_sols (k + 1) (n + 1) → 
 { s : finset (fin n) // s.card = k} := sorry
-/

end pnat_sols

end combinatorics