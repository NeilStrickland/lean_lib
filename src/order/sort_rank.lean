/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file formalises the fact that any finite, linearly ordered
set of size n has a unique order-isomorphism with the set 
fin n =  {0,...,n-1}.
-/

import data.finset data.fintype.basic
import data.fin_extra
open list 

variables {α : Type*} 

namespace list

/-
 If we have a list l (of length n) and a natural number i, we might 
 want to refer to the i'th entry in the list, but then we have to 
 decide what to do about the possibility that i is too large so that 
 there is no i'th entry.  We always use 0-based indexing so the 
 i'th entry is defined for i < n but not for i ≥ n.  

 The standard library defines (l.nth i) to be of type (option α),
 and to have value (some x) if i < n and x is the i'th entry, but to
 have value (none) if i ≥ n.  The standard library also defines 
 (l.nth_le i h) to be x if h is a proof of i < n.  Here we just 
 repackage this slightly: the pair ⟨i,h⟩ gives a term of type
 (fin n), and we define l.fin_nth ⟨i,h⟩ to be x again. 
-/
def fin_nth (l : list α) (i : fin l.length) : α := 
 l.nth_le i.val i.is_lt

/- An obvious lemma about the behaviour of fin_nth. -/
lemma fin_nth_cons (a : α) (l : list α) (i : fin l.length) :
 (list.cons a l).fin_nth i.succ = l.fin_nth i := 
begin
 cases i,dsimp[fin.succ,fin_nth],refl,
end

/-
 If R is a relation on α and l is a list, we define 
 (pairwise_nth R l) to be true if all entries in l are R-related
 to all strictly later entries.  For example, if R is an order
 relation then this just means that the list is sorted, and if 
 R is the relation x ≠ y then this just means that l has no
 duplicates.  Here we define pairwise_nth in the obvious way
 using indices.  We then prove that our pairwise_nth is 
 equivalent to the definition of pairwise in the standard 
 library, which is formulated by structural induction rather
 than using indices.
-/

def pairwise_nth₀ (R : α → α → Prop) (l : list α) := 
 ∀ (i j : fin l.length), i < j → R (l.fin_nth i) (l.fin_nth j)

def pairwise_nth (R : α → α → Prop) (l : list α) := 
 ∀ {i j : ℕ} (hi : i < j) (hj : j < l.length), 
   R (l.nth_le i (lt_trans hi hj)) (l.nth_le j hj)

lemma pairwise_nth_mp {R : α → α → Prop} {l : list α} 
 (p : pairwise R l) : pairwise_nth R l :=
begin
  induction p with a l0 R_a_l0 p0 ih,
  { intros i j hi hj, cases hj },
  { intros i j hi hj,
    cases j with j₀, { cases hi },
    have hj0 : j₀ < l0.length := nat.lt_of_succ_lt_succ hj,
    cases i with i₀,
    { exact R_a_l0 _ (l0.nth_le_mem j₀ hj0) },
    { exact ih (nat.lt_of_succ_lt_succ hi) hj0 } }
end

lemma pairwise_nth_mpr {R : α → α → Prop} {l : list α} 
 (hl : pairwise_nth R l) : (pairwise R l) := 
begin
  induction l with a l ih,
  { exact @pairwise.nil _ R },
  { have R_a_l : ∀ (b ∈ l), (R a b) :=
    begin
      intros b b_in_l,
      rcases nth_le_of_mem b_in_l with ⟨j,⟨hj,eq_b⟩⟩,
      rw [← eq_b],
      exact hl (nat.zero_lt_succ j) (nat.succ_lt_succ hj)
    end,
    have : l.pairwise R := 
    begin
      apply ih,
      intros i j hi hj,
      exact hl (nat.succ_lt_succ hi) (nat.succ_lt_succ hj),
    end,
    exact pairwise.cons R_a_l this }
end

lemma pairwise_nth_iff {R : α → α → Prop} {l : list α} :
 (pairwise R l) ↔ (pairwise_nth R l) :=
  iff.intro (@pairwise_nth_mp _ R l) (@pairwise_nth_mpr _ R l)

/-
 The standard library defines a list to be sorted if all entries are
 less than or equal to all strictly later entries.  Here we define 
 a list to be strongly sorted if the relevant inequalities hold 
 strictly.  This is clearly equivalent to saying that the list is
 sorted and has distinct entries; we also formalise this equivalence.
-/

variables [linear_order α] [decidable_rel (@has_le.le α _)]

def strongly_sorted (l : list α) : Prop := 
 list.pairwise has_lt.lt l

lemma strongly_sorted_of_sorted_nodup (l : list α) :
 l.sorted has_le.le → l.nodup → l.strongly_sorted := 
begin
 intro l_sorted,
 induction l_sorted with a l0 a_le_l0 l0_sorted ih,
 {intro,exact pairwise.nil},
 {intro l_nodup,
  cases l_nodup with _ _ a_ne_l0 l0_nodup,
  have l0_strongly_sorted := ih l0_nodup,
  have a_lt_l0 : ∀ (x : α) (x_in_l0 : x ∈ l0), (a < x) := 
  begin
   intros x x_in_l0,
   exact lt_of_le_of_ne (a_le_l0 x x_in_l0) (a_ne_l0 x x_in_l0),
  end,
  exact pairwise.cons a_lt_l0 l0_strongly_sorted,
 }
end

lemma sorted_of_strongly_sorted (l : list α) : 
 l.strongly_sorted → l.sorted has_le.le := 
begin
 intro l_strongly_sorted,
 induction l_strongly_sorted with a l0 a_lt_l0 l0_strongly_sorted ih,
 {exact pairwise.nil},
 {have a_le_l0 : ∀ x ∈ l0, a ≤ x := 
   λ x x_in_l0,le_of_lt (a_lt_l0 x x_in_l0),
  have l0_sorted := ih,
  exact pairwise.cons a_le_l0 l0_sorted
 }
end

lemma nodup_of_strongly_sorted (l : list α) : 
 l.strongly_sorted → l.nodup := 
begin
 intro l_strongly_sorted,
 induction l_strongly_sorted with a l0 a_ne_l0 l0_strongly_sorted ih,
 {exact pairwise.nil},
 {have a_ne_l0 : ∀ x ∈ l0, a ≠ x := 
   λ x x_in_l0,ne_of_lt (a_ne_l0 x x_in_l0),
  have l0_nodup := ih,
  exact pairwise.cons a_ne_l0 l0_nodup
 }
end

/-
 Sortedness is defined in the standard library by structural
 induction. Here we reformulate it in terms of indices.
-/

lemma sorted_nth_lt_mp {l : list α} 
 (l_nodup : list.nodup l)
 (l_sorted : list.sorted has_le.le l)
 {i j : ℕ} (hi : i < j) (hj : j < l.length) :
 (l.nth_le i (lt_trans hi hj) < l.nth_le j hj) := 
begin
  let x := l.nth_le i (lt_trans hi hj),
  let y := l.nth_le j hj,
  have x_ne_y : x ≠ y := pairwise_nth_mp l_nodup hi hj,
  have x_le_y : x ≤ y := pairwise_nth_mp l_sorted hi hj,
  exact lt_of_le_of_ne x_le_y x_ne_y,
end

lemma sorted_nth_le_mp {l : list α} 
 (l_nodup : list.nodup l)
 (l_sorted : list.sorted has_le.le l)
 {i j : ℕ} (hi : i ≤ j) (hj : j < l.length) :
 (l.nth_le i (lt_of_le_of_lt hi hj) ≤ l.nth_le j hj) := 
begin
 by_cases h : i = j,
 { cases h, refl },
 { have hi' : i < j := lt_of_le_of_ne hi h,
   exact (le_of_lt $ sorted_nth_lt_mp l_nodup l_sorted hi' hj) }
end

lemma sorted_nth_lt {l : list α} 
 (l_nodup : list.nodup l)
 (l_sorted : list.sorted has_le.le l) 
 { i j : ℕ } (hi : i < l.length) (hj : j < l.length) :
  (i < j) ↔ (l.nth_le i hi < l.nth_le j hj) := 
begin
 split,
 { intro hi', 
   exact sorted_nth_lt_mp l_nodup l_sorted hi' hj },
 { intro x_lt_y,
   rcases lt_or_ge i j with i_lt_j | j_le_i,
   { assumption },
   { exfalso,
     let y_le_x := sorted_nth_le_mp l_nodup l_sorted j_le_i hi,
     exact not_lt_of_ge y_le_x x_lt_y } }
end

lemma sorted_nth_le {l : list α} 
 (l_nodup : list.nodup l)
 (l_sorted : list.sorted has_le.le l) 
 { i j : ℕ } (hi : i < l.length) (hj : j < l.length) :
  (i ≤ j) ↔ (l.nth_le i hi ≤ l.nth_le j hj) := 
begin
 split,
 { intro hi', 
   exact sorted_nth_le_mp l_nodup l_sorted hi' hj },
 { intro x_le_y,
   rcases le_or_gt i j with i_le_j | j_lt_i,
   { assumption },
   { exfalso,
     let y_lt_x := sorted_nth_lt_mp l_nodup l_sorted j_lt_i hi,
     exact not_le_of_gt y_lt_x x_le_y } }
end

end list 

namespace finset 

variables [linear_order α] [decidable_rel (@has_le.le α _)]

/-
 The standard library defines a function that accepts a finite set s
 and returns the list of elements in sorted order.  The next lemma 
 tells us how we can recognise that list if we have obtained it by
 other means.
-/

theorem list.perm.eqv' (α : Type*) : equivalence (@perm α) :=
mk_equivalence (@perm α) (@perm.refl α) (@perm.symm α) (@perm.trans α)

instance list.is_setoid' (α : Type*) : setoid (list α) :=
setoid.mk (@perm α) (list.perm.eqv' α)

lemma sort_spec (s : finset α) (l : list α) 
 (l_nodup : l.nodup) (l_sorted : l.sorted has_le.le) 
  (s_eq_l : s = l.to_finset) : s.sort has_le.le = l := 
begin
 let h0 := (congr_arg val
            (eq.trans (eq.trans (to_finset_eq (sort_nodup has_le.le s)) (eq.trans (sort_to_finset has_le.le s) s_eq_l)) 
                      (eq.symm (to_finset_eq l_nodup)))),
 let h1 := list.eq_of_perm_of_sorted (@quotient.exact (list α) (list.is_setoid' α) _ _ h0) (sort_sorted has_le.le s) l_sorted,
 let ll : multiset α := quot.mk _ l,
 have ll_nodup : ll.nodup := multiset.coe_nodup.mpr l_nodup,
 have ll_eq : (⟨ll,ll_nodup⟩ : finset α) = l.to_finset := list.to_finset_eq l_nodup,
 let m := s.sort has_le.le,
 have m_nodup : m.nodup := s.sort_nodup has_le.le,
 have m_sorted : m.sorted has_le.le := s.sort_sorted has_le.le,
 let mm : multiset α := quot.mk _ m,
 have mm_nodup : mm.nodup := multiset.coe_nodup.mpr m_nodup,
 have mm_eq : (⟨mm,mm_nodup⟩ : finset α) = m.to_finset := list.to_finset_eq m_nodup,
 have m_to_finset : m.to_finset = s :=
  s.sort_to_finset has_le.le,
 let mm_eq_ll :=
  congr_arg finset.val ((mm_eq.trans (m_to_finset.trans s_eq_l)).trans ll_eq.symm),
 dsimp[finset.val] at mm_eq_ll,
 have perm_m_l : perm m l := quotient.exact mm_eq_ll,
 exact list.eq_of_perm_of_sorted perm_m_l m_sorted l_sorted,
end

/-
 The next lemma is equivalent to the previous one.  However, as an 
 experiment we have written it as a single term rather than using 
 tactics.  We used the command "#print sort_spec" to print the 
 proof term generated automatically be Lean from the tactic proof, 
 and then reorganised it a bit to eliminate some inefficiencies.
-/

lemma sort_spec_alt (s : finset α) (l : list α) 
 (l_nodup : l.nodup) (l_sorted : l.sorted has_le.le) 
  (s_eq_l : s = l.to_finset) : s.sort has_le.le = l := 
    list.eq_of_perm_of_sorted
     (@quotient.exact 
      (list α)
      (list.is_setoid' α) 
      _ 
      _ 
      (@congr_arg 
       (finset α)
       (multiset α) 
       _ 
       _ 
       finset.val 
       (eq.trans
        (eq.trans (to_finset_eq (sort_nodup has_le.le s)) (eq.trans (sort_to_finset has_le.le s) s_eq_l))
        (eq.symm (to_finset_eq l_nodup))
       )
      )
     )
     (sort_sorted has_le.le s) 
     l_sorted

section rank_equiv 

/-
 We now give our first version of the fact that any finite, linearly ordered 
 set of size n is order-isomorphic to (fin n). In this version, the type α has
 a decidable linear order and s is a finite subset of α that need not contain 
 all elements of α.  In order to talk about an order-equivalence we need to 
 convert s into a separate type by considering {a // a ∈ s}. The definition 
 (rank_equiv s) gives an equivalence from this type to (fin n), but it is not 
 initially packaged with any information about order-preserving properties.  
 Instead, we prove those properties as four separate lemmas after the 
 definition of rank_equiv.

 Note that we have arguments n and s_card : s.card = n, and we produce an
 equivalence with (fin n).  One might think that it would be more natural to
 just produce an equivalence with (fin s.card), and then use eq.mp to convert
 this to (fin n) if necessary.  Unfortunately, this leads to a lot of tedious 
 troubles with heterogenous equality.  As far as I can tell, the present 
 approach is the simplest way to avoid that.
-/

variables {s : finset α} {n : ℕ} (s_card : s.card = n)
include s_card

def rank_equiv : { a // a ∈ s } ≃ fin n := 
begin
 let l := s.sort has_le.le,
 have l_nodup : list.nodup l := finset.sort_nodup has_le.le s,
 have l_eq_s : l.to_finset = s := by simp[finset.sort_eq],
 have l_len : l.length = n := 
  ((@eq.subst (finset α) (λ t, t.card = l.length) _ _ l_eq_s
             (list.to_finset_card_of_nodup l_nodup)).symm).trans s_card,
 let mem_equiv : ∀ a : α, a ∈ s ↔ a ∈ l :=
  λ a, @eq.subst (finset α) (λ t, a ∈ t ↔ a ∈ l) _ _ l_eq_s
         (@list.mem_to_finset α _ a l),
 let to_fun : { a // a ∈ s } → fin n := 
 begin
  intro a,
  have a_in_l : a.val ∈ l := (mem_equiv a.val).mp a.property,
  let i : ℕ := list.index_of a.val l,
  have i_lt_n : i < n :=
   l_len.subst (list.index_of_lt_length.mpr a_in_l),
  exact ⟨i,i_lt_n⟩ 
 end,
 let inv_fun : fin n → { a // a ∈ s } := 
 begin
  intro i,
  have i_is_lt : i.val < l.length := @eq.subst ℕ (λ m, i.val < m) _ _ l_len.symm i.is_lt,
  let a := l.nth_le i.val i_is_lt,
  have a_in_s : a ∈ s := (mem_equiv a).mpr (l.nth_le_mem i.val i_is_lt),
  exact ⟨a,a_in_s⟩ 
 end,
 have left_inv : ∀ a, inv_fun (to_fun a) = a := 
 begin
  intro a,
  rcases a with ⟨a_val,a_in_s⟩,
  have a_in_l : a_val ∈ l := (mem_equiv a_val).mp a_in_s, 
  let i := list.index_of a_val l,
  have i_lt_len : i < l.length := list.index_of_lt_length.mpr a_in_l,
  have i_lt_n : i < n := l_len.subst i_lt_len,
  dsimp[inv_fun,to_fun],
  apply subtype.eq,dsimp[subtype.val],
  exact list.index_of_nth_le i_lt_len,
 end,
 have right_inv : ∀ i, to_fun (inv_fun i) = i := 
 begin
  intro i,
  rcases i with ⟨i_val,i_lt_n⟩,
  have i_lt_len : i_val < l.length := l_len.symm.subst i_lt_n,
  dsimp[inv_fun,to_fun],
  apply fin.eq_of_veq,dsimp[subtype.val],
  exact list.nth_le_index_of l_nodup i_val i_lt_len,
 end,
 exact ⟨to_fun,inv_fun,left_inv,right_inv⟩, 
end

lemma seq_le (i1 i2 : fin n) :
 i1 ≤ i2 ↔ (((rank_equiv s_card).inv_fun i1).val ≤ ((rank_equiv s_card).inv_fun i2).val) := 
begin
 dsimp [rank_equiv, nth_le, has_le.le, fin.le],
 let l := s.sort has_le.le,
 have l_nodup : list.nodup l := finset.sort_nodup has_le.le s,
 have l_sorted : l.sorted has_le.le := sort_sorted has_le.le s,
 have l_eq_s : l.to_finset = s := by simp[finset.sort_eq],
 have l_len : l.length = n := 
  ((@eq.subst (finset α) (λ t, t.card = l.length) _ _ l_eq_s
             (list.to_finset_card_of_nodup l_nodup)).symm).trans s_card,
 have i1p : i1.val < l.length := by { rw[l_len], exact i1.is_lt },
 have i2p : i2.val < l.length := by { rw[l_len], exact i2.is_lt },
 exact list.sorted_nth_le l_nodup l_sorted i1p i2p
end

lemma seq_lt (i1 i2 : fin n) :
 i1 < i2 ↔ (((rank_equiv s_card).inv_fun i1).val < ((rank_equiv s_card).inv_fun i2).val) := 
begin
 dsimp [rank_equiv, nth_le, has_le.le, fin.le],
 let l := s.sort has_le.le,
 have l_nodup : list.nodup l := finset.sort_nodup has_le.le s,
 have l_sorted : l.sorted has_le.le := sort_sorted has_le.le s,
 have l_eq_s : l.to_finset = s := by simp[finset.sort_eq],
 have l_len : l.length = n := 
  ((@eq.subst (finset α) (λ t, t.card = l.length) _ _ l_eq_s
             (list.to_finset_card_of_nodup l_nodup)).symm).trans s_card,
 have i1p : i1.val < l.length := by { rw[l_len], exact i1.is_lt },
 have i2p : i2.val < l.length := by { rw[l_len], exact i2.is_lt },
 exact list.sorted_nth_lt l_nodup l_sorted i1p i2p
end

lemma rank_le (a1 a2 : {a // a ∈ s }) :
 a1.val ≤ a2.val ↔ (rank_equiv s_card).to_fun a1 ≤ (rank_equiv s_card).to_fun a2 := 
begin
 let f := rank_equiv s_card,
 let i1 := f.to_fun a1,
 let i2 := f.to_fun a2,
 let a1a := f.inv_fun i1,
 let a2a := f.inv_fun i2,
 let h := ((seq_le s_card) (f.to_fun a1) (f.to_fun a2)).symm,
 let e1 : (f.inv_fun i1).val = a1.val := congr_arg subtype.val (f.left_inv a1),
 let e2 : (f.inv_fun i2).val = a2.val := congr_arg subtype.val (f.left_inv a2),
 split,
 {intro h1,rw[← e1,← e2] at h1,exact h.mp h1,},
 {intro h2,let h3 := h.mpr h2,rw[e1,e2] at h3,exact h3}
end

lemma rank_lt (a1 a2 : {a // a ∈ s }) :
 a1.val < a2.val ↔ ((rank_equiv s_card).to_fun a1) < ((rank_equiv s_card).to_fun a2) := 
begin
 let f := rank_equiv s_card,
 let i1 := f.to_fun a1,
 let i2 := f.to_fun a2,
 let a1a := f.inv_fun i1,
 let a2a := f.inv_fun i2,
 let h := ((seq_lt s_card) (f.to_fun a1) (f.to_fun a2)).symm,
 let e1 : (f.inv_fun i1).val = a1.val := congr_arg subtype.val (f.left_inv a1),
 let e2 : (f.inv_fun i2).val = a2.val := congr_arg subtype.val (f.left_inv a2),
 split,
 {intro h1,rw[← e1,← e2] at h1,exact h.mp h1,},
 {intro h2,let h3 := h.mpr h2,rw[e1,e2] at h3,exact h3}
end

lemma rank_as_card (a : { x // x ∈ s}) :
 ((rank_equiv s_card).to_fun a).val = card (s.filter (λ x, x < a.val)) := 
begin
 let f := rank_equiv s_card,
 let u := s.filter (λ x, x < a.val),
 let ut := {x // x ∈ u},
 let k := f.to_fun a,
 have fi_k : f.inv_fun k = a := f.left_inv a,
 let g_to_fun : ut → fin k.val := 
 begin
  intro x,
  let x0 : { x // x ∈ s } := ⟨x.val,(mem_filter.mp x.property).left⟩,
  let x_lt_a : x0.val < a.val := (mem_filter.mp x.property).right,
  let i := f.to_fun x0,
  let i_lt_k : i < k := ((rank_lt s_card) x0 a).mp x_lt_a,
  let i_lt_k_val : i.val < k.val := 
  begin
   let h := i_lt_k,
   dsimp[has_lt.lt,fin.lt] at h,
   exact h,
  end,
  exact ⟨i.val,i_lt_k_val⟩,
 end,
 let g_inv_fun : fin k.val → ut := 
 begin
  intro i,
  let i0 : fin n := ⟨i.val,lt_trans i.is_lt k.is_lt⟩,
  have i0_lt_k : i0 < k := by { simp[has_lt.lt,fin.lt], exact i.is_lt,},
  let x0 := f.inv_fun i0,
  let x_lt_a := ((seq_lt s_card) i0 k).mp i0_lt_k,
  rw[fi_k] at x_lt_a,
  have x_in_u : x0.val ∈ u := 
  begin
   apply mem_filter.mpr,
   exact ⟨x0.property,x_lt_a⟩,
  end,
  exact ⟨x0.val,x_in_u⟩, 
 end,
 have g_left_inv : ∀ x, g_inv_fun (g_to_fun x) = x := 
 begin
  intro x,
  dsimp[g_to_fun,g_inv_fun],
  apply subtype.eq; simp[subtype.val]
 end,
 have g_right_inv : ∀ i, g_to_fun (g_inv_fun i) = i := 
 begin
  intro i,
  dsimp[g_to_fun,g_inv_fun],
  apply fin.eq_of_veq; simp[subtype.val]
 end,
 let g : ut ≃ fin k.val := ⟨g_to_fun,g_inv_fun,g_left_inv,g_right_inv⟩,
 let h0 := fintype.card_congr g, 
 let h1 := @finset.card_attach α u,
 let h2 := fintype.card_fin k.val,
 exact (h1.symm.trans (h0.trans h2)).symm,
end

end rank_equiv

end finset

namespace fintype
open finset fintype 

variables [linear_order α] [decidable_rel (@has_le.le α _)]
variables [fintype α] {n : ℕ} (α_card : card α = n)
include α_card

/-
 We now give our second version of the fact that any finite, linearly ordered 
 set of size n is order-isomorphic to (fin n). In this version we assume given
 an instance of (fintype α), which is essentially a proof that the whole type 
 α is finite. From this we build an equivalence from α to (fin n), and again 
 we prove the order properties as separate lemmas.
-/

def rank_equiv : α ≃ fin n := 
begin
 have h0 : finset.card (@elems α _) = n := α_card,
 let f := finset.rank_equiv h0,
 let to_fun : α → fin n := λ a, f.to_fun ⟨a,mem_univ a⟩,
 let inv_fun : fin n → α := λ i, (f.inv_fun i).val,
 have left_inv : ∀ a : α, inv_fun (to_fun a) = a := 
  λ a, congr_arg subtype.val (f.left_inv ⟨a,mem_univ a⟩),
 have right_inv : ∀ i : fin n, to_fun (inv_fun i) = i := 
 begin
  intro i,
  have e : f.inv_fun i = ⟨inv_fun i,mem_univ _⟩ := 
   by {apply subtype.eq,simp[inv_fun]},
  dsimp[inv_fun,to_fun],simp[e]
 end,
 exact ⟨to_fun,inv_fun,left_inv,right_inv⟩,
end

lemma seq_le (i1 i2 : fin n) : 
 i1 ≤ i2 ↔ (rank_equiv α_card).inv_fun i1 ≤ (rank_equiv α_card).inv_fun i2 := 
  (seq_le α_card) i1 i2

lemma seq_lt (i1 i2 : fin n) : 
 i1 < i2 ↔ (rank_equiv α_card).inv_fun i1 < (rank_equiv α_card).inv_fun i2 := 
  (seq_lt α_card) i1 i2

lemma rank_le (a1 a2 : α) : 
 a1 ≤ a2 ↔ (rank_equiv α_card).to_fun a1 ≤ (rank_equiv α_card).to_fun a2 := 
  (rank_le α_card) ⟨a1,mem_univ a1⟩ ⟨a2,mem_univ a2⟩

lemma rank_lt (a1 a2 : α) : 
 a1 < a2 ↔ (rank_equiv α_card).to_fun a1 < (rank_equiv α_card).to_fun a2 := 
  (rank_lt α_card) ⟨a1,mem_univ a1⟩ ⟨a2,mem_univ a2⟩

end fintype

namespace fin 
/-
 The only strictly increasing self-map of (fin n) is the identity
-/
lemma rigid {n : ℕ} {f : fin n → fin n} 
 (f_mono : ∀ {i1 i2 : fin n}, i1 < i2 → (f i1) < (f i2)) :
  ∀ (i : fin n), f i = i := 
begin
 induction n with n0 ih,
 {intro i,exact fin.elim0 i},
 {
  let f0 : fin n0 → fin n0 := 
  begin
   intro i0,
   let h0 := ne_of_lt (lt_of_le_of_lt (fin.zero_le (f 0)) (f_mono (@fin.zero_lt_succ n0 i0))), 
   exact fin.pred (f i0.succ) h0.symm,
  end,
  have succ_f0 : ∀ (i0 : fin n0), (f0 i0).succ = f i0.succ := 
  begin
   intro i0,
   let h0 := ne_of_lt (lt_of_le_of_lt (fin.zero_le (f 0)) (f_mono (@fin.zero_lt_succ n0 i0))), 
   exact fin.succ_pred (f i0.succ) h0.symm,
  end,
  have f0_mono : ∀ {i1 i2 : fin n0}, i1 < i2 → (f0 i1) < (f0 i2) :=
  begin
   intros i1 i2 i1_lt_i2,
   let h0 := f_mono (fin.succ_lt_succ i1_lt_i2),
   rw[← (succ_f0 i1)] at h0,
   rw[← (succ_f0 i2)] at h0,
   exact fin.lt_of_succ_lt_succ h0,
  end,
  let f0_id := ih @f0_mono,
  have f_zero_a : ∀ (j : fin n0.succ), f 0 = j → j = 0 := 
  begin
   intros j e, cases j with j_val j_is_lt, cases j_val with j0_val,
   {refl},
   {
     exfalso,
     have j0_is_lt : j0_val < n0 := nat.lt_of_succ_lt_succ j_is_lt,
     let j0 : fin n0 := ⟨j0_val,j0_is_lt⟩,
     let j := j0.succ,
     have h0 : f j = j := (succ_f0 j0).symm.trans (congr_arg fin.succ (f0_id j0)), 
     have h1 : f 0 < f j := f_mono (@fin.zero_lt_succ n0 j0),
     have h2 : j < f j := @eq.subst (fin n0.succ) (λ k, k < f j) _ _ e h1,
     exact (ne_of_lt h2) h0.symm,
   }
  end,
  have f_zero : f 0 = 0 := f_zero_a (f 0) rfl,
  intro i, cases i with i_val i_is_lt, cases i_val with i0_val,
  {exact f_zero,},
  {
   have i0_is_lt : i0_val < n0 := nat.lt_of_succ_lt_succ i_is_lt,
   let h0 := congr_arg fin.succ (f0_id ⟨i0_val,i0_is_lt⟩),
   let h1 := succ_f0 ⟨i0_val,i0_is_lt⟩,
   let h2 := h1.symm.trans h0,
   exact h2,
  }
 }
end

end fin