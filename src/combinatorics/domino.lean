/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

(This is part of an attempt to formalise some material from
 a basic undergraduate combinatorics course.)

 A "domino" means a subset of ℕ × ℕ of the form 
 {i} × {j,j+1} or {i,i+1} × {j}.  Given a finite subset 
 B ⊆ ℕ × ℕ, we ask whether B can be written as a disjoint
 union of dominos.  One basic tool that we can use is the
 chessboard colouring map c : ℕ × ℕ → {black,white}.
 (Probably it is more convenient to use bool = {ff,tt} 
 instead of {black,white}.)  If B can be covered by a
 disjoint set of dominos, then it is clear that the 
 number of black squares in B must be equal to the number 
 of white squares.   Examples should be given to show that
 the converse fails.
-/

import data.fintype.basic algebra.group tactic.ring

namespace combinatorics

lemma finset.mem_pair {α : Type} [decidable_eq α] {u v w : α} :
 u ∈ [v,w].to_finset ↔ u = v ∨ u = w := 
by { intros, simp } 

lemma finset.pair_eq  {α : Type} [decidable_eq α] {u v w x : α} :
 [u,v].to_finset = [w,x].to_finset ↔ 
   (u = w ∧ v = x) ∨ (u = x ∧ v = w) :=
begin
  split,
  { intro h, 
    have hu : u ∈ [u,v].to_finset := by simp,
    have hv : v ∈ [u,v].to_finset := by simp,
    have hw : w ∈ [w,x].to_finset := by simp,
    have hx : x ∈ [w,x].to_finset := by simp,
    rw [  h, finset.mem_pair] at hu hv,
    rw [← h, finset.mem_pair] at hw hx,
    cases hu with hu hu; cases hu;
    cases hv with hv hv; cases hv;
    cases hw with hw hw; cases hw;
    cases hx with hx hx; cases hx;
    try { left , exact ⟨rfl,rfl⟩ } ; 
    try { right, exact ⟨rfl,rfl⟩ } },
  { intro h, 
    cases h with h h; rcases h with ⟨⟨h₀⟩,⟨h₁⟩⟩, 
    { refl },
    { ext z, rw[finset.mem_pair, finset.mem_pair],
      split; exact or.symm } }
end

lemma finset.pair_disjoint {α : Type} [decidable_eq α] {u v w x : α} :
  disjoint [u,v].to_finset [w,x].to_finset ↔ 
  (u ≠ w ∧ u ≠ x ∧ v ≠ w ∧ v ≠ x) :=
begin
  rw [disjoint_iff], change _ ∩ _ = ∅ ↔ _,
  rw [finset.eq_empty_iff_forall_not_mem],
  split,
  { intro h, 
    have hu := h u, have hv := h v, 
    have hw := h w, have hx := h x,
    rw [finset.mem_inter, finset.mem_pair, finset.mem_pair,
        decidable.not_and_iff_or_not,
        decidable.not_or_iff_and_not,decidable.not_or_iff_and_not]
         at hu hv hw hx,
    tauto },
  { rintro ⟨h₀,h₁,h₂,h₃⟩ a ha,
    rw [ finset.mem_inter, finset.mem_pair, finset.mem_pair ] at ha,
    cases ha with ha₀ ha₁, 
    cases ha₀ with ha₀ ha₀; cases ha₀;
    cases ha₁ with ha₁ ha₁; cases ha₁; 
    contradiction }
end

lemma prod.ne {α β : Type*} [decidable_eq α] [decidable_eq β] 
  (a a' : α) (b b' : β) :
  prod.mk a b ≠ prod.mk a' b' ↔ (a ≠ a' ∨ b ≠ b') :=
begin
  rw [ne,prod.eq_iff_fst_eq_snd_eq, decidable.not_and_iff_or_not]
end

lemma mem_list_union {α : Type*} [decidable_eq α] {a : α} {l : list (finset α)} :
  a ∈ l.foldr has_union.union ∅ ↔ ∃ s, s ∈ l ∧ a ∈ s := 
begin
  induction l with s l ih,
  { rw [list.foldr], split; intro h,
    { exfalso, exact finset.not_mem_empty a h },
    { rcases h with ⟨s,hs⟩, exfalso, exact list.not_mem_nil s hs.left } },
  { rw [list.foldr, finset.mem_union], split; intro h,
    { cases h,
      { use s, exact ⟨list.mem_cons_self s l,h⟩ },
      { rcases (ih.mp h) with ⟨t,ht⟩,
        use t, exact ⟨list.mem_cons_of_mem s ht.left, ht.right⟩ } },
    { rcases h with ⟨t,ht⟩,
      rcases (list.mem_cons_iff t s l).mp ht.left with ⟨⟨_⟩|ht⟩ ,
      { left, exact ht.right },
      { right, exact ih.mpr ⟨t,⟨h,ht.right⟩⟩ } } }
end

namespace chess

def square := ℕ × ℕ 

namespace square 

lemma eq_iff {u v : square} : u = v ↔ u.1 = v.1 ∧ u.2 = v.2 := 
prod.eq_iff_fst_eq_snd_eq

def rank : square → ℕ := λ u, u.1 + u.2
def color : square → bool := λ u, u.rank.bodd

def hstep : square → square := λ u, ⟨u.1 + 1,u.2⟩
def vstep : square → square := λ u, ⟨u.1,u.2 + 1⟩

lemma hstep_eq (u v : square) : u.hstep = v.hstep ↔ u = v := 
begin
  cases u with i j, cases v with k l, rw [eq_iff, eq_iff],
  change i + 1 = k + 1 ∧ j = l ↔ i = k ∧ j = l,
  rw [nat.succ_inj']
end

lemma vstep_eq (u v : square) : u.vstep = v.vstep ↔ u = v := 
begin
  cases u with i j, cases v with k l, rw [eq_iff, eq_iff],
  change i = k ∧ j + 1 = l + 1 ↔ i = k ∧ j = l,
  rw [nat.succ_inj']
end

lemma hstep_ne_self (u : square) : u.hstep ≠ u := λ h,
by { rw[eq_iff] at h, exact nat.succ_ne_self _ h.1 }

lemma vstep_ne_self (u : square) : u.vstep ≠ u := λ h,
by { rw[eq_iff] at h, exact nat.succ_ne_self _ h.2 }

lemma rank_vstep (u : square) : u.vstep.rank = u.rank + 1 := rfl
lemma rank_hstep (u : square) : u.hstep.rank = u.rank + 1 :=  nat.succ_add _ _

lemma color_vstep (u : square) : u.vstep.color = bnot u.color := 
  by { simp only [color], rw [rank_vstep, nat.bodd_succ] }

lemma color_hstep (u : square) : u.hstep.color = bnot u.color := 
  by { simp only [color], rw [rank_hstep, nat.bodd_succ] }
  
end square

def count_pair := bool → ℕ 

namespace count_pair

instance : add_comm_monoid count_pair := 
 by {unfold count_pair, pi_instance, }

def both : count_pair 
| _ := 1

def delta : bool → count_pair
| ff ff := 1
| ff tt := 0
| tt ff := 0
| tt tt := 1

def delta' (n : ℕ) : count_pair := delta n.bodd

def tot (x : count_pair) : ℕ := (x ff) + (x tt)

lemma tot_both : tot both = 2 := rfl

lemma tot_delta : ∀ b : bool, tot (delta b) = 1
| ff := rfl
| tt := rfl

lemma delta_succ (b : bool) : (delta b) + (delta (bnot b)) = both :=
by { ext x, cases b; cases x; refl }

lemma delta'_succ (n : ℕ) : (delta' n) + (delta' n.succ) = both :=
by { dsimp [delta'], rw [nat.bodd_succ], exact delta_succ n.bodd }

lemma tot_delta' (n : ℕ) : tot (delta' n) = 1 := tot_delta n.bodd

instance tot_hom : is_add_monoid_hom tot := {
 map_zero := rfl,
 map_add := λ u v, 
 begin
  unfold tot, 
  change ((u ff) + (v ff)) + ((u tt) + (v tt)) = 
         ((u ff) + (u tt)) + ((v ff) + (v tt)),
  rw[add_assoc,← add_assoc (v ff)],
  rw[add_comm (v ff) (u tt),add_assoc,add_assoc],
 end
}

def diff (x : count_pair) : ℤ := (x tt) - (x ff)

instance diff_hom : is_add_monoid_hom diff := {
 map_zero := rfl,
 map_add := λ u v, 
 begin
  unfold diff, 
  have : (u + v) tt = (u tt) + (v tt) := rfl, rw[this,int.coe_nat_add],
  have : (u + v) ff = (u ff) + (v ff) := rfl, rw[this,int.coe_nat_add],
  ring,
 end
}

lemma diff_both : diff both = 0 := rfl

end count_pair

open chess

def color_count (s : finset square) : count_pair := 
 s.sum (λ x, (count_pair.delta x.color))

def black_count (s : finset square) : ℕ := color_count s ff

def white_count (s : finset square) : ℕ := color_count s tt

def color_diff (s : finset (ℕ × ℕ)) : ℤ := (color_count s).diff

lemma count_eq (s : finset (ℕ × ℕ)) : 
 (color_count s).tot = s.card := 
begin
 rw[color_count,← finset.sum_hom _ count_pair.tot],
 have : (λ x : square, (count_pair.delta x.color).tot) = (λ x, 1) := 
  by {funext, apply count_pair.tot_delta},
 rw[this,finset.sum_const,nat.smul_eq_mul,mul_one],
end

namespace color_count

lemma empty : color_count ∅ = 0 := by {rw[color_count,finset.sum_empty]}

lemma sum (s t : finset square) : 
 (color_count (s ∪ t)) + (color_count (s ∩ t)) = 
 (color_count s) + (color_count t) := 
  finset.sum_union_inter

lemma disjoint_sum (s t : finset (ℕ × ℕ)) (h : disjoint s t) : 
 (color_count (s ∪ t)) = (color_count s) + (color_count t) := 
   finset.sum_union h

lemma disjoint_sum' (ss : list (finset (ℕ × ℕ)))
 (h : ss.pairwise disjoint) : 
  color_count (ss.foldr has_union.union ∅) = (ss.map color_count).sum := 
begin
  induction ss with s ss ih,
  { refl },
  { let t := ss.foldr has_union.union ∅,
    rw [list.pairwise_cons] at h,
    rw [list.foldr, list.map, list.sum_cons, ← ih h.right],
    apply disjoint_sum s t, rw [disjoint_iff], 
    change s ∩ t = ∅, apply finset.eq_empty_of_forall_not_mem,
    intros x hx,
    replace hx := finset.mem_inter.mp hx,
    rcases mem_list_union.mp hx.right with ⟨u,hu⟩,
    have hx' := finset.mem_inter.mpr ⟨hx.1,hu.2⟩,
    have hsu : s ∩ u = ∅ := disjoint_iff.mp (h.left u hu.left),
    rw [hsu] at hx', exact finset.not_mem_empty x hx' }
end 

end color_count

end chess

open chess

inductive domino : Type
| horizontal : square → domino
| vertical : square → domino

namespace domino

def to_list : domino → list square 
| (horizontal u) := [u, u.hstep]
| (vertical   u) := [u, u.vstep]

lemma to_list_length (d : domino) : 
  d.to_list.length = 2 := by { cases d; refl }

lemma to_list_nodup (d : domino) : d.to_list.nodup := 
begin
  cases d with u u; simp [to_list, list.nodup_cons],
  exact u.hstep_ne_self.symm, exact u.vstep_ne_self.symm
end

def to_finset (d : domino) : finset square :=
  ⟨d.to_list,d.to_list_nodup⟩ 

lemma to_list_coe (d : domino) : 
  d.to_finset = d.to_list.to_finset := list.to_finset_eq d.to_list_nodup

lemma color_count (d : domino) :
  color_count d.to_finset = count_pair.both :=
begin
  rw [chess.color_count],
  rw [finset.sum_eq_multiset_sum d.to_finset 
       (count_pair.delta ∘ square.color)],
  have : d.to_finset.val = d.to_list := rfl, 
  rw [this, multiset.coe_map, multiset.coe_sum],
  cases d with u u;
  rw [to_list, list.map_cons, list.map_singleton,
      list.sum_cons, list.sum_cons, list.sum_nil, add_zero];
  rw [function.comp_app, function.comp_app],
  rw [square.color_hstep, count_pair.delta_succ],
  rw [square.color_vstep, count_pair.delta_succ]
end

def overlap : domino → domino → Prop
| (horizontal u) (horizontal v) := u = v ∨ u = v.hstep ∨ u.hstep = v 
| (horizontal u) (vertical v)   := u = v ∨ u = v.vstep ∨ u.hstep = v ∨ u.hstep = v.vstep  
| (vertical u) (horizontal v)   := u = v ∨ u = v.hstep ∨ u.vstep = v ∨ u.vstep = v.hstep
| (vertical u) (vertical v)     := u = v ∨ u = v.vstep ∨ u.vstep = v

instance overlap_dec : decidable_rel overlap := 
 λ a b, by {cases a with u u; cases b with v v; 
            rw[overlap]; apply_instance}

def disjoint : domino → domino → Prop := 
 λ a b , ¬ (overlap a b)

instance disjoint_dec : decidable_rel disjoint := 
 λ a b, by {dsimp[disjoint],apply_instance}

lemma disjoint_iff {a b : domino} :
 disjoint a b ↔ _root_.disjoint a.to_finset b.to_finset  := 
begin
  cases a with u u; cases b with v v;
  simp only [disjoint, to_list_coe, to_list, finset.pair_disjoint, ne];
  rw [overlap];
  try { rw[square.hstep_eq] at * }; try { rw[square.vstep_eq] at * };
  tauto
end

def track (l : list domino) := (l.map to_finset).foldr has_union.union ∅

def is_cover (s : finset (ℕ × ℕ)) (l : list domino) := 
  l.pairwise disjoint ∧ (track l) = s 

def has_cover (s : finset (ℕ × ℕ)) := ∃ l, is_cover s l

lemma diff_eq_zero {l : list domino} 
  (hl : l.pairwise disjoint) : 
      (chess.color_count (track l)).diff = 0 :=
begin
  rw [chess.count_pair.diff],
  let h₀ := list.pairwise.imp 
    (λ a b,(@disjoint_iff a b).mp) hl,
  let h₁ := (list.pairwise_map to_finset).mpr h₀,
  let h₂ := 
   chess.color_count.disjoint_sum' (l.map to_finset) h₁,
end

end domino
end combinatorics