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

import data.fintype algebra.group tactic.ring

namespace combinatorics

namespace chess
def color : (ℕ × ℕ) → bool := λ ⟨i,j⟩, nat.bodd (i + j)

def count_pair := bool → ℕ 

namespace count_pair

instance : add_comm_monoid count_pair := 
 by {unfold count_pair, pi_instance, }

def delta : bool → count_pair
| ff ff := 1
| ff tt := 0
| tt ff := 0
| tt tt := 1

def tot (x : count_pair) : ℕ := (x ff) + (x tt)

lemma tot_delta : ∀ b : bool, tot (delta b) = 1
| ff := rfl
| tt := rfl

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

end count_pair

def color_count (s : finset (ℕ × ℕ)) : count_pair := 
 s.sum (λ x, (count_pair.delta (color x)))

def black_count (s : finset (ℕ × ℕ)) : ℕ := color_count s ff

def white_count (s : finset (ℕ × ℕ)) : ℕ := color_count s tt

lemma count_eq (s : finset (ℕ × ℕ)) : 
 (color_count s).tot = s.card := 
begin
 rw[color_count,← finset.sum_hom count_pair.tot],
 have : (λ x, count_pair.tot (count_pair.delta (color x))) = (λ x, 1) := 
  by {funext, apply count_pair.tot_delta},
 rw[this,finset.sum_const,nat.smul_eq_mul,mul_one],
end

namespace color_count

lemma empty : color_count ∅ = 0 := by {rw[color_count,finset.sum_empty]}

lemma sum (s t : finset (ℕ × ℕ)) : 
 (color_count (s ∪ t)) + (color_count (s ∩ t)) = 
 (color_count s) + (color_count t) := 
  finset.sum_union_inter

lemma disjoint_sum (s t : finset (ℕ × ℕ)) (h : disjoint s t) : 
 (color_count (s ∪ t)) = (color_count s) + (color_count t) := 
   finset.sum_union (disjoint_iff.mp h)

lemma disjoint_sum' (ss : list (finset (ℕ × ℕ)))
 (h : ss.pairwise disjoint) : 
  color_count (ss.foldl has_union.union ∅) = (ss.map color_count).sum := sorry

end color_count

end chess

inductive domino : Type
| horizontal : ℕ → ℕ → domino
| vertical : ℕ → ℕ → domino

namespace domino

def to_finset : domino → finset (ℕ × ℕ) 
| (horizontal i j) := [(prod.mk i j),(prod.mk i.succ j)].to_finset
| (vertical   i j) := [(prod.mk i j),(prod.mk i j.succ)].to_finset

def overlap : domino → domino → Prop
| (horizontal i j) (horizontal k l) :=
    (i = k ∨ i = k.succ ∨ i.succ = k) ∧ j = l
| (horizontal i j) (vertical k l) :=
    (i = k ∨ i.succ = k) ∧ (j = l ∨ j = l.succ)
| (vertical i j) (horizontal k l) :=
    (i = k ∨ i = k.succ) ∧ (j = l ∨ j.succ = l)
| (vertical i j) (vertical k l) :=
    i = k ∧ (j = l ∨ j = l.succ ∨ j.succ = l)

instance overlap_dec : decidable_rel overlap := 
 λ a b, by {cases a with i j i j;cases b with k l k l; 
            rw[overlap]; apply_instance,}

def disjoint : domino → domino → Prop := 
 λ a b , ¬ (overlap a b)

instance disjoint_dec : decidable_rel disjoint := 
 λ a b, by {dsimp[disjoint],apply_instance}

lemma disjoint_iff (a b : domino) :
 disjoint a b ↔ _root_.disjoint a.to_finset b.to_finset  

end domino
end combinatorics