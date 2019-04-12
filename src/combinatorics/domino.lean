import data.fintype algebra.group

/-
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

def diff (x : count_pair) : ℤ := (x tt) - (x ff)

end count_pair

def color_count (s : finset (ℕ × ℕ)) : count_pair := 
 s.sum (λ x, (count_pair.delta (color x)))

def black_count (s : finset (ℕ × ℕ)) : ℕ := color_count s ff

def white_count (s : finset (ℕ × ℕ)) : ℕ := color_count s tt

lemma count_eq (s : finset (ℕ × ℕ)) : 
 (color_count s).tot = s.card := sorry

namespace color_count

lemma empty : color_count ∅ = 0 := sorry

lemma sum (s t : finset (ℕ × ℕ)) : 
 (color_count (s ∪ t)) + (color_count (s ∩ t)) = 
 (color_count s) + (color_count t) := sorry

lemma disjoint_sum (s t : finset (ℕ × ℕ)) (h : s ∩ t = ∅) : 
 (color_count (s ∪ t)) = (color_count s) + (color_count t) := sorry

lemma disjoint_sum' (ss : list (finset (ℕ × ℕ)))
 (h : ss.pairwise (λ u v, u ∩ v = ∅)) : 
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

instance overlap_dec : decidable_rel overlap := sorry

def disjoint : domino → domino → Prop := 
 λ x y , ¬ (overlap x y)

instance disjoint_dec : decidable_rel disjoint := sorry

end domino
end combinatorics