import data.fintype group_theory.group_action 
 algebra.group_power algebra.big_operators data.zmod.basic
import tactic.ring
import group_theory.pow_mod group_theory.self_map group_theory.burnside_count

namespace MAS114
namespace exercises_2
namespace Q01

def s_W : (fin 4) → (fin 4) := 
 λ ⟨i,i_is_lt⟩, ⟨3 - i,nat.lt_succ_of_le (nat.sub_le 3 i)⟩  

lemma hs_W : ∀ i, s_W (s_W i) = i := 
 λ ⟨i,i_is_lt⟩, begin
  have i_is_le : i ≤ 3 := nat.le_of_lt_succ i_is_lt,
  let h := nat.add_sub_of_le i_is_le,
  apply fin.eq_of_veq,
  change 3 - (3 - i) = i,
  exact calc
   3 - (3 - i) = (i + (3 - i)) - (3 - i) : by rw[h]
   ... = i : nat.add_sub_cancel i (3 - i),
 end

def X := (fin 4) × (fin 4)

def s_X : X → X := λ ⟨i,j⟩, ⟨i,s_W j⟩
def r_X : X → X := λ ⟨i,j⟩, ⟨s_W j,i⟩

lemma hs_X : ∀ ij, s_X (s_X ij) = ij := 
 λ ⟨i,j⟩, by {
   change prod.mk i (s_W (s_W j)) = prod.mk i j,
   rw[hs_W j],
 }

lemma hr_X : ∀ ij, r_X (r_X (r_X (r_X ij))) = ij := 
 λ ⟨i,j⟩, by {
   change prod.mk (s_W (s_W i)) (s_W (s_W j)) = prod.mk i j,
   rw[hs_W i,hs_W j],
 } 

lemma hrs_X : ∀ ij, r_X (s_X (r_X ij)) = s_X ij := 
 λ ⟨i,j⟩, by {
   change prod.mk (s_W (s_W i)) (s_W j) = prod.mk i (s_W j),
   rw[hs_W i],
 } 

end Q01
end exercises_2
end MAS114