import data.fintype
import tactic.squeeze

namespace MAS114

universes u v
variables {α : Type u} {β : Type v} (p : α → β) 
variables [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]

def fiber (b : β) : Type* := { a : α // p a = b } 

instance (b : β) : fintype (fiber p b) := 
 by { dsimp[fiber], apply_instance }

def fiber' (b : β) : finset α := finset.univ.filter (λ a, p a = b) 

lemma mem_fiber' (b : β) (a : α) : a ∈ fiber' p b ↔ p a = b := 
 ⟨λ h,(finset.mem_filter.mp h).right,
  λ h,finset.mem_filter.mpr ⟨finset.mem_univ a,h⟩⟩ 

lemma card_fiber (b : β) : fintype.card (fiber p b) = (fiber' p b).card := 
 fintype.subtype_card (fiber' p b) (mem_fiber' p b)

lemma equiv_fibre_sigma : α ≃ Σ (b : β), (fiber p b) := 
begin
 let to_fun : α → Σ (b : β), (fiber p b) := λ a, ⟨p a,⟨a,rfl⟩⟩,
 let inv_fun : ∀ x : Σ (b : β), (fiber p b), α := λ x, x.2.val,
 let left_inv : function.left_inverse inv_fun to_fun :=
  λ a, by { dsimp[to_fun,inv_fun],refl },
 let right_inv : function.right_inverse inv_fun to_fun := λ ⟨b,⟨a,e⟩⟩, begin 
  rcases e,
  dsimp[inv_fun,to_fun],simp only[heq_iff_eq],split; refl,
 end,
 exact ⟨to_fun,inv_fun,left_inv,right_inv⟩, 
end

lemma card_eq_fiber_sum :
 fintype.card α = finset.univ.sum (λ b, fintype.card (fiber p b)) := 
 (fintype.card_congr (equiv_fibre_sigma p)).trans (fintype.card_sigma (fiber p))

lemma card_eq_fiber_sum' :
 fintype.card α = finset.univ.sum (λ b, finset.card (fiber' p b)) := 
begin
 let e0 := card_eq_fiber_sum p,
 let e1 : ∀ b : β, b ∈ finset.univ → fintype.card (fiber p b) = finset.card (fiber' p b)
  := λ b _, card_fiber p b,
 let e2 := @finset.sum_congr β ℕ finset.univ _ _ _ _ rfl e1,
 exact e0.trans e2,
end

variable {p}

lemma fiber_nonempty_of_surjective 
 (p_surj : function.surjective p) (b : β) : nonempty (fiber p b) := 
begin
 rcases p_surj b with ⟨a,e⟩,
 exact ⟨⟨a,e⟩⟩,
end

lemma card_le_of_surjective :
 function.surjective p → (fintype.card β) ≤ (fintype.card α) := 
begin
 intro p_surj,
 have h0 : ∀ b, b ∈ finset.univ → 1 ≤ fintype.card (fiber p b) := 
  λ b _, fintype.card_pos_iff.mpr (fiber_nonempty_of_surjective p_surj b),
 let h1 := @finset.sum_le_sum β ℕ finset.univ _ _ _ _ h0,
 let h2 := calc 
  finset.sum finset.univ (λ b : β, 1) = 
   add_monoid.smul finset.univ.card 1 : 
     @finset.sum_const β ℕ finset.univ _ 1
  ... = ↑finset.univ.card : @add_monoid.smul_one ℕ _ _ finset.univ.card
  ... = finset.univ.card : nat.cast_id _
  ... = fintype.card β : rfl,
 rw[h2,← card_eq_fiber_sum p] at h1,
 exact h1
end

end MAS114
