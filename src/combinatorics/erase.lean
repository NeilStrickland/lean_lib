import data.fintype

namespace combinatorics

variables {α : Type*} [fintype α] [decidable_eq α]

def erase (a : α) := {b : α // b ≠ a}

namespace erase

instance (a : α) : decidable_eq (erase a) := by { apply_instance }
instance (a : α) : fintype (erase a) := by { dsimp[erase], apply_instance }

def option_equiv (a : α) : option (erase a) ≃ α := begin
 let to_fun : option (erase a) → α :=
   λ x, @option.cases_on (erase a) (λ _, α) x a (λ b,b.val),
 have to_fun_none : to_fun none = a := rfl,
 have to_fun_some : ∀ b, to_fun (some b) = b.val := λ b,rfl,
 let inv_fun : ∀ b : α, option (erase a) := 
  λ b, (if h : b = a then none else (some ⟨b,h⟩)),
 have inv_fun_a : inv_fun a = none := dif_pos rfl,
 have inv_fun_not_a : ∀ (b : α) (h : b ≠ a), inv_fun b = some ⟨b,h⟩ :=
  λ b h,dif_neg h,
 have left_inv : function.left_inverse inv_fun to_fun := 
  begin 
   rintro (_ | ⟨b,b_ne_a⟩),
   {rw[to_fun_none,inv_fun_a],},
   {rw[to_fun_some,inv_fun_not_a],}
  end,
 have right_inv : function.right_inverse inv_fun to_fun := 
  begin
   intro b,
   by_cases h : b = a,
   {rw[h,inv_fun_a]},
   {rw[inv_fun_not_a b h]}
  end,
 exact ⟨to_fun,inv_fun,left_inv,right_inv⟩,
end

lemma card (a : α) : fintype.card (erase a) + 1 = fintype.card α := 
 (@fintype.card_option (erase a) _).symm.trans
   (fintype.card_congr (option_equiv a))

def inc {a : α} (b : erase a) : α := b.val

def inc_inj (a : α) : function.injective (@inc α _ _ a) := 
 λ b₁ b₂ e, subtype.eq e

end erase

end combinatorics