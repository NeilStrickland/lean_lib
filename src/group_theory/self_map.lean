import algebra.group group_theory.group_action

variable (T : Type*)

def self_map (T : Type*) : Type* := (T → T)

instance [fintype T] [decidable_eq T] : fintype (self_map T) := 
 by {dsimp[self_map],apply_instance}

instance [fintype T] [decidable_eq T] : decidable_eq (self_map T) := 
 by {dsimp[self_map],apply_instance}

instance self_map_monoid (T : Type*) : monoid (self_map T) := {
 mul := λ f g x, f (g x),
 mul_assoc := λ f g h, by {funext,refl},
 one := λ x, x,
 one_mul := λ f, by {funext,refl},
 mul_one := λ f, by {funext,refl},
}

namespace self_map

def units_equiv : units (self_map T) ≃ equiv.perm T := {
  to_fun := λ u, equiv.mk u.val u.inv 
   (begin
     intro x, 
     change (u.inv * u.val) x = x,
     rw[u.inv_val],
     refl,
    end) 
   (begin 
     intro x, 
     change (u.val * u.inv) x = x,
     rw[u.val_inv],
     refl,   
    end),
  inv_fun := λ v, units.mk v.to_fun v.inv_fun 
   (by {funext,exact v.right_inv x})
   (by {funext,exact v.left_inv x}),
  left_inv := λ u,begin ext,refl, end,
  right_inv := λ v,begin ext,refl end
}

variable {T}

instance : mul_action (self_map T) T := {
 smul := λ f x, f x,
 one_smul := λ x, rfl,
 mul_smul := λ f g x, rfl   
}

def mul_action_of_hom {M X : Type*} [monoid M]
 (act : M → self_map X) [is_monoid_hom act] :
  mul_action M X := 
   @mul_action.mk M X _
    ⟨λ m x, (act m) x⟩
    (λ x,by {change (act 1) x = x,rw[is_monoid_hom.map_one act],refl,})
    (λ m n x,by {change act (m * n) x = act m (act n x),
                 rw[is_monoid_hom.map_mul act],refl})

end self_map
