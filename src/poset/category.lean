import category_theory.concrete_category

universes u v

open category_theory

@[reducible] def POSet : Type (u+1) := bundled partial_order

namespace POSet

instance (P : POSet) : partial_order P := P.str

/-
instance concrete_is_poset_hom :
  concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

def of (X : Type u) [group X] : Group := ⟨X⟩

instance hom_is_group_hom {G₁ G₂ : Group} (f : G₁ ⟶ G₂) :
  is_group_hom (f : G₁ → G₂) := f.2
-/

end POSet