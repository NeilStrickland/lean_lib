
instance : large_category.{u} HSNAb :=
{ hom := λ X Y, { f : normed_group_hom X Y // f.norm_noninc },
  id := λ X, ⟨normed_group_hom.id X, normed_group_hom.norm_noninc.id⟩,
  comp := λ X Y Z f g, ⟨(g : normed_group_hom Y Z).comp (f : normed_group_hom X Y), g.2.comp f.2⟩, }

@[ext] lemma hom_ext {M N : SemiNormedGroup₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
  f = g :=
subtype.eq (normed_group_hom.ext (congr_fun w))



attribute [derive [category_theory.large_category.{u}]] HSNAb

instance : category_theory.concrete_category.{u} HAbsn := {
  forget := {
    obj := λ A, A.val,
    map := λ A B f, f,
  },
  forget_faithful := {
    map_injective' := λ A B f g f_eq_g, by { ext, simp at f_eq_g, rw[f_eq_g] }
  }
}

def transfer {A : Ab} {A' : HAbsn} (f : A ≅ AddCommGroup.of A'.val) : semi_normed_group A := 
  semi_normed_group.induced f.hom

def Z (A : Type*) (S : add_comm_group A) : Ab := {
 α := A,
 str := S
}

#check category_theory.bundled

lemma transfer_homogeneous {A : Ab} {A' : HAbsn} (f : A ≅ AddCommGroup.of A'.val) :
  is_homogeneous { α := A, str := transfer f }

instance has_forget_HAbsn_Ab : category_theory.has_forget₂ HAbsn Ab := {
  forget₂ := {
    obj := λ A, AddCommGroup.of A.val,
    map := λ A B f, AddCommGroup.of_hom (normed_group_hom.to_add_monoid_hom f)
  }
}

notation ` forget_sn ` := has_forget_HAbsn_Ab.forget₂

/- ffsn_on F F' is the type of natural isomorphisms from F to U ∘ F',
   where U : HAbsn ⥤ Ab is the forgetful functor
-/

variables {C : Type*} [category_theory.category C] 

structure functorial_seminorm (F : C ⥤ Ab) := 
(lift : C ⥤ HAbsn)
(lift_iso : F ≅ (lift ⋙ forget_sn))

instance {F : C ⥤ Ab} (F' : functorial_seminorm F) (X : C) : semi_normed_group (F.obj X) := 
  transfer (F'.lift_iso.app X)

#check category_theory.iso

def lift' {F : C ⥤ Ab} (F' : functorial_seminorm F) : C ⥤ HAbsn := {
  obj := λ X, ⟨F.obj X, λ (n : ℤ) (a : F.obj X), by {
    let na' : (F'.lift.obj X).val := (F'.lift_iso.app X).hom (n • a),
    let a' : (F'.lift.obj X).val := (F'.lift_iso.app X).hom a,
    change _ = _ * ∥ a' ∥,
    have h' : (F'.lift_iso.app X).hom (n • a) = n • a' := 
      by rw[(F'.lift_iso.app X).hom.map_zsmul],
  }⟩,
}

lemma lift_norm_noninc {F : C ⥤ Ab} (F' : functorial_seminorm F) 
  {X Y : C} (f : X ⟶ Y) (a : (F'.lift.obj X).val) : ∥ F'.lift.map f a ∥ ≤ ∥ a ∥ := 
 (F'.lift.map f).2 a

def lift_iso' {F : C ⥤ Ab} (F' : functorial_seminorm F) (X : C) : 
  F.obj X ≅ (category_theory.functor.obj forget_sn) (F'.lift.obj X) := 
   F'.lift_iso.app X

