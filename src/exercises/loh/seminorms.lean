import data.real.basic
import algebra.category.Group.basic
import category_theory.functor category_theory.yoneda
import analysis.normed.group.SemiNormedGroup

notation `Ab` := AddCommGroup

universes u

noncomputable theory
open category_theory 

instance : concrete_category Ab := by apply_instance

@[protect_proj, ancestor semi_normed_group]
class homogeneous_semi_normed_group (E : Type*) extends semi_normed_group E :=
(is_homogeneous : ∀ (n : ℤ) (a : E), norm ( n • a ) = (abs n) * (norm a))

@[reducible]
def homogeneous_semi_normed_group.induced 
 {F} [homogeneous_semi_normed_group F] {E} [add_comm_group E] 
  (f : E →+ F) : homogeneous_semi_normed_group E :=
{ is_homogeneous := λ n a, by { 
    change ∥ f (n • a) ∥ = _ * ∥ f a ∥, 
    rw[add_monoid_hom.map_zsmul, homogeneous_semi_normed_group.is_homogeneous]
  },
  .. semi_normed_group.induced f
}

instance : bundled_hom.parent_projection 
  @homogeneous_semi_normed_group.to_semi_normed_group := ⟨⟩

def homogeneous_normed_group_hom (V W : Type*) 
  [homogeneous_semi_normed_group V] [homogeneous_semi_normed_group W] :=
    normed_group_hom V W

def HSNAb : Type (u + 1) := bundled homogeneous_semi_normed_group

namespace HSNAb

attribute [derive [large_category, concrete_category]] HSNAb

instance : has_coe_to_sort HSNAb (Type u) := bundled.has_coe_to_sort

def of (M : Type u) [homogeneous_semi_normed_group M] : HSNAb := bundled.of M

instance (M : HSNAb) : homogeneous_semi_normed_group M := M.str

end HSNAb

def HSNAb₁ : Type (u+1) := bundled homogeneous_semi_normed_group

namespace HSNAb₁

instance : has_coe_to_sort HSNAb₁ (Type u) := bundled.has_coe_to_sort

instance : large_category.{u} HSNAb₁ :=
{ hom := λ X Y, { f : normed_group_hom X Y // f.norm_noninc },
  id := λ X, ⟨normed_group_hom.id X, normed_group_hom.norm_noninc.id⟩,
  comp := λ X Y Z f g, ⟨(g : normed_group_hom Y Z).comp (f : normed_group_hom X Y), g.2.comp f.2⟩, }

@[ext] lemma hom_ext {M N : HSNAb₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) :
  f = g :=
subtype.eq (normed_group_hom.ext (congr_fun w))

instance : concrete_category.{u} HSNAb₁ :=
{ forget :=
  { obj := λ X, X,
    map := λ X Y f, f, },
  forget_faithful := {} }

instance has_forget_Ab : category_theory.has_forget₂ HSNAb₁ Ab := {
  forget₂ := {
    obj := λ A, AddCommGroup.of A,
    map := λ A B f, AddCommGroup.of_hom (normed_group_hom.to_add_monoid_hom f)
  }
}

notation `U` := HSNAb₁.has_forget_Ab.forget₂ 

instance (A : HSNAb₁) : homogeneous_semi_normed_group (AddCommGroup.of A) := A.str

end HSNAb₁

def transfer {A : Ab} {A' : HSNAb₁} (f : A ≅ AddCommGroup.of A') : 
  homogeneous_semi_normed_group A := 
  homogeneous_semi_normed_group.induced f.hom

variables {C : Type*} [category C] 

def is_wf_pair {F : C ⥤ Ab} {X Y : C} (α : F.obj X) (β : F.obj Y) := 
  ∀ (n : ℕ), ∃ (m : ℤ) (f : X ⟶ Y), m.nat_abs ≥ n ∧ (F.map f) α = m • β

def is_weakly_flexible {F : C ⥤ Ab} {Y : C} (β : F.obj Y) := 
  ∃ (X : C) (α : F.obj X), is_wf_pair α β

structure functorial_semi_norm (F : C ⥤ Ab) := 
(lift : C ⥤ HSNAb₁)
(lift_iso : F ≅ (lift ⋙ U))

example (n : ℕ) (x : ℝ) : n • x = (n : ℝ) * x := by library_search 

example (n m : ℕ) (h : n ≤ m) : (n : ℝ) ≤ (m : ℝ) := nat.cast_le.mpr h

example (x y z : ℝ) (h : 0 ≤ x) (h' : y ≤ z) : x * y ≤ x * z := mul_le_mul_of_nonneg_left h' h

lemma is_zero_of_bounds {c d : ℝ} (hc : c ≥ 0) (hd : d ≥ 0)
 (h : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ (m : ℝ) * c ≤ d ) : c = 0 := 
begin
  by_contra h', change c ≠ 0 at h',
  replace h' := lt_of_le_of_ne hc h'.symm,
  rcases (archimedean.arch (d + 1) h') with ⟨n, hn⟩,
  rw[nsmul_eq_mul] at hn,
  rcases (h n) with ⟨m, hnm, hm⟩,
  exact not_le_of_gt (lt_add_one d) 
   (le_trans hn (le_trans (mul_le_mul_of_nonneg_right (nat.cast_le.mpr hnm) hc) hm))
end

lemma zero_norm_of_fsn {F : C ⥤ Ab} (F' : functorial_semi_norm F) 
  {Y : C} {β : F.obj Y} (h : is_weakly_flexible β) : 
    (norm : F'.lift.obj Y → ℝ) ((F'.lift_iso.app Y).hom β) = 0 := 
begin
  rcases h with ⟨X,α,hα⟩,
  let fX : F.obj X ≅ AddCommGroup.of (F'.lift.obj X) := F'.lift_iso.app X,
  let fY : F.obj Y ≅ AddCommGroup.of (F'.lift.obj Y) := F'.lift_iso.app Y,
  let α' := fX.hom α,
  let β' := fY.hom β,
  change ∥ β' ∥ = 0,
  apply is_zero_of_bounds (norm_nonneg β') (norm_nonneg α'),
  intro n,
  rcases (hα n) with ⟨m, g, hnm, hg⟩,
  use m.nat_abs, split, exact hnm,
  rw[int.cast_nat_abs, ← homogeneous_semi_normed_group.is_homogeneous],
  let g' : F'.lift.obj X ⟶ F'.lift.obj Y := F'.lift.map g,
  have : g' α' = m • β' := by {
    have := congr_hom (F'.lift_iso.hom.naturality g) α,
    change fY.hom ((F.map g) α) = g' (fX.hom α) at this,
    rw[hg, fY.hom.map_zsmul] at this,
    symmetry, exact this
  },
  rw[← this],
  exact g'.property α'
end

def is_indiscrete (A : HSNAb₁) := ∀ (a : A), ∥ a ∥ = 0

def UAb : Ab ⥤ Type u := AddCommGroup.concrete_category.forget

lemma corep_is_wf {F : C ⥤ Ab} [functor.corepresentable (F ⋙ UAb)]
 {Y : C} (β : F.obj Y) : is_weakly_flexible β := 
begin
  have c : functor.corepresentable (F ⋙ UAb) := by apply_instance,
  rcases c with ⟨T, p, hp⟩,
  let T' : C := opposite.unop T,
  haveI := hp, 
  let p' : (T' ⟶ Y) → (F.obj Y) := p.app Y,
  let p'' : (F.obj Y) → (T' ⟶ Y) := ((as_iso p).app Y).inv,
  let u : (F.obj T') := p.app T' (𝟙 T'),
  let v : ∀ (n : ℤ), T' ⟶ Y := λ n, p'' (n • β),
  have hv : ∀ (n : ℤ), (F.map (v n)) u = n • β := λ n,
  begin
    have h : p' (v n) = (p' ∘ p'') (n • β) := rfl,
    have : p' ∘ p'' = id := ((as_iso p).app Y).inv_hom_id, rw[this, id.def] at h,
    rw[← h],
    have : p' (v n) = p' ((coyoneda.obj T).map (v n) (𝟙 T')) := by simp,
    rw[this],
    change (F.map (v n)) (p.app T' (𝟙 T')) = (p.app Y) _,
    have := (congr_hom (p.naturality (v n)) (𝟙 T')).symm,
    exact this,
  end,
  use T', use u, intro n, use n, use (v n),
  split, exact le_refl _, exact hv n
end

lemma corep_fsn_indiscrete {F : C ⥤ Ab} [functor.corepresentable (F ⋙ UAb)]
  (F' : functorial_semi_norm F) : ∀ (X : C), is_indiscrete (F'.lift.obj X) := 
begin
  intros Y β', 
  let β : F.obj Y := (F'.lift_iso.app Y).inv β',
  have : β' = (F'.lift_iso.app Y).hom β := (congr_hom (F'.lift_iso.app Y).inv_hom_id β').symm,
  rw[this],
  exact zero_norm_of_fsn F' (corep_is_wf β),
end