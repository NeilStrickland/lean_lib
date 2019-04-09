import group_theory.group_action
import tactic.interactive

universes uM uX uY
namespace mul_action 

variables {M : Type uM} {X : Type uX} {Y : Type uY} 
 [monoid M] [mul_action M X] [mul_action M Y]

lemma one_act : ((•) (1 : M)) = @id X :=
 by {funext x,rw[one_smul,id],}

lemma mul_act (m n : M) : (((•) (m * n)) : X → X) = ((•) m) ∘ ((•) n) := 
 by {funext x,rw[mul_smul],}

instance empty_action : mul_action M empty := {
 smul := λ m, empty.elim,
 one_smul := empty.rec _, 
 mul_smul := λ m n,empty.rec _
}

instance sum_action : mul_action M (X ⊕ Y) := {
 smul := λ m z,sum.cases_on z (λ x, sum.inl (m • x)) (λ y, sum.inr (m • y)),
 one_smul := λ z,begin 
  rcases z with x | y,
  { change sum.inl ((1 : M) • x) = sum.inl x, rw[one_smul], },
  { change sum.inr ((1 : M) • y) = sum.inr y, rw[one_smul], }
 end,
 mul_smul := λ m n z,begin
  rcases z with x | y,
  { change sum.inl ((m * n) • x) = sum.inl (m • n • x), rw[mul_smul], },
  { change sum.inr ((m * n) • y) = sum.inr (m • n • y), rw[mul_smul], }
 end
}

instance prod_action : mul_action M (X × Y) := { 
 smul := λ m ⟨x,y⟩, ⟨m • x,m • y⟩,
 one_smul := λ ⟨x,y⟩,
  by {change (prod.mk ((1 : M) • x) ((1 : M) • y)) = prod.mk x y,
      rw[one_smul,one_smul],},
 mul_smul := λ m n ⟨x,y⟩,
  by {change (prod.mk ((m * n) • x) ((m * n) • y)) = (prod.mk (m • n • x) (m • n • y)),
      rw[mul_smul,mul_smul],} 
}

instance list_scalar : has_scalar M (list X) := ⟨λ m xs,xs.map ((•) m)⟩

instance list_action : mul_action M (list X) := {
 one_smul := λ xs,
  begin
   change xs.map ((•) (1 : M)) = xs,
   rw[one_act,list.map_id],
  end,
 mul_smul := λ m n xs,calc
   (m * n) • xs = xs.map ((•) (m * n)) : rfl
   ... = xs.map (((•) m) ∘ ((•) n)) : by rw[mul_act]
   ... = m • n • xs : by { rw[← list.map_map],refl, }
  , 
 .. mul_action.list_scalar
}

instance finset_scalar [decidable_eq X] : has_scalar M (finset X) := ⟨λ m xs,xs.image ((•) m)⟩

instance finset_action [decidable_eq X] : mul_action M (finset X) := {
 one_smul := λ xs,
  begin
   change xs.image ((•) (1 : M)) = xs,
   rw[one_act,finset.image_id],
  end,
 mul_smul := λ m n xs,calc
   (m * n) • xs = xs.image ((•) (m * n)) : rfl
   ... = xs.image (((•) m) ∘ ((•) n)) : by rw[mul_act]
   ... = m • n • xs : by { rw[← finset.image_image],refl, }
  , 
 .. mul_action.finset_scalar
}

variables (M X)
structure equivariant_set : Type uX :=
(carrier : set X)
(smul : ∀ (m : M) {x : X}, x ∈ carrier → m • x ∈ carrier)
variables {M X}

namespace equivariant_set 
instance : has_coe (equivariant_set M X) (set X) := ⟨equivariant_set.carrier⟩
instance : has_mem X (equivariant_set M X) := ⟨λ x Y, x ∈ (Y : set X)⟩

@[simp] theorem mem_coe {Y : equivariant_set M X} (x : X) :
 x ∈ (Y : set X) ↔ x ∈ Y := iff.rfl

theorem ext' {Y₀ Y₁ : equivariant_set M X}
 (h : (Y₀ : set X) = (Y₁ : set X)) : Y₀ = Y₁ :=
  by cases Y₀; cases Y₁; congr'

protected theorem ext'_iff {Y₀ Y₁ : equivariant_set M X}  : 
 (Y₀ : set X) = (Y₁ : set X) ↔ Y₀ = Y₁ := ⟨ext', λ h, h ▸ rfl⟩

@[extensionality] theorem ext {Y₀ Y₁ : equivariant_set M X}
  (h : ∀ x, x ∈ Y₀ ↔ x ∈ Y₁) : Y₀ = Y₁ := ext' $ set.ext h

instance restricted_action (Y : equivariant_set M X) : mul_action M Y.carrier := {
  smul := λ m ⟨y,y_in_Y⟩, ⟨m • y,Y.smul m y_in_Y⟩,
  one_smul := λ ⟨y,y_in_Y⟩,
   by { apply subtype.eq, change (1 : M) • y = y, apply one_smul,},
  mul_smul := λ m n ⟨y,y_in_Y⟩,
   by { apply subtype.eq, change (m * n) • y = m • n • y, apply mul_smul,},
} 

end equivariant_set

variables (M X)
structure equivariant_setoid extends (setoid X) := 
(smul : ∀ (m : M) {x y : X}, r x y → r (m • x) (m • y))
variables {M X}

namespace equivariant_setoid
instance : has_coe (equivariant_setoid M X) (setoid X) := ⟨λ E, ⟨E.r,E.iseqv⟩⟩ 

def quotient (E : equivariant_setoid M X) := quotient (E : setoid X)

instance induced_action (E : equivariant_setoid M X) : mul_action M (quotient E) := 
begin 
 haveI := (E : setoid X),
 exact {
  smul := λ m, quotient.lift (λ x, (quotient.mk (m • x))) 
           (λ x₀ x₁ e,  quotient.sound (equivariant_setoid.smul _ m e)),
  one_smul := sorry,
  mul_smul := sorry
 }
end

end equivariant_setoid

end mul_action
