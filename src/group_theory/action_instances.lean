/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

If we have types `X` and `Y` with a left action of a monoid `M`,
then there are also natural actions of `M` on various other types
defined in terms of `X` and/or `Y`, such as `X × Y` and 
`finset X` and `X / E` (for an equivalence relation `E` with 
appropriate properties).  This file defines typeclass instances
that encode these natural actions.

-/

import group_theory.group_action
import tactic.interactive

universes uM uG uX uY uZ

variables {M : Type uM} [monoid M] 
variables {G : Type uG} [group G ] 
variables {X : Type uX} {Y : Type uY} {Z : Type uZ}
variables [mul_action M X] [mul_action M Y] [mul_action M Z]
variables [mul_action G X] [mul_action G Y] [mul_action G Z]

namespace mul_action 

lemma smul_cancel_left {g : G} {x : X} : g⁻¹ • g • x  = x := 
by { rw [← mul_smul, mul_left_inv, one_smul] }

lemma smul_cancel_right {g : G} {x : X} : g • g⁻¹ • x  = x := 
by { rw [← mul_smul, mul_right_inv, one_smul] }

lemma smul_eq_iff_eq_smul_inv {g : G} {x y : X} :
    g • x = y ↔ x = g⁻¹ • y := 
begin
  split; intro h,
  { rw [← h, smul_cancel_left ] },
  { rw [  h, smul_cancel_right] }
end

lemma one_act : ((•) (1 : M)) = @id X :=
 by { funext x, rw[one_smul,id] }

lemma mul_act (m n : M) : (((•) (m * n)) : X → X) = ((•) m) ∘ ((•) n) := 
 by { funext x, rw[mul_smul] }

variable (M)
def trivial_action (Z : Type*) : mul_action M Z := {
  smul := λ a z, z,
  one_smul := λ z, rfl,
  mul_smul := λ a b z, rfl
}
variable {M}

instance empty_action : mul_action M empty := trivial_action _ _

instance unit_action : mul_action M unit := trivial_action _ _

instance sum_action : mul_action M (X ⊕ Y) := {
 smul := λ m z,sum.cases_on z (λ x, sum.inl (m • x)) (λ y, sum.inr (m • y)),
 one_smul := λ z,begin 
  rcases z with x | y,
  { change sum.inl ((1 : M) • x) = sum.inl x, rw[one_smul], },
  { change sum.inr ((1 : M) • y) = sum.inr y, rw[one_smul], }
 end,
 mul_smul := λ m n z,begin
  rcases z with x | y,
  { change sum.inl ((m * n) • x) = sum.inl (m • n • x), rw[mul_smul] },
  { change sum.inr ((m * n) • y) = sum.inr (m • n • y), rw[mul_smul] }
 end
}

instance prod_action : mul_action M (X × Y) := { 
 smul := λ m xy, ⟨m • xy.1,m • xy.2⟩,
 one_smul := λ ⟨x,y⟩,
  by {change (prod.mk ((1 : M) • x) ((1 : M) • y)) = prod.mk x y,
      rw[one_smul,one_smul] },
 mul_smul := λ m n ⟨x,y⟩,
  by {change (prod.mk ((m * n) • x) ((m * n) • y)) = 
             (prod.mk (m • n • x) (m • n • y)),
      rw[mul_smul,mul_smul] } 
}

lemma smul_prod (m : M) (xy : X × Y) : m • xy = ⟨m • xy.1, m • xy.2⟩ := rfl 

variables (M G)
def is_equivariant (f : X → Y) := ∀ (m : M) (x : X), f (m • x) = m • (f x)

def equivariantizer (f : X → Y) : submonoid M := {
  carrier := { m : M | ∀ (x : X), f (m • x) = m • (f x) },
  one_mem' := λ x, by { rw [one_smul, one_smul] },
  mul_mem' := λ a b ha hb x, 
    by { rw[mul_smul, mul_smul, ha, hb] }
}

def equivariantizer_subgroup (f : X → Y) : subgroup G := {
   inv_mem' := λ g hg x, by {
     rw [← smul_eq_iff_eq_smul_inv, ← hg, ← mul_smul, 
         mul_right_inv, one_smul] },
   .. mul_action.equivariantizer G f
}

variables {M G}

lemma is_equivariant_id : is_equivariant M (id : X → X) := λ m x, rfl

lemma is_equivariant_comp {g : Y → Z} {f : X → Y} 
  (hg : is_equivariant M g) (hf : is_equivariant M f) : 
    (is_equivariant M (g ∘ f)) := 
λ m x,  by { rw [function.comp_app, hf, hg] }

instance map_action : mul_action G (X → Y) := {
 smul := λ g u x, g • (u (g⁻¹ • x)),
 one_smul := λ u, funext $ λ x, 
   by { change _ • (u _) = u x, rw [inv_one, one_smul, one_smul] },
 mul_smul := λ a b u, funext $ λ x, 
   by { change _ • (u _) = _ • (_ • _),
        rw [mul_inv_rev, mul_smul, mul_smul] } 
}

lemma smul_map (g : G) (u : X → Y) (x : X) : 
  (g • u) x = g • (u (g⁻¹ • x)) := rfl

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
   ... = m • n • xs : by { rw[← list.map_map], refl },
 .. mul_action.list_scalar
}

lemma smul_list (m : M) (xs : list X) : m • xs = xs.map ((•) m) := rfl

instance finset_scalar [decidable_eq X] : has_scalar M (finset X) := 
 ⟨λ m xs,xs.image ((•) m)⟩

instance finset_action [decidable_eq X] : mul_action M (finset X) := {
 one_smul := λ xs,
  begin
   change xs.image ((•) (1 : M)) = xs,
   rw [one_act, finset.image_id],
  end,
 mul_smul := λ m n xs, calc
   (m * n) • xs = xs.image ((•) (m * n)) : rfl
   ... = xs.image (((•) m) ∘ ((•) n)) : by rw [mul_act]
   ... = m • n • xs : by { rw [← finset.image_image], refl }, 
 .. mul_action.finset_scalar
}

lemma smul_finset [decidable_eq X] (m : M) (xs : finset X) : 
  m • xs = xs.image ((•) m) := rfl 

lemma mem_smul_finset [decidable_eq X] {x : X} {m : M} {xs : finset X} :
  x ∈ m • xs ↔ ∃ (x' : X), x' ∈ xs ∧ m • x' = x := 
by { rw [smul_finset, finset.mem_image]; simp only [exists_prop] }

lemma mem_smul_finset_of_mem [decidable_eq X] (m : M) {xs : finset X} 
  {x : X} (hx : x ∈ xs) : m • x ∈ m • xs := 
finset.mem_image_of_mem ((•) m) hx

lemma mem_smul_finset' [decidable_eq X]
  {x : X} {g : G} {xs : finset X} : 
    x ∈ g • xs ↔ (g⁻¹ • x) ∈ xs := 
begin
  rw [mem_smul_finset], split,
  { rintro ⟨x',⟨hm,he⟩⟩, 
    have := calc g⁻¹ • x = g⁻¹ • (g • x') : by { rw [← he] }
      ... = x' : by { rw [smul_cancel_left] },
    rw [← this] at hm, exact hm },
  { intro h, use g⁻¹ • x, split, 
    { exact h },
    { rw [smul_cancel_right] } }
end

lemma smul_finset_eq_iff [decidable_eq X]
  {g : G} {xs ys : finset X} : 
    g • xs = ys ↔ (∀ {x : X}, x ∈ xs → g • x ∈ ys) ∧ 
                  (∀ {y : X}, y ∈ ys → g⁻¹ • y ∈ xs) := 
begin
  split,
  { intro h, split, 
    { intros x hx, rw [← h, mem_smul_finset', smul_cancel_left], exact hx },
    { let h' : xs = g⁻¹ • ys := smul_eq_iff_eq_smul_inv.mp h,
      intros y hy, rw [h'],
      exact mem_smul_finset_of_mem g⁻¹ hy
    } },
  { rintro ⟨h₀,h₁⟩, ext y, split; intro hy,
    { replace hy := h₀ (mem_smul_finset'.mp hy),
      rw [smul_cancel_right] at hy, exact hy },
    { rw [mem_smul_finset'], exact h₁ hy } }
end

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

@[ext] theorem ext {Y₀ Y₁ : equivariant_set M X}
  (h : ∀ x, x ∈ Y₀ ↔ x ∈ Y₁) : Y₀ = Y₁ := ext' $ set.ext h

instance restricted_action (Y : equivariant_set M X) : mul_action M Y.carrier := {
  smul := λ m ⟨y,y_in_Y⟩, ⟨m • y,Y.smul m y_in_Y⟩,
  one_smul := λ ⟨y,y_in_Y⟩,
   by { apply subtype.eq, change (1 : M) • y = y, apply one_smul },
  mul_smul := λ m n ⟨y,y_in_Y⟩,
   by { apply subtype.eq, change (m * n) • y = m • n • y, apply mul_smul }
} 

lemma coe_smul {Y : equivariant_set M X} (m : M) (y : Y) : 
  ((m • y) : X) = m • (y : X) := rfl

end equivariant_set

variables (M X)
structure equivariant_setoid extends (setoid X) := 
(smul : ∀ (m : M) {x y : X}, r x y → r (m • x) (m • y))
variables {M X}

namespace equivariant_setoid
instance : has_coe (equivariant_setoid M X) (setoid X) := ⟨λ E, ⟨E.r,E.iseqv⟩⟩ 

def quotient (E : equivariant_setoid M X) := quotient (E : setoid X)
def quotient.mk (E : equivariant_setoid M X) (x : X) : quotient E := 
  @_root_.quotient.mk X E x

instance induced_action (E : equivariant_setoid M X) : 
  mul_action M (quotient E) := 
begin 
 exact {
  smul :=  λ m, @quotient.lift X _ E
           (λ x, (@_root_.quotient.mk X E (m • x))) 
           (λ x₀ x₁ e, begin
             let h := @quotient.sound X E,
             exact h (equivariant_setoid.smul _ m e),
           end),
  one_smul :=
    begin 
      rintro ⟨x⟩, change @_root_.quotient.mk X E _ = _,
      rw [one_smul], refl
    end,
  mul_smul := 
    begin
      rintro a b ⟨x⟩, 
      change @_root_.quotient.mk X E _ = @_root_.quotient.mk X E _,
      rw [mul_smul]
    end
 }
end

lemma smul_mk (E : equivariant_setoid M X) (m : M) (x : X) : 
  m • (quotient.mk E x) = quotient.mk E (m • x) := rfl

end equivariant_setoid

end mul_action

namespace mul_action

variables [decidable_eq X]

variable (X)
def smul_equiv (g : G) : X ≃ X := {
  to_fun    := λ x, g • x,
  inv_fun   := λ x, g⁻¹ • x,
  left_inv  := λ x, by { change g⁻¹ • (g • x) = x, rw [← mul_smul, inv_mul_self, one_smul] },
  right_inv := λ x, by { change g • (g⁻¹ • x) = x, rw [← mul_smul, mul_inv_self, one_smul] }
}
variable {X}

lemma finset_action_eq_map (g : G) (s : finset X) :
  g • s = s.map (smul_equiv X g).to_embedding :=
begin
  change s.image _ = s.map _,
  rw [finset.map_eq_image], refl
end

lemma finset_action.card (g : G) (s : finset X) : (g • s).card = s.card :=
begin
  rw [finset_action_eq_map, finset.card_map]
end

end mul_action