/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This contains some additional lemmas for working with heterogenous 
equality.  It is far from clear that the approach taken here 
(or in places where these results are used) is optimal.

-/

import data.fintype

lemma heq_rec {B : Type*} {X : B → Type*} {b0 b1 : B} (eb : b0 = b1) (x : X b0) :
 x == (@eq.rec_on B b0 X b1 eb x) := 
begin
 exact eq.dcases_on eb (heq.refl x)
end

lemma cast_eq_heq {B : Type*} {X : B → Type*} {b0 b1 : B} (eb : b0 = b1)
 (x0 : X b0) (x1 : X b1) :
  (x0 == x1) ↔ (@eq.rec_on B b0 X b1 eb x0 = x1) :=
begin
 let e0 := (@heq_rec B X b0 b1 eb x0),
 split, 
 {intro e1, exact eq_of_heq (e0.symm.trans e1)},
 {intro e2, exact (e0.trans (heq_of_eq e2))}
end

lemma eq_mp_heq {B : Type*} {X : B → Type*} {b0 b1 : B} (eb : b0 = b1)
 (x0 : X b0) (x1 : X b1) :
  (x0 == x1) ↔ (eq.mp (congr_arg X eb) x0 == x1) :=
begin
 let eX := congr_arg X eb,
 cases eb,
 have h : eX = rfl := rfl,
 have : eq.mp eX x0 = x0 := rfl,
 rw[this],
end

lemma eq_mpr_a {α β : Type*} (e : β = α) (a : α) :
 e.mpr a == a :=
begin
 cases e; simp[eq.mpr],
end

lemma heq_snd {B : Type*} {X : B → Type*} {x0 x1 : sigma X} (ex : x0 = x1) :
 x0.2 == x1.2 :=
begin
 let C : ∀ (x : sigma X) (e : x0 = x), Prop := (λ x _,x0.2 == x.2),
 let c : C x0 rfl := heq_of_eq rfl,
 exact @eq.dcases_on (sigma X) x0 C x1 ex c,
end

lemma heq_subst {B C : Type*} {X : B → Type*} {Y : C → Type*} 
 (f : B → C) (g : ∀ b : B, (X b) → (Y (f b)))
 {b0 b1 : B} {x0 : X b0} {x1 : X b1}
 (eb : b0 = b1) (ex : x0 == x1) : 
  (g b0 x0) == (g b1 x1) := 
begin
 have e0 : (@eq.rec_on B b0 X b1 eb x0 = x1) :=
  (@cast_eq_heq B X b0 b1 eb x0 x1).mp ex,
 let e1 := congr_arg (g b1) e0,
 let e2 := @eq.dcases_on B b0
            (λ b e,g b0 x0 == g b (@eq.rec_on B b0 X b e x0))
              b1 eb (heq.refl (g b0 x0)),
 exact heq_of_heq_of_eq e2 e1
end

lemma heq_section_subst {B : Sort*} {X : B → Type*} 
 (s : ∀ b : B, X b) {b0 b1 : B} (eb : b0 = b1) : (s b0) == (s b1) :=
begin
 let F : ∀ (b : B) (e : b0 = b), Prop := 
  λ b e, s b0 == s b,
 let e0 : F b0 rfl := heq.refl (s b0),
 exact @eq.dcases_on B b0 F b1 eb e0,
end

lemma heq_sigma {B : Type*} {X : B → Type*} {Y : Type*} (f : ∀ (b : B) (x : X b), Y)
 {b0 b1 : B} {x0 : X b0} {x1 : X b1} (eb : b0 = b1) (ex : x0 == x1) : (f b0 x0) = (f b1 x1) := 
begin
 let F : ∀ (b : B) (e : b0 = b), Prop := 
  λ b e , (∀ (x : X b), x0 == x → (f b0 x0) = (f b x)), 
 let e0 : F b0 rfl := λ x e1,congr_arg (f b0) (eq_of_heq e1),
 exact (@eq.dcases_on B b0 F b1 eb e0) x1 ex
end

lemma heq_prod {A0 A1 B0 B1 : Type*} {a0 : A0} {a1 : A1} {b0 : B0} {b1 : B1}
 (ea : a0 == a1) (eb : b0 == b1) : prod.mk a0 b0 == prod.mk a1 b1 := 
begin
 let e0 : prod.mk a0 b0 == prod.mk a1 b0 :=
  @heq.cases_on A0 a0 (λ X x,prod.mk a0 b0 == prod.mk x b0) A1 a1 ea (heq.refl _),
 let e1 : prod.mk a1 b0 == prod.mk a1 b1 :=
  @heq.cases_on B0 b0 (λ X x,prod.mk a1 b0 == prod.mk a1 x) B1 b1 eb (heq.refl _),
 exact e0.trans e1,
end

lemma subtype_heq_of_iff {α : Type*} {p q : (α → Prop)}
 (epq : ∀ a, p a ↔ q a) (x : subtype p) (y : subtype q) 
 (exy : x.val = y.val) : x == y := 
begin
 let s : ∀ (p0 : α → Prop) (e0 : p = p0), subtype p0 := 
  λ p0 e0, ⟨x.val,eq.subst e0 x.property⟩,
 let C : ∀ (p0 : α → Prop) (e0 : p = p0), Prop := 
  λ p0 e0, x == s p0 e0,
 let c : C p rfl := by simp[C,s],
 have epq1 : ∀ a, p a = q a := λ a, propext (epq a),
 have epq2 : p = q := funext epq1,
 let y0 : subtype q := s q epq2,
 have x_heq_y0 : x == y0 := @eq.dcases_on (α → Prop) p C q epq2 c,
 have x_eq_y0_val : x.val = y0.val := by simp[s],
 exact x_heq_y0.trans (heq_of_eq (subtype.eq (x_eq_y0_val.symm.trans exy))),
end

