/-
 This file sets up some definitions for working with parametrised families
 of types, and morphisms between them.  In other words, we essentially 
 work with the category of arrows in the category of types.

 A key issue is as follows.  Suppose we have a family X : B → Type*, 
 and two terms b0 and b1 of B, and terms x0 : (X b0) and x1 : (X b1) of
 the corresponding fibres.  Suppose that b0 and b1 are provably 
 equal, but not definitionally equal.  Lean will then regard the 
 expression x0 = x1 as not being meaningful.  There are two ways 
 around this.  One way is to use the heterogenous equality relation
 x0 == x1 instead of x0 = x1.  The other is to find an explicit term
 e of type b0 = b1, then (eq.mp e x0) will have type (X b1) and so 
 (eq.mp e x0) = x1 will be meaningful.  A large part of this file
 deals with the properties of these two approaches and the relationship
 between them.
-/

import data.equiv.basic
import data.heq_extra 

/-
 This defines the notion of a morphism between two parametrised families.
-/
structure family_fun {B : Type*} (X : B → Type*) {C : Type*} (Y : C → Type*) := 
(base : B → C)
(fiber : ∀ {b : B}, (X b) → (Y (base b)))

/-
 The following lemma says roughly the following: if some property P makes
 sense for heterogenously equal pairs, and is true for definitionally 
 equal pairs, then it is true for all heterogenously equal pairs.
-/
lemma family_eq_rec {B : Type*} {X : B → Type*}
 (P : ∀ {b0 b1 : B} {x0 : X b0} {x1 : X b1} (eb : b0 = b1) (ex : x0 == x1), Prop)
 (p : ∀ (b : B) (x : X b), @P b b x x (@rfl B b) (heq.refl x)) :
 ∀ b0 b1 x0 x1 eb ex, @P b0 b1 x0 x1 eb ex :=
begin
 intros b0 b1 x0 x1 eb ex,
 rcases eb,
 rcases (eq_of_heq ex),
 exact p b0 x0
end

namespace family_fun

def total : ∀ {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*} 
 (f : family_fun X Y) (x : Σ (b : B), X b), (Σ (c : C), Y c) := 
begin
 intros,exact ⟨f.base x.1, f.fiber x.2⟩ 
end

/- This just makes b explicit as an argument of f.fiber
-/
def fiber_alt  {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*} 
 (f : family_fun X Y) : ∀ (b : B), (X b) → (Y (f.base b)) := f.fiber

/- The identity morphism of a parametrised family -/
def id {B : Type*} (X : B → Type*) : family_fun X X := 
{ base := @id B, fiber := λ b, (@id (X b))}

/- Composition of morphisms of parametrised families -/
def compose
 {B : Type*} {X : B → Type*}
 {C : Type*} {Y : C → Type*}
 {D : Type*} {Z : D → Type*}
 (g : family_fun Y Z) (f : family_fun X Y) : (family_fun X Z) :=
 { base := g.base ∘ f.base,
   fiber := λ (b : B) (x : X b), g.fiber (f.fiber x)
 }

/- Morphisms preserve heterogenous equality -/
def congr_args  {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f : family_fun X Y)
 {b0 b1 : B} (eb : b0 = b1)
 {x0 : X b0} {x1 : X b1} (ex : x0 == x1) : 
  f.fiber x0 == f.fiber x1 := 
   heq_subst f.base f.fiber eb ex

/- 
 We now define a notion of equivalence for morphisms:
 morphisms f0 and f1 are equivalent if they are pointwise equal on
 the base and pointwise heterogenously equal on fibres.

 Later we prove a kind of function extensionality result, that 
 equivalent morphisms are equal.  However, I think that this result
 is not "computationally pure" and so inhibits virtual machine 
 compilation; so it is preferable to avoid it and work with 
 equivalence.  But I do not have a good understanding of all the
 relevant issues. 
-/
def hequiv  {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*} 
 (f0 : family_fun X Y) (f1 : family_fun X Y) : Prop := 
  (∀ (b : B), f0.base b = f1.base b) ∧ 
  (forall (b : B) (x : X b), f0.fiber x == f1.fiber x)  
lemma heq_rec (B : Type*) (X : B → Type*) (b0 b1 : B) (eb : b0 = b1) (x : X b0) :
 x == (@eq.rec_on B b0 X b1 eb x) := 
begin
 exact eq.dcases_on eb (heq.refl x)
end

/-
 The next three lemmas show that we have indeed defined an 
 equivalence relation on morphisms.
-/
lemma hequiv.refl {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f : family_fun X Y) : hequiv f f := begin
 split,
 exact λ (b : B), rfl,
 exact λ (b : B) (x : X b), heq.refl (f.fiber x)
end

lemma hequiv.symm {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f0 f1 : family_fun X Y) : (hequiv f0 f1) → (hequiv f1 f0) := begin
 intro e,
 let eb := λ (b : B), (e.left b).symm,
 let ex := λ (b : B) (x : X b), (e.right b x).symm,
 exact and.intro eb ex
end

lemma hequiv.trans {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f0 f1 f2 : family_fun X Y) :
  (hequiv f0 f1) → (hequiv f1 f2) → (hequiv f0 f2) := begin
 intros e01 e12,split,
 {intro b,
  exact (e01.left b).trans(e12.left b),
 },{
  intros b x,
  exact (e01.right b x).trans(e12.right b x),
 }
end

/-
 We now have three different results, all of which prove that two 
 different morphisms are equal.  The hypotheses involve several
 different combinations of pointwise/global (heterogenous)
 equality on the base or fibres.
-/

lemma ext0 {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f0 f1 : family_fun X Y)
  (eb : f0.base = f1.base)
   (et : f0.fiber == f1.fiber) :
  f0 = f1 :=
begin
 cases f0 with f0b f0t,
 cases f1 with f1b f1t,
 exact @heq_sigma (B → C) (λ fb, Π b,(X b) → (Y (fb b))) (family_fun X Y) 
  family_fun.mk f0b f1b @f0t @f1t eb et
end

lemma ext1 {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f0 f1 : family_fun X Y)
  (eb : f0.base = f1.base)
   (et : ∀ b, f0.fiber_alt b == f1.fiber_alt b) :
  f0 = f1 :=
begin
 let M : (B → C) → (B → C) → Prop := 
  λ g0 g1,
   (∀ h0 : (∀ b, (X b) → (Y (g0 b))),
    ∀ h1 : (∀ b, (X b) → (Y (g1 b))),
    ∀ eh : (∀ b, (h0 b) == (h1 b)),
    h0 == h1),
 have m : ∀ g : B → C, M g g := 
 begin 
  intros g h0 h1 eh,
  have eh1 : ∀ b, h0 b = h1 b := λ b,eq_of_heq (eh b),
  exact heq_of_eq (@funext B (λ b, (X b) → (Y (g b))) h0 h1 eh1),
 end,
 let N : ∀ (g0 g1 : (B → C)), g0 = g1 → M g0 g1 :=
  begin
   intros g0 g1 e,cases e, exact m g0,
  end,
 have et1 : f0.fiber == f1.fiber := 
 begin
  exact N f0.base f1.base eb f0.fiber f1.fiber et,
 end,
 exact ext0 f0 f1 eb et1
end

lemma ext {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f0 f1 : family_fun X Y) (e : hequiv f0 f1) : f0 = f1 :=
begin
 have eb : f0.base = f1.base := funext e.left,
 let M : (B → C) → (B → C) → Prop := 
  λ g0 g1,
   (∀ h0 : (∀ b, (X b) → (Y (g0 b))),
    ∀ h1 : (∀ b, (X b) → (Y (g1 b))),
    ∀ eh : (∀ b x, (h0 b x) == (h1 b x)),
    ∀ b, h0 b == h1 b),
 have m : ∀ (g : B → C), M g g := 
 begin
  intros g h0 h1 e b,
  have e1 : ∀ x, h0 b x = h1 b x := λ x,eq_of_heq (e b x),
  exact heq_of_eq (@funext (X b) (λ _,Y (g b)) (h0 b) (h1 b) e1),
 end,
 let N : ∀ (g0 g1 : (B → C)), g0 = g1 → M g0 g1 :=
 begin
  intros g0 g1 e,cases e, exact m g0,
 end,
 have et : ∀ b, f0.fiber_alt b == f1.fiber_alt b := 
 begin
  exact N f0.base f1.base eb f0.fiber f1.fiber e.right,
 end,
 exact ext1 f0 f1 eb et
end

end family_fun

/-
 We now have some definitions and results about equivalences between
 parametrised families.  Such an equivalence is encoded as a structure
 involving two morphisms of families, together with proofs that the 
 relevant composites are equivalent to identities with respect to the
 equivalence relation defined above.
-/
structure family_equiv {B : Type*} (X : B → Type*) {C : Type*} (Y : C → Type*) := 
(to_fun  : family_fun X Y)
(inv_fun : family_fun Y X)
(left_inv  : family_fun.hequiv (family_fun.compose inv_fun to_fun) (family_fun.id X))
(right_inv : family_fun.hequiv (family_fun.compose to_fun inv_fun) (family_fun.id Y))

namespace family_equiv

/-
 In the standard library there is an existing notion of an equivalence
 between two types.  In the next two results, we prove that an equivalence
 of families gives an equivalence between base types, and also equivalences
 between fiber types.
-/
def base {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*} 
 (f : family_equiv X Y) :
 equiv B C := {
   to_fun := f.to_fun.base,
   inv_fun := f.inv_fun.base,
   left_inv := f.left_inv.left,
   right_inv := f.right_inv.left
 }

def fiber {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*} 
 (f : family_equiv X Y) (b : B) :
 equiv (X b) (Y (f.to_fun.base b)) := begin
  let c : C := f.to_fun.base b,
  let b0 : B := f.inv_fun.base c,
  let eb : b0 = b := f.left_inv.left b,
  let tfn := f.to_fun.fiber_alt b,
  let ifn : (Y c) → (X b) := λ y, @eq.rec_on B (f.inv_fun.base c) X b eb (f.inv_fun.fiber y),
  let e0 : ∀ (y : Y c), ifn y == f.inv_fun.fiber y :=
    λ y, (heq_rec eb (f.inv_fun.fiber y)).symm,
  let li : ∀ x : (X b), ifn (tfn x) = x := 
   λ x, eq_of_heq ((e0 (tfn x)).trans (f.left_inv.right b x)),
  let ri : ∀ y : (Y c), tfn (ifn y) = y := 
  begin
   intro y,
   let x0 := ifn y,
   let x1 := f.inv_fun.fiber y,
   let y0 := f.to_fun.fiber x0,
   let y1 := f.to_fun.fiber x1,
   let e3 : y1 == y0 := heq_subst f.to_fun.base f.to_fun.fiber eb (e0 y).symm,
   exact eq_of_heq (e3.symm.trans (f.right_inv.right c y)),
  end,
  exact {
    to_fun := tfn,
    inv_fun := ifn,
    left_inv := li,
    right_inv := ri
  }
 end

/-
 We next show that there are identity equivalences of families, and that 
 equivalences of families can be reversed or composed.  The corresponding
 results for equivalences of types are proved in the standard library.  We
 follow the notational conventions established there by writing refl, 
 symm and trans rather than referring to identities, reversal and 
 composition. 
-/
def refl {B : Type*} (X : B → Type*) : family_equiv X X := {
  to_fun := family_fun.id X,
  inv_fun := family_fun.id X,
  left_inv  := and.intro (λ (b : B),@rfl B b) (λ (b : B) (x : X b),heq.refl x),
  right_inv := and.intro (λ (b : B),@rfl B b) (λ (b : B) (x : X b),heq.refl x),
 }

def symm {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*}
 (f : family_equiv X Y) : family_equiv Y X := {
   to_fun := f.inv_fun,
   inv_fun := f.to_fun,
   left_inv := f.right_inv,
   right_inv := f.left_inv
 }

def trans {B : Type*} {X : B → Type*} {C : Type*} {Y : C → Type*} {D : Type*} {Z : D → Type*}
 (f : family_equiv X Y) (g : family_equiv Y Z) : (family_equiv X Z) := {
   to_fun := family_fun.compose g.to_fun f.to_fun,
   inv_fun := family_fun.compose f.inv_fun g.inv_fun,
   left_inv := begin
    split,
    {intro b,
    let e0 := f.left_inv.left b,
    let e1 := g.left_inv.left (f.to_fun.base b),
    dsimp[family_fun.compose,family_fun.id] at e0 e1 ⊢,
    exact (congr_arg f.inv_fun.base e1).trans e0
    },{
     intros b x,
     let c := f.to_fun.base b,
     let y := f.to_fun.fiber x,
     let eb0 := f.left_inv.left b,
     let eb1 := g.left_inv.left c,
     let et0 := f.left_inv.right b x,
     let et1 := g.left_inv.right c y,
     dsimp[family_fun.compose,family_fun.id] at eb0 eb1 et0 et1 ⊢,
     exact (family_fun.congr_args f.inv_fun eb1 et1).trans et0,
    }
   end,
   right_inv := begin
    split,
    {intro d,
    let e0 := g.right_inv.left d,
    let e1 := f.right_inv.left (g.inv_fun.base d),
    dsimp[family_fun.compose,family_fun.id] at e0 e1 ⊢,
    exact (congr_arg g.to_fun.base e1).trans e0
    },{
     intros d z,
     let c := g.inv_fun.base d,
     let y := g.inv_fun.fiber z,
     let eb0 := g.right_inv.left d,
     let eb1 := f.right_inv.left c,
     let et0 := g.right_inv.right d z,
     let et1 := f.right_inv.right c y,
     dsimp[family_fun.compose,family_fun.id] at eb0 eb1 et0 et1 ⊢,
     exact (family_fun.congr_args g.to_fun eb1 et1).trans et0,
    }
   end,
 }
 
end family_equiv
