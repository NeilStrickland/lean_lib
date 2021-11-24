/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file effectively deals with the cartesian-closed category
of finite posets and the associated "strong homotopy category".
However, we have taken an ad hoc approach rather than using the
category theory library.
-/

import order.basic order.sort_rank
import data.equiv.basic
import data.fintype.basic data.fin_extra
import logic.relation
import algebra.punit_instances

universes uP uQ uR uS

variables (P : Type uP) [partial_order P]
variables (Q : Type uQ) [partial_order Q]
variables (R : Type uR) [partial_order R]
variables (S : Type uS) [partial_order S]

namespace poset 

structure hom := 
(val : P → Q)
(property : monotone val)

instance : has_coe_to_fun (hom P Q) (λ _, P → Q) := {
 coe := λ f, f.val
}

@[ext]
lemma hom_ext (f g : hom P Q) : 
  (∀ (p : P), f p = g p) → f = g :=
begin
  rcases f with ⟨f,hf⟩,
  rcases g with ⟨g,hg⟩,
  intro h,
  have h' : f = g := funext h,
  rcases h', refl,
end

def id : hom P P := ⟨_root_.id,monotone_id⟩

lemma id_val : (id P).val = _root_.id := rfl

variables {P Q R}

instance hom_order : partial_order (hom P Q) := {
 le := λ f g, ∀ p, (f p) ≤ (g p),
 le_refl := λ f p,le_refl (f p),
 le_antisymm := λ f g f_le_g g_le_f,
  begin ext p, exact le_antisymm (f_le_g p) (g_le_f p), end,
 le_trans := λ f g h f_le_g g_le_h p,
   le_trans (f_le_g p) (g_le_h p)
}

@[simp]
lemma id_eval (p : P) : (id P) p = p := rfl

variable (P)
def const (q : Q) : hom P Q := ⟨λ p,q, λ p₀ p₁ hp, le_refl q⟩

def terminal : hom P punit.{uP + 1} := const P punit.star
variable {P}

lemma eq_terminal (f : hom P punit.{uP + 1}) : f = terminal P := by { ext p }

@[irreducible] 
def adjoint (f : hom P Q) (g : hom Q P) : Prop :=
  ∀ {p : P} {q : Q}, f p ≤ q ↔ p ≤ g q

def adjoint.iff {f : hom P Q} {g : hom Q P} (h : adjoint f g) : 
  ∀ {p : P} {q : Q}, f p ≤ q ↔ p ≤ g q := 
    by { intros p q, unfold adjoint at h, exact h }

def comp : (hom Q R) → (hom P Q) → (hom P R) := 
 λ g f, ⟨g.val ∘ f.val, monotone.comp g.property f.property⟩

lemma comp_val (g : hom Q R) (f : hom P Q) : 
 (comp g f).val = g.val ∘ f.val := rfl

lemma id_comp (f : hom P Q) : comp (id Q) f = f := by {ext, refl}
lemma comp_id (f : hom P Q) : comp f (id P) = f := by {ext, refl}
lemma comp_assoc (h : hom R S) (g : hom Q R) (f : hom P Q) : 
 comp (comp h g) f = comp h (comp g f) := by {ext, refl}

lemma const_comp (r : R) (f : hom P Q) :
 comp (const Q r) f = const P r := by {ext, refl}

lemma comp_const (g : hom Q R) (q : Q) :
 comp g (const P q) = const P (g q) := by {ext, refl}

lemma comp_mono₂ {g₀ g₁ : hom Q R} {f₀ f₁ : hom P Q} 
 (eg : g₀ ≤ g₁) (ef : f₀ ≤ f₁) : comp g₀ f₀ ≤ comp g₁ f₁ := 
 λ p, calc 
  g₀.val (f₀.val p) ≤ g₀.val (f₁.val p) : g₀.property (ef p)
  ... ≤ g₁.val (f₁.val p) : eg (f₁.val p)

@[simp]
lemma comp_eval (g : hom Q R) (f : hom P Q) (p : P) : 
 (comp g f) p = g (f p) := rfl

def comp' : (hom Q R) × (hom P Q) → (hom P R) := 
 λ ⟨g,f⟩, comp g f

lemma comp'_mono : monotone (@comp' P _ Q _ R _) := 
 λ ⟨g₀,f₀⟩ ⟨g₁,f₁⟩ ⟨eg,ef⟩, comp_mono₂ eg ef

def eval : (hom P Q) → P → Q := λ f p, f.val p

lemma eval_mono₂ {f₀ f₁ : hom P Q} {p₀ p₁ : P} 
 (ef : f₀ ≤ f₁) (ep : p₀ ≤ p₁) : eval f₀ p₀ ≤ eval f₁ p₁ := 
calc 
  f₀.val p₀ ≤ f₀.val p₁ : f₀.property ep
  ... ≤ f₁.val p₁ : ef p₁  

def eval' : (hom P Q) × P → Q := λ ⟨f,p⟩, eval f p

lemma eval'_mono : monotone (@eval' P _ Q _) := 
 λ ⟨f₀,p₀⟩ ⟨f₁,p₁⟩ ⟨ef,ep⟩, eval_mono₂ ef ep

def ins' : P → (hom Q (P × Q)) := 
 λ p, ⟨λ q,⟨p,q⟩, λ q₀ q₁ eq, ⟨le_refl p,eq⟩⟩ 

lemma ins_mono : monotone (@ins' P _ Q _) := 
 λ p₀ p₁ ep q, ⟨ep,le_refl q⟩

lemma adjoint.unit {f : hom P Q} {g : hom Q P} (h : adjoint f g) :
  id P ≤ comp g f := λ p, h.iff.mp (le_refl (f p))

lemma adjoint.counit {f : hom P Q} {g : hom Q P} (h : adjoint f g) :
  comp f g ≤ id Q := λ q, h.iff.mpr (le_refl (g q))

variable (P)
def π₀ : Type* := quot (has_le.le : P → P → Prop)
variable {P}

def component (p : P) : π₀ P := quot.mk _ p

def connected : P → P → Prop := λ p₀ p₁, component p₀ = component p₁ 

lemma π₀.sound {p₀ p₁ : P} (hp : p₀ ≤ p₁) : 
 component p₀ = component p₁ := quot.sound hp

lemma π₀.epi {X : Type*} (f₀ f₁ : π₀ P → X) 
 (h : ∀ p, f₀ (component p) = f₁ (component p)) : f₀ = f₁ := 
  by {apply funext, rintro ⟨p⟩, exact (h p),}

def π₀.lift {X : Type*} (f : P → X)
 (h : ∀ p₀ p₁ : P, p₀ ≤ p₁ → f p₀ = f p₁) : 
  (π₀ P) → X := @quot.lift P has_le.le X f h

lemma π₀.lift_beta {X : Type*} (f : P → X)
 (h : ∀ p₀ p₁ : P, p₀ ≤ p₁ → f p₀ = f p₁) (p : P) :
  π₀.lift f h (component p) = f p := 
   @quot.lift_beta P has_le.le X f h p 

def π₀.lift₂ {X : Type*} (f : P → Q → X)
 (h : ∀ p₀ p₁ q₀ q₁, p₀ ≤ p₁ → q₀ ≤ q₁ → f p₀ q₀ = f p₁ q₁) : 
  (π₀ P) → (π₀ Q) → X := 
begin
 let h1 := λ p q₀ q₁ hq, h p p q₀ q₁ (le_refl p) hq,
 let f1 : P → (π₀ Q) → X := λ p, π₀.lift (f p) (h1 p),
 let hf1 : ∀ p q, f1 p (component q) = f p q := λ p, π₀.lift_beta (f p) (h1 p),
 let h2 : ∀ p₀ p₁, p₀ ≤ p₁ → f1 p₀ = f1 p₁ := λ p₀ p₁ hp,
  begin
   apply π₀.epi,intro q,rw[hf1,hf1],
   exact h p₀ p₁ q q hp (le_refl q),
  end,
 exact π₀.lift f1 h2
end

lemma π₀.lift₂_beta {X : Type*} (f : P → Q → X)
 (h : ∀ p₀ p₁ q₀ q₁, p₀ ≤ p₁ → q₀ ≤ q₁ → f p₀ q₀ = f p₁ q₁)
  (p : P) (q : Q) : (π₀.lift₂ f h) (component p) (component q) = f p q := 
begin
 unfold π₀.lift₂,simp only [],rw[π₀.lift_beta,π₀.lift_beta],
end

lemma parity_induction (u : ℕ → Prop)
  (h_zero : u 0)
  (h_even : ∀ i, u (2 * i) → u (2 * i + 1))
  (h_odd  : ∀ i, u (2 * i + 1) → u (2 * i + 2)) : 
  ∀ i, u i
| 0 := h_zero 
| (i + 1) := 
begin
  have ih := parity_induction i,
  let k := i.div2, 
  have hi : cond i.bodd 1 0 + 2 * k = i := nat.bodd_add_div2 i,
  rcases i.bodd ; intro hk; rw[cond] at hk,
  { rw [zero_add] at hk,
    rw [← hk] at ih ⊢, 
    exact h_even k ih },
  { rw [add_comm] at hk,
    rw [← hk] at ih ⊢, 
    exact h_odd k ih }
end

lemma zigzag (u : ℕ → P) 
  (h_even : ∀ i, u (2 * i) ≤ u (2 * i + 1))
  (h_odd : ∀ i, u (2 * i + 2) ≤ u(2 * i + 1)) : 
   ∀ i, component (u i) = component (u 0) := 
parity_induction 
 (λ i, component (u i) = component (u 0))
 rfl 
 (λ i h, (π₀.sound (h_even i)).symm.trans h)
 (λ i h, (π₀.sound (h_odd i)).trans h)

variables (P Q)
def homₕ := π₀ (hom P Q)

def idₕ : homₕ P P := component (id P)

variables {P Q}

def compₕ : (homₕ Q R) → (homₕ P Q) → (homₕ P R) := 
 π₀.lift₂ (λ g f, component (comp g f)) (begin 
  intros g₀ g₁ f₀ f₁ hg hf,
  let hgf := comp_mono₂ hg hf,
  let hgf' := π₀.sound hgf,
  exact (π₀.sound (comp_mono₂ hg hf))
 end)

lemma compₕ_def (g : hom Q R) (f : hom P Q) : 
 compₕ (component g) (component f) = component (comp g f) := 
  by {simp[compₕ,π₀.lift₂_beta]}

lemma id_compₕ (f : homₕ P Q) : compₕ (idₕ Q) f = f := 
 begin 
  rcases f with ⟨f⟩,
  change compₕ (component (id Q)) (component f) = component f,
  rw[compₕ_def,id_comp],
 end 

lemma comp_idₕ (f : homₕ P Q) : compₕ f (idₕ P) = f := 
 begin 
  rcases f with ⟨f⟩,
  change compₕ (component f) (component (id P)) = component f,
  rw[compₕ_def,comp_id],
 end 

lemma comp_assocₕ (h : homₕ R S) (g : homₕ Q R) (f : homₕ P Q) : 
 compₕ (compₕ h g) f = compₕ h (compₕ g f) := 
 begin
  rcases h with ⟨h⟩, rcases g with ⟨g⟩, rcases f with ⟨f⟩,
  change compₕ (compₕ (component h) (component g)) (component f) =
         compₕ (component h) (compₕ (component g) (component f)),
  repeat {rw[compₕ_def]},rw[comp_assoc],
 end

variables (P Q)
structure equivₕ :=
(to_fun : homₕ P Q)
(inv_fun : homₕ Q P)
(left_inv : compₕ inv_fun to_fun = idₕ P)
(right_inv : compₕ to_fun inv_fun = idₕ Q)

@[refl] def equivₕ.refl : equivₕ P P := 
{ to_fun := idₕ P, inv_fun := idₕ P,
  left_inv := comp_idₕ _,
  right_inv := comp_idₕ _ }

variables {P Q}

@[symm] def equivₕ.symm (e : equivₕ P Q) : equivₕ Q P := 
{ to_fun := e.inv_fun, inv_fun := e.to_fun, 
  left_inv := e.right_inv, right_inv := e.left_inv }

@[trans] def equivₕ.trans (e : equivₕ P Q) (f : equivₕ Q R) : (equivₕ P R) := 
{ to_fun  := compₕ f.to_fun e.to_fun,
  inv_fun := compₕ e.inv_fun f.inv_fun,
  left_inv := by
    rw [comp_assocₕ, ← comp_assocₕ _ f.inv_fun, f.left_inv,
        id_compₕ, e.left_inv],
  right_inv := by
    rw [comp_assocₕ, ← comp_assocₕ _ e.to_fun, e.right_inv,
        id_compₕ, f.right_inv] }

lemma adjoint.unitₕ {f : hom P Q} {g : hom Q P} (h : adjoint f g) : 
  compₕ (component g) (component f) = idₕ P := 
begin
  have : id P ≤ comp g f := by { apply adjoint.unit, assumption },
  exact (π₀.sound this).symm
end

lemma adjoint.counitₕ {f : hom P Q} {g : hom Q P} (h : adjoint f g) : 
  compₕ (component f) (component g) = idₕ Q := 
begin
  have : comp f g ≤ id Q := by { apply adjoint.counit, assumption },
  exact (π₀.sound this)
end

/-- LaTeX: rem-adjoint-strong -/
def equivₕ_of_adjoint {f : hom P Q} {g : hom Q P} (h : adjoint f g) : 
  equivₕ P Q :=
{ to_fun := component f, 
  inv_fun := component g,
  left_inv := adjoint.unitₕ h,
  right_inv := adjoint.counitₕ h }

variable (P)

/-- defn-strongly-contractible -/
def contractibleₕ := nonempty (equivₕ P punit.{uP + 1})

variable {P}

lemma contractibleₕ_of_smallest {m : P} (h : ∀ p, m ≤ p) : contractibleₕ P := 
begin
  have : adjoint (const punit.{uP + 1} m) (terminal P) :=
  begin
    unfold adjoint,
    rintro ⟨⟩ p,
    change m ≤ p ↔ punit.star ≤ punit.star,
    simp only [le_refl, h p],
  end,
  let hh := equivₕ_of_adjoint this,
  exact ⟨hh.symm⟩,
end

def π₀.map (f : hom P Q) : (π₀ P) → (π₀ Q) := 
 π₀.lift (λ p, component (f p)) (λ p₀ p₁ ep, quot.sound (f.property ep))

lemma π₀.map_def (f : hom P Q) (p : P) : π₀.map f (component p) = component (f p) := 
 by { simp [π₀.map, π₀.lift_beta] }

lemma π₀.map_congr {f₀ f₁ : hom P Q} (ef : f₀ ≤ f₁) : π₀.map f₀ = π₀.map f₁ := 
begin 
  apply π₀.epi,
  intro p,
  rw [π₀.map_def, π₀.map_def],
  exact π₀.sound (ef p)
end

variable (P)
lemma π₀.map_id : π₀.map (id P) = _root_.id := 
 by { apply π₀.epi, intro p, rw[π₀.map_def], refl }
variable {P}

lemma π₀.map_comp (g : hom Q R) (f : hom P Q) :
 π₀.map (comp g f) = (π₀.map g) ∘ (π₀.map f) := 
  by { apply π₀.epi, intro p, rw[π₀.map_def], refl }

def evalₕ : (homₕ P Q) → (π₀ P) → (π₀ Q) := 
 π₀.lift π₀.map (@π₀.map_congr _ _ _ _)

variables {P Q}

def comma (f : hom P Q) (q : Q) := { p : P // f p ≤ q }

instance comma_order (f : hom P Q) (q : Q) :
  partial_order (comma f q) := by { dsimp[comma], apply_instance }

def cocomma (f : hom P Q) (q : Q) := { p : P // q ≤ f p }

instance cocomma_order (f : hom P Q) (q : Q) :
  partial_order (cocomma f q) := by { dsimp[cocomma], apply_instance }

/-- Here we define predicates finalₕ and cofinalₕ.  
  If (finalₕ f) holds then f is homotopy cofinal, by 
  prop-cofinal.  The dual is also valid, but the converse 
  is not.  
-/

def finalₕ (f : hom P Q) : Prop := 
  ∀ q, contractibleₕ (cocomma f q)

def cofinalₕ (f : hom P Q) : Prop := 
  ∀ q, contractibleₕ (comma f q)


variable (P)

structure fin_ranking := 
(card : ℕ)
(rank : P ≃ fin card)
(rank_mono : monotone rank.to_fun)

section sort 

variable {P}
variable [decidable_rel (has_le.le : P → P → Prop)]

def is_semisorted (l : list P) : Prop := 
  l.pairwise (λ a b, ¬ b < a)

lemma mem_ordered_insert (x p : P) (l : list P) : 
  x ∈ (l.ordered_insert has_le.le p) ↔ x = p ∨ x ∈ l := 
begin
  rw [list.perm.mem_iff (list.perm_ordered_insert _ _ _)],
  apply list.mem_cons_iff  
end

lemma insert_semisorted (p : P) (l : list P) (h : is_semisorted l) : 
  is_semisorted (l.ordered_insert has_le.le p) :=
begin
  induction h with q l hq hl ih,
  { apply list.pairwise_singleton },
  { dsimp [list.ordered_insert], 
    split_ifs with hpq, 
    { apply list.pairwise.cons, 
      { intros x x_in_ql,
        rcases (list.mem_cons_iff _ _ _).mp x_in_ql with ⟨⟨⟩⟩ | x_in_l,
        { exact not_lt_of_ge hpq },
        { intro x_lt_p, 
          exact hq x x_in_l (lt_of_lt_of_le x_lt_p hpq) } },
      { exact list.pairwise.cons hq hl } }, 
    { apply list.pairwise.cons,
      { intros x x_in_pl x_lt_q, 
        rw [mem_ordered_insert] at x_in_pl,
        rcases x_in_pl with ⟨⟨⟩⟩ | x_in_l,
        { exact hpq (le_of_lt x_lt_q) },
        { exact hq x x_in_l x_lt_q } },
      { exact ih } } }
end

lemma insertion_sort_semisorted (l : list P) : 
  is_semisorted (l.insertion_sort (has_le.le : P → P → Prop)) :=
begin
  induction l with p l ih,
  { apply list.pairwise.nil },
  { dsimp [list.insertion_sort],
    apply insert_semisorted,
    exact ih }
end

variable (P) 

lemma exists_fin_ranking [fintype P] : nonempty (fin_ranking P) := 
begin
  rcases fintype.equiv_fin P with f,
  let n := fintype.card P,
  let l := (fin.elems_list n).map f.symm,
  have l_nodup : l.nodup :=
    list.nodup_map f.symm.injective (fin.elems_list_nodup _),
  have l_univ : ∀ p, p ∈ l := λ p,
  begin 
    apply list.mem_map.mpr,
    exact ⟨f.to_fun p, ⟨fin.elems_list_complete (f.to_fun p),f.left_inv p⟩⟩
  end,
  have l_length : l.length = n := 
    (list.length_map f.symm (fin.elems_list _)).trans (fin.elems_list_length _),
  let ls := l.insertion_sort has_le.le,
  let ls_perm := list.perm_insertion_sort has_le.le l,
  have ls_sorted : is_semisorted ls := 
    insertion_sort_semisorted l,
  have ls_nodup : ls.nodup := 
    (list.perm.nodup_iff ls_perm).mpr l_nodup,
  have ls_univ : ∀ p, p ∈ ls := λ p, 
    (list.perm.mem_iff ls_perm).mpr (l_univ p),
  have ls_length : ls.length = n := 
    (list.perm.length_eq ls_perm).trans l_length,
  let inv_fun : (fin n) → P := 
    λ i, ls.nth_le i.val (@eq.subst ℕ (nat.lt i.val) _ _ ls_length.symm i.is_lt),
  let to_fun_aux : ∀ a : P, {i : fin n // inv_fun i = a} := 
  begin
    intro p,
    let i_val := ls.index_of p,
    let i_lt_l := list.index_of_lt_length.mpr (ls_univ p),
    let i_lt_n : i_val < n := @eq.subst ℕ (nat.lt i_val) _ _ ls_length i_lt_l,
    let i : fin n := ⟨i_val,i_lt_n⟩,
    have : inv_fun i = p := list.index_of_nth_le i_lt_l,
    exact ⟨i,this⟩ 
  end,
  let to_fun : P → (fin n) := λ p, (to_fun_aux p).val,
  let left_inv : ∀ p : P, inv_fun (to_fun p) = p := 
    λ p, (to_fun_aux p).property,
  let right_inv : ∀ i : (fin n), to_fun (inv_fun i) = i := 
  begin
   intro i,cases i with i_val i_is_lt,
   apply fin.eq_of_veq,
   let i_lt_l : i_val < ls.length := 
    @eq.subst ℕ (nat.lt i_val) _ _ ls_length.symm i_is_lt,
   exact list.nth_le_index_of ls_nodup i_val i_lt_l,
  end,
  let g : P ≃ (fin n) := ⟨to_fun,inv_fun,left_inv,right_inv⟩,
  have g_mono : monotone g.to_fun := λ p q hpq, 
  begin
    let i := g.to_fun p,
    let j := g.to_fun q,
    have hp : g.inv_fun i = p := g.left_inv p,
    have hq : g.inv_fun j = q := g.left_inv q,
    have hi : i.val < ls.length := by { rw [ls_length], exact i.is_lt },
    have hj : j.val < ls.length := by { rw [ls_length], exact j.is_lt },
    by_cases h : i ≤ j, { exact h },
    exfalso,
    replace h := lt_of_not_ge h,
    have hp' : ls.nth_le i.val hi = g.inv_fun i := rfl,
    have hq' : ls.nth_le j.val hj = g.inv_fun j := rfl,
    let h_ne  := list.pairwise_nth_iff.mp ls_nodup h hi,
    let h_ngt := list.pairwise_nth_iff.mp ls_sorted h hi,
    rw [hp', hq', hp, hq] at h_ne h_ngt,
    exact h_ngt (lt_of_le_of_ne hpq h_ne.symm),
  end,
  exact ⟨⟨n,g,g_mono⟩⟩
end

end sort 


end poset