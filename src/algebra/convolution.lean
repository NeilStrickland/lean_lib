/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file sets up a framework for convolution.  The first ingredient
is an additive monoid `M` with the property that for any `m ∈ M`, the
set `{⟨x,y⟩ : x + y = m}` is finite.  If `M` has this property and `R`
is a ring and `f,g : M → R` then we can define `(f * g) m` to be the 
sum of `(f x) * (g y)` for all pairs `⟨x,y⟩` with `x + y = m`.  If 
`M = ℕ` then this rule gives us the power series ring `R[[x]]`.  

The first part of this file defines a typeclass `sum_set M` for 
additive monoids `M` with the finiteness property mentioned above,
and derives some additional properties of such monoids.

We then define convolution.  In order to cover some additional 
applications, we work in a context slightly more general than outlined
above.  First, we define `convolution.map M P := M → P`, and attach 
the convolution structure to the name `convolution.map`.  This is 
intended to accomodate the fact that we might want to use pointwise
products on `M → P` in some other contexts.  I am not sure whether
this is the best way to address that issue.  Also, we will assume 
that we have a biadditive map `m₁₂ : P₁ → P₂ → P₁₂` of additive
commutative monoids, and we will use it to define a convolution 
operation `map M P₁ → map M P₂ → map M P₁₂`.  We can recover the
ring structure on `map M R` by taking `P₁ = P₂ = P₁₂ = R`.
-/

import data.fintype data.finsupp algebra.big_operators algebra.pi_instances 
import data.list_extra algebra.biadditive algebra.prod_equiv
import tactic.squeeze tactic.pi_instances

namespace convolution

open finset

class sum_set (M : Type*) [add_monoid M] := 
 (els : M → finset (M × M))
 (mem_els : forall (m : M) (xy : M × M), xy ∈ els m ↔ xy.1 + xy.2 = m)

namespace sum_set 

variables {M : Type*} [add_monoid M] [decidable_eq M] [sum_set M]
variable (m : M)

def incl (x : M) : (M × M) ↪ (M × M × M) := 
 ⟨prod.mk x,λ yz₀ yz₁ e, by {injection e}⟩ 

def incr (z : M) : (M × M) ↪ (M × M × M) := 
 ⟨λ xy, ⟨xy.1,xy.2,z⟩,λ ⟨x₀,y₀⟩ ⟨x₁,y₁⟩ e,
  by {injection e with ex eyz,injection eyz with ey ez,
      change x₀ = x₁ at ex,change y₀ = y₁ at ey,rw[ex,ey],}⟩ 

variable (M)
def twist : M × M ↪ M × M := 
 ⟨λ xy, ⟨xy.2,xy.1⟩,
  λ ⟨x₀,y₀⟩ ⟨x₁,y₁⟩ e,
   by {injection e with hy hx, 
       change x₀ = x₁ at hx, change y₀ = y₁ at hy, rw[hx,hy],}⟩ 
variable {M}

def els3 : finset (M × M × M) := 
 (els m).bind (λ xv,(els xv.2).map (incl xv.1))

def els3' : finset (M × M × M) := 
 (els m).bind (λ uz,(els uz.1).map (incr uz.2))

lemma els3_disjoint (m : M)
 (xv₁ : M × M) (h₁ : xv₁ ∈ els m) (xv₂ : M × M) (h₂ : xv₂ ∈ els m) 
 (h : xv₁ ≠ xv₂) :
  (els xv₁.2).map (incl xv₁.1) ∩ (els xv₂.2).map (incl xv₂.1) = ∅ := 
begin
 rcases xv₁ with ⟨x₁,v₁⟩,
 rcases xv₂ with ⟨x₂,v₂⟩,
 apply eq_empty_iff_forall_not_mem.mpr,intros w hw,apply h,
 rcases (mem_inter.mp hw) with ⟨hw₁,hw₂⟩,
 rcases mem_map.mp hw₁ with ⟨yz₁,⟨w_sum₁,w_eq₁⟩⟩,
 rcases mem_map.mp hw₂ with ⟨yz₂,⟨w_sum₂,w_eq₂⟩⟩,
 injection (w_eq₁.trans w_eq₂.symm) with ex eyz,
 change x₁ = x₂ at ex,
 replace w_sum₁ := (mem_els v₁ _).mp w_sum₁,
 replace w_sum₂ := (mem_els v₂ _).mp w_sum₂,
 rw[eyz] at w_sum₁,
 have ev : v₁ = v₂ := w_sum₁.symm.trans w_sum₂,
 rw[ex,ev],
end

lemma els3'_disjoint (m : M)
 (uz₁ : M × M) (h₁ : uz₁ ∈ els m) (uz₂ : M × M) (h₂ : uz₂ ∈ els m) 
 (h : uz₁ ≠ uz₂) :
  (els uz₁.1).map (incr uz₁.2) ∩ (els uz₂.1).map (incr uz₂.2) = ∅ := 
begin
 rcases uz₁ with ⟨u₁,z₁⟩,
 rcases uz₂ with ⟨u₂,z₂⟩,
 apply eq_empty_iff_forall_not_mem.mpr,intros w hw,apply h,
 rcases (mem_inter.mp hw) with ⟨hw₁,hw₂⟩,
 rcases mem_map.mp hw₁ with ⟨xy₁,⟨w_sum₁,w_eq₁⟩⟩,
 rcases mem_map.mp hw₂ with ⟨xy₂,⟨w_sum₂,w_eq₂⟩⟩,
 injection (w_eq₁.trans w_eq₂.symm) with ex eyz,
 injection eyz with ey ez,
 change z₁ = z₂ at ez,
 replace w_sum₁ := (mem_els u₁ _).mp w_sum₁,
 replace w_sum₂ := (mem_els u₂ _).mp w_sum₂,
 rw[ex,ey] at w_sum₁,
 have eu : u₁ = u₂ := w_sum₁.symm.trans w_sum₂,
 rw[eu,ez],
end

lemma mem_els3 (xyz : M × M × M) : 
 xyz ∈ els3 m ↔ xyz.1 + xyz.2.1 + xyz.2.2 = m := 
begin
 rcases xyz with ⟨x,y,z⟩,
 change (⟨x,y,z⟩ : M × M × M) ∈ els3 m ↔ x + y + z = m,
 split,
 {intro hw,
  rcases mem_bind.mp hw with ⟨xv,⟨hxv,h⟩⟩,
  replace hxv := (mem_els m xv).mp hxv,
  rcases mem_map.mp h with ⟨yz,⟨hyz,h'⟩⟩,
  replace hyz := (mem_els _ yz).mp hyz,
  injection h' with ex eyz, rw[eyz] at hyz,
  rw[← hyz,ex,← add_assoc] at hxv,exact hxv,
 },
 {intro e,
  apply mem_bind.mpr,
  use ⟨x,y + z⟩,
  have : x + (y + z) = m := by {rw[← add_assoc,e]},
  use (mem_els m ⟨x,y + z⟩).mpr this,
  apply mem_map.mpr,
  use ⟨y,z⟩, use (mem_els _ _).mpr rfl,refl,
 }
end

lemma els3_assoc : els3 m = els3' m :=
begin 
 ext ⟨x,y,z⟩,rw[mem_els3],
 change x + y + z = m ↔ (⟨x,y,z⟩ : M × M × M) ∈ els3' m,
 split,
 {intro e,
  apply mem_bind.mpr,use ⟨x + y,z⟩,use (mem_els m _).mpr e,
  apply mem_map.mpr,
  use ⟨x,y⟩, use (mem_els _ _).mpr rfl,refl,
 },
 {intro hw,
  rcases mem_bind.mp hw with ⟨uz,⟨huz,h⟩⟩,
  replace huz := (mem_els m uz).mp huz,
  rcases mem_map.mp h with ⟨xy,⟨hxy,h'⟩⟩,
  replace hxy := (mem_els _ xy).mp hxy,
  injection h' with hx hyz,injection hyz with hy hz,
  rw[hx,hy] at hxy, rw[← hxy,hz] at huz,
  exact huz,
 }
end

lemma els_zero_left : 
 (els m).filter (λ xy, 0 = xy.1) = finset.singleton ⟨0,m⟩ := 
begin
 ext ⟨x,y⟩,
 rw[mem_filter,mem_els,mem_singleton],
 split,
 {rintro ⟨h,h'⟩,change x + y = m at h, change 0 = x at h',
  rw[← h'] at h ⊢,rw[zero_add] at h,rw[h],
 },{
  intro e,injection e with ex ey,rw[ex,ey],
  split,{change 0 + m = m,rw[zero_add],},{refl}
 }
end

lemma els_zero_right : 
 (els m).filter (λ xy, 0 = xy.2) = finset.singleton ⟨m,0⟩ := 
begin
 ext ⟨x,y⟩,
 rw[mem_filter,mem_els,mem_singleton],
 split,
 {rintro ⟨h,h'⟩,change x + y = m at h, change 0 = y at h',
  rw[← h'] at h ⊢,rw[add_zero] at h,rw[h],
 },{
  intro e,injection e with ex ey,rw[ex,ey],
  split,{change m + 0 = m,rw[add_zero],},{refl}
 }
end

instance : sum_set ℕ := {
  els := λ m, (range m.succ).image (λ i, ⟨i,m - i⟩),
  mem_els := λ m ⟨x,y⟩, begin 
   split,
   {intro h,rcases mem_image.mp h with ⟨i,⟨i_is_le,e⟩⟩,
    replace i_is_le : i ≤ m := mem_range_succ.mp i_is_le,
    injection e with ex ey,rw[← ex,← ey],
    exact nat.add_sub_of_le i_is_le,
   },
   {intro e,rw[mem_image],use x,
    use mem_range_succ.mpr (e ▸ (nat.le_add_right x y)),congr,
    exact nat.sub_eq_of_eq_add e.symm,
   }
  end
}

def shuffle (M₁ : Type*) (M₂ : Type*) :
 (M₁ × M₁) × (M₂ × M₂) ↪ (M₁ × M₂) × (M₁ × M₂) := {
 to_fun := λ x, ⟨⟨x.1.1,x.2.1⟩,⟨x.1.2,x.2.2⟩⟩,
 inj := begin
  rintros ⟨⟨x₁,x₂⟩,⟨x₃,x₄⟩⟩ ⟨⟨y₁,y₂⟩,⟨y₃,y₄⟩⟩ e,
  injection e with e₁₃ e₂₄,
  injection e₁₃ with e₁ e₃, injection e₂₄ with e₂ e₄,
  change x₁ = y₁ at e₁, change x₂ = y₂ at e₂,
  change x₃ = y₃ at e₃, change x₄ = y₄ at e₄,
  rw[e₁,e₂,e₃,e₄],
 end
}

instance product
         (M₁ : Type*) [add_monoid M₁] [sum_set M₁] 
         (M₂ : Type*) [add_monoid M₂] [sum_set M₂] : sum_set (M₁ × M₂) := {
 els := λ m, (finset.product (els m.1) (els m.2)).map (shuffle M₁ M₂),
 mem_els := begin 
  rintros ⟨m₁,m₂⟩ ⟨⟨x₁,x₃⟩,⟨x₂,x₄⟩⟩,
  simp only[],split,
  {intro h₁,rcases (mem_map.mp h₁) with ⟨⟨⟨y₁,y₂⟩,⟨y₃,y₄⟩⟩,⟨h₂,e⟩⟩,
   dsimp[shuffle] at e,injection e with e₁₃ e₂₄,
   injection e₁₃ with e₁ e₃, injection e₂₄ with e₂ e₄,
   rw[← e₁,← e₂,← e₃,← e₄],
   change prod.mk (y₁ + y₂) (y₃ + y₄) = prod.mk m₁ m₂,
   rcases mem_product.mp h₂ with ⟨h₃,h₄⟩,
   replace h₃ : y₁ + y₂ = m₁ := (mem_els _ _).mp h₃,
   replace h₄ : y₃ + y₄ = m₂ := (mem_els _ _).mp h₄,
   rw[h₃,h₄],
  },{
   intro e,injection e with e₁ e₂,
   apply mem_map.mpr, use ⟨⟨x₁,x₂⟩,⟨x₃,x₄⟩⟩,
   have h₁ : (prod.mk x₁ x₂) ∈ els m₁ := (mem_els _ _).mpr e₁,
   have h₂ : (prod.mk x₃ x₄) ∈ els m₂ := (mem_els _ _).mpr e₂,
   use mem_product.mpr ⟨h₁,h₂⟩,refl,
  }
 end
} 

end sum_set

namespace sum_set

variables {M : Type*} [add_comm_monoid M] [decidable_eq M] [sum_set M]
variable (m : M)

lemma els_twist :
 (els m).map (twist M) = els m := 
begin
 ext ⟨x,y⟩,rw[mem_els],split,
 {intro h,rcases mem_map.mp h with ⟨⟨y',x'⟩,⟨yx_sum,e⟩⟩,
  change (⟨x',y'⟩ : M × M) = ⟨x,y⟩ at e,injection e with ex ey,
  replace yx_sum : y' + x' = m := (mem_els _ _).mp yx_sum,
  rw[ex,ey,add_comm y x] at yx_sum,exact yx_sum,
 },{
  intro e,rw[add_comm] at e,change y + x = m at e,
  apply mem_map.mpr,use ⟨y,x⟩,
  use (mem_els _ _).mpr e,refl,
 }
end

end sum_set

def map (M : Type*) (P : Type*) := M → P

namespace map

variables (M : Type*) (P : Type*)

instance : has_coe_to_fun (map M P) := ⟨λ _, M → P,id⟩

variables {M} {P}

instance [has_zero P] : has_zero (map M P) := 
 by {dsimp[map],apply_instance}

@[simp]
lemma zero_apply [has_zero P] {m : M} :
 (0 : map M P) m = 0 := rfl

instance [has_add P] : has_add (map M P) := 
 by {dsimp[map],apply_instance}

@[simp]
lemma add_apply [has_add P] {a₁ a₂ : map M P} {m : M} : 
 (a₁ + a₂) m = a₁ m + a₂ m := rfl

instance [add_semigroup P] : add_semigroup (map M P) := 
 by {dsimp[map],apply_instance}

instance [add_comm_semigroup P] : add_comm_semigroup (map M P) := 
 by {dsimp[map],apply_instance}

instance [add_monoid P] : add_monoid (map M P) := 
 by {dsimp[map],apply_instance}

instance [add_comm_monoid P] : add_comm_monoid (map M P) := 
 by {dsimp[map],apply_instance}

instance [add_group P] : add_group (map M P) := 
 by {dsimp[map],apply_instance}

instance [add_comm_group P] : add_comm_group (map M P) := 
 by {dsimp[map],apply_instance}

instance [has_zero M] [decidable_eq M] [has_zero P] [has_one P] : has_one (map M P) := 
 ⟨λ m, ite (m = 0) 1 0⟩

@[simp]
lemma one_apply [has_zero M] [decidable_eq M] [has_zero P] [has_one P] (m : M) :
 (1 : map M P) m = ite (m = 0) 1 0 := rfl

@[simp]
lemma one_apply_zero [has_zero M] [decidable_eq M] [has_zero P] [has_one P] :
 (1 : map M P) 0 = 1 := by { dsimp[has_one.one],rw[if_pos rfl] }

lemma one_apply_nz [has_zero M] [decidable_eq M] [has_zero P] [has_one P]
 {m : M} (h : m ≠ 0) : (1 : map M P) m = 0 := 
  by { dsimp[has_one.one],rw[if_neg h] }

@[extensionality]
lemma ext : ∀ {a₁ a₂ : map M P}, (∀ m, a₁ m = a₂ m) → a₁ = a₂ := @funext _ _

section single 

variables [decidable_eq M] 

def single [has_zero P] (m : M) (p : P) : (map M P) := 
 λ x, ite (m = x) p (0 : P)

lemma single_apply [has_zero P] {m : M} {p : P} (x : M) :
 (single m p) x = ite (m = x) p 0 := rfl

@[simp] lemma single_eq_same [has_zero P] {m : M} {p : P} :
 (single m p) m = p := if_pos rfl

@[simp] lemma single_eq_of_ne [has_zero P] {m x : M} {p : P} (h : m ≠ x) :
 (single m p) x = 0 := if_neg h

@[simp] lemma single_zero [has_zero P] {m : M} : single m (0 : P) = 0 := 
 by {ext x,dsimp[single],split_ifs; refl}

lemma single_add [add_monoid P] {m : M} {p₁ p₂ : P} :
 single m (p₁ + p₂) = single m p₁ + single m p₂ := 
  by {ext x,dsimp[single],split_ifs,refl,rw[zero_add],}

def delta [has_zero P] [has_zero M] (p : P) : map M P := single (0 : M) p

lemma delta_apply [has_zero P] [has_zero M] {p : P} {x : M} : 
 (delta p) x = ite ((0 : M) = x) p (0 : P) := rfl

lemma delta_eq_zero [has_zero P] [has_zero M] {p : P} : 
 (delta p) (0 : M) = p := if_pos rfl

lemma delta_eq_of_ne [has_zero P] [has_zero M] {p : P} {x : M} (h : 0 ≠ x) :
 (delta p) x = 0 := single_eq_of_ne h

lemma delta_zero [has_zero P] [has_zero M] :
 ((delta (0 : P)) : map M P) = 0 := single_zero

lemma delta_add [add_monoid P] [has_zero M] {p₁ p₂ : P} :
 (delta (p₁ + p₂) : map M P) = delta p₁ + delta p₂ := single_add

end single

end map

section convolve 

variables {M : Type*} [add_monoid M] [decidable_eq M] [sum_set M]

open sum_set
open map

variables {P₁ : Type*} {P₂ : Type*} {P₃ : Type*} 
variables {P₁₂ : Type*} {P₂₃ : Type*} {P₁₂₃ : Type*}
variables [add_comm_monoid P₁] [add_comm_monoid P₂] [add_comm_monoid P₃]
variables [add_comm_monoid P₁₂] [add_comm_monoid P₂₃] [add_comm_monoid P₁₂₃]

variables (m₁₂ : P₁ → P₂ → P₁₂) [is_biadditive m₁₂] 
variables (m₂₃ : P₂ → P₃ → P₂₃) [is_biadditive m₂₃] 
variables (m₁₂₃  : P₁₂ → P₃ → P₁₂₃) [is_biadditive m₁₂₃] 
variables (m'₁₂₃ : P₁ → P₂₃ → P₁₂₃) [is_biadditive m'₁₂₃] 

def convolve (u₁ : map M P₁) (u₂ : map M P₂) : (map M P₁₂) := 
 λ m, (els m).sum (λ x, m₁₂ (u₁ x.1) (u₂ x.2)) 

lemma zero_convolve (p₂ : map M P₂) : convolve m₁₂ 0 p₂ = 0 := begin
 ext m,dsimp[convolve],
 have : (els m).sum (λ x, (0 : P₁₂)) = 0 := sum_const_zero,
 rw[← this],congr,funext x,rw[is_biadditive.zero_mul m₁₂],
end

lemma convolve_zero (p₁ : map M P₁) : convolve m₁₂ p₁ 0 = 0 := begin
 ext m,dsimp[convolve],
 have : (els m).sum (λ x, (0 : P₁₂)) = 0 := sum_const_zero,
 rw[← this],congr,funext x,rw[is_biadditive.mul_zero m₁₂],
end

lemma add_convolve (p₁ q₁ : map M P₁) (p₂ : map M P₂) : 
 convolve m₁₂ (p₁ + q₁) p₂ = convolve m₁₂ p₁ p₂ + convolve m₁₂ q₁ p₂ := begin
 ext m,
 dsimp[convolve],rw[← sum_add_distrib],congr,funext x,
 rw[is_biadditive.add_mul m₁₂],
end

lemma convolve_add (p₁ : map M P₁) (p₂ q₂ : map M P₂) : 
 convolve m₁₂ p₁ (p₂ + q₂) = convolve m₁₂ p₁ p₂ + convolve m₁₂ p₁ q₂ := begin
 ext m,
 dsimp[convolve],rw[← sum_add_distrib],congr,funext x,
 rw[is_biadditive.mul_add m₁₂],
end

instance biadditive_convolve:
 is_biadditive (convolve m₁₂ : (map M P₁) → (map M P₂) → (map M P₁₂)) := {
  zero_mul := zero_convolve m₁₂,
  add_mul  := add_convolve  m₁₂,
  mul_zero := convolve_zero m₁₂,
  mul_add  := convolve_add  m₁₂,
}

lemma convolve_assoc (p₁ : map M P₁) (p₂ : map M P₂) (p₃ : map M P₃) 
 (m_assoc : ∀ (p₁ : P₁) (p₂ : P₂) (p₃ : P₃), m₁₂₃ (m₁₂ p₁ p₂) p₃ = m'₁₂₃ p₁ (m₂₃ p₂ p₃)) :
 convolve m₁₂₃ (convolve m₁₂ p₁ p₂) p₃ = 
 convolve m'₁₂₃ p₁ (convolve m₂₃ p₂ p₃) := 
begin
 ext m,
 let f' : M × M × M → P₁₂₃ := λ x, m₁₂₃  (m₁₂ (p₁ x.1) (p₂ x.2.1)) (p₃ x.2.2),
 let f  : M × M × M → P₁₂₃ := λ x, m'₁₂₃ (p₁ x.1) (m₂₃ (p₂ x.2.1) (p₃ x.2.2)),
 have ef : f' = f := by {funext x,apply m_assoc},
 have em' : (els3' m).sum f' = (convolve m₁₂₃ (convolve m₁₂ p₁ p₂) p₃) m := 
 begin
  dsimp[convolve,els3'],
  rw[sum_bind (els3'_disjoint m)],congr,ext ⟨x,v⟩,
  rw[is_biadditive.sum_mul m₁₂₃,sum_map],congr,
 end,
 have em : (els3 m).sum f    = (convolve m'₁₂₃ p₁ (convolve m₂₃ p₂ p₃)) m := 
 begin
  dsimp[convolve,els3],
  rw[sum_bind (els3_disjoint m)],congr,ext ⟨u,z⟩,
  rw[is_biadditive.mul_sum m'₁₂₃,sum_map],congr,  
 end,
 rw[← em,← em',ef,els3_assoc],
end

lemma delta_convolve (p₁ : P₁) (u₂ : map M P₂) (m : M) :
 (convolve m₁₂ (delta p₁) u₂) m = m₁₂ p₁ (u₂ m) := 
begin
 dsimp[convolve],
 let f  : M × M → P₁₂ := λ x, m₁₂ (delta p₁ x.1) (u₂ x.2),
 let f' : M × M → P₁₂ := λ x, ite (0 = x.1) (f x) 0,
 have ef : f = f' :=
  by {ext x,dsimp[f,f'],
      split_ifs with hx,{refl},{rw[delta_eq_of_ne hx,is_biadditive.zero_mul m₁₂]}},
 change (els m).sum f = m₁₂ p₁ (u₂ m),
 rw[ef],
 have : ((els m).filter (λ (x : M × M), 0 = x.1)).sum f = (els m).sum f' := 
  sum_filter (λ (x : M × M), 0 = x.1) f,
 rw[← this],rw[els_zero_left,sum_singleton],
 dsimp[f],rw[delta_eq_zero],
end

lemma convolve_delta (u₁ : M → P₁) (p₂ : P₂) (m : M) :
 (convolve m₁₂ u₁ (delta p₂)) m = m₁₂ (u₁ m) p₂ := 
begin
 dsimp[convolve],
 let f  : M × M → P₁₂ := λ x, m₁₂ (u₁ x.1) (delta p₂ x.2),
 let f' : M × M → P₁₂ := λ x, ite (0 = x.2) (f x) 0,
 have ef : f = f' :=
  by {ext x,dsimp[f,f'],
      split_ifs with hx,{refl},{rw[delta_eq_of_ne hx,is_biadditive.mul_zero m₁₂]}},
 change (els m).sum f = m₁₂ (u₁ m) p₂,
 rw[ef],
 have : ((els m).filter (λ (x : M × M), 0 = x.2)).sum f = (els m).sum f' := 
  sum_filter (λ x, 0 = x.2) f,
 rw[← this,els_zero_right,sum_singleton],
 dsimp[f],rw[delta_eq_zero],
end

lemma delta_convolve_delta (p₁ : P₁) (p₂ : P₂) :
 (convolve m₁₂ (delta p₁) (delta p₂) : map M P₁₂) = delta (m₁₂ p₁ p₂) := 
by { ext m, rw[delta_convolve,delta_apply,delta_apply],
     split_ifs,refl,rw[is_biadditive.mul_zero m₁₂]}

end convolve 

namespace map

variables {M : Type*} [add_monoid M] [decidable_eq M] [sum_set M]

instance to_semiring {R : Type*} [semiring R] : semiring (map M R) := {
  one := delta (1 : R),
  mul := convolve ((*) : R → R → R),
  zero_mul := λ a, zero_convolve (*) a,
  mul_zero := λ a, convolve_zero (*) a,
  one_mul := λ a, begin 
   ext m, 
   change convolve (*) (delta (1 : R)) a m = a m,
   rw[delta_convolve,one_mul], 
  end,
  mul_one := λ a, begin 
   ext m,
   change convolve (*) a (delta (1 : R)) m = a m,
   rw[convolve_delta,mul_one], 
  end,
  mul_assoc := λ a b c, convolve_assoc (*) (*) (*) (*) a b c (mul_assoc),
  left_distrib  := λ a b c, convolve_add (*) a b c,
  right_distrib := λ a b c, add_convolve (*) a b c,
  .. (by apply_instance : add_comm_monoid (map M R))
}

instance to_ring {R : Type*} [ring R] : ring (map M R) := {
  .. (by apply_instance : add_comm_group (map M R)),
  .. (by apply_instance : semiring (map M R))
}

end map

namespace map 

open sum_set

variables {M : Type*} [add_comm_monoid M] [decidable_eq M] [sum_set M]

instance to_comm_semiring {R : Type*} [comm_semiring R] : comm_semiring (map M R) := {
 mul_comm := λ a₁ a₂, begin 
  let f  : M × M → R := λ x, (a₁ x.1) * (a₂ x.2),
  let f' : M × M → R := λ x, (a₂ x.1) * (a₁ x.2),
  have ef : (λ x, f (twist M x)) = f' := by {
   ext x,dsimp[f,f',twist],rw[mul_comm],
  },
  ext m, change (els m).sum f = (els m).sum f',
  rw[← ef, ← sum_map (els m) (twist M) f,els_twist],
 end,
 .. map.to_semiring
}

instance to_comm_ring {R : Type*} [comm_ring R] : comm_ring (map M R) := {
  .. (by apply_instance : add_comm_group (map M R)),
  .. (by apply_instance : comm_semiring (map M R))
}

end map

end convolution

