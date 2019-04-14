/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Given a finite poset `P`, we define `upper P` to be the set of
subsets `U ⊆ P` that are closed upwards.  We order this by 
*reverse* inclusion, to ensure that the map 
`u : p ↦ {x : p ≤ x}` is a morphism of posets.  We prove that
`upper P` is a bounded distributive lattice with this order.
-/

import homotopy.poset

universes uP uQ uR uS

variables (P : Type uP) [decidable_eq P] [fintype P]
variables [partial_order P] [decidable_rel (has_le.le : P → P → Prop)]

namespace poset

variable {P}
def is_upper : finset P → Prop := 
 λ (U : finset P), ∀ (p₀ p₁ : P), (p₀ ≤ p₁) → (p₀ ∈ U) → (p₁ ∈ U) 
variable (P)

lemma is_upper_empty : is_upper (@finset.empty P) := 
 λ p₀ p₁ hp hU, (finset.not_mem_empty p₀ hU).elim

lemma is_upper_univ : is_upper (@finset.univ P _) := 
  λ p₀ p₁ hp hU, (finset.mem_univ p₁)

variable {P}

lemma is_upper_union (U V : finset P) (hU : is_upper U) (hV : is_upper V) : 
  is_upper (U ∪ V) := 
   λ p₀ p₁ hp hpUV,
  begin
   rcases (finset.mem_union.mp hpUV) with hpU | hpV,
   {exact finset.mem_union_left  V (hU p₀ p₁ hp hpU)},
   {exact finset.mem_union_right U (hV p₀ p₁ hp hpV)},
  end

lemma is_upper_inter (U V : finset P) (hU : is_upper U) (hV : is_upper V) : 
  is_upper (U ∩ V) := 
   λ p₀ p₁ hp hpUV,
  begin
   replace hpUV := finset.mem_inter.mp  hpUV,
   apply finset.mem_inter.mpr,
   split,
   {exact (hU p₀ p₁ hp hpUV.left)},
   {exact (hV p₀ p₁ hp hpUV.right)},
  end

def distrib (U V W : finset P) : 
 U ∩ (V ∪ W) ⊆ (U ∩ V) ∪ (U ∩ W) := 
begin 
 intros A h,
 rw[finset.mem_inter,finset.mem_union] at h,
 rw[finset.mem_union,finset.mem_inter,finset.mem_inter],
 rcases h with ⟨hU,hV | hW⟩,
 exact or.inl ⟨hU,hV⟩,
 exact or.inr ⟨hU,hW⟩
end

variable (P)

def upper := { U : finset P // is_upper U }

namespace upper 

instance : has_mem P (upper P) := ⟨λ p  U, p ∈ U.val⟩ 

instance bdl : lattice.bounded_distrib_lattice (upper P) := {
  le := λ U V, V.val ⊆ U.val,
  le_refl := λ U, le_refl U.val,
  le_antisymm := λ U V (h0 : V.val ⊆ U.val) (h1 : U.val ⊆ V.val),
                   begin apply subtype.eq, exact le_antisymm h1 h0, end,
  le_trans := λ U V W (h0 : V.val ⊆ U.val) (h1 : W.val ⊆ V.val), 
                 @le_trans (finset P) _ W.val V.val U.val h1 h0,
  bot := ⟨finset.univ,is_upper_univ P⟩,
  top := ⟨finset.empty,is_upper_empty P⟩,
  inf := λ U V, ⟨U.val ∪ V.val,
                is_upper_union U.val V.val U.property V.property⟩,
  sup := λ U V, ⟨U.val ∩ V.val,
                is_upper_inter U.val V.val U.property V.property⟩,
  bot_le := λ U,finset.subset_univ U.val,
  le_top := λ U,finset.empty_subset U.val,
  le_sup_left  := λ U V,finset.inter_subset_left  U.val V.val,
  le_sup_right := λ U V,finset.inter_subset_right U.val V.val,
  sup_le := λ U V W 
             (U_le_W : W.val ⊆ U.val) 
             (V_le_W : W.val ⊆ V.val), 
             finset.subset_inter U_le_W V_le_W,
  inf_le_left  := λ U V,finset.subset_union_left  U.val V.val,
  inf_le_right := λ U V,finset.subset_union_right U.val V.val,
  le_inf := λ U V W 
             (U_le_V : V.val ⊆ U.val) 
             (U_le_W : W.val ⊆ U.val), 
             finset.union_subset U_le_V U_le_W,
  le_sup_inf := λ U V W A h,
    distrib U.val V.val W.val h,
}

variable {P}

/-
 We embed `P` in `upper P` using the map `u : A ↦ { B : A ⊆ B }` 
-/

def u : P → upper P := 
 λ p, ⟨finset.univ.filter (λ q, p ≤ q),
  begin intros q r hqr hpq,
   replace hpq := (finset.mem_filter.mp hpq).right,
   exact finset.mem_filter.mpr ⟨finset.mem_univ r,le_trans hpq hqr⟩,
  end
 ⟩

end upper

end poset