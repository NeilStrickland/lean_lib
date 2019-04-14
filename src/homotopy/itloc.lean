/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file formalises some of the combinatorial part of the 
paper "Iterated chromatic localization" by Nicola Bellumat and
Neil Strickland (which is in preparation).  We expect to 
formalise all of the combinatorial content (including the 
results in the combinatorial homotopy theory of finite 
posets).  We may or may not add in a kind of "formal abstracts"
account of the theory of derivators and chromatic homotopy 
theory that forms the rest of the paper.
-/

import data.list.basic
import data.fin
import data.fintype
import order.bounded_lattice
import algebra.big_operators
import data.fin_extra 
import homotopy.poset homotopy.upper

import tactic.squeeze

open poset

namespace itloc

/-
 `𝕀 n` is the set {0,1,...,n-1}
-/
variable (n : ℕ)

def 𝕀 := fin n

namespace 𝕀 
instance : fintype (𝕀 n) := by {dsimp[𝕀],apply_instance}
instance : decidable_eq (𝕀 n) := by {dsimp[𝕀],apply_instance}

instance : decidable_linear_order (𝕀 n) := 
  (@fin.decidable_linear_order n).

end 𝕀 

/-
 `ℙ n` is the poset of subsets of `𝕀 n`, ordered by inclusion
-/

def ℙ := finset (𝕀 n)

namespace ℙ 

instance : fintype (ℙ n) := by {dsimp[ℙ],apply_instance}
instance : decidable_eq (ℙ n) := by {dsimp[ℙ],apply_instance}
instance : has_mem (𝕀 n) (ℙ n) := by {dsimp[𝕀,ℙ], apply_instance }

instance dl : lattice.distrib_lattice (ℙ n) := 
 by {dsimp[ℙ],apply_instance}.

instance : lattice.bounded_distrib_lattice (ℙ n) := {
  bot := finset.empty,
  top := finset.univ,
  le_top := λ (A : finset (𝕀 n)),
   begin change A ⊆ finset.univ,intros i _,exact finset.mem_univ i end,
  bot_le := λ (A : finset (𝕀 n)),
   begin change finset.empty ⊆ A,intros i h,
    exact (finset.not_mem_empty i h).elim end,
  .. (ℙ.dl n)
}

instance : decidable_rel (λ (A B : ℙ n), A ≤ B) := 
 λ (A B : finset (𝕀 n)), by { change decidable (A ⊆ B), apply_instance, }

variable {n} 

lemma not_mem_bot (i : 𝕀 n) : ¬ (i ∈ (⊥ : ℙ n)) := finset.not_mem_empty i

lemma mem_top     (i : 𝕀 n) :   (i ∈ (⊤ : ℙ n)) := finset.mem_univ i

lemma mem_sup {A B : ℙ n} {i : 𝕀 n} : 
 i ∈ A ⊔ B ↔ (i ∈ A) ∨ (i ∈ B) := finset.mem_union

lemma mem_inf {A B : ℙ n} {i : 𝕀 n} : 
 i ∈ A ⊓ B ↔ (i ∈ A) ∧ (i ∈ B) := finset.mem_inter

def filter_lt (i : ℕ) (A : ℙ n) := A.filter (λ a, a.val < i)
def filter_le (i : ℕ) (A : ℙ n) := A.filter (λ a, a.val ≤ i)
def filter_gt (i : ℕ) (A : ℙ n) := A.filter (λ a, a.val > i)
def filter_ge (i : ℕ) (A : ℙ n) := A.filter (λ a, a.val ≥ i)

lemma mem_filter_lt {i : ℕ} {A : ℙ n} {a : 𝕀 n} : 
 a ∈ (filter_lt i A) ↔ a ∈ A ∧ a.val < i := finset.mem_filter 

lemma mem_filter_le {i : ℕ} {A : ℙ n} {a : 𝕀 n} : 
 a ∈ (filter_le i A) ↔ a ∈ A ∧ a.val ≤ i := finset.mem_filter 

lemma mem_filter_gt {i : ℕ} {A : ℙ n} {a : 𝕀 n} : 
 a ∈ (filter_gt i A) ↔ a ∈ A ∧ a.val > i := finset.mem_filter 

lemma mem_filter_ge {i : ℕ} {A : ℙ n} {a : 𝕀 n} : 
 a ∈ (filter_ge i A) ↔ a ∈ A ∧ a.val ≥ i := finset.mem_filter 

lemma filter_lt_ge (i : ℕ) (A : ℙ n) :
 A = (filter_lt i A) ⊔ (filter_ge i A) := 
begin 
 ext a,
 rw[mem_sup,mem_filter_lt,mem_filter_ge,← and_or_distrib_left],
 rw[eq_true_intro (lt_or_ge a.val i),and_true],
end

lemma filter_le_gt (i : ℕ) (A : ℙ n) :
 A = (filter_le i A) ⊔ (filter_gt i A) := 
begin 
 ext a,
 rw[mem_sup,mem_filter_le,mem_filter_gt,← and_or_distrib_left],
 rw[eq_true_intro (le_or_gt a.val i),and_true],
end

lemma filter_le_ge (i : ℕ) (A : ℙ n) :
 A = (filter_le i A) ⊔ (filter_ge i A) := 
begin 
 ext a,
 rw[mem_sup,mem_filter_le,mem_filter_ge,← and_or_distrib_left],
 have h : a.val ≤ i ∨ a.val ≥ i := begin
  rcases le_or_gt a.val i with h_le | h_gt,
  exact or.inl h_le,
  exact or.inr (le_of_lt h_gt),
 end,
 rw[eq_true_intro h,and_true],
end

lemma filter_lt_zero (A : ℙ n) : A.filter_lt 0 = ⊥ := 
 by { ext a,
      rw[ℙ.mem_filter_lt],
      have : ¬ (a ∈ ⊥) := finset.not_mem_empty a,
      simp only [nat.not_lt_zero,this,iff_self,and_false]}

lemma filter_ge_zero (A : ℙ n) : A.filter_ge 0 = A := 
 by { ext a,
      rw[ℙ.mem_filter_ge],
      have : a.val ≥ 0 := nat.zero_le a.val,
      simp only [this,iff_self,and_true]}

lemma filter_lt_last (A : ℙ n) : A.filter_lt n = A := 
 by { ext a,
      rw[ℙ.mem_filter_lt],
      simp only [a.is_lt,iff_self,and_true]}

lemma filter_ge_last (A : ℙ n) : A.filter_ge n = ⊥ := 
 by { ext a,
      rw[ℙ.mem_filter_ge],
      have h0 : ¬ (a ∈ ⊥) := finset.not_mem_empty a,
      have h1 : ¬ (a.val ≥ n) := not_le_of_gt a.is_lt,
      simp only [h0,h1,iff_self,and_false]}

/-
 For subsets `A,B ⊆ 𝕀 n`, the notation `A ∟ B` means that every 
 element of `A` is less than or equal to every element of `B` 
-/

def angle : (ℙ n) → (ℙ n) → Prop := 
 λ A B, ∀ (i j : 𝕀 n), i ∈ A → j ∈ B → i ≤ j

reserve infix ` ∟ `:50
notation A ∟ B := angle A B

instance : ∀ (A B : ℙ n), decidable (angle A B) := 
 by {dsimp[angle],apply_instance}

lemma bot_angle (B : ℙ n) : ⊥ ∟ B := 
 λ i j i_in_A j_in_B, (finset.not_mem_empty i i_in_A).elim

lemma angle_bot (A : ℙ n) : A ∟ ⊥ := 
 λ i j i_in_A j_in_B, (finset.not_mem_empty j j_in_B).elim

lemma sup_angle (A B C : ℙ n) : A ⊔ B ∟ C ↔ (A ∟ C) ∧ (B ∟ C) := 
begin
 split,
 {rintro hAB,split,
  exact λ i k i_in_A k_in_C,
          hAB i k (finset.subset_union_left A B i_in_A) k_in_C,
  exact λ j k j_in_B k_in_C,
          hAB j k (finset.subset_union_right A B j_in_B) k_in_C,
 },{
  rintros ⟨hA,hB⟩ i k i_in_AB k_in_C,
  rcases finset.mem_union.mp i_in_AB with i_in_A | i_in_B,
  exact hA i k i_in_A k_in_C,
  exact hB i k i_in_B k_in_C,  
 }
end

lemma angle_sup (A B C : ℙ n) : A ∟ B ⊔ C ↔ (A ∟ B) ∧ (A ∟ C) := 
begin
 split,
 {rintro hBC,split,
  exact λ i j i_in_A j_in_B,
          hBC i j i_in_A (finset.subset_union_left  B C j_in_B),
  exact λ i k i_in_A k_in_C,
          hBC i k i_in_A (finset.subset_union_right B C k_in_C),
 },{
  rintros ⟨hB,hC⟩ i j i_in_A j_in_BC,
  rcases finset.mem_union.mp j_in_BC with j_in_B | j_in_C,
  exact hB i j i_in_A j_in_B,
  exact hC i j i_in_A j_in_C,  
 }
end

lemma lt_angle_ge (k : ℕ) (A : ℙ n) : (A.filter_lt k) ∟ (A.filter_ge k) := 
 λ i j i_small j_large,begin 
  let h0 := (ℙ.mem_filter_lt.mp i_small).right,
  let h1 := (ℙ.mem_filter_ge.mp j_large).right,
  let h2 := le_of_lt (lt_of_lt_of_le h0 h1),
  exact h2,
 end

lemma le_angle_gt (k : ℕ) (A : ℙ n) : (A.filter_le k) ∟ (A.filter_gt k) := 
 λ i j i_small j_large,begin 
  let h0 := (ℙ.mem_filter_le.mp i_small).right,
  let h1 := (ℙ.mem_filter_gt.mp j_large).right,
  let h2 := le_of_lt (lt_of_le_of_lt h0 h1),
  exact h2,
 end

lemma le_angle_ge (k : ℕ) (A : ℙ n) : (A.filter_le k) ∟ (A.filter_ge k) := 
 λ i j i_small j_large,begin 
  let h0 := (ℙ.mem_filter_le.mp i_small).right,
  let h1 := (ℙ.mem_filter_ge.mp j_large).right,
  let h2 := le_trans h0 h1,
  exact h2,
 end

lemma filter_lt_angle_of_angle (k : ℕ) (A B : ℙ n) (h : A ∟ B) : 
 (A.filter_lt k) ∟ B := 
  λ i j i_in_A' j_in_B, h i j (mem_filter_lt.mp i_in_A').left j_in_B

lemma filter_le_angle_of_angle (k : ℕ) (A B : ℙ n) (h : A ∟ B) : 
 (A.filter_le k) ∟ B := 
  λ i j i_in_A' j_in_B, h i j (mem_filter_le.mp i_in_A').left j_in_B

lemma angle_filter_gt_of_angle (k : ℕ) (A B : ℙ n) (h : A ∟ B) : 
 A ∟ (B.filter_gt k) := 
  λ i j i_in_A j_in_B', h i j i_in_A (mem_filter_gt.mp j_in_B').left

lemma angle_filter_ge_of_angle (k : ℕ) (A B : ℙ n) (h : A ∟ B) : 
 A ∟ (B.filter_ge k) := 
  λ i j i_in_A j_in_B', h i j i_in_A (mem_filter_ge.mp j_in_B').left

lemma split_angle {A B : ℙ n} (k : 𝕀 n) 
 (hA : ∀ i, i ∈ A → i ≤ k) (hB : ∀ j, j ∈ B → k ≤ j) : A ∟ B := 
  λ i j i_in_A j_in_B, le_trans (hA i i_in_A) (hB j j_in_B)

lemma angle_iff {A B : ℙ n} : 
 A ∟ B ↔ (A = ⊥ ∧ B = ⊥) ∨ 
          ∃ (k : 𝕀 n), (∀ i, (i ∈ A) → i ≤ k) ∧ (∀ i, i ∈ B → k ≤ i) := 
begin
 split,
 {intro h,
  by_cases hA : A = ⊥,
  {by_cases hB : B = ⊥,
   {left, exact ⟨hA,hB⟩},
   {rcases (fin.finset_least_element B hB) with ⟨k,⟨k_in_B,k_least⟩⟩,
    right,use k,split,
    {intros i i_in_A,exact h i k i_in_A k_in_B,},
    {exact k_least,}
   },
  },{
   rcases (fin.finset_largest_element A hA) with ⟨k,⟨k_in_A,k_largest⟩⟩,
   right,use k,split,
   {exact k_largest},
   {intros j j_in_B,exact h k j k_in_A j_in_B,}
  }
 },
 {rintro (⟨A_empty,B_empty⟩ | ⟨k,⟨hA,hB⟩⟩),
  {rw[A_empty],exact bot_angle B},
  {exact split_angle k hA hB,}
 }
end

end ℙ 

/-
 We define `ℚ n` to be the poset of upwards-closed subsets of 
 `ℙ n`, ordered by reverse inclusion.  
-/

variable (n)
def ℚ := poset.upper (ℙ n)

instance : lattice.bounded_distrib_lattice (ℚ n) := 
  @upper.bdl (ℙ n) _ _ _ _

instance ℙ_mem_ℚ : has_mem (ℙ n) (ℚ n) := 
 by { unfold ℚ, apply_instance }

variable {n}

/-
 We make `ℚ n` into a monoid as follows: `U * V` is the set of all
 sets of the form `A ∪ B`, where `A ∈ U` and `B ∈ V` and `A ∟ B`.
 The monoid structure is compatible with the partial order, and this
 allows us to regard `ℚ n` as a monoidal category (in which all
 hom sets have size at most one).  
-/

def mul0 (U V : finset (ℙ n)) : finset (ℙ n) := 
 U.bind (λ A, (V.filter (λ B,A ∟ B)).image (λ B, A ⊔ B))

lemma mem_mul0 (U V : finset (ℙ n)) (C : ℙ n) : 
 (C ∈ (mul0 U V)) ↔ ∃ A B, A ∈ U ∧ B ∈ V ∧ (A ∟ B) ∧ (A ⊔ B = C) := 
begin
 split,
 {intro hC,
  rcases finset.mem_bind.mp hC with ⟨A,⟨A_in_U,C_in_image⟩⟩,
  rcases finset.mem_image.mp C_in_image with ⟨B,⟨B_in_filter,e⟩⟩,
  rcases finset.mem_filter.mp B_in_filter with ⟨B_in_V,A_angle_B⟩,
  use A, use B,
  exact ⟨A_in_U,B_in_V,A_angle_B,e⟩,
 },{
  rintro ⟨A,B,A_in_U,B_in_V,A_angle_B,e⟩,
  apply finset.mem_bind.mpr,use A,use A_in_U,
  apply finset.mem_image.mpr,use B,
  have B_in_filter : B ∈ V.val.filter _ := 
   finset.mem_filter.mpr ⟨B_in_V,A_angle_B⟩,
  use B_in_filter,
  exact e,
 }
end

lemma bot_mul0 (V : finset (ℙ n)) (hV : is_upper V) : mul0 finset.univ V = V := 
begin 
 ext C,
 rw[mem_mul0 finset.univ V C],
 split,
 {rintro ⟨A,B,hA,hB,hAB,hC⟩,
  have B_le_C : B ≤ C := hC ▸ (@lattice.le_sup_right _ _ A B),
  exact hV B C B_le_C hB,
 },{
  intro C_in_V,
  have A_in_U : (⊥ : ℙ n) ∈ finset.univ := @finset.mem_univ (ℙ n) _ ⊥,
  use ⊥,use C,
  exact ⟨A_in_U,C_in_V,C.bot_angle,lattice.bot_sup_eq⟩, 
 }
end

lemma mul0_bot (U : finset (ℙ n)) (hU : is_upper U) : mul0 U finset.univ = U := 
begin
 ext C,
 rw[mem_mul0 U finset.univ C],
 split,
 {rintro ⟨A,B,hA,hB,hAB,hC⟩,
  have A_le_C : A ≤ C := hC ▸ (@lattice.le_sup_left _ _ A B),
  exact hU A C A_le_C hA,
 },{
  intro C_in_U,
  have B_in_V : (⊥ : ℙ n) ∈ (⊥ : ℚ n) := @finset.mem_univ (ℙ n) _ ⊥,
  use C,use ⊥,
  exact ⟨C_in_U,B_in_V,C.angle_bot,lattice.sup_bot_eq⟩, 
 } 
end

lemma is_upper_mul0 (U V : finset (ℙ n)) 
 (hU : is_upper U) (hV : is_upper V) : is_upper (mul0 U V) := 
begin
 intros C C' C_le_C' C_in_mul,
 rcases (mem_mul0 U V C).mp C_in_mul with ⟨A,B,A_in_U,B_in_V,A_angle_B,e⟩,
 apply (mem_mul0 U V C').mpr,
 rcases (ℙ.angle_iff.mp A_angle_B) with ⟨A_empty,B_empty⟩ | ⟨k,⟨hA,hB⟩⟩,
 {use A, use C',
  have B_le_C' : ⊥ ≤ C' := lattice.bot_le,
  rw[← B_empty] at B_le_C',
  have C'_in_V : C' ∈ V := hV B C' B_le_C' B_in_V,
  have A_angle_C' : A ∟ C' := A_empty.symm ▸ C'.bot_angle,
  have e : ⊥ ⊔ C' = C' := lattice.bot_sup_eq,
  rw[← A_empty] at e,
  exact ⟨A_in_U,C'_in_V,A_angle_C',e⟩, 
 },{
  let A' := C'.filter (λ i, i ≤ k),
  let B' := C'.filter (λ j, k ≤ j),
  have A'_angle_B' : A' ∟ B' := λ i j i_in_A' j_in_B', 
   le_trans (finset.mem_filter.mp i_in_A').right (finset.mem_filter.mp j_in_B').right,
  have A_le_C : A ≤ C := e ▸ (@lattice.le_sup_left _ _ A B),
  have B_le_C : B ≤ C := e ▸ (@lattice.le_sup_right _ _ A B),
  have A_le_A' : A ≤ A' := λ i i_in_A, 
   finset.mem_filter.mpr ⟨(le_trans A_le_C C_le_C') i_in_A,hA i i_in_A⟩,
  have B_le_B' : B ≤ B' := λ j j_in_B, 
   finset.mem_filter.mpr ⟨(le_trans B_le_C C_le_C') j_in_B,hB j j_in_B⟩,
  have A'_in_U : A' ∈ U.val := hU A A' A_le_A' A_in_U,
  have B'_in_V : B' ∈ V.val := hV B B' B_le_B' B_in_V,
  have eC' : C' = A' ⊔ B' := begin
   ext i,split,
   {intro i_in_C',
    by_cases h : i ≤ k,
    {exact finset.mem_union_left  B' (finset.mem_filter.mpr ⟨i_in_C',h⟩)},
    {replace h := le_of_lt (lt_of_not_ge h),
     exact finset.mem_union_right A' (finset.mem_filter.mpr ⟨i_in_C',h⟩)
    }
   },{
    intro i_in_union,
    rcases finset.mem_union.mp i_in_union with i_in_A' | i_in_B',
    {exact (finset.mem_filter.mp i_in_A').left,},
    {exact (finset.mem_filter.mp i_in_B').left,}
   }
  end,
  use A', use B',
  exact ⟨A'_in_U,B'_in_V,A'_angle_B',eC'.symm⟩,
 }
end

instance : monoid (ℚ n) := {
  one := ⊥, 
  mul := λ U V, ⟨mul0 U.val V.val,is_upper_mul0 U.val V.val U.property V.property⟩,
  one_mul := λ V, subtype.eq (bot_mul0 V.val V.property),
  mul_one := λ U, subtype.eq (mul0_bot U.val U.property),
  mul_assoc := λ ⟨U,hU⟩ ⟨V,hV⟩ ⟨W,hW⟩, 
  begin 
   apply subtype.eq,
   change mul0 (mul0 U V) W = mul0 U (mul0 V W),
   ext E,split,
   {intro h,
    rcases (mem_mul0 _ W E).mp h with ⟨AB,C,⟨hAB,hC,AB_angle_C,e_AB_C⟩⟩,
    rcases (mem_mul0 U V AB).mp hAB with ⟨A,B,hA,hB,A_angle_B,e_A_B⟩,
    have A_le_AB : A ≤ AB := e_A_B ▸ (finset.subset_union_left  A B),
    have B_le_AB : B ≤ AB := e_A_B ▸ (finset.subset_union_right A B),
    have A_angle_C : A ∟ C := λ i k i_in_A k_in_C, 
     AB_angle_C i k (A_le_AB i_in_A) k_in_C,
    have B_angle_C : B ∟ C := λ j k j_in_B k_in_C, 
     AB_angle_C j k (B_le_AB j_in_B) k_in_C,
    let BC := B ⊔ C,
    have A_angle_BC : A ∟ BC := begin
     rintros i j i_in_A j_in_BC,
     rcases (finset.mem_union.mp j_in_BC) with j_in_B | j_in_C,
     {exact A_angle_B i j i_in_A j_in_B,},
     {exact A_angle_C i j i_in_A j_in_C,}
    end,
    have hBC : BC ∈ mul0 V W := begin 
     apply (mem_mul0 V W BC).mpr,use B, use C,
     exact ⟨hB,hC,B_angle_C,rfl⟩
    end,
    have e_A_BC := calc
     A ⊔ BC = A ⊔ (B ⊔ C) : rfl
     ... = (A ⊔ B) ⊔ C : by rw[lattice.sup_assoc]
     ... = E : by rw[e_A_B,e_AB_C],
    apply (mem_mul0 U (mul0 V W) E).mpr,
    use A,use BC,
    exact ⟨hA,hBC,A_angle_BC,e_A_BC⟩,
   },
   {intro h,
    rcases (mem_mul0 U _ E).mp h with ⟨A,BC,⟨hA,hBC,A_angle_BC,e_A_BC⟩⟩,
    rcases (mem_mul0 V W BC).mp hBC with ⟨B,C,hB,hC,B_angle_C,e_B_C⟩,
    have B_le_BC : B ≤ BC := e_B_C ▸ (finset.subset_union_left  B C),
    have C_le_BC : C ≤ BC := e_B_C ▸ (finset.subset_union_right B C),
    have A_angle_B : A ∟ B := λ i j i_in_A j_in_B, 
     A_angle_BC i j i_in_A (B_le_BC j_in_B),
    have A_angle_C : A ∟ C := λ i k i_in_A k_in_C, 
     A_angle_BC i k i_in_A (C_le_BC k_in_C),
    let AB := A ⊔ B,
    have AB_angle_C : AB ∟ C := begin
     rintros i k i_in_AB k_in_C,
     rcases (finset.mem_union.mp i_in_AB) with i_in_A | i_in_B,
     {exact A_angle_C i k i_in_A k_in_C,},
     {exact B_angle_C i k i_in_B k_in_C,}
    end,
    have hAB : AB ∈ mul0 U V := begin 
     apply (mem_mul0 U V AB).mpr,use A, use B,
     exact ⟨hA,hB,A_angle_B,rfl⟩
    end,
    have e_AB_C := calc
     AB ⊔ C = (A ⊔ B) ⊔ C : rfl
     ... = A ⊔ (B ⊔ C) : by rw[← lattice.sup_assoc]
     ... = E : by rw[e_B_C,e_A_BC],
    apply (mem_mul0 (mul0 U V) W E).mpr,
    use AB,use C,
    exact ⟨hAB,hC,AB_angle_C,e_AB_C⟩,
   }
  end
}

lemma ℚ.mul_le_mul (U₀ V₀ U₁ V₁ : ℚ n) (hU : U₀ ≤ U₁ ) (hV : V₀ ≤ V₁) : 
 U₀ * V₀ ≤ U₁ * V₁ := 
begin
 change (mul0 U₁.val V₁.val) ⊆ (mul0 U₀.val V₀.val),
 intros C C_in_W₁,
 rcases (mem_mul0 _ _ C).mp C_in_W₁ with ⟨A,B,hA,hB,A_angle_B,e_A_B⟩,
 exact (mem_mul0 U₀.val V₀.val C).mpr ⟨A,B,hU hA,hV hB,A_angle_B,e_A_B⟩, 
end

variable (n)

def 𝕄 := { AB : (ℙ n) × (ℙ n) // AB.1 ∟ AB.2 }

namespace 𝕄 

instance : partial_order (𝕄 n) := {
 le := λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩, (A ≤ C) ∧ (B ≤ D),
 le_refl := λ ⟨⟨A,B⟩,hAB⟩, by { split; apply @le_refl (ℙ n) _, },
 le_antisymm := λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩ ⟨hCA,hDB⟩, 
  begin congr,exact le_antisymm hAC hCA,exact le_antisymm hBD hDB end,
 le_trans :=
  λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨⟨E,F⟩,hEF⟩ ⟨hAC,hBD⟩ ⟨hCE,hDF⟩,
   ⟨le_trans hAC hCE,le_trans hBD hDF⟩, 
}

instance : fintype (𝕄 n) := by { unfold 𝕄, apply_instance }

instance : decidable_rel (λ (AB CD : 𝕄 n), AB ≤ CD) := 
 λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩, 
  by { change decidable ((A ≤ C) ∧ (B ≤ D)), apply_instance, }

end 𝕄 

def ζ : poset.hom (ℙ n) (𝕄 n) := 
 ⟨λ B, ⟨⟨⊥,B⟩,B.bot_angle⟩, λ B D hBD, ⟨le_refl ⊥,hBD⟩⟩

def ξ : poset.hom (ℙ n) (𝕄 n) := 
 ⟨λ A, ⟨⟨A,⊥⟩,A.angle_bot⟩, λ A C hAC, ⟨hAC,le_refl ⊥⟩⟩ 

def σ : poset.hom (𝕄 n) (ℙ n) := 
 ⟨λ ⟨⟨A,B⟩,hAB⟩, A ⊔ B,
  λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩, lattice.sup_le_sup hAC hBD⟩ 

def α' : ℕ → 𝕄 n → 𝕄 n := 
 λ i ⟨⟨A,B⟩,hAB⟩, 
  ⟨⟨A.filter_lt i,(A.filter_ge i) ⊔ B⟩,
   begin 
    change (A.filter_lt i) ∟ ((A.filter_ge i) ⊔ B),
    rw[ℙ.angle_sup],split,apply ℙ.lt_angle_ge,
    exact ℙ.filter_lt_angle_of_angle i A B hAB,
   end⟩ 

def β' : ℕ → 𝕄 n → 𝕄 n := 
 λ i ⟨⟨A,B⟩,hAB⟩, 
  ⟨⟨A.filter_le i,(A.filter_ge i) ⊔ B⟩,
   begin 
    change (A.filter_le i) ∟ ((A.filter_ge i) ⊔ B),
    rw[ℙ.angle_sup],split,apply ℙ.le_angle_ge,
    exact ℙ.filter_le_angle_of_angle i A B hAB,
   end⟩ 

def γ' : ℕ → 𝕄 n → 𝕄 n := 
 λ i ⟨⟨A,B⟩,hAB⟩, 
  ⟨⟨A ⊔ B.filter_lt i,B.filter_ge i⟩,
   begin 
    change (A ⊔ (B.filter_lt i)) ∟ (B.filter_ge i),
    rw[ℙ.sup_angle],split,
    exact ℙ.angle_filter_ge_of_angle i A B hAB,
    apply ℙ.lt_angle_ge,
   end⟩ 

def δ' : ℕ → 𝕄 n → 𝕄 n := 
 λ i ⟨⟨A,B⟩,hAB⟩, 
  ⟨⟨A ⊔ B.filter_le i,B.filter_ge i⟩,
   begin 
    change (A ⊔ (B.filter_le i)) ∟ (B.filter_ge i),
    rw[ℙ.sup_angle],split,
    exact ℙ.angle_filter_ge_of_angle i A B hAB,
    apply ℙ.le_angle_ge,
   end⟩ 

lemma α_mono (i : ℕ) : monotone (@α' n i) := 
 λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩, begin 
  split,
  {intros a a_prop,
   rcases finset.mem_filter.mp a_prop with ⟨a_in_A,a_lt_i⟩,
   exact finset.mem_filter.mpr ⟨hAC a_in_A,a_lt_i⟩},
  {intros a a_prop,
   rcases finset.mem_union.mp a_prop with a_in_A_top | a_in_B,
   {rcases finset.mem_filter.mp a_in_A_top with ⟨a_in_A,i_le_a⟩,
    exact finset.mem_union_left D (finset.mem_filter.mpr ⟨hAC a_in_A,i_le_a⟩),
   },{
    exact finset.mem_union_right _ (hBD a_in_B),
   }
  }
 end

lemma β_mono (i : ℕ) : monotone (@β' n i) := 
 λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩, begin 
  split,
  {intros a a_prop,
   rcases finset.mem_filter.mp a_prop with ⟨a_in_A,a_le_i⟩,
   exact finset.mem_filter.mpr ⟨hAC a_in_A,a_le_i⟩},
  {intros a a_prop,
   rcases finset.mem_union.mp a_prop with a_in_A_top | a_in_B,
   {rcases finset.mem_filter.mp a_in_A_top with ⟨a_in_A,i_le_a⟩,
    exact finset.mem_union_left D (finset.mem_filter.mpr ⟨hAC a_in_A,i_le_a⟩),
   },{
    exact finset.mem_union_right _ (hBD a_in_B),
   }
  }
 end

lemma γ_mono (i : ℕ) : monotone (@γ' n i) := 
 λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩, begin 
  split,
  {intros a a_prop,
   rcases finset.mem_union.mp a_prop with a_in_A | a_in_B_bot,
   {exact finset.mem_union_left _ (hAC a_in_A)},
   {rcases finset.mem_filter.mp a_in_B_bot with ⟨a_in_B,a_lt_i⟩,
    exact finset.mem_union_right C (finset.mem_filter.mpr ⟨hBD a_in_B,a_lt_i⟩),
   }
  },
  {intros a a_prop,
   rcases finset.mem_filter.mp a_prop with ⟨a_in_B,i_le_a⟩,
   exact finset.mem_filter.mpr ⟨hBD a_in_B,i_le_a⟩}
 end

lemma δ_mono (i : ℕ) : monotone (@δ' n i) := 
 λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩, begin 
  split,
  {intros a a_prop,
   rcases finset.mem_union.mp a_prop with a_in_A | a_in_B_bot,
   {exact finset.mem_union_left _ (hAC a_in_A)},
   {rcases finset.mem_filter.mp a_in_B_bot with ⟨a_in_B,a_le_i⟩,
    exact finset.mem_union_right C (finset.mem_filter.mpr ⟨hBD a_in_B,a_le_i⟩),
   }
  },
  {intros a a_prop,
   rcases finset.mem_filter.mp a_prop with ⟨a_in_B,i_le_a⟩,
   exact finset.mem_filter.mpr ⟨hBD a_in_B,i_le_a⟩}
 end

def α (i : ℕ) : poset.hom (𝕄 n) (𝕄 n) := ⟨α' n i,α_mono n i⟩
def β (i : ℕ) : poset.hom (𝕄 n) (𝕄 n) := ⟨β' n i,β_mono n i⟩
def γ (i : ℕ) : poset.hom (𝕄 n) (𝕄 n) := ⟨γ' n i,γ_mono n i⟩
def δ (i : ℕ) : poset.hom (𝕄 n) (𝕄 n) := ⟨δ' n i,δ_mono n i⟩

lemma σα (i : ℕ) : poset.comp (σ n) (α n i) = σ n :=
begin
 apply subtype.eq,rw[poset.comp_val],funext AB,
 rcases AB with ⟨⟨A,B⟩,hAB⟩,
 change (A.filter_lt i) ⊔ ((A.filter_ge i) ⊔ B) = A ⊔ B,
 rw[← lattice.sup_assoc,← @ℙ.filter_lt_ge n i A],
end

lemma σβ (i : ℕ) : poset.comp (σ n) (β n i) = σ n :=
begin
 apply subtype.eq,rw[poset.comp_val],funext AB,
 rcases AB with ⟨⟨A,B⟩,hAB⟩,
 change (A.filter_le i) ⊔ ((A.filter_ge i) ⊔ B) = A ⊔ B,
 rw[← lattice.sup_assoc,← @ℙ.filter_le_ge n i A],
end

lemma σγ (i : ℕ) : poset.comp (σ n) (γ n i) = σ n :=
begin
 apply subtype.eq,rw[poset.comp_val],funext AB,
 rcases AB with ⟨⟨A,B⟩,hAB⟩,
 change (A ⊔ (B.filter_lt i)) ⊔ (B.filter_ge i) = A ⊔ B,
 rw[lattice.sup_assoc,← @ℙ.filter_lt_ge n i B],
end

lemma σδ (i : ℕ) : poset.comp (σ n) (δ n i) = σ n :=
begin
 apply subtype.eq,rw[poset.comp_val],funext AB,
 rcases AB with ⟨⟨A,B⟩,hAB⟩,
 change (A ⊔ (B.filter_le i)) ⊔ (B.filter_ge i) = A ⊔ B,
 rw[lattice.sup_assoc,← @ℙ.filter_le_ge n i B],
end

lemma α_zero : (α n 0) = poset.comp (ζ n) (σ n) := 
begin
 apply subtype.eq,
 funext AB,rcases AB with ⟨⟨A,B⟩,hAB⟩,apply subtype.eq,
 change prod.mk (A.filter_lt 0) ((A.filter_ge 0) ⊔ B) = 
        prod.mk ⊥ (A ⊔ B),
 rw[ℙ.filter_lt_zero,ℙ.filter_ge_zero],
end

lemma γ_zero : (γ n 0) = poset.id _ := 
 begin
  apply subtype.eq,
  funext AB,rcases AB with ⟨⟨A,B⟩,hAB⟩,apply subtype.eq,
  change prod.mk (A ⊔ B.filter_lt 0) (B.filter_ge 0) = 
         prod.mk A B,
  rw[ℙ.filter_lt_zero,ℙ.filter_ge_zero],congr,
  exact @lattice.sup_bot_eq _ _ A,
 end

lemma α_last : (α n n) = poset.id _ := 
 begin
  apply subtype.eq,
  funext AB,rcases AB with ⟨⟨A,B⟩,hAB⟩,apply subtype.eq,
  change prod.mk (A.filter_lt n) ((A.filter_ge n) ⊔ B) = 
         prod.mk A B,
  rw[ℙ.filter_lt_last,ℙ.filter_ge_last],congr,
  exact @lattice.bot_sup_eq _ _ B,
 end

lemma γ_last : (γ n n) = poset.comp (ξ n) (σ n) := 
 begin
  apply subtype.eq,
  funext AB,rcases AB with ⟨⟨A,B⟩,hAB⟩,apply subtype.eq,
  change prod.mk (A ⊔ B.filter_lt n) (B.filter_ge n) = 
         prod.mk (A ⊔ B) ⊥,
  rw[ℙ.filter_lt_last,ℙ.filter_ge_last],
 end

lemma αβ_same (i : ℕ) : (α n i) ≤ (β n i) := 
 begin 
  rintro ⟨⟨A,B⟩,hAB⟩,
  change ((A.filter_lt i) ≤ (A.filter_le i)) ∧ 
         ((A.filter_ge i) ⊔ B  ≤ (A.filter_ge i) ⊔ B),
  split,
  {rintros a h,rcases ℙ.mem_filter_lt.mp h with ⟨a_in_A,a_is_lt⟩,
   exact ℙ.mem_filter_le.mpr ⟨a_in_A,le_of_lt a_is_lt⟩, 
  },{
   exact le_refl _, 
  }
 end

lemma αβ_step (i : ℕ) : (α n i.succ) ≤ (β n i) :=
 begin
  rintro ⟨⟨A,B⟩,hAB⟩,
  change ((A.filter_lt i.succ) ≤ (A.filter_le i)) ∧ 
         ((A.filter_ge i.succ) ⊔ B  ≤ (A.filter_ge i) ⊔ B),
  split,
  {rintros a h,rcases ℙ.mem_filter_lt.mp h with ⟨a_in_A,a_is_le⟩,
   replace a_is_le : a.val ≤ i := nat.le_of_lt_succ a_is_le,
   exact ℙ.mem_filter_le.mpr ⟨a_in_A,a_is_le⟩, 
  },{
   have h : A.filter_ge i.succ ≤ A.filter_ge i := 
    λ a h0,begin 
     rcases ℙ.mem_filter_ge.mp h0 with ⟨a_in_A,h1⟩,
     have h2 : a.val ≥ i := le_trans (le_of_lt i.lt_succ_self) h1,
     exact ℙ.mem_filter_ge.mpr ⟨a_in_A,h2⟩,
    end,
   exact lattice.sup_le_sup h (le_refl B),
  }
 end

lemma γδ_same (i : ℕ) : (γ n i) ≤ (δ n i) := 
 begin 
  rintro ⟨⟨A,B⟩,hAB⟩,
  change (A ⊔ (B.filter_lt i) ≤ A ⊔ (B.filter_le i)) ∧ 
          (B.filter_ge i)  ≤ (B.filter_ge i),
  split,
  {have h : B.filter_lt i ≤ B.filter_le i := 
    λ b h0,begin 
     rcases ℙ.mem_filter_lt.mp h0 with ⟨b_in_B,b_is_lt⟩,
      exact ℙ.mem_filter_le.mpr ⟨b_in_B,le_of_lt b_is_lt⟩,
    end,
    exact lattice.sup_le_sup (le_refl A) h,
  },{
   exact le_refl _, 
  }
 end

lemma γδ_step (i : ℕ) : (γ n i.succ) ≤ (δ n i) := 
 begin 
  rintro ⟨⟨A,B⟩,hAB⟩,
  change (A ⊔ (B.filter_lt i.succ) ≤ A ⊔ (B.filter_le i)) ∧ 
          (B.filter_ge i.succ)  ≤ (B.filter_ge i),
  split,
  {have h : B.filter_lt i.succ = B.filter_le i := 
    by {ext a, rw[ℙ.mem_filter_lt,ℙ.mem_filter_le,nat.lt_succ_iff]},
   rw[h],exact le_refl _,
  },{
   rintros b h,rcases (ℙ.mem_filter_ge.mp h) with ⟨b_in_B,b_is_ge⟩ ,
   replace b_is_ge : b.val ≥ i := le_of_lt b_is_ge,
   exact ℙ.mem_filter_ge.mpr ⟨b_in_B,b_is_ge⟩, 
  }
 end

lemma γδ_component : ∀ i,
 (poset.component (γ n i) = poset.idₕ _) ∧ 
 (poset.component (δ n i) = poset.idₕ _) 
| 0 := 
  begin 
   have h0 : poset.component (γ n 0) = poset.idₕ _ := 
    by {rw[γ_zero],refl,},
   let h1 := poset.π₀.sound (γδ_same n 0),
   exact ⟨h0,h1.symm.trans h0⟩,
  end
| (nat.succ i) := 
  begin
   rcases γδ_component i with ⟨h0,h1⟩,
   let h2 := poset.π₀.sound (γδ_step n i),
   let h3 := poset.π₀.sound (γδ_same n i.succ),
   exact ⟨h2.trans h1,h3.symm.trans (h2.trans h1)⟩, 
  end

lemma γ_component (i : ℕ) : (poset.component (γ n i) = poset.idₕ _) := 
 (γδ_component n i).left

lemma δ_component (i : ℕ) : (poset.component (δ n i) = poset.idₕ _) := 
 (γδ_component n i).right

lemma ξσ_component : poset.component (poset.comp (ξ n) (σ n)) = poset.idₕ _ := 
  (congr_arg poset.component (γ_last n)).symm.trans (γ_component n n)

lemma αβ_component : ∀ i,
 (poset.component (α n i) = poset.component (α n 0)) ∧ 
 (poset.component (β n i) = poset.component (α n 0)) 
| 0 := 
  begin 
   let h1 := poset.π₀.sound (αβ_same n 0),
   exact ⟨rfl,h1.symm⟩,
  end
| (nat.succ i) := 
  begin
   rcases αβ_component i with ⟨h0,h1⟩,
   let h2 := poset.π₀.sound (αβ_step n i),
   let h3 := poset.π₀.sound (αβ_same n i.succ),
   exact ⟨h2.trans h1,h3.symm.trans (h2.trans h1)⟩, 
  end

lemma α_component (i : ℕ) : (poset.component (α n i) = poset.idₕ _) := 
 begin
  let h0 := (αβ_component n i).left,
  let h1 := (αβ_component n n).left,
  let h2 := congr_arg poset.component (α_last n),
  exact (h0.trans h1.symm).trans h2,
 end

lemma β_component (i : ℕ) : (poset.component (β n i) = poset.idₕ _) := 
 begin
  let h0 := (αβ_component n i).right,
  let h1 := (αβ_component n n).left,
  let h2 := congr_arg poset.component (α_last n),
  exact (h0.trans h1.symm).trans h2,
 end

lemma ζσ_component : poset.component (poset.comp (ζ n) (σ n)) = poset.idₕ _ := 
  (congr_arg poset.component (α_zero n)).symm.trans (α_component n 0)

def 𝕃 (n : ℕ) := poset.upper (𝕄 n)

namespace 𝕃 

instance : _root_.lattice.bounded_distrib_lattice (𝕃 n) := 
  @upper.bdl (𝕄 n) _ _ _ _

instance 𝕄_mem_𝕃 : has_mem (𝕄 n) (𝕃 n) := 
 by { unfold 𝕃, apply_instance }

end 𝕃 

def omul0 (U V : finset (ℙ n)) : finset (𝕄 n) := 
 (U.bind (λ A, V.image (λ B, prod.mk A B))).subtype (λ AB, AB.1 ∟ AB.2)

lemma mem_omul0 (U V : finset (ℙ n)) (AB : 𝕄 n) : 
 AB ∈ omul0 n U V ↔ AB.val.1 ∈ U ∧ AB.val.2 ∈ V := 
begin
 rw[omul0,finset.mem_subtype],
 split,
 {intro h0,
  rcases (finset.mem_bind.mp h0) with ⟨A,⟨hAU,h1⟩⟩,
  rcases (finset.mem_image.mp h1) with ⟨B,⟨hBV,h2⟩⟩,
  rw[← h2],
  exact ⟨hAU,hBV⟩,
 },
 {rcases AB with ⟨⟨A,B⟩,hAB⟩,
  rintros ⟨hAU,hBV⟩,
  apply finset.mem_bind.mpr,use A,use hAU,
  apply finset.mem_image.mpr,use B,use hBV,
 }
end

lemma is_upper_omul0 {U V : finset (ℙ n)}
 (hU : is_upper U) (hV : is_upper V) : is_upper (omul0 n U V) := 
begin
 rintros ⟨⟨A₀,B₀⟩,hAB₀⟩ ⟨⟨A₁,B₁⟩,hAB₁⟩ ⟨h_le_A,h_le_B⟩ AB₀_in_omul,
 rcases (mem_omul0 n U V _).mp AB₀_in_omul with ⟨A₀_in_U,B₀_in_V⟩,
 apply (mem_omul0 n U V _).mpr,
 simp only [],
 exact ⟨hU A₀ A₁ h_le_A A₀_in_U,hV B₀ B₁ h_le_B B₀_in_V⟩,
end

def omul : (ℚ n) → (ℚ n) → (𝕃 n) := 
 λ U V, ⟨omul0 n U.val V.val,is_upper_omul0 n U.property V.property⟩ 

lemma omul_mono₂ : 
 ∀ {U₀ U₁ V₀ V₁ : ℚ n} (hU : U₀ ≤ U₁) (hV : V₀ ≤ V₁), 
  omul n U₀ V₀ ≤ omul n U₁ V₁
| ⟨U₀,hU₀⟩ ⟨U₁,hU₁⟩ ⟨V₀,hV₀⟩ ⟨V₁,hV₁⟩ hU hV ⟨A,B⟩ h := 
begin
 rcases (mem_omul0 n U₁ V₁ ⟨A,B⟩).mp h with ⟨hAU,hBV⟩,
 apply (mem_omul0 n U₀ V₀ ⟨A,B⟩).mpr,
 exact ⟨hU hAU,hV hBV⟩,
end

def σ0 : 𝕃 n → ℚ n := λ W, ⟨W.val.image (σ n),sorry⟩

def σ' : poset.hom (𝕃 n) (ℚ n) := ⟨σ0 n,sorry⟩ 

lemma factor_σ : 
 ∀ U V : ℚ n, U * V = σ' n (omul n U V) := sorry


end itloc

