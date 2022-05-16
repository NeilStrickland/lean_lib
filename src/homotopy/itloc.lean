/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file formalises part of the paper "Iterated chromatic 
localization" by Nicola Bellumat and Neil Strickland.  We have 
formalised all of the combinatorial content (including the 
results in the combinatorial homotopy theory of finite 
posets).  We have not formalised any of the theory of derivators.
-/

import data.list.basic
import data.fin.basic
import data.fintype.basic
import order.lattice
import algebra.big_operators
import data.fin_extra 
import poset.basic poset.upper

import tactic.squeeze

open poset

namespace itloc

lemma two_pos' : 2 > 0 := dec_trivial

/-- `𝕀 n` is the set {0,1,...,n-1} -/
variable (n : ℕ)

def 𝕀 := fin n

namespace 𝕀 

/-- The type `𝕀 n` is finite, with decidable equality, and there
  is an obvious way of printing a string representation of any
  element.  The lines below use the `apply_instance` tactic to
  deal with these things. 
-/
instance : fintype (𝕀 n)      := by { dsimp [𝕀], apply_instance }
instance : decidable_eq (𝕀 n) := by { dsimp [𝕀], apply_instance }
instance : has_repr (𝕀 n)     := by { dsimp [𝕀], apply_instance }

instance : linear_order (𝕀 n) := (@fin.linear_order n).

end 𝕀 

/--
 `ℙ n` is the poset of subsets of `𝕀 n`, ordered by inclusion

 LaTeX: defn-P
-/

def ℙ := finset (𝕀 n)

namespace ℙ 

/-- The type `ℙ n` is finite, with decidable equality, and 
  an obvious string representation.  Additionally, there 
  is a membership relation between `𝕀 n` and `ℙ n`, for which
  we have a `has_mem` instance.
-/

instance : fintype (ℙ n)             := by { dsimp [  ℙ] , apply_instance }
instance : decidable_eq (ℙ n)        := by { dsimp [  ℙ] , apply_instance }
instance : has_mem (𝕀 n) (ℙ n)       := by { dsimp [𝕀,ℙ], apply_instance }
instance : has_singleton (𝕀 n) (ℙ n) := by { dsimp [𝕀,ℙ], apply_instance }
instance : has_repr (ℙ n)            := by { dsimp [  ℙ] , apply_instance }

/-- The `apply_instance` tactic also knows enough to give
  `ℙ n` a structure as a distributive lattice.  However, 
  the library does not contain any general rule showing that
  `ℙ n` has a top and bottom element, so we prove that 
  explicitly.
-/

instance dl : distrib_lattice (ℙ n) := 
by { dsimp [ℙ], apply_instance }

instance bo : bounded_order (ℙ n) := {
  bot := finset.empty,
  top := finset.univ,
  le_top := λ (A : finset (𝕀 n)),
   begin change A ⊆ finset.univ,intros i _,exact finset.mem_univ i end,
  bot_le := λ (A : finset (𝕀 n)),
   begin change finset.empty ⊆ A,intros i h,
    exact (finset.not_mem_empty i h).elim end,
  .. (ℙ.dl n)
}

/-- From the lattice structure we can obtain a partial order.
  It is not normally necessary to mention that fact explicitly,
  but we do so here to avoid some subtle technical issues later.
-/

instance po : partial_order (ℙ n) := by apply_instance

/-- The only element of `ℙ 0` is the empty set. -/
lemma mem_zero (A : ℙ 0) : A = ⊥ := 
by {ext a, exact fin.elim0 a}

/-- The order relation on `ℙ n` is decidable -/
instance decidable_le : decidable_rel (λ (A B : ℙ n), A ≤ B) := 
 λ (A B : finset (𝕀 n)), by { change decidable (A ⊆ B), apply_instance, }

variable {n} 

/-- The bottom element is the empty set, so nothing is a member. -/
lemma not_mem_bot (i : 𝕀 n) : ¬ (i ∈ (⊥ : ℙ n)) := finset.not_mem_empty i

/-- The top element is the full set `ℙ n`, so everything is a member. -/
lemma mem_top     (i : 𝕀 n) :   (i ∈ (⊤ : ℙ n)) := finset.mem_univ i

/-- The membership rule for a union (= sup in the lattice) -/
lemma mem_sup {A B : ℙ n} {i : 𝕀 n} : 
 i ∈ A ⊔ B ↔ (i ∈ A) ∨ (i ∈ B) := finset.mem_union

/-- The membership rule for an intersection (= inf in the lattice) -/
lemma mem_inf {A B : ℙ n} {i : 𝕀 n} : 
 i ∈ A ⊓ B ↔ (i ∈ A) ∧ (i ∈ B) := finset.mem_inter

/-- `A.filter_lt i` is Lean notation for `{a ∈ A : a < i}` -/
def filter_lt (i : ℕ) (A : ℙ n) := A.filter (λ a, a.val < i)

/-- `A.filter_ge i` is Lean notation for `{a ∈ A : a ≥ i}` -/
def filter_ge (i : ℕ) (A : ℙ n) := A.filter (λ a, a.val ≥ i)

/-- Membership rule for these sets. -/
lemma mem_filter_lt {i : ℕ} {A : ℙ n} {a : 𝕀 n} : 
 a ∈ (A.filter_lt i) ↔ a ∈ A ∧ a.val < i := finset.mem_filter 

lemma mem_filter_ge {i : ℕ} {A : ℙ n} {a : 𝕀 n} : 
 a ∈ (A.filter_ge i) ↔ a ∈ A ∧ a.val ≥ i := finset.mem_filter 

lemma filter_lt_is_le (i : ℕ) (A : ℙ n) : 
  A.filter_lt i ≤ A := λ a ha, (mem_filter_lt.mp ha).left

lemma filter_ge_is_le (i : ℕ) (A : ℙ n) : 
  A.filter_ge i ≤ A := λ a ha, (mem_filter_ge.mp ha).left

lemma filter_sup {i j : ℕ} (h : i ≥ j) (A : ℙ n) : 
  A.filter_lt i ⊔ A.filter_ge j = A := 
begin
  ext a,
  rw [mem_sup, mem_filter_lt, mem_filter_ge, ← and_or_distrib_left],
  have : a.val < i ∨ a.val ≥ j := 
  begin
    rcases lt_or_ge a.val i with h_lt | h_ge,
    exact or.inl h_lt, exact or.inr (le_trans h h_ge) 
  end,
  rw [eq_true_intro this, and_true],
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

lemma filter_lt_last {i : ℕ} (hi : i ≥ n) (A : ℙ n) : 
 A.filter_lt i = A := 
begin
  ext a,
  rw[ℙ.mem_filter_lt],
  simp only [lt_of_lt_of_le a.is_lt hi, and_true, fin.val_eq_coe]
end

lemma filter_ge_last {i : ℕ} (hi : i ≥ n) (A : ℙ n) : 
 A.filter_ge i = ⊥ := 
begin
  ext a,
  rw[ℙ.mem_filter_ge],
  have h₀ : ¬ (a ∈ ⊥) := finset.not_mem_empty a,
  have h₁ : ¬ (a.val ≥ i) := 
    not_le_of_gt (lt_of_lt_of_le a.is_lt hi),
  simp only [h₀, h₁, iff_self, and_false]
end

/-
 For subsets `A,B ⊆ 𝕀 n`, the notation `A ∟ B` means that every 
 element of `A` is less than or equal to every element of `B` 

 LaTeX: defn-P
-/

def angle : (ℙ n) → (ℙ n) → Prop := 
 λ A B, ∀ {{i j : 𝕀 n}}, i ∈ A → j ∈ B → i ≤ j

reserve infix ` ∟ `:50
notation A ∟ B := angle A B

/-- The angle relation is decidable -/
instance : ∀ (A B : ℙ n), decidable (angle A B) := 
by { dsimp [angle], apply_instance }

lemma bot_angle (B : ℙ n) : ⊥ ∟ B := 
λ i j i_in_A j_in_B, (finset.not_mem_empty i i_in_A).elim

lemma angle_bot (A : ℙ n) : A ∟ ⊥ := 
λ i j i_in_A j_in_B, (finset.not_mem_empty j j_in_B).elim

lemma sup_angle (A B C : ℙ n) : A ⊔ B ∟ C ↔ (A ∟ C) ∧ (B ∟ C) := 
begin
  split,
  { rintro hAB, split,
    exact λ i k i_in_A k_in_C,
          hAB (finset.subset_union_left A B i_in_A) k_in_C,
    exact λ j k j_in_B k_in_C,
          hAB (finset.subset_union_right A B j_in_B) k_in_C },
  { rintro ⟨hA,hB⟩ i k i_in_AB k_in_C,
    rcases finset.mem_union.mp i_in_AB with i_in_A | i_in_B,
    exact hA i_in_A k_in_C,
    exact hB i_in_B k_in_C }
end

lemma angle_sup (A B C : ℙ n) : A ∟ B ⊔ C ↔ (A ∟ B) ∧ (A ∟ C) := 
begin
  split,
  { rintro hBC, split,
    exact λ i j i_in_A j_in_B,
          hBC i_in_A (finset.subset_union_left  B C j_in_B),
    exact λ i k i_in_A k_in_C,
          hBC i_in_A (finset.subset_union_right B C k_in_C) },
  { rintro ⟨hB,hC⟩ i j i_in_A j_in_BC,
    rcases finset.mem_union.mp j_in_BC with j_in_B | j_in_C,
    exact hB i_in_A j_in_B,
    exact hC i_in_A j_in_C }
end

lemma filter_angle {i j : ℕ} (h : i ≤ j + 1) (A : ℙ n) : 
  (A.filter_lt i) ∟ (A.filter_ge j) := 
begin
  intros a b ha hb,
  replace ha : a.val + 1 ≤ i := (mem_filter_lt.mp ha).right,
  replace hb := nat.succ_le_succ (mem_filter_ge.mp hb).right, 
  exact nat.le_of_succ_le_succ (le_trans (le_trans ha h) hb)
end

lemma angle_mono {A₀ A₁ B₀ B₁ : ℙ n} 
  (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) (h : A₁ ∟ B₁) : A₀ ∟ B₀ := 
λ x y hx hy, h (hA hx) (hB hy)

lemma split_angle {A B : ℙ n} (k : 𝕀 n) 
 (hA : ∀ i, i ∈ A → i ≤ k) (hB : ∀ j, j ∈ B → k ≤ j) : A ∟ B := 
  λ i j i_in_A j_in_B, le_trans (hA i i_in_A) (hB j j_in_B)

lemma angle_iff {A B : ℙ n} : 
 A ∟ B ↔ n = 0 ∨ 
          ∃ (k : 𝕀 n), (∀ {i}, (i ∈ A) → i ≤ k) ∧ (∀ {i}, i ∈ B → k ≤ i) := 
begin
 cases n with n,
 { rw[A.mem_zero, B.mem_zero], simp only [bot_angle], simp },
 split,
 { intro h_angle, right,
   let z : 𝕀 n.succ := ⟨0,nat.zero_lt_succ n⟩,
   let A0 : finset (𝕀 n.succ) := insert z A,
   rcases fin.finset_largest_element A0 
    ⟨_,finset.mem_insert_self z A⟩
      with ⟨k, k_in_A0, k_largest⟩,
   use k,
   split,
   { intros a a_in_A, 
     exact k_largest a (finset.mem_insert_of_mem a_in_A) },
   { intros b b_in_B,
     rcases (finset.mem_insert.mp k_in_A0) with k_eq_z | k_in_A,
     { rw [k_eq_z], exact nat.zero_le b.val },
     { exact h_angle k_in_A b_in_B } } },
 { rintro (⟨⟨⟩⟩ | ⟨k,hA,hB⟩) a b a_in_A b_in_B,
   exact le_trans (hA a_in_A) (hB b_in_B) }
end

lemma not_angle_iff {A B : ℙ n} : 
 ¬ (A ∟ B) ↔ (∃ (a ∈ A) (b ∈ B), a > b) := 
begin
  dsimp[angle],
  rw [not_forall],
  apply exists_congr, intro a,
  rw [not_forall],
  split; intro h,
  { rcases h with ⟨b,hb⟩,
    rw[not_imp, not_imp, ← lt_iff_not_ge] at hb,
    exact ⟨hb.1,b,hb.2.1,hb.2.2⟩ },
  { rcases h with ⟨ha,b,hb,h_lt⟩,
    change b < a at h_lt,
    use b,
    simp [ha, hb, h_lt] }
end

lemma angle_iff' {A B : ℙ n} : 
 A ∟ B ↔ (A = ⊥ ∧ B = ⊥) ∨ 
          ∃ (k : 𝕀 n), (∀ i, (i ∈ A) → i ≤ k) ∧ (∀ i, i ∈ B → k ≤ i) := 
begin
 split,
 {intro h,
  by_cases hA : A.nonempty,
  {
   rcases (fin.finset_largest_element A hA) with ⟨k,⟨k_in_A,k_largest⟩⟩,
   right,use k,split,
   {exact k_largest},
   {intros j j_in_B,exact h k_in_A j_in_B,}
  },{
   by_cases hB : B.nonempty,
   {rcases (fin.finset_least_element B hB) with ⟨k,⟨k_in_B,k_least⟩⟩,
    right,use k,split,
    {intros i i_in_A,exact h i_in_A k_in_B,},
    {exact k_least,}
   },
   {left, split,
    exact finset.not_nonempty_iff_eq_empty.mp hA,
    exact finset.not_nonempty_iff_eq_empty.mp hB}
  },
 },
 {rintro (⟨A_empty,B_empty⟩ | ⟨k,⟨hA,hB⟩⟩),
  {rw[A_empty],exact bot_angle B},
  {exact split_angle k hA hB,}
 }
end

end ℙ 

/-
 We define `𝕂 n` to be the poset of upwards-closed subsets of 
 `ℙ n`, ordered by reverse inclusion.  

 LaTeX: defn-Q
-/

variable (n)
def 𝕂 := poset.upper (ℙ n)

namespace 𝕂 

instance : distrib_lattice (𝕂 n) := 
@upper.dl (ℙ n) _ _ _ _

instance : bounded_order (𝕂 n) := 
@upper.bo (ℙ n) _ _ _ _

instance : partial_order (𝕂 n) := by apply_instance 

instance : fintype  (𝕂 n) := upper.fintype (ℙ n)
instance : has_repr (𝕂 n) := upper.has_repr (ℙ n)

instance ℙ_mem_𝕂 : has_mem (ℙ n) (𝕂 n) := 
by { unfold 𝕂, apply_instance }

instance decidable_mem (A : ℙ n) (U : 𝕂 n) : decidable (A ∈ U) := 
by { change decidable (A ∈ U.val), apply_instance }

variable {n}

/-- LaTeX: defn-Q -/
def u : poset.hom (ℙ n) (𝕂 n) := upper.u

lemma mem_u {T : ℙ n} {A : ℙ n} : A ∈ @u n T ↔ T ≤ A := 
begin
  change A ∈ finset.filter _ _ ↔ T ≤ A,
  simp [finset.mem_filter, finset.mem_univ]
end

/-- LaTeX: defn-Q -/
def v (T : ℙ n) : (𝕂 n) := 
⟨ finset.univ.filter (λ A, ∃ i, i ∈ A ∧ i ∈ T), 
  begin 
    rintro A B A_le_B h,
    rw [finset.mem_filter] at *,
    rcases h with ⟨A_in_univ,i,i_in_A,i_in_T⟩,
    exact ⟨finset.mem_univ B,⟨i,⟨A_le_B i_in_A,i_in_T⟩⟩⟩
  end ⟩ 

lemma mem_v {T : ℙ n} {A : ℙ n} : A ∈ v T ↔ ∃ i, i ∈ A ∧ i ∈ T := 
begin
  change (A ∈ finset.filter _ _) ↔ _,
  rw [finset.mem_filter],
  simp [finset.mem_univ A]
end

lemma v_mono {T₀ T₁ : ℙ n} (h : T₀ ≤ T₁) : v T₀ ≥ v T₁ := 
begin
  intros A h₀,
  rcases finset.mem_filter.mp h₀ with ⟨A_in_univ,⟨i,i_in_A,i_in_T₀⟩⟩,
  exact finset.mem_filter.mpr ⟨A_in_univ,⟨i,i_in_A,h i_in_T₀⟩⟩
end

/-
 We make `𝕂 n` into a monoid as follows: `U * V` is the set of all
 sets of the form `A ∪ B`, where `A ∈ U` and `B ∈ V` and `A ∟ B`.
 The monoid structure is compatible with the partial order, and this
 allows us to regard `𝕂 n` as a monoidal category (in which all
 hom sets have size at most one).  

 LaTeX: lem-mu
-/

def mul0 (U V : finset (ℙ n)) : finset (ℙ n) := 
 U.bUnion (λ A, (V.filter (λ B,A ∟ B)).image (λ B, A ⊔ B))

lemma mem_mul0 (U V : finset (ℙ n)) (C : ℙ n) : 
 (C ∈ (mul0 U V)) ↔ ∃ A B, A ∈ U ∧ B ∈ V ∧ (A ∟ B) ∧ (A ⊔ B = C) := 
begin
 split,
 {intro hC,
  rcases finset.mem_bUnion.mp hC with ⟨A,⟨A_in_U,C_in_image⟩⟩,
  rcases finset.mem_image.mp C_in_image with ⟨B,⟨B_in_filter,e⟩⟩,
  rcases finset.mem_filter.mp B_in_filter with ⟨B_in_V,A_angle_B⟩,
  use A, use B,
  exact ⟨A_in_U,B_in_V,A_angle_B,e⟩,
 },{
  rintro ⟨A,B,A_in_U,B_in_V,A_angle_B,e⟩,
  apply finset.mem_bUnion.mpr,use A,use A_in_U,
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
  exact ⟨A_in_U,C_in_V,C.bot_angle,bot_sup_eq⟩, 
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
  have B_in_V : (⊥ : ℙ n) ∈ (⊥ : 𝕂 n) := @finset.mem_univ (ℙ n) _ ⊥,
  use C,use ⊥,
  exact ⟨C_in_U,B_in_V,C.angle_bot,sup_bot_eq⟩, 
 } 
end

lemma is_upper_mul0 (U V : finset (ℙ n)) 
 (hU : is_upper U) (hV : is_upper V) : is_upper (mul0 U V) := 
begin
 intros C C' C_le_C' C_in_mul,
 rcases (mem_mul0 U V C).mp C_in_mul with ⟨A,B,A_in_U,B_in_V,A_angle_B,e⟩,
 apply (mem_mul0 U V C').mpr,
 rcases (ℙ.angle_iff.mp A_angle_B) with ⟨⟨⟩⟩ | ⟨k,⟨hA,hB⟩⟩,
 { rw[C.mem_zero] at *, rw[C'.mem_zero] at *,
   use A, use B,
   exact ⟨A_in_U, B_in_V, A_angle_B, e⟩ },
 { let A' := C'.filter (λ i, i ≤ k),
   let B' := C'.filter (λ j, k ≤ j),
   have A'_angle_B' : A' ∟ B' := λ i j i_in_A' j_in_B', 
    le_trans (finset.mem_filter.mp i_in_A').right (finset.mem_filter.mp j_in_B').right,
   have A_le_C : A ≤ C := e ▸ (@lattice.le_sup_left _ _ A B),
   have B_le_C : B ≤ C := e ▸ (@lattice.le_sup_right _ _ A B),
   have A_le_A' : A ≤ A' := λ i i_in_A, 
    finset.mem_filter.mpr ⟨(le_trans A_le_C C_le_C') i_in_A,hA i_in_A⟩,
   have B_le_B' : B ≤ B' := λ j j_in_B, 
    finset.mem_filter.mpr ⟨(le_trans B_le_C C_le_C') j_in_B,hB j_in_B⟩,
   have A'_in_U : A' ∈ U.val := hU A A' A_le_A' A_in_U,
   have B'_in_V : B' ∈ V.val := hV B B' B_le_B' B_in_V,
   have eC' : C' = A' ⊔ B' := 
   begin
    ext i,split,
    { intro i_in_C',
      by_cases h : i ≤ k,
      { exact finset.mem_union_left  B' (finset.mem_filter.mpr ⟨i_in_C',h⟩)},
      { replace h := le_of_lt (lt_of_not_ge h),
        exact finset.mem_union_right A' (finset.mem_filter.mpr ⟨i_in_C',h⟩) } },
    { intro i_in_union,
      rcases finset.mem_union.mp i_in_union with i_in_A' | i_in_B',
      { exact (finset.mem_filter.mp i_in_A').left },
      { exact (finset.mem_filter.mp i_in_B').left } }
  end,
  use A', use B',
  exact ⟨A'_in_U,B'_in_V,A'_angle_B',eC'.symm⟩,
 }
end

variable (n) 

instance : monoid (𝕂 n) := {
  one := ⊥, 
  mul := λ U V, ⟨mul0 U.val V.val,is_upper_mul0 U.val V.val U.property V.property⟩,
  one_mul := λ V, subtype.eq (bot_mul0 V.val V.property),
  mul_one := λ U, subtype.eq (mul0_bot U.val U.property),
  mul_assoc := λ ⟨U,hU⟩ ⟨V,hV⟩ ⟨W,hW⟩, 
  begin -- Proof of associativity
   apply subtype.eq,
   change mul0 (mul0 U V) W = mul0 U (mul0 V W),
   ext E,split,
   {intro h,
    rcases (mem_mul0 _ W E).mp h with ⟨AB,C,⟨hAB,hC,AB_angle_C,e_AB_C⟩⟩,
    rcases (mem_mul0 U V AB).mp hAB with ⟨A,B,hA,hB,A_angle_B,e_A_B⟩,
    have A_le_AB : A ≤ AB := e_A_B ▸ (finset.subset_union_left  A B),
    have B_le_AB : B ≤ AB := e_A_B ▸ (finset.subset_union_right A B),
    have A_angle_C : A ∟ C := λ i k i_in_A k_in_C, 
     AB_angle_C (A_le_AB i_in_A) k_in_C,
    have B_angle_C : B ∟ C := λ j k j_in_B k_in_C, 
     AB_angle_C (B_le_AB j_in_B) k_in_C,
    let BC := B ⊔ C,
    have A_angle_BC : A ∟ BC := begin
     rintros i j i_in_A j_in_BC,
     rcases (finset.mem_union.mp j_in_BC) with j_in_B | j_in_C,
     {exact A_angle_B i_in_A j_in_B,},
     {exact A_angle_C i_in_A j_in_C,}
    end,
    have hBC : BC ∈ mul0 V W := begin 
     apply (mem_mul0 V W BC).mpr,use B, use C,
     exact ⟨hB,hC,B_angle_C,rfl⟩
    end,
    have e_A_BC := calc
     A ⊔ BC = A ⊔ (B ⊔ C) : rfl
     ... = (A ⊔ B) ⊔ C : by rw[sup_assoc]
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
     A_angle_BC i_in_A (B_le_BC j_in_B),
    have A_angle_C : A ∟ C := λ i k i_in_A k_in_C, 
     A_angle_BC i_in_A (C_le_BC k_in_C),
    let AB := A ⊔ B,
    have AB_angle_C : AB ∟ C := begin
     rintros i k i_in_AB k_in_C,
     rcases (finset.mem_union.mp i_in_AB) with i_in_A | i_in_B,
     {exact A_angle_C i_in_A k_in_C,},
     {exact B_angle_C i_in_B k_in_C,}
    end,
    have hAB : AB ∈ mul0 U V := begin 
     apply (mem_mul0 U V AB).mpr,use A, use B,
     exact ⟨hA,hB,A_angle_B,rfl⟩
    end,
    have e_AB_C := calc
     AB ⊔ C = (A ⊔ B) ⊔ C : rfl
     ... = A ⊔ (B ⊔ C) : by rw[← sup_assoc]
     ... = E : by rw[e_B_C,e_A_BC],
    apply (mem_mul0 (mul0 U V) W E).mpr,
    use AB,use C,
    exact ⟨hAB,hC,AB_angle_C,e_AB_C⟩,
   }
  end
}

variable {n} 

/-- Membership rule for `U * V` -/
lemma mem_mul (U V : 𝕂 n) (C : ℙ n) : C ∈ U * V ↔  
  ∃ A B, A ∈ U ∧ B ∈ V ∧ (A ∟ B) ∧ (A ⊔ B = C) := mem_mul0 U.val V.val C 

/-- Multiplication is monotone in both variables. -/
lemma mul_le_mul (U₀ V₀ U₁ V₁ : 𝕂 n) (hU : U₀ ≤ U₁ ) (hV : V₀ ≤ V₁) : 
 U₀ * V₀ ≤ U₁ * V₁ := 
begin
 change (mul0 U₁.val V₁.val) ⊆ (mul0 U₀.val V₀.val),
 intros C C_in_W₁,
 rcases (mem_mul0 _ _ C).mp C_in_W₁ with ⟨A,B,hA,hB,A_angle_B,e_A_B⟩,
 exact (mem_mul0 U₀.val V₀.val C).mpr ⟨A,B,hU hA,hV hB,A_angle_B,e_A_B⟩, 
end

/-- Multiplication distributes over union (on both sides).
  Recall that we order 𝕂 n by reverse inclusion, so the union
  is the lattice inf operation, and is written as U ⊓ V.

  LaTeX: lem-mu
-/

lemma mul_inf (U V W : 𝕂 n) : U * (V ⊓ W) = (U * V) ⊓ (U * W) := 
begin
  ext C,
  rw [upper.mem_inf, mem_mul U (V ⊓ W)],
  split, 
  { rintro ⟨A,B,hAU,hBVW,h_angle,h_ABC⟩, 
    rw [upper.mem_inf] at hBVW,
    rcases hBVW with hBV | hBW,
    { left , exact (mem_mul U V C).mpr ⟨A,B,hAU,hBV,h_angle,h_ABC⟩ },
    { right, exact (mem_mul U W C).mpr ⟨A,B,hAU,hBW,h_angle,h_ABC⟩ } },
  { rintro (hCUV | hCUW),
    { rcases (mem_mul U V C).mp hCUV with ⟨A,B,hAU,hBV,h_angle,h_ABC⟩,
      have hBVW : B ∈ V ⊓ W := (upper.mem_inf B).mpr (or.inl hBV),
      exact ⟨A,B,hAU,hBVW,h_angle,h_ABC⟩ },
    { rcases (mem_mul U W C).mp hCUW with ⟨A,B,hAU,hBW,h_angle,h_ABC⟩,
      have hBVW : B ∈ V ⊓ W := (upper.mem_inf B).mpr (or.inr hBW),
      exact ⟨A,B,hAU,hBVW,h_angle,h_ABC⟩ } }
end

lemma inf_mul (U V W : 𝕂 n) : (U ⊓ V) * W = (U * W) ⊓ (V * W) := 
begin
  ext C,
  rw [upper.mem_inf, mem_mul (U ⊓ V) W],
  split, 
  { rintro ⟨A,B,hAUV,hBW,h_angle,h_ABC⟩, 
    rw [upper.mem_inf] at hAUV,
    rcases hAUV with hAU | hAV,
    { left , exact (mem_mul U W C).mpr ⟨A,B,hAU,hBW,h_angle,h_ABC⟩ },
    { right, exact (mem_mul V W C).mpr ⟨A,B,hAV,hBW,h_angle,h_ABC⟩ } },
  { rintro (hCUW | hCVW),
    { rcases (mem_mul U W C).mp hCUW with ⟨A,B,hAU,hBW,h_angle,h_ABC⟩,
      have hAUV : A ∈ U ⊓ V := (upper.mem_inf A).mpr (or.inl hAU),
      exact ⟨A,B,hAUV,hBW,h_angle,h_ABC⟩ },
    { rcases (mem_mul V W C).mp hCVW with ⟨A,B,hAV,hBW,h_angle,h_ABC⟩,
      have hAUV : A ∈ U ⊓ V := (upper.mem_inf A).mpr (or.inr hAV),
      exact ⟨A,B,hAUV,hBW,h_angle,h_ABC⟩ } }
end

/-- LaTeX: rem-kp -/

def κ (U : 𝕂 n) : ℙ n := 
  finset.univ.filter (λ i, {i} ∈ U)

lemma κ_mul (U V : 𝕂 n) : κ (U * V) = (κ U) ⊓ (κ V) := 
begin
  ext i,
  let ii : (ℙ n) := {i},
  have ii_angle : ii ∟ ii := λ j k hj hk, 
    by { rw[finset.mem_singleton.mp hj, finset.mem_singleton.mp hk] },
  have ii_union : ii ⊔ ii = ii := sup_idem,
  have : ii ∈ U * V ↔ ii ∈ U ∧ ii ∈ V := 
  begin
    rw[𝕂.mem_mul],
    split,
    { rintro ⟨A,B,A_in_U,B_in_V,h_angle,h_union⟩,
      have hA : A ≤ ii := by { rw[← h_union], exact le_sup_left },
      have hB : B ≤ ii := by { rw[← h_union], exact le_sup_right },
      have hU : ii ∈ U := U.property A ii hA A_in_U,
      have hV : ii ∈ V := V.property B ii hB B_in_V,
      exact ⟨hU,hV⟩ },
    { rintro ⟨hU,hV⟩, 
      use ii, use ii,
      exact ⟨hU,hV,ii_angle,ii_union⟩ }
  end,
  rw [ℙ.mem_inf],
  repeat {rw [κ, finset.mem_filter]},
  simp [this]
end

/-- LaTeX: defn-thread -/
def threads : list (ℙ n) → finset (list (𝕀 n)) 
| list.nil := {list.nil}
| (list.cons A AA) := 
    A.bUnion (λ a, ((threads AA).filter (λ B, ∀ b ∈ B, a ≤ b)).image (list.cons a))

def thread_sets (AA : list (ℙ n)) : 𝕂 n := 
⟨ finset.univ.filter (λ T, ∃ u ∈ threads AA, (∀ a ∈ u, a ∈ T)),
  begin
    intros T₀ T₁ h_le h_mem,
    rcases finset.mem_filter.mp h_mem with ⟨_,⟨u,h_thread,u_in_T₀⟩⟩,
    apply finset.mem_filter.mpr,
    exact ⟨finset.mem_univ T₁,u, h_thread,λ a ha, h_le (u_in_T₀ a ha)⟩
  end ⟩ 

lemma mem_thread_sets {AA : list (ℙ n)} {T : ℙ n} : 
  T ∈ thread_sets AA ↔ ∃ u ∈ threads AA, (∀ a ∈ u, a ∈ T) := 
begin
  change T ∈ (finset.univ.filter _) ↔ _,
  rw [finset.mem_filter],
  simp [finset.mem_univ T]
end

/-- LaTeX: prop-thread -/
lemma v_mul (AA : list (ℙ n)) : (AA.map v).prod = thread_sets AA := 
begin
  induction AA with A AA ih,
  { change ⊥ = _,
    ext A,
    have : A ∈ (⊥ : 𝕂 n) := upper.mem_bot A, simp[this],
    apply finset.mem_filter.mpr ⟨finset.mem_univ A,_⟩,
    use list.nil,
    use finset.mem_singleton_self list.nil,
    intros a a_in_nil,
    exact false.elim (list.not_mem_nil a a_in_nil) },
  { rw [list.map_cons, list.prod_cons],
    ext T,
    rw [ih, 𝕂.mem_mul (v A) _],
    split; intro h,
    { rcases h with ⟨R,S,hR,hS,h_angle,h_union⟩, 
      rcases mem_thread_sets.mp hS with ⟨u,u_in_threads,u_in_S⟩,
      rcases mem_v.mp hR with ⟨i,i_in_R,i_in_A⟩,
      apply (@mem_thread_sets n (A :: AA) T).mpr,
      use (i :: u),
      have : (list.cons i u) ∈ threads (A :: AA) := 
      begin
        rw [threads, finset.mem_bUnion],
        use i, use i_in_A,
        rw [finset.mem_image],
        use u,
        have : u ∈ finset.filter (λ (v : list (𝕀 n)), ∀ (b : 𝕀 n), b ∈ v → i ≤ b) (threads AA) := 
        begin
          rw [finset.mem_filter],
          split, {exact u_in_threads},
          intros a a_in_u,
          exact h_angle i_in_R (u_in_S a a_in_u),
        end,
        use this,
      end,
      use this,
      rintro a (a_eq_i | a_in_u); rw [← h_union],
      { rw[a_eq_i],
        exact finset.mem_union_left S i_in_R },
      { exact finset.mem_union_right R (u_in_S a a_in_u), } },
    {
      rcases (@mem_thread_sets n (A :: AA) T).mp h with ⟨w,w_in_threads,w_in_T⟩,
      rw [threads, finset.mem_bUnion] at w_in_threads,
      rcases w_in_threads with ⟨a,a_in_A,w_in_image⟩,
      rcases finset.mem_image.mp w_in_image with ⟨u,⟨u_in_filter,au_eq_w⟩⟩,
      rcases finset.mem_filter.mp u_in_filter with ⟨u_in_threads, u_ge_a⟩,
      use T.filter_lt a.val.succ,
      use T.filter_ge a.val,
      have a_in_w : a ∈ w := 
        by { rw[← au_eq_w], exact list.mem_cons_self a u },
      have a_in_T : a ∈ T := w_in_T a a_in_w,
      have u_in_T1 : ∀ (i : 𝕀 n) (i_in_u : i ∈ u), i ∈ (T.filter_ge a.val) := λ i i_in_u,
      begin
        apply ℙ.mem_filter_ge.mpr,
        have : i ∈ (list.cons a u) := list.mem_cons_of_mem a i_in_u,
        rw [au_eq_w] at this,
        exact ⟨w_in_T i this, u_ge_a i i_in_u⟩,
      end,
      split,
      { exact mem_v.mpr ⟨a,⟨ℙ.mem_filter_lt.mpr ⟨a_in_T,a.val.lt_succ_self⟩,a_in_A⟩⟩ },
      split, 
      { rw [mem_thread_sets],
        use u, use u_in_threads, exact u_in_T1 },
      split, 
      { exact ℙ.filter_angle (le_refl _) T },
      { exact ℙ.filter_sup (le_of_lt a.val.lt_succ_self) T } } }
end

end 𝕂 

def is_universal {α : Type*} [fintype α] [decidable_eq α] (l : list α) := 
  l.nodup ∧ l.to_finset = finset.univ

instance {α : Type*} [fintype α] [decidable_eq α] (l : list α) : 
  decidable (is_universal l) := 
by { dsimp[is_universal], apply_instance }

/- LaTeX: eg-fracture-obj -/
namespace example_two

def i₀ : 𝕀 2 := ⟨0,dec_trivial⟩ 
def i₁ : 𝕀 2 := ⟨1,dec_trivial⟩ 

lemma 𝕀_univ : is_universal [i₀, i₁] := dec_trivial

def p   : ℙ 2 := ⊥ 
def p₀  : ℙ 2 := [i₀].to_finset 
def p₁  : ℙ 2 := [i₁].to_finset 
def p₀₁ : ℙ 2 := ⊤ 

lemma ℙ_univ : is_universal [p, p₀, p₁, p₀₁] := dec_trivial

def u := @𝕂.u 2

def L : list (𝕂 2) := [u p, u p₀, u p₁, u p₀₁, u p₀ ⊓ u p₁, ⊤]

#eval (L.nodup : bool)
#eval (is_universal L : bool)

lemma 𝕂_univ : is_universal L := dec_trivial

end example_two 

/- LaTeX: eg-fracture-obj -/
namespace example_three

def i₀ : 𝕀 3 := ⟨0,dec_trivial⟩ 
def i₁ : 𝕀 3 := ⟨1,dec_trivial⟩ 
def i₂ : 𝕀 3 := ⟨2,dec_trivial⟩ 

lemma 𝕀_univ : is_universal [i₀, i₁, i₂] := dec_trivial

def p    : ℙ 3 := ⊥ 
def p₀   : ℙ 3 := [i₀].to_finset 
def p₁   : ℙ 3 := [i₁].to_finset 
def p₂   : ℙ 3 := [i₂].to_finset 
def p₀₁  : ℙ 3 := [i₀,i₁].to_finset
def p₀₂  : ℙ 3 := [i₀,i₂].to_finset
def p₁₂  : ℙ 3 := [i₁,i₂].to_finset
def p₀₁₂ : ℙ 3 := ⊤ 

lemma ℙ_univ :
 is_universal [p, p₀, p₁, p₂, p₀₁, p₀₂, p₁₂, p₀₁₂] := dec_trivial

def u := @𝕂.u 3
def v := @𝕂.v 3

def u₀ : 𝕂 3 := u p₀ 
def u₁ : 𝕂 3 := u p₁ 
def u₂ : 𝕂 3 := u p₂ 

def u₀₁ : 𝕂 3 := u p₀₁  
def u₀₂ : 𝕂 3 := u p₀₂ 
def u₁₂ : 𝕂 3 := u p₁₂ 

def u₀₁₂ : 𝕂 3 := u p₀₁₂ 

def v₀₁ : 𝕂 3 := u p₀ ⊓ u p₁ 
def v₀₂ : 𝕂 3 := u p₀ ⊓ u p₂ 
def v₁₂ : 𝕂 3 := u p₁ ⊓ u p₂ 

def x₀ : 𝕂 3 := u p₀ ⊓ u p₁₂ 
def x₁ : 𝕂 3 := u p₁ ⊓ u p₀₂ 
def x₂ : 𝕂 3 := u p₂ ⊓ u p₀₁ 

def w₀ : 𝕂 3 := u₀₁ ⊓ u₀₂ 
def w₁ : 𝕂 3 := u₀₁ ⊓ u₁₂ 
def w₂ : 𝕂 3 := u₀₂ ⊓ u₁₂ 

def y := u₀₁ ⊓ u₀₂ ⊓ u₁₂ 

def L : list (𝕂 3) := [
 ⊥, v p₀₁₂, v₀₁, v₀₂, v₁₂, x₀, x₁, x₂, 
 u₀, u₁, u₂, w₀, w₁, w₂, u₀₁, u₀₂, u₁₂, 
 u₀₁₂, y, ⊤ ]

#eval (L.nodup : bool)
#eval (is_universal L : bool)

-- lemma 𝕂_univ : is_universal L := dec_trivial

lemma eqs : 
 x₀ = v₀₁ * v₀₂ ∧ x₁ = v₀₁ * v₁₂ ∧ x₂ = v₀₂ * v₁₂ ∧ 
 w₀ = u₀  * v₁₂ ∧ w₂ = v₀₁ * u₂  ∧ y = v₀₁ * v₀₂ * v₁₂ := 
begin 
  repeat { split }; 
  ext A; revert A; exact dec_trivial,
end

end example_three 

variable (n)

/-- LaTeX : defn-doubly-localising-alt -/
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

instance : has_bot (𝕄 n) := ⟨⟨⟨⊥,⊥⟩,ℙ.bot_angle ⊥⟩⟩

/-- The only element of `𝕄 0` is `⊥`. -/
lemma mem_zero (AB : 𝕄 0) : AB = ⊥ := 
begin
  apply subtype.eq, 
  apply prod.ext, 
  { rw [ℙ.mem_zero AB.val.1], refl },
  { rw [ℙ.mem_zero AB.val.2], refl }
end

instance : fintype (𝕄 n) := by { unfold 𝕄, apply_instance }

end 𝕄 

instance 𝕄.decidable_rel : decidable_rel (λ (AB CD : 𝕄 n), AB ≤ CD) := 
 λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩, 
  by { change decidable ((A ≤ C) ∧ (B ≤ D)), apply_instance, }

variable {n} 

/-- LaTeX : defn-doubly-localising-alt -/
def σ : poset.hom (𝕄 n) (ℙ n) := 
 ⟨λ ⟨⟨A,B⟩,hAB⟩, A ⊔ B,
  λ ⟨⟨A,B⟩,hAB⟩ ⟨⟨C,D⟩,hCD⟩ ⟨hAC,hBD⟩, sup_le_sup hAC hBD⟩ 

def ζ : poset.hom (ℙ n) (𝕄 n) := 
 ⟨λ B, ⟨⟨⊥,B⟩,B.bot_angle⟩, λ B D hBD, ⟨le_refl ⊥,hBD⟩⟩

def ξ : poset.hom (ℙ n) (𝕄 n) := 
 ⟨λ A, ⟨⟨A,⊥⟩,A.angle_bot⟩, λ A C hAC, ⟨hAC,le_refl ⊥⟩⟩ 

lemma half_step (i : ℕ) : 
  (i / 2) ≤ ((i + 1) / 2) ∧ 
  ((i + 1) / 2) ≤ (i / 2) + 1 := 
begin
  split,
  exact nat.div_le_div_right (le_of_lt i.lt_succ_self),
  exact calc 
    (i + 1) / 2 ≤ (i + 2) / 2 : 
          nat.div_le_div_right (le_of_lt i.succ.lt_succ_self)
    ... = (i / 2) + 1 : nat.add_div_right i two_pos'
end

lemma half_misc (i : ℕ) :
  ((2 * i) / 2) = i ∧ 
  ((2 * i + 1) / 2) = i ∧ 
  ((2 * i + 2) / 2) = i + 1 ∧ 
  ((2 * i + 3) / 2) = i + 1 :=
begin
  have h₁ : 1 / 2 = 0 := rfl,
  have h₂ : 2 / 2 = 1 := rfl,
  have h₃ : 3 / 2 = 1 := rfl,
  rw [mul_comm, 
      add_comm _ 1, add_comm _ 2, add_comm _ 3,
      nat.mul_div_cancel i two_pos',
      nat.add_mul_div_right 1 i two_pos', 
      nat.add_mul_div_right 2 i two_pos', 
      nat.add_mul_div_right 3 i two_pos', 
      h₁, h₂, h₃, zero_add, add_comm 1],
  repeat {split}; refl
end

/-- LaTeX: defn-al-bt -/
def α (i : ℕ) : hom (𝕄 n) (𝕄 n) := 
⟨λ ABh,
 ⟨⟨ABh.val.1.filter_lt ((i + 1)/2),
  ABh.val.1.filter_ge (i / 2) ⊔ ABh.val.2⟩,
  begin -- Proof that we have an element of 𝕄 n
    rcases ABh with ⟨⟨A,B⟩,h_angle⟩,
    let u := (i + 1) / 2,
    let v := i / 2,
    rcases half_step i with ⟨hvu,huv⟩,
    change (A.filter_lt u) ∟ ((A.filter_ge v) ⊔ B),
    rw[ℙ.angle_sup],
    split,
    { exact ℙ.filter_angle huv A },
    { exact ℙ.angle_mono (A.filter_lt_is_le u) (le_refl _) h_angle } 
  end⟩,
 begin -- Proof of monotonicity
   rintro ⟨⟨A₀,B₀⟩,h_angle₀⟩ ⟨⟨A₁,B₁⟩,h_angle₁⟩ ⟨hA,hB⟩,
   let u := (i + 1) / 2,
   let v := i / 2,
   change 
    (A₀.filter_lt u ≤ A₁.filter_lt u) ∧ 
    (A₀.filter_ge v ⊔ B₀) ≤ (A₁.filter_ge v ⊔ B₁),
   split; intros x hx,
   { rw[ℙ.mem_filter_lt] at hx ⊢, exact ⟨hA hx.1,hx.2⟩ },
   { rw [ℙ.mem_sup, ℙ.mem_filter_ge] at hx ⊢, 
     rcases hx with hxA | hxB,
     { exact or.inl ⟨hA hxA.1,hxA.2⟩ },
     { exact or.inr (hB hxB) } }
 end⟩ 

def β (i : ℕ) : hom (𝕄 n) (𝕄 n) := 
⟨λ ABh,
 ⟨⟨ABh.val.1 ⊔ ABh.val.2.filter_lt ((i + 1)/2),
  ABh.val.2.filter_ge (i / 2)⟩,
  begin -- Proof that we have an element of 𝕄 n
    rcases ABh with ⟨⟨A,B⟩,h_angle⟩,
    let u := (i + 1) / 2,
    let v := i / 2,
    rcases half_step i with ⟨hvu,huv⟩,
    change (A ⊔ B.filter_lt u) ∟ (B.filter_ge v),
    rw[ℙ.sup_angle],
    split,
    { exact ℙ.angle_mono (le_refl A) (B.filter_ge_is_le v) h_angle },
    { exact ℙ.filter_angle huv B }
  end⟩,
 begin -- Proof of monotonicity
   rintro ⟨⟨A₀,B₀⟩,h_angle₀⟩ ⟨⟨A₁,B₁⟩,h_angle₁⟩ ⟨hA,hB⟩,
   let u := (i + 1) / 2,
   let v := i / 2,
   change 
    (A₀ ⊔ B₀.filter_lt u ≤ A₁ ⊔ B₁.filter_lt u) ∧ 
    (B₀.filter_ge v) ≤ (B₁.filter_ge v),
   split; intros x hx,
   { rw [ℙ.mem_sup, ℙ.mem_filter_lt] at hx ⊢, 
     rcases hx with hxA | hxB,
     { exact or.inl (hA hxA) },
     { exact or.inr ⟨hB hxB.1,hxB.2⟩ } },
   { rw[ℙ.mem_filter_ge] at hx ⊢, exact ⟨hB hx.1,hx.2⟩ }
 end⟩ 

/-- The relation `σ αᵢ = σ` -/
lemma σα (i : ℕ) : poset.comp (@σ n) (@α n i) = @σ n :=
begin
 apply poset.hom_ext, 
 rintro ⟨⟨A,B⟩,h_angle⟩, 
 let u := (i + 1) / 2,
 let v := i / 2,
 rcases half_step i with ⟨hvu,huv⟩,
 rw[poset.comp],
 change (A.filter_lt u) ⊔ ((A.filter_ge v) ⊔ B) = A ⊔ B,
 rw [← sup_assoc, ℙ.filter_sup hvu A]
end

/-- The relation `σ βᵢ = σ` -/
lemma σβ (i : ℕ) : poset.comp (@σ n) (@β n i) = @σ n :=
begin
 apply poset.hom_ext, 
 rintro ⟨⟨A,B⟩,h_angle⟩, 
 let u := (i + 1) / 2,
 let v := i / 2,
 rcases half_step i with ⟨hvu,huv⟩,
 rw[poset.comp],
 change (A ⊔ B.filter_lt u) ⊔ (B.filter_ge v) = A ⊔ B,
 rw [sup_assoc, ℙ.filter_sup hvu B]
end

/-- The relation `α₀ ⟨A,B⟩ = ⟨⊥, A⊔ B⟩` -/
lemma α_zero : (@α n 0) = poset.comp (@ζ n) (@σ n) := 
begin
  apply poset.hom_ext, 
  rintro ⟨⟨A,B⟩,h_angle⟩, 
  rw[poset.comp],
  apply subtype.eq,
  change prod.mk (A.filter_lt 0) ((A.filter_ge 0) ⊔ B) = 
         prod.mk ⊥ (A ⊔ B),
  rw[ℙ.filter_lt_zero, ℙ.filter_ge_zero]
end

/-- The relation `αᵢ = 1` for `i ≥ 2n` -/
lemma α_last {i : ℕ} (hi : i ≥ 2 * n) :
  (@α n i) = poset.id _ := 
begin
  apply poset.hom_ext, 
  rintro ⟨⟨A,B⟩,h_angle⟩, 
  rw[poset.id],
  apply subtype.eq,
  let u := (i + 1) / 2,
  let v := i / 2,
  have hv : v ≥ n := calc 
    n = (2 * n) / 2 : by rw [mul_comm, nat.mul_div_cancel n two_pos']
    ... ≤ v : nat.div_le_div_right hi,
  have hu : u ≥ n :=
   le_trans hv (nat.div_le_div_right (le_of_lt i.lt_succ_self)),
  change prod.mk (A.filter_lt u) ((A.filter_ge v) ⊔ B) = 
         prod.mk A B,
  rw [ℙ.filter_lt_last hu, ℙ.filter_ge_last hv],
  congr,
  exact bot_sup_eq
end

/-- The relation `β₀ = 1` -/
lemma β_zero : (@β n 0) = poset.id _ := 
begin
  apply poset.hom_ext, 
  rintro ⟨⟨A,B⟩,h_angle⟩, 
  rw[poset.id],
  apply subtype.eq,
  change prod.mk (A ⊔ B.filter_lt 0) (B.filter_ge 0) = 
         prod.mk A B,
  rw[ℙ.filter_lt_zero, ℙ.filter_ge_zero],
  congr,
  exact sup_bot_eq
end

/-- The relation `βᵢ ⟨A,B⟩ = ⟨A⊔ B, ⊥⟩` for `i ≥ 2n` -/
lemma β_last {i : ℕ} (hi : i ≥ 2 * n) :
  (@β n i) = poset.comp (@ξ n) (@σ n)  := 
begin
  apply poset.hom_ext, 
  rintro ⟨⟨A,B⟩,h_angle⟩, 
  rw [poset.comp],
  apply subtype.eq,
  let u := (i + 1) / 2,
  let v := i / 2,
  have hv : v ≥ n := calc 
    n = (2 * n) / 2 : by rw [mul_comm, nat.mul_div_cancel n two_pos']
    ... ≤ v : nat.div_le_div_right hi,
  have hu : u ≥ n :=
   le_trans hv (nat.div_le_div_right (le_of_lt i.lt_succ_self)),
  change prod.mk (A ⊔ B.filter_lt u) (B.filter_ge v) = 
         prod.mk (A ⊔ B) ⊥,
  rw [ℙ.filter_lt_last hu, ℙ.filter_ge_last hv]
end

/-- The inequality `α₂ᵢ ≤ α₂ᵢ₊₁` -/
lemma α_even_step (i : ℕ) : (@α n (2 * i)) ≤ (@α n (2 * i + 1)) := 
begin
  rcases half_misc i with ⟨h₀,h₁,h₂,h₃⟩,
  rintro ⟨⟨A,B⟩,h_angle⟩,
  change
   ((A.filter_lt ((2*i+1)/2) ≤ (A.filter_lt ((2*i+2)/2))) ∧ 
    (A.filter_ge ((2*i)/2) ⊔ B  ≤ (A.filter_ge ((2*i+1)/2)) ⊔ B)),
  rw [h₀, h₁, h₂],
  split,
  { intros x hx, 
    rw[ℙ.mem_filter_lt] at hx ⊢, 
    exact ⟨hx.1, lt_trans hx.2 i.lt_succ_self⟩ },
  { exact le_refl _ }
end

/-- The inequality `α₂ᵢ₊₂ ≤ α₂ᵢ₊₁` -/
lemma α_odd_step (i : ℕ) : (@α n (2 * i + 2)) ≤ (@α n (2 * i + 1)) := 
begin
  rcases half_misc i with ⟨h₀,h₁,h₂,h₃⟩,
  rintro ⟨⟨A,B⟩,h_angle⟩,
  change
   ((A.filter_lt ((2*i+3)/2) ≤ (A.filter_lt ((2*i+2)/2))) ∧ 
    (A.filter_ge ((2*i+2)/2) ⊔ B  ≤ (A.filter_ge ((2*i+1)/2)) ⊔ B)),
  rw [h₁, h₂, h₃],
  split,
  { exact le_refl _ },
  { apply sup_le_sup _ (le_refl _),
    intros x hx,
    rw[ℙ.mem_filter_ge] at hx ⊢, 
    exact ⟨hx.1,le_trans (le_of_lt i.lt_succ_self) hx.2⟩ }
end

/-- The inequality `β₂ᵢ ≤ β₂ᵢ₊₁` -/
lemma β_even_step (i : ℕ) : (@β n (2 * i)) ≤ (@β n (2 * i + 1)) := 
begin
  rcases half_misc i with ⟨h₀,h₁,h₂,h₃⟩,
  rintro ⟨⟨A,B⟩,h_angle⟩,
  change
   ((A ⊔ B.filter_lt ((2*i+1)/2) ≤ (A ⊔ B.filter_lt ((2*i+2)/2))) ∧ 
    (B.filter_ge ((2*i)/2)  ≤ (B.filter_ge ((2*i+1)/2)))),
  rw [h₀, h₁, h₂],
  split,
  { apply sup_le_sup (le_refl _) _,
    intros x hx, 
    rw[ℙ.mem_filter_lt] at hx ⊢, 
    exact ⟨hx.1, lt_trans hx.2 i.lt_succ_self⟩ },
  { exact le_refl _ }
end

/-- The inequality `β₂ᵢ₊₁ ≤ β₂ᵢ₊₁` -/
lemma β_odd_step (i : ℕ) : (@β n (2 * i + 2)) ≤ (@β n (2 * i + 1)) := 
begin
  rcases half_misc i with ⟨h₀,h₁,h₂,h₃⟩,
  rintro ⟨⟨A,B⟩,h_angle⟩,
  change
   ((A ⊔ B.filter_lt ((2*i+3)/2) ≤ (A ⊔ B.filter_lt ((2*i+2)/2))) ∧ 
    (B.filter_ge ((2*i+2)/2)  ≤ (B.filter_ge ((2*i+1)/2)))),
  rw [h₁, h₂, h₃],
  split,
  { exact le_refl _ },
  { intros x hx, 
    rw[ℙ.mem_filter_ge] at hx ⊢, 
    exact ⟨hx.1, le_trans (le_of_lt i.lt_succ_self) hx.2⟩ }
end

/-- All `αᵢ` are in the identity component.  -/
lemma α_component : ∀ i, poset.component (@α n i) = poset.idₕ _ := 
begin
  let c := λ i, poset.component (@α n i),
  change ∀ i, c i = poset.idₕ _,
  have h_all : ∀ i, c i = c 0 := 
    poset.zigzag α α_even_step α_odd_step,
  have : c (2 * n) = poset.idₕ _ := 
    congr_arg component (α_last (le_refl _)),
  intro i,
  exact ((h_all i).trans (h_all (2 * n)).symm).trans this 
end

/-- All `βᵢ` are in the identity component.  -/
lemma β_component : ∀ i, poset.component (@β n i) = poset.idₕ _ := 
begin
  let c := λ i, poset.component (@β n i),
  change ∀ i, c i = poset.idₕ _,
  have h_all : ∀ i, c i = c 0 := 
    poset.zigzag β β_even_step β_odd_step,
  intro i,
  have : c 0 = poset.idₕ _ := congr_arg component β_zero,
  rw [← this],
  exact h_all i
end

/-- `ζσ = 1` up to strong homotopy  -/
lemma ζσ_component : poset.component (poset.comp (@ζ n) (@σ n)) = poset.idₕ _ := 
  (congr_arg poset.component (@α_zero n)).symm.trans (@α_component n 0)

/-- `𝕃 n` is the poset of upper sets in `𝕄 n`.  This is 
  not mentioned explicitly in the LaTeX document, but is
  there in the background.
-/
def 𝕃 (n : ℕ) := poset.upper (𝕄 n)

namespace 𝕃 

instance : distrib_lattice (𝕃 n) := 
  @upper.dl (𝕄 n) _ _ _ _

instance : bounded_order  (𝕃 n) := 
  @upper.bo (𝕄 n) _ _ _ _

instance : partial_order (𝕄 n) := by apply_instance 

instance 𝕄_mem_𝕃 : has_mem (𝕄 n) (𝕃 n) := 
 by { unfold 𝕃, apply_instance }

end 𝕃 

/-- LaTeX : defn-ostar -/
def omul0 (U V : finset (ℙ n)) : finset (𝕄 n) := 
 (U.bUnion (λ A, V.image (λ B, prod.mk A B))).subtype (λ AB, AB.1 ∟ AB.2)

lemma mem_omul0 (U V : finset (ℙ n)) (AB : 𝕄 n) : 
 AB ∈ omul0 U V ↔ AB.val.1 ∈ U ∧ AB.val.2 ∈ V := 
begin
 rw[omul0,finset.mem_subtype],
 split,
 {rcases AB with ⟨⟨A,B⟩,h⟩, change A ∟ B at h,
  intro h0,
  rcases (finset.mem_bUnion.mp h0) with ⟨C,⟨hCU,h1⟩⟩,
  rcases (finset.mem_image.mp h1) with ⟨D,⟨hDV,h2⟩⟩,
  cases h2,
  exact ⟨hCU,hDV⟩,
 },
 {rcases AB with ⟨⟨A,B⟩,hAB⟩, change A ∟ B at hAB,
  rintros ⟨hAU,hBV⟩, change A ∈ U at hAU, change B ∈ V at hBV,
  apply finset.mem_bUnion.mpr,use A,use hAU,
  apply finset.mem_image.mpr,use B,use hBV, simp,
 }
end

lemma is_upper_omul0 {U V : finset (ℙ n)}
 (hU : is_upper U) (hV : is_upper V) : is_upper (omul0 U V) := 
begin
 rintros ⟨⟨A₀,B₀⟩,hAB₀⟩ ⟨⟨A₁,B₁⟩,hAB₁⟩ ⟨h_le_A,h_le_B⟩ AB₀_in_omul,
 rcases (mem_omul0 U V _).mp AB₀_in_omul with ⟨A₀_in_U,B₀_in_V⟩,
 apply (mem_omul0 U V _).mpr,
 simp only [],
 exact ⟨hU A₀ A₁ h_le_A A₀_in_U,hV B₀ B₁ h_le_B B₀_in_V⟩,
end

def omul : (𝕂 n) → (𝕂 n) → (𝕃 n) := 
 λ U V, ⟨omul0 U.val V.val, is_upper_omul0 U.property V.property⟩ 

lemma mem_omul (U V : (𝕂 n)) (AB : 𝕄 n) : 
 AB ∈ omul U V ↔ AB.val.1 ∈ U ∧ AB.val.2 ∈ V := 
mem_omul0 U.val V.val AB  

lemma omul_mono₂ : 
 ∀ {U₀ U₁ V₀ V₁ : 𝕂 n} (hU : U₀ ≤ U₁) (hV : V₀ ≤ V₁), 
  omul U₀ V₀ ≤ omul U₁ V₁
| ⟨U₀,hU₀⟩ ⟨U₁,hU₁⟩ ⟨V₀,hV₀⟩ ⟨V₁,hV₁⟩ hU hV ⟨A,B⟩ h := 
begin
 rcases (mem_omul0 U₁ V₁ ⟨A,B⟩).mp h with ⟨hAU,hBV⟩,
 apply (mem_omul0 U₀ V₀ ⟨A,B⟩).mpr,
 exact ⟨hU hAU,hV hBV⟩,
end

def σ0 (W : 𝕃 n) : 𝕂 n := 
 ⟨W.val.image (@σ n),
  begin
   intros C C' h_le C_in_sg_W,
   rcases finset.mem_image.mp C_in_sg_W with ⟨⟨⟨A,B⟩,h_angle⟩,h_mem,h_eq⟩,
   let AB : 𝕄 n := ⟨⟨A,B⟩,h_angle⟩,
   rcases ℙ.angle_iff.mp h_angle with ⟨⟨⟨⟩⟩ | h⟩,
   { rw[C.mem_zero] at *, rw[C'.mem_zero], exact C_in_sg_W },
   { rcases h with ⟨k,hA,hB⟩,
     change (A ∪ B : finset _) = C at h_eq,
     rw [← h_eq] at h_le,
     let A' := C'.filter_lt k.val.succ,
     let B' := C'.filter_ge k.val,
     have h_angle' : A' ∟ B' := ℙ.filter_angle k.val.lt_succ_self C',
     let AB' : 𝕄 n := ⟨⟨A',B'⟩,h_angle'⟩,
     have h_le' : AB ≤ AB' := 
     begin
      split,
      { intros a a_in_A, 
        exact finset.mem_filter.mpr
          ⟨h_le (finset.mem_union_left B a_in_A),
           lt_of_le_of_lt (hA a_in_A) k.val.lt_succ_self⟩ },
      { intros b b_in_B, 
        exact finset.mem_filter.mpr
          ⟨h_le (finset.mem_union_right A b_in_B),hB b_in_B⟩ }
     end,
     have h_mem' : AB' ∈ W.val := W.property AB AB' h_le' h_mem,
     have h_eq' :  (@σ n) AB' = C' := 
     begin 
       change A' ∪ B' = C',
       ext c,
       rw [finset.mem_union, ℙ.mem_filter_lt, ℙ.mem_filter_ge,
           ← and_or_distrib_left, nat.lt_succ_iff],
       simp [le_total]
     end,
     exact finset.mem_image.mpr ⟨AB',h_mem',h_eq'⟩
   }
  end⟩

def σ' : poset.hom (𝕃 n) (𝕂 n) := ⟨@σ0 n,
begin
  rintro W₀ W₁ h_le C C_in_sg_W,
  rcases finset.mem_image.mp C_in_sg_W with ⟨AB,h_mem,h_eq⟩,
  exact finset.mem_image.mpr ⟨AB,h_le h_mem,h_eq⟩
end⟩ 

lemma mem_σ' (W : 𝕃 n) (C : ℙ n) : 
  C ∈ @σ' n W ↔ ∃ AB, AB ∈ W ∧ @σ n AB = C := 
begin
  change (C ∈ W.val.image (@σ n) ↔ _),
  rw[finset.mem_image],
  apply exists_congr,
  intro AB,
  have : AB ∈ W.val ↔ AB ∈ W := by { refl }, rw[this], simp,
end

lemma factor_σ (U V : 𝕂 n) : U * V = @σ' n (omul U V) := 
begin
  ext C,
  rw [𝕂.mem_mul U V C, mem_σ' (omul U V)],
  split; intro h,
  { rcases h with ⟨A,B,A_in_U,B_in_V,h_angle,h_eq⟩, 
    use ⟨⟨A,B⟩,h_angle⟩,
    exact ⟨(mem_omul U V ⟨⟨A,B⟩,h_angle⟩).mpr ⟨A_in_U,B_in_V⟩,h_eq⟩ },
  { rcases h with ⟨⟨⟨A,B⟩,h_angle⟩,h_mem,h_eq⟩, 
    use A, use B,
    replace h_mem := (mem_omul U V ⟨⟨A,B⟩,h_angle⟩).mp h_mem,
    change A ∈ U ∧ B ∈ V at h_mem,
    exact ⟨h_mem.left,h_mem.right,h_angle,h_eq⟩ }
end

/-- LaTeX: lem-mu-u -/
lemma mul_u (A B : ℙ n) : (@𝕂.u n A) * (@𝕂.u n B) =
  ite (A ∟ B) (@𝕂.u n (A ⊔ B)) ⊤ := 
begin
  ext C, 
  rw [𝕂.mem_mul (@𝕂.u n A) (@𝕂.u n B) C],  
  split; intro h,
  { rcases h with ⟨A',B',hA,hB,h_angle,h_union⟩, 
    rw [𝕂.mem_u] at hA hB,
    have : A ∟ B := λ a b ha hb, h_angle (hA ha) (hB hb),
    rw [if_pos this, @𝕂.mem_u n (A ⊔ B) C, ← h_union],
    exact sup_le_sup hA hB },
  { by_cases h_angle : A ∟ B, 
    { rw [if_pos h_angle, @𝕂.mem_u n] at h, 
      rcases (ℙ.angle_iff.mp h_angle) with ⟨⟨⟩⟩ | ⟨k,⟨hA,hB⟩⟩,
      { use ⊥, use ⊥, 
        rw[ℙ.mem_zero A, ℙ.mem_zero B, ℙ.mem_zero C, 𝕂.mem_u],
        simp only [ℙ.bot_angle, le_refl, sup_bot_eq, true_and] },
      { use C.filter_lt k.val.succ, 
        use C.filter_ge k.val,
        rw [𝕂.mem_u, 𝕂.mem_u],
        have hA' : A ≤ C.filter_lt k.val.succ := λ a ha, 
         ℙ.mem_filter_lt.mpr
           ⟨h (finset.mem_union_left B ha),nat.lt_succ_iff.mpr (hA ha)⟩,
        have hB' : B ≤ C.filter_ge k.val := λ b hb, 
         ℙ.mem_filter_ge.mpr
           ⟨h (finset.mem_union_right A hb),hB hb⟩,
        exact ⟨hA', hB', 
               ℙ.filter_angle k.val.lt_succ_self C,
               ℙ.filter_sup (le_of_lt k.val.lt_succ_self) C⟩ } },
    { rw [if_neg h_angle] at h,
      exact (upper.not_mem_top C h).elim } }
end

/-- `σ_slice U V` is the map from `U # V` to `U * V` whose
  (co)finality is proved in prop-sg-final and prop-sg-cofinal.
-/
def σ_slice (U V : 𝕂 n) : hom (omul U V).els (U * V).els := 
⟨ λ ABh, ⟨@σ n ABh.val, 
 begin 
  rw [factor_σ U V],
  exact finset.mem_image_of_mem _ ABh.property, 
 end ⟩,
 λ ABh₀ ABh₁ h, σ.property h ⟩ 

namespace σ_slice

variables (U V : 𝕂 n) (C : (U * V).els)

/-- This is the map sending `A` to `C_{≤ max A}`, which is 
  used (but not named) in prop-sg-cofinal. -/
def η : hom (ℙ n) (ℙ n) := 
⟨ λ A, C.val.filter (λ c, ∃ a, a ∈ A ∧ c ≤ a),
  λ A₀ A₁ h c hc, 
  begin 
    rw [finset.mem_filter] at *,
    rcases hc with ⟨hcC,⟨a,⟨haA,hca⟩⟩⟩,
    exact ⟨hcC,⟨a,⟨h haA,hca⟩⟩⟩
  end⟩ 

/-- This is the map sending `A` to `C_{≥ min A}`, which is 
  used (but not named) in prop-sg-cofinal. -/
def θ : hom (ℙ n) (ℙ n) := 
⟨ λ B, C.val.filter (λ c, ∃ b, b ∈ B ∧ b ≤ c),
  λ B₀ B₁ h c hc, 
  begin 
    rw [finset.mem_filter] at *,
    rcases hc with ⟨hcC,⟨b,⟨hbB,hbc⟩⟩⟩,
    exact ⟨hcC,⟨b,⟨h hbB,hbc⟩⟩⟩
  end⟩ 

lemma η_angle_θ (A B : ℙ n) : A ∟ B → (η U V C A) ∟ (θ U V C B) := 
λ h_angle x y hx hy, 
begin 
  rcases (finset.mem_filter.mp hx).right with ⟨a,⟨haA,hxa⟩⟩,
  rcases (finset.mem_filter.mp hy).right with ⟨b,⟨hbB,hby⟩⟩,
  exact le_trans (le_trans hxa (h_angle haA hbB)) hby,
end

def φ₀ : hom (𝕄 n) (𝕄 n) := 
⟨λ AB, ⟨⟨η U V C AB.val.1,θ U V C AB.val.2⟩, 
        η_angle_θ U V C AB.val.1 AB.val.2 AB.property⟩,
 λ ⟨⟨A₀,B₀⟩,h_angle₀⟩ ⟨⟨A₁,B₁⟩,h_angle₁⟩ h,
 begin 
   change A₀ ≤ A₁ ∧ B₀ ≤ B₁ at h,
   change ((η U V C A₀) ≤ (η U V C A₁)) ∧ 
          ((θ U V C B₀) ≤ (θ U V C B₁)),
   exact ⟨(η U V C).property h.left,(θ U V C).property h.right⟩
 end⟩

/-- This is the main map used in prop-sg-cofinal -/
def φ : hom (comma (σ_slice U V) C) (comma (σ_slice U V) C) := 
⟨ λ X, 
  ⟨⟨φ₀ U V C X.val.val,
    begin 
      rcases X with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h_omul⟩,hABC⟩,
      rcases (mem_omul U V _).mp h_omul with ⟨hAU,hBV⟩,
      have hABC' : A ⊔ B ≤ C.val := hABC,
      rcases sup_le_iff.mp hABC' with ⟨hAC,hBC⟩, 
      apply (mem_omul U V _).mpr,
      let A₁ := η U V C A,
      let B₁ := θ U V C B,
      change A₁ ∈ U ∧ B₁ ∈ V,
      split,
      { have : A ≤ A₁ := λ a ha, 
          finset.mem_filter.mpr ⟨hAC ha,⟨a,⟨ha,le_refl a⟩⟩⟩,
          exact U.property A A₁ this hAU },
      { have : B ≤ B₁ := λ b hb, 
          finset.mem_filter.mpr ⟨hBC hb,⟨b,⟨hb,le_refl b⟩⟩⟩,
          exact V.property B B₁ this hBV }
    end⟩, 
    begin 
      rcases X with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h_omul⟩,hABC⟩,
      change (η U V C A) ⊔ (θ U V C B) ≤ C.val,
      intros x hx,
      rcases finset.mem_union.mp hx with hx' | hx';
      exact (finset.mem_filter.mp hx').left,
    end⟩, 
  begin
    rintro ⟨⟨AB₀,h_omul₀⟩,hABC₀⟩ ⟨⟨AB₁,h_omul₁⟩,hABC₁⟩ h,
    exact (φ₀ U V C).property (h : AB₀ ≤ AB₁),
  end⟩ 

lemma id_le_φ : (id (comma (σ_slice U V) C)) ≤ (φ U V C) := 
begin
  intro X,
  rcases X with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h_omul⟩,hABC⟩,
  change A ∟ B at h_angle,
  rcases (mem_omul U V _).mp h_omul with ⟨hAU,hBV⟩,
  change A ∈ U at hAU, change B ∈ V at hBV, 
  change A ⊔ B ≤ C.val at hABC,
  rcases sup_le_iff.mp hABC with ⟨hAC,hBC⟩,
  change (A ≤ η U V C A) ∧ (B ≤ θ U V C B),
  split, 
  { intros a ha, 
    exact finset.mem_filter.mpr ⟨hAC ha, ⟨a,⟨ha,le_refl a⟩⟩⟩, },
  { intros b hb, 
    exact finset.mem_filter.mpr ⟨hBC hb, ⟨b,⟨hb,le_refl b⟩⟩⟩, },
end

/-- The proof of prop-sg-cofinal uses a pair of natural 
  numbers `i` and `j` with certain properties.  The definition
  below encapsulates these properties.
-/
def ij_spec (i j : ℕ) := 
    i ≤ n ∧ j ≤ n ∧ 
    C.val.filter_lt i ∈ U ∧ 
    C.val.filter_ge j ∈ V ∧ 
    (∀ k, k ≤ n → C.val.filter_lt k ∈ U → i ≤ k) ∧ 
    (∀ k, k ≤ n → C.val.filter_ge k ∈ V → k ≤ j) ∧ 
    i ≤ j + 1

/-- We now prove that a pair of numbers with the required
  properties exists.  Note that this is formulated as a 
  bare existence statement, from which we cannot extract a 
  witness.  A constructive version would be possible but 
  would require a little reorganisation.  
-/

lemma ij_exists  :
 ∃ i j : ℕ, ij_spec U V C i j := 
begin 
  rcases C with ⟨C,hC⟩,
  rcases (𝕂.mem_mul U V C).mp hC with ⟨A₀,B₀,hA₀,hB₀,h_angle₀,h_eq₀⟩,
  have hAC₀ : A₀ ≤ C := by { rw[← h_eq₀], exact le_sup_left },
  have hBC₀ : B₀ ≤ C := by { rw[← h_eq₀], exact le_sup_right },
  let i_prop : fin n.succ → Prop := λ i, C.filter_lt i.val ∈ U,
  let j_prop : fin n.succ → Prop := λ j, C.filter_ge j ∈ V,
  let k_zero : fin n.succ := ⟨0, n.zero_lt_succ⟩,
  let k_last : fin n.succ := ⟨n, n.lt_succ_self⟩,
  have i_prop_last : i_prop k_last := 
  begin
    have : A₀ ≤ C.filter_lt n := 
      λ a ha, ℙ.mem_filter_lt.mpr ⟨hAC₀ ha, a.is_lt⟩,
    exact U.property A₀ _ this hA₀,
  end,
  have j_prop_zero : j_prop k_zero := 
  begin
    have : B₀ ≤ C.filter_ge 0 := 
      λ b hb, ℙ.mem_filter_ge.mpr ⟨hBC₀ hb, nat.zero_le _⟩,
    exact V.property B₀ _ this hB₀,
  end,
  have i_prop_last' : k_last ∈ finset.univ.filter i_prop := 
      finset.mem_filter.mpr ⟨finset.mem_univ k_last, i_prop_last⟩,
  have j_prop_zero' : k_zero ∈ finset.univ.filter j_prop := 
      finset.mem_filter.mpr ⟨finset.mem_univ k_zero, j_prop_zero⟩,
  rcases fin.finset_least_element
    (finset.univ.filter i_prop) ⟨_,i_prop_last'⟩ 
      with ⟨i,⟨i_prop_i',i_least'⟩⟩,
  rcases fin.finset_largest_element
    (finset.univ.filter j_prop) ⟨_,j_prop_zero'⟩
        with ⟨j,⟨j_prop_j',j_largest'⟩⟩,
  let i_prop_i := (finset.mem_filter.mp i_prop_i').right,
  let j_prop_j := (finset.mem_filter.mp j_prop_j').right,
  have i_least : ∀ (k : fin n.succ) (hk : i_prop k), i ≤ k := 
    λ k hk, i_least' k (finset.mem_filter.mpr ⟨finset.mem_univ _,hk⟩),
  have j_largest : ∀ (k : fin n.succ) (hk : j_prop k), k ≤ j := 
    λ k hk, j_largest' k (finset.mem_filter.mpr ⟨finset.mem_univ _,hk⟩),
  use i.val, use j.val,
  split, exact nat.le_of_lt_succ i.is_lt,
  split, exact nat.le_of_lt_succ j.is_lt,
  split, exact i_prop_i,
  split, exact j_prop_j,
  split, 
  { intros k hkn hk,
    exact i_least ⟨k, nat.lt_succ_of_le hkn⟩ hk },
  split, 
  { intros k hkn hk,
    exact j_largest ⟨k, nat.lt_succ_of_le hkn⟩ hk },
  rcases ℙ.angle_iff.mp h_angle₀ with ⟨⟨⟩⟩ | ⟨k,hkA₀,hkB₀⟩,
  { apply le_add_left, exact le_of_lt i.is_lt },
  { let k₀ : fin n.succ := ⟨k.val, lt_trans k.is_lt n.lt_succ_self⟩,
    let k₁ : fin n.succ := ⟨k.val.succ, nat.succ_lt_succ k.is_lt⟩,
    have i_prop_k : i_prop k₁ :=  
    begin
      have : A₀ ≤ C.filter_lt k₁ := 
      λ i hi, ℙ.mem_filter_lt.mpr
        ⟨by { rw[← h_eq₀], exact finset.mem_union_left B₀ hi}, 
         nat.lt_succ_of_le (hkA₀ hi) ⟩,
      exact U.property A₀ (C.filter_lt k₁) this hA₀,
    end,
    have j_prop_k : j_prop k₀ := 
    begin
      have : B₀ ≤ C.filter_ge k₀ := 
      λ i hi, ℙ.mem_filter_ge.mpr
        ⟨by { rw[← h_eq₀], exact finset.mem_union_right A₀ hi}, 
         hkB₀ hi ⟩,
      exact V.property B₀ (C.filter_ge k.val) this hB₀,
    end,
    have hik : i.val ≤ k.val + 1 := i_least k₁ i_prop_k,
    have hkj : k.val ≤ j.val := j_largest k₀ j_prop_k,
    exact le_trans hik (nat.succ_le_succ hkj) },
end

section with_ij
/-- In this section, we assume that we are given `i` and `j`,
  together with a proof of the required properties.  
  Only in the final part of the proof do we invoke `ij_exists`.
-/

variables (i j : ℕ) (h : ij_spec U V C i j) 
include i j h

/-- This is the basepoint to which we will contract the comma poset. -/
def base : comma (σ_slice U V) C := 
begin
  rcases h with ⟨hi_is_le,hj_is_le,hiU,hjV,hi,hj,hij⟩,
  let A₁ := C.val.filter_lt i,
  let B₁ := C.val.filter_ge j,
  have hA₁ : A₁ ∈ U := hiU,
  have hB₁ : B₁ ∈ V := hjV,
  have h_angle₁ : A₁ ∟ B₁ := λ a b ha hb, 
    nat.le_of_lt_succ $
    calc 
      a.val < i : (finset.mem_filter.mp ha).right
      ... ≤ j + 1 : hij 
      ... ≤ b.val + 1 : nat.succ_le_succ (finset.mem_filter.mp hb).right,
  let AB₁ : 𝕄 n := ⟨⟨A₁,B₁⟩,h_angle₁⟩,
  let AB₂ : (omul U V).els := ⟨AB₁,(mem_omul U V AB₁).mpr ⟨hA₁,hB₁⟩⟩,
  have hABC : σ_slice U V AB₂ ≤ C := 
  begin
    let hAC : A₁ ≤ C.val := ℙ.filter_lt_is_le i C.val,
    let hBC : B₁ ≤ C.val := ℙ.filter_ge_is_le j C.val,
    exact sup_le hAC hBC,
  end,
  exact ⟨AB₂, hABC⟩
end

/-- The values of the map `φ` lie above the basepoint. -/
lemma base_le_φ (X : (comma (σ_slice U V) C)) : 
    base U V C i j h ≤ (φ U V C).val X := 
begin
  rcases h with ⟨hi_is_le,hj_is_le,hiU,hjV,hi,hj,hij⟩,
  rcases X with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h_omul⟩,hABC⟩,
  change A ∟ B at h_angle,
  rcases (mem_omul U V _).mp h_omul with ⟨hAU,hBV⟩,
  change A ∈ U at hAU, change B ∈ V at hBV, 
  change A ⊔ B ≤ C.val at hABC,
  rcases sup_le_iff.mp hABC with ⟨hAC,hBC⟩,
  have hi' : ((C.val.filter_lt i) ≤ η U V C A) := 
  begin 
    intros c hc, 
    rw [ℙ.mem_filter_lt] at hc,
    apply finset.mem_filter.mpr,
    split, {exact hc.left},
    by_contradiction h,
    rw [not_exists] at h,
    have : A ≤ C.val.filter_lt c.val := λ a ha,
    begin 
      rw [ℙ.mem_filter_lt],
      exact ⟨hAC ha, lt_of_not_ge (λ h₀, h a ⟨ha,h₀⟩)⟩,
    end, 
    have : C.val.filter_lt c.val ∈ U :=
      U.property A (C.val.filter_lt c.val) this hAU,
    have : i ≤ c.val := hi c.val (le_of_lt c.is_lt) this,
    exact not_lt_of_ge this hc.right,
  end,
  have hj' : ((C.val.filter_ge j) ≤ θ U V C B) := 
  begin 
    intros c hc, 
    rw [ℙ.mem_filter_ge] at hc,
    apply finset.mem_filter.mpr,
    split, {exact hc.left},
    by_contradiction h,
    rw [not_exists] at h,
    have : B ≤ C.val.filter_ge c.val.succ := λ b hb,
    begin 
      rw [ℙ.mem_filter_ge],
      exact ⟨hBC hb, le_of_not_gt (λ h₀, h b ⟨hb, nat.le_of_lt_succ h₀⟩)⟩,
    end, 
    have : C.val.filter_ge c.val.succ ∈ V :=
      V.property B (C.val.filter_ge c.val.succ) this hBV,
    have : c.val < j := hj c.val.succ c.is_lt this,
    exact not_le_of_gt this hc.right,
  end,
  exact ⟨hi',hj'⟩
end

end with_ij

/-- LaTeX: prop-sg-cofinal -/
theorem cofinal : cofinalₕ (σ_slice U V) := 
begin
  intro C,
  rcases ij_exists U V C with ⟨i,j,hij⟩,
  let M := (comma (σ_slice U V) C),
  change nonempty (equivₕ M unit),
  let m : M := base U V C i j hij,
  let f : hom M unit := const M unit.star,
  let g : hom unit M := const unit m,
  have hfg : comp f g = id unit := by { ext p },
  have gf_le_φ : comp g f ≤ φ U V C := 
    λ X, base_le_φ U V C i j hij X,
  have hgf : compₕ (component g) (component f) = idₕ M := 
    (π₀.sound gf_le_φ).trans (π₀.sound (id_le_φ U V C)).symm,
  let e : equivₕ M unit := 
    { to_fun    := component f,
      inv_fun   := component g, 
      left_inv  := hgf, 
      right_inv := congr_arg component hfg },
  exact ⟨e⟩
end


/-- The proof of prop-sg-final uses a number `k` with 
  certain properties.  We handle this in the same way as 
  the pair `⟨i,j⟩` in the previous proof.
-/
def k_spec (k : ℕ) : Prop :=
 k ≤ n ∧ C.val.filter_lt k.succ ∈ U ∧ C.val.filter_ge k ∈ V

lemma k_exists : ∃ (k : ℕ), k_spec U V C k := 
begin
  rcases C with ⟨C,hC⟩,
  rcases (𝕂.mem_mul U V C).mp hC with ⟨A,B,hAU,hBV,h_angle,hABC⟩,
  rcases ℙ.angle_iff.mp h_angle with ⟨⟨⟩⟩ | ⟨k,hkA,hkB⟩,
  { use 0, 
    dsimp [k_spec],
    rw [ℙ.mem_zero A] at hAU, 
    rw [ℙ.mem_zero B] at hBV, 
    rw [ℙ.mem_zero (C.filter_lt 1), ℙ.mem_zero (C.filter_ge 0)],
    exact ⟨le_refl 0, hAU, hBV⟩ },
  { use k.val, 
    dsimp [k_spec],
    split, { exact le_of_lt k.is_lt },
    have hAC : A ≤ C := by { rw[← hABC], exact le_sup_left  },
    have hBC : B ≤ C := by { rw[← hABC], exact le_sup_right },
    let A' := C.filter_lt k.val.succ,
    let B' := C.filter_ge k.val,
    have hABC' : A' ⊔ B' = C :=
      ℙ.filter_sup (le_of_lt k.val.lt_succ_self) C,
    have h_angle' : A' ∟ B' := ℙ.filter_angle (le_refl _) C,
    have hAA' : A ≤ A' := 
     λ a ha, ℙ.mem_filter_lt.mpr ⟨hAC ha,nat.lt_succ_iff.mpr (hkA ha)⟩, 
    have hBB' : B ≤ B' := λ b hb, ℙ.mem_filter_ge.mpr ⟨hBC hb,hkB hb⟩,
    have hAU' : A' ∈ U := U.property A A' hAA' hAU, 
    have hBV' : B' ∈ V := V.property B B' hBB' hBV, 
    exact ⟨hAU',hBV'⟩ }
end

section with_k 

variables (k : ℕ) (hk : k_spec U V C k)
include k hk


/-- The restrictions of `αᵢ` and `βᵢ` to the comma poset are 
  denoted by `α'` and `β'`.
-/
def α' (i : ℕ) (hi : i > 2 * k) : 
  hom (cocomma (σ_slice U V) C) (cocomma (σ_slice U V) C) := 
let u := (i + 1)/2 in let v := i / 2 in
⟨ λ x, ⟨⟨(α i).val x.val.val, 
  begin
   have hu : u > k := 
   begin
     have : 2 * k + 2 ≤ i + 1 := nat.succ_le_succ hi,
     have : (2 * k + 2) / 2 ≤ u := nat.div_le_div_right this,
     exact calc
       k + 1 = ((k + 1) * 2) / 2 : 
         (nat.mul_div_cancel (k + 1) two_pos').symm
       ... = (2 * k + 2) / 2 : by { rw [add_mul, one_mul, mul_comm] }
       ... ≤ u : this,
   end,
   rcases half_step i with ⟨hvu,huv⟩,
   rcases x with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h₀⟩,h₁⟩,
   rcases (mem_omul U V _).mp h₀ with ⟨hAU,hBV⟩,
   rcases hk with ⟨hkn,hkU,hkV⟩,
   change A ∟ B at h_angle, 
   change A ∈ U at hAU, change B ∈ V at hBV,
   change C.val ≤ A ⊔ B at h₁, 
   apply (mem_omul U V _).mpr,
   change A.filter_lt u ∈ U ∧ (A.filter_ge v ⊔ B) ∈ V,
   split,
   { by_cases h : ∃ (a : 𝕀 n), a ∈ A ∧ a.val ≥ u,
     { rcases h with ⟨a,ha⟩,
       have : C.val.filter_lt k.succ ≤ A.filter_lt u := λ c hc,
       begin
         rcases ℙ.mem_filter_lt.mp hc with ⟨hcC,hck⟩, 
         replace hck := nat.lt_succ_iff.mp hck,
         have hcu : c.val < u := lt_of_le_of_lt hck hu,
         rcases finset.mem_union.mp (h₁ hcC) with hcA | hcB,
         { rw [ℙ.mem_filter_lt], exact ⟨hcA,hcu⟩ },
         { exfalso, 
           have hca : c.val < a.val := lt_of_lt_of_le hcu ha.right,
           exact not_le_of_gt hca (h_angle ha.left hcB) }
       end,
       exact U.property (C.val.filter_lt k.succ) (A.filter_lt u) this hkU },
     { have : A.filter_lt u = A := 
       begin
         rw [not_exists] at h,
         ext a,
         rw [ℙ.mem_filter_lt],
         split,
         { exact λ h, h.left },
         { exact λ ha, ⟨ha, lt_of_not_ge (λ h₀, h a ⟨ha,h₀⟩)⟩ }
       end,
       rw [this], 
       exact hAU } },
     { exact V.property B (A.filter_ge v ⊔ B) le_sup_right hBV } 
  end⟩, 
  begin 
    rcases half_step i with ⟨hvu,huv⟩,
    rcases x with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h₀⟩,h₁⟩,
    change C.val ≤ ((A.filter_lt u) ⊔ (A.filter_ge v ⊔ B)),
    rw [← sup_assoc, ℙ.filter_sup hvu A],
    exact h₁, 
  end⟩,
 begin 
   rintro ⟨⟨X₀,_⟩,_⟩ ⟨⟨X₁,_⟩,_⟩ h,
   exact (α i).property h
 end⟩ 

def β' (i : ℕ) (hi : i ≤ 2 * k + 1) : 
  hom (cocomma (σ_slice U V) C) (cocomma (σ_slice U V) C) := 
let u := (i + 1)/2 in let v := i / 2 in
⟨ λ x, ⟨⟨(β i).val x.val.val, 
  begin
   have hv : i/2 ≤ k := calc
     i / 2 ≤ (2 * k + 1) / 2 : nat.div_le_div_right hi
     ... = k : (half_misc k).2.1,
   rcases half_step i with ⟨hvu,huv⟩,
   rcases x with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h₀⟩,h₁⟩,
   rcases (mem_omul U V _).mp h₀ with ⟨hAU,hBV⟩,
   rcases hk with ⟨hkn,hkU,hkV⟩,
   change A ∟ B at h_angle, 
   change A ∈ U at hAU, change B ∈ V at hBV,
   change C.val ≤ A ⊔ B at h₁, 
   apply (mem_omul U V _).mpr,
   change A ⊔ B.filter_lt u ∈ U ∧ B.filter_ge v ∈ V,
   split,
   { exact U.property A (A ⊔ B.filter_lt u) le_sup_left hAU }, 
   { by_cases h : ∃ (b : 𝕀 n), b ∈ B ∧ b.val < v,
     { rcases h with ⟨b,hb⟩,
       have : C.val.filter_ge k ≤ B.filter_ge v := λ c hc,
       begin
         rcases ℙ.mem_filter_ge.mp hc with ⟨hcC,hck⟩, 
         have hcu : c.val ≥ v := le_trans hv hck,
         rcases finset.mem_union.mp (h₁ hcC) with hcA | hcB,
         { exfalso, 
           have hbc : b.val < c.val := lt_of_lt_of_le hb.right hcu,
           exact not_le_of_gt hbc (h_angle hcA hb.left) },
         { rw [ℙ.mem_filter_ge], exact ⟨hcB,hcu⟩ }
       end,
       exact V.property (C.val.filter_ge k) (B.filter_ge v) this hkV },
     { have : B.filter_ge v = B := 
       begin
         rw [not_exists] at h,
         ext a,
         rw [ℙ.mem_filter_ge],
         split,
         { exact λ h, h.left },
         { exact λ ha, ⟨ha, le_of_not_gt (λ h₀, h a ⟨ha,h₀⟩)⟩ }
       end,
       rw [this], 
       exact hBV } },
  end⟩, 
  begin 
    rcases half_step i with ⟨hvu,huv⟩,
    rcases x with ⟨⟨⟨⟨A,B⟩,h_angle⟩,h₀⟩,h₁⟩,
    change C.val ≤ A ⊔ (B.filter_lt u) ⊔ (B.filter_ge v),
    rw [sup_assoc, ℙ.filter_sup hvu B],
    exact h₁, 
  end⟩,
 begin 
   rintro ⟨⟨X₀,_⟩,_⟩ ⟨⟨X₁,_⟩,_⟩ h,
   exact (β i).property h
 end⟩ 

lemma α'_last : 
  α' U V C k hk (2 * n + 1) 
   (lt_of_le_of_lt (nat.mul_le_mul_left 2 hk.1) (2 * n).lt_succ_self)
     = poset.id _ :=
begin
  ext1 X,
  rcases X with ⟨⟨Y,_⟩,_⟩,
  apply subtype.eq,
  apply subtype.eq,
  change (α (2 * n + 1)).val Y = Y,
  rw [α_last (le_of_lt (2 * n).lt_succ_self)],
  refl,
end

lemma β'_zero  : 
  β' U V C k hk 0 (nat.zero_le _) = poset.id _ := 
begin
  ext1 X,
  rcases X with ⟨⟨Y,_⟩,_⟩,
  apply subtype.eq,
  apply subtype.eq,
  change (β 0).val Y = Y,
  rw [β_zero],
  refl,
end

/-- All the maps `α'` lie in the identity component. -/
lemma α'_component : 
  ∀ (i : ℕ) (hi : i > 2 * k), 
   component (α' U V C k hk i hi) = poset.idₕ _ := 
begin
  let c := λ (i : ℕ) (hi : i > 2 * k), component (α' U V C k hk i hi),
  change ∀ (i : ℕ) (hi : i > 2 * k), c i hi = poset.idₕ _,
  let u := λ (i : ℕ), ∀ (hi : i > 2 * k), 
                         c i hi = c (2 * k + 1) (2 * k).lt_succ_self,
  have u_zero : u 0 := λ hi, (nat.not_lt_zero _ hi).elim,
  have u_even : ∀ i, u (2 * i) → u (2 * i + 1) := 
  begin
    intros i hu hm,
    let hi : k ≤ i :=
      (mul_le_mul_left two_pos').mp (nat.le_of_succ_le_succ hm),
    by_cases h : k = i,
    { cases h, refl },
    replace hi := lt_of_le_of_ne hi h, 
    have hm' : 2 * i > 2 * k := 
      (mul_lt_mul_left two_pos').mpr hi,
    rw [← hu hm'], symmetry,
    apply π₀.sound,
    rintro ⟨⟨X,_⟩,_⟩,
    exact α_even_step i X  
  end,
  have u_odd : ∀ i, u (2 * i + 1) → u (2 * i + 2) := 
  begin
    intros i hu hm,
    let hi := @nat.div_le_div_right _ _ (nat.le_of_succ_le_succ hm) 2,
    rw [(half_misc k).1, (half_misc i).2.1] at hi,
    have hm' : 2 * i + 1 > 2 * k := 
      lt_of_le_of_lt ((mul_le_mul_left two_pos').mpr hi) (2 * i).lt_succ_self,
    rw [← hu hm'],
    apply π₀.sound,
    rintro ⟨⟨X,_⟩,_⟩,
    exact α_odd_step i X  
  end,
  have u_all := parity_induction u u_zero u_even u_odd,
  have h : (2 * n + 1) > 2 * k := 
   lt_of_le_of_lt ((mul_le_mul_left two_pos').mpr hk.1) (2 * n).lt_succ_self, 
  have : c (2 * n + 1) h = poset.idₕ _ := 
    congr_arg component (α'_last U V C k hk),
  intros i hi,
  rw [← this, u_all i hi, u_all (2 * n + 1) h]
end

/-- All the maps `β'` lie in the identity component. -/
lemma β'_component : 
  ∀ (i : ℕ) (hi : i ≤ 2 * k + 1), 
   component (β' U V C k hk i hi) = poset.idₕ _ := 
begin
  let c := λ (i : ℕ) (hi : i ≤ 2 * k + 1), component (β' U V C k hk i hi),
  let u := λ (i : ℕ), ∀ (hi : i ≤ 2 * k + 1), c i hi = idₕ _,
  change ∀ (i : ℕ), u i,
  have u_zero : u 0 := λ _, congr_arg component (β'_zero U V C k hk),
  have u_even : ∀ i, u (2 * i) → u (2 * i + 1) := 
  begin
    intros i hu hm,
    have hm' := le_trans (le_of_lt (2 * i).lt_succ_self) hm,
    rw [← hu hm'], symmetry,
    apply π₀.sound,
    rintro ⟨⟨X,_⟩,_⟩,
    exact β_even_step i X
  end,
  have u_odd : ∀ i, u (2 * i + 1) → u (2 * i + 2) := 
  begin
    intros i hu hm,
    have hm' := le_trans (le_of_lt (2 * i + 1).lt_succ_self) hm,
    rw [← hu hm'],
    apply π₀.sound,
    rintro ⟨⟨X,_⟩,_⟩,
    exact β_odd_step i X
  end,
  exact parity_induction u u_zero u_even u_odd
end

def α_middle := α' U V C k hk (2 * k + 1) (2 * k).lt_succ_self
def β_middle := β' U V C k hk (2 * k + 1) (le_refl _)

def α_middle' : (ℙ n) × (ℙ n) → (ℙ n) × (ℙ n) := 
λ AB, ⟨AB.1.filter_lt k.succ,AB.1.filter_ge k ⊔ AB.2⟩ 

def β_middle' : (ℙ n) × (ℙ n) → (ℙ n) × (ℙ n) := 
λ AB, ⟨AB.1 ⊔ AB.2.filter_lt k.succ,AB.2.filter_ge k⟩ 

lemma α_middle_val (X : cocomma (σ_slice U V) C) : 
 ((α_middle U V C k hk).val X).val.val.val = 
   α_middle' U V C k hk X.val.val.val := 
begin
  rcases X with ⟨⟨⟨⟨A,B⟩,_⟩,_⟩,_⟩, 
  change (prod.mk _ _) = (prod.mk _ _),
  rcases half_misc k with ⟨h₀,h₁,h₂,h₃⟩,
  rw [h₁, h₂]
end

lemma β_middle_val (X : cocomma (σ_slice U V) C) : 
 ((β_middle U V C k hk).val X).val.val.val = 
   β_middle' U V C k hk X.val.val.val := 
begin
  rcases X with ⟨⟨⟨⟨A,B⟩,_⟩,_⟩,_⟩, 
  change (prod.mk _ _) = (prod.mk _ _),
  rcases half_misc k with ⟨h₀,h₁,h₂,h₃⟩,
  rw [h₁, h₂]
end

def αβ_middle := 
 comp (α_middle U V C k hk) (β_middle U V C k hk)

def αβ_middle' : (ℙ n) × (ℙ n) → (ℙ n) × (ℙ n) := 
λ AB, ⟨(AB.1 ⊔ AB.2).filter_lt k.succ,
       (AB.1 ⊔ AB.2).filter_ge k⟩ 

lemma αβ_middle_val (X : cocomma (σ_slice U V) C) : 
 ((αβ_middle U V C k hk).val X).val.val.val = 
   αβ_middle' U V C k hk X.val.val.val := 
begin
  dsimp [αβ_middle, comp], 
  change ((α_middle U V C k hk).val _).val.val.val = _,
  rw[α_middle_val,β_middle_val,α_middle',β_middle'],
  change (prod.mk _ _) = (prod.mk _ _),
  apply prod.ext ; simp only [],
  { ext x, 
    simp [ℙ.mem_filter_lt, ℙ.mem_filter_ge, ℙ.mem_sup],
    tauto },
  { ext x, 
    simp [ℙ.mem_filter_lt, ℙ.mem_filter_ge, ℙ.mem_sup],
    tauto },
end

/-- This defines the basepoint to which we will contract -/
def cobase : cocomma (σ_slice U V) C := 
⟨⟨⟨⟨C.val.filter_lt k.succ,C.val.filter_ge k⟩,
  ℙ.filter_angle (le_refl k.succ) C.val⟩,
  (mem_omul U V _).mpr hk.2⟩,
  begin
    change _ ≤ _ ⊔ _,
    rw [ℙ.filter_sup (le_of_lt k.lt_succ_self) C.val], 
    exact le_refl C.val
  end⟩

lemma cocomma_order (X Y : cocomma (σ_slice U V) C) : 
  X ≤ Y ↔ X.val.val.val ≤ Y.val.val.val :=
begin
  rcases X with ⟨⟨⟨⟨A,B⟩,u₀⟩,u₁⟩,u₂⟩,
  rcases Y with ⟨⟨⟨⟨C,D⟩,v₀⟩,v₁⟩,v₂⟩,
  let X₀ : (ℙ n) × (ℙ n) := ⟨A,B⟩,
  let Y₀ : (ℙ n) × (ℙ n) := ⟨C,D⟩,
  change (X₀ ≤ Y₀) ↔ (A ≤ C ∧ B ≤ D),
  dsimp [X₀, Y₀], refl
end

lemma αβ_middle_ge (X : cocomma (σ_slice U V) C) : 
  (cobase U V C k hk) ≤ ((αβ_middle U V C k hk).val X) := 
begin 
  let h := cocomma_order U V C k hk,
  let hh := h (cobase U V C k hk) ((αβ_middle U V C k hk).val X),
  rw [hh, αβ_middle_val, αβ_middle', cobase],
  rcases X with ⟨⟨⟨⟨A,B⟩,h₀⟩,h₁⟩,h₂⟩,
  let D := A ⊔ B,
  change C.val ≤ D at h₂, 
  change (C.val.filter_lt k.succ) ≤ (D.filter_lt k.succ) ∧ 
         (C.val.filter_ge k) ≤ (D.filter_ge k),
  split; intros x hx,
  { rw[ℙ.mem_filter_lt] at hx ⊢, exact ⟨h₂ hx.1, hx.2⟩ }, 
  { rw[ℙ.mem_filter_ge] at hx ⊢, exact ⟨h₂ hx.1, hx.2⟩ } 
end

end with_k

theorem final : finalₕ (σ_slice U V) := 
begin
  intro C,
  let M := (cocomma (σ_slice U V) C),
  change nonempty (equivₕ M unit),
  let f : hom M unit := const M unit.star,
  rcases k_exists U V C with ⟨k, hk⟩,
  let m := cobase U V C k hk,
  let g : hom unit M := const unit m,
  have hfg : comp f g = id unit := by { ext t },
  have hgf : component (comp g f) = idₕ _ := 
  begin 
   let gf₀ : hom M M := comp g f,
   let gf₁ : hom M M := αβ_middle U V C k hk,
   let gf₂ : hom M M := poset.id _,
   have : gf₀ ≤ gf₁ := λ X, αβ_middle_ge U V C k hk X,
   rw [π₀.sound this],
   let u := component (α_middle U V C k hk),
   let v := component (β_middle U V C k hk),
   have huv : component gf₁ = compₕ u v := rfl,
   have : u = idₕ _ := α'_component U V C k hk (2 * k + 1) _,
   rw [this] at huv,
   have : v = idₕ _ := β'_component U V C k hk (2 * k + 1) _,
   rw [this, comp_idₕ] at huv,
   exact huv,
  end,
  let e : equivₕ M unit := 
  { to_fun := component f, inv_fun := component g,
    left_inv := hgf, right_inv := congr_arg component hfg },
  exact ⟨e⟩ 
end

end σ_slice

end itloc

