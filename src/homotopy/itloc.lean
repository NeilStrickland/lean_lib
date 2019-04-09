import data.list.basic
import data.fin
import data.fintype
import order.bounded_lattice
import algebra.big_operators
import data.fin_extra 

import tactic.squeeze
namespace lattice
open lattice 

instance bounded_distrib_lattice_of_decidable_linear_order 
  {α : Type*} [decidable_linear_order α]
  (top : α) (le_top : ∀ a, a ≤ top)
  (bot : α) (bot_le : ∀ a, bot ≤ a) :
  bounded_distrib_lattice α := {
   top          := top,     bot          := bot,
   le_top       := le_top,  bot_le       := bot_le,
   .. (lattice.distrib_lattice_of_decidable_linear_order)
  }

instance wtb_bdl_of_dlo (α : Type*) [decidable_linear_order α] :
 bounded_distrib_lattice (with_top (with_bot α)) := 
  @lattice.bounded_distrib_lattice_of_decidable_linear_order 
   (with_top (with_bot α)) _ 
    (has_top.top _) (@lattice.le_top _ _)
    (has_bot.bot _) (@lattice.bot_le _ _)

instance inf_monoid {α : Type*} [semilattice_inf_top α] :
 comm_monoid α := {
    mul := has_inf.inf,
    one := has_top.top α,
    one_mul := @top_inf_eq α _,
    mul_one := @inf_top_eq α _,
    mul_comm := @inf_comm α _,
    mul_assoc := @inf_assoc α _,
}

instance sup_monoid {α : Type*} [semilattice_sup_bot α] :
 comm_monoid α := {
    mul := has_sup.sup,
    one := has_bot.bot α,
    one_mul := @bot_sup_eq α _,
    mul_one := @sup_bot_eq α _,
    mul_comm := @sup_comm α _,
    mul_assoc := @sup_assoc α _,
}

end lattice

namespace itloc

variable (n : ℕ)

def 𝕀 := fin n

instance 𝕀.fintype : fintype (𝕀 n) := by {dsimp[𝕀],apply_instance}
instance 𝕀.deceq : decidable_eq (𝕀 n) := by {dsimp[𝕀],apply_instance}

instance 𝕀.dlo : decidable_linear_order (𝕀 n) := 
  (@fin.decidable_linear_order n).

def ℙ := finset (𝕀 n)
instance ℙ.fintype : fintype (ℙ n) := by {dsimp[ℙ],apply_instance}
instance ℙ.deceq : decidable_eq (ℙ n) := by {dsimp[ℙ],apply_instance}
instance : has_mem (𝕀 n) (ℙ n) := by {dsimp[𝕀,ℙ], apply_instance }

def ℙ.dl : lattice.distrib_lattice (ℙ n) := 
 by {dsimp[ℙ],apply_instance}.

instance ℙ.bdl : lattice.bounded_distrib_lattice (ℙ n) := {
  bot := finset.empty,
  top := finset.univ,
  le_top := λ (A : finset (𝕀 n)),
   begin change A ⊆ finset.univ,intros i _,exact finset.mem_univ i end,
  bot_le := λ (A : finset (𝕀 n)),
   begin change finset.empty ⊆ A,intros i h,
    exact (finset.not_mem_empty i h).elim end,
  .. (ℙ.dl n)
}

instance ℙ.decidable_le : decidable_rel (λ (A B : ℙ n), A ≤ B) := 
 λ (A B : finset (𝕀 n)), by { change decidable (A ⊆ B), apply_instance, }

variable {n} 

def angle : (ℙ n) → (ℙ n) → Prop := 
 λ A B, ∀ (i j : 𝕀 n), i ∈ A → j ∈ B → i ≤ j

instance : ∀ (A B : ℙ n), decidable (angle A B) := 
 by {dsimp[angle],apply_instance}

lemma bot_angle (B : ℙ n) : angle ⊥ B := 
 λ i j i_in_A j_in_B, (finset.not_mem_empty i i_in_A).elim

lemma angle_bot (A : ℙ n) : angle A ⊥ := 
 λ i j i_in_A j_in_B, (finset.not_mem_empty j j_in_B).elim

lemma split_angle {A B : ℙ n} (k : 𝕀 n) 
 (hA : ∀ i, i ∈ A → i ≤ k) (hB : ∀ j, j ∈ B → k ≤ j) : angle A B := 
  λ i j i_in_A j_in_B, le_trans (hA i i_in_A) (hB j j_in_B)

lemma angle_iff {A B : ℙ n} : 
 angle A B ↔ (A = ⊥ ∧ B = ⊥) ∨ 
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

def is_upper : finset (ℙ n) → Prop := 
 λ (U : finset (ℙ n)), ∀ (A B : ℙ n) (A_le_B : A ≤ B) (A_in_U : A ∈ U), B ∈ U 

lemma is_upper_empty : is_upper (@finset.empty (ℙ n)) := 
 λ A B A_le_B A_in_U,(finset.not_mem_empty A A_in_U).elim

lemma is_upper_univ : is_upper (@finset.univ (ℙ n) _) := 
 λ A B A_le_B A_in_U,(finset.mem_univ B)

lemma is_upper_union (U V : finset (ℙ n)) (hU : is_upper U) (hV : is_upper V) : 
  is_upper (U ∪ V) := 
  λ A B A_le_B A_in_UV, 
  begin
   rcases (finset.mem_union.mp A_in_UV) with A_in_U | A_in_V,
   {exact finset.mem_union_left  V (hU A B A_le_B A_in_U)},
   {exact finset.mem_union_right U (hV A B A_le_B A_in_V)},
  end

lemma is_upper_inter (U V : finset (ℙ n)) (hU : is_upper U) (hV : is_upper V) : 
  is_upper (U ∩ V) := 
  λ A B A_le_B A_in_UV, 
  begin
   replace A_in_UV := finset.mem_inter.mp  A_in_UV,
   apply finset.mem_inter.mpr,
   split,
   {exact (hU A B A_le_B A_in_UV.left)},
   {exact (hV A B A_le_B A_in_UV.right)},
  end

variable (n)

def ℚ := { U : finset (ℙ n) // is_upper U }

instance ℙ_mem_ℚ : has_mem (ℙ n) (ℚ n) := ⟨λ A  U, A ∈ U.val⟩ 

def ℚ.distrib (U V W : finset (ℙ n)) : 
 U ∩ (V ∪ W) ⊆ (U ∩ V) ∪ (U ∩ W) := 
begin 
 intros A h,
 rw[finset.mem_inter,finset.mem_union] at h,
 rw[finset.mem_union,finset.mem_inter,finset.mem_inter],
 rcases h with ⟨hU,hV | hW⟩,
 exact or.inl ⟨hU,hV⟩,
 exact or.inr ⟨hU,hW⟩
end

instance ℚ_bdl : lattice.bounded_distrib_lattice (ℚ n) := {
  le := λ U V, V.val ⊆ U.val,
  le_refl := λ U, le_refl U.val,
  le_antisymm := λ U V (h0 : V.val ⊆ U.val) (h1 : U.val ⊆ V.val),
                   begin apply subtype.eq, exact le_antisymm h1 h0, end,
  le_trans := λ U V W (h0 : V.val ⊆ U.val) (h1 : W.val ⊆ V.val), 
                 @le_trans (finset (ℙ n)) _ W.val V.val U.val h1 h0,
  bot := ⟨finset.univ,is_upper_univ⟩,
  top := ⟨finset.empty,is_upper_empty⟩,
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
    ℚ.distrib n U.val V.val W.val h,
}

variable {n}

def ℚ.u : ℙ n → ℚ n := 
 λ A, ⟨finset.univ.filter (λ B, A ≤ B),
  begin intros B C B_le_C A_le_B,
   replace A_le_B := (finset.mem_filter.mp A_le_B).right,
   exact finset.mem_filter.mpr ⟨finset.mem_univ C,le_trans A_le_B B_le_C⟩,
  end
 ⟩

def omul0 (U V : finset (ℙ n)) : finset ((ℙ n) × (ℙ n)) := 
 U.bind (λ A, (V.filter (λ B,angle A B)).image (λ B, prod.mk A B))

def mul0 (U V : finset (ℙ n)) : finset (ℙ n) := 
 U.bind (λ A, (V.filter (λ B,angle A B)).image (λ B, A ⊔ B))

lemma mem_mul0 (U V : finset (ℙ n)) (C : ℙ n) : 
 (C ∈ (mul0 U V)) ↔ ∃ A B, A ∈ U ∧ B ∈ V ∧ (angle A B) ∧ (A ⊔ B = C) := 
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
  exact ⟨A_in_U,C_in_V,bot_angle C,lattice.bot_sup_eq⟩, 
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
  exact ⟨C_in_U,B_in_V,angle_bot C,lattice.sup_bot_eq⟩, 
 } 
end

lemma is_upper_mul0 (U V : finset (ℙ n)) (hU : is_upper U) (hV : is_upper V) : is_upper (mul0 U V) := 
begin
 intros C C' C_le_C' C_in_mul,
 rcases (mem_mul0 U V C).mp C_in_mul with ⟨A,B,A_in_U,B_in_V,A_angle_B,e⟩,
 apply (mem_mul0 U V C').mpr,
 rcases (angle_iff.mp A_angle_B) with ⟨A_empty,B_empty⟩ | ⟨k,⟨hA,hB⟩⟩,
 {use A, use C',
  have B_le_C' : ⊥ ≤ C' := lattice.bot_le,
  rw[← B_empty] at B_le_C',
  have C'_in_V : C' ∈ V := hV B C' B_le_C' B_in_V,
  have A_angle_C' : angle A C' := A_empty.symm ▸ (bot_angle C'),
  have e : ⊥ ⊔ C' = C' := lattice.bot_sup_eq,
  rw[← A_empty] at e,
  exact ⟨A_in_U,C'_in_V,A_angle_C',e⟩, 
 },{
  let A' := C'.filter (λ i, i ≤ k),
  let B' := C'.filter (λ j, k ≤ j),
  have A'_angle_B' : angle A' B' := λ i j i_in_A' j_in_B', 
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
    have A_angle_C : angle A C := λ i k i_in_A k_in_C, 
     AB_angle_C i k (A_le_AB i_in_A) k_in_C,
    have B_angle_C : angle B C := λ j k j_in_B k_in_C, 
     AB_angle_C j k (B_le_AB j_in_B) k_in_C,
    let BC := B ⊔ C,
    have A_angle_BC : angle A BC := begin
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
    have A_angle_B : angle A B := λ i j i_in_A j_in_B, 
     A_angle_BC i j i_in_A (B_le_BC j_in_B),
    have A_angle_C : angle A C := λ i k i_in_A k_in_C, 
     A_angle_BC i k i_in_A (C_le_BC k_in_C),
    let AB := A ⊔ B,
    have AB_angle_C : angle AB C := begin
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

end itloc

