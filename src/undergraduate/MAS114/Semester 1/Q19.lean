import data.int.modeq data.fintype data.zmod.basic
import tactic.linarith

namespace MAS114
namespace exercises_1
namespace Q19

def f (n : ℤ) : ℤ := n * (n + 1) * (n + 2) * (n + 3)

lemma f_mod (p n₀ n₁ : ℤ) (h0 : n₀ ≡ n₁ [ZMOD p]) : f n₀ ≡ f n₁ [ZMOD p] := 
begin
 have h1 : n₀ + 1 ≡ n₁ + 1 [ZMOD p] := int.modeq.modeq_add h0 rfl,
 have h2 : n₀ + 2 ≡ n₁ + 2 [ZMOD p] := int.modeq.modeq_add h0 rfl,
 have h3 : n₀ + 3 ≡ n₁ + 3 [ZMOD p] := int.modeq.modeq_add h0 rfl,
 have h01 : n₀ * (n₀ + 1) ≡ n₁ * (n₁ + 1) [ZMOD p] := 
  int.modeq.modeq_mul h0 h1,
 have h02 : n₀ * (n₀ + 1) * (n₀ + 2) ≡ n₁ * (n₁ + 1) * (n₁ + 2) [ZMOD p] := 
  int.modeq.modeq_mul h01 h2,
 exact int.modeq.modeq_mul h02 h3,
end

lemma f_mod_3 (n : ℕ) : f n ≡ 0 [ZMOD 3] := 
begin
 have three_pos : (3 : ℤ) > 0 := dec_trivial,
 rcases int.modeq.exists_unique_equiv_nat n three_pos with ⟨r,⟨r_is_lt,r_equiv⟩⟩,
 let e := (f_mod 3 r n r_equiv).symm,
 suffices : f r ≡ 0 [ZMOD 3],
 {exact e.trans this,},
 rcases r with _ | _ | _ | r0; rw[f]; try {refl},
 {exfalso,
  have : (3 : ℤ) = ((3 : ℕ) : ℤ) := rfl,
  rw[this] at r_is_lt,
  let h0 := int.coe_nat_lt.mp r_is_lt,
  replace h0 := nat.lt_of_succ_lt_succ h0,
  replace h0 := nat.lt_of_succ_lt_succ h0,
  replace h0 := nat.lt_of_succ_lt_succ h0,
  exact nat.not_lt_zero r0 h0,
 }
end

lemma f_mod_8 (n : ℕ) : f n ≡ 0 [ZMOD 8] := 
begin
 have eight_pos : (8 : ℤ) > 0 := dec_trivial,
 rcases int.modeq.exists_unique_equiv_nat n eight_pos with ⟨r,⟨r_is_lt,r_equiv⟩⟩,
 let e := (f_mod 8 r n r_equiv).symm,
 suffices : f r ≡ 0 [ZMOD 8],
 {exact e.trans this,},
 rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r0;
  rw[int.modeq,f]; try {norm_num},
 {exfalso,
  have : (8 : ℤ) = ((8 : ℕ) : ℤ) := rfl,
  rw[this] at r_is_lt,
  let h0 := int.coe_nat_lt.mp r_is_lt,
  repeat { replace h0 := nat.lt_of_succ_lt_succ h0 },
  exact nat.not_lt_zero r0 h0,
 }
end

lemma f_mod_24 (n : ℕ) : f n ≡ 0 [ZMOD 24] := 
begin
 let i3 : ℤ := 3,
 let i8 : ℤ := 8,
 have : (24 : ℤ) = i3 * i8 := rfl,
 rw[this],
 have cp : nat.coprime i3.nat_abs i8.nat_abs := dec_trivial,
 exact (int.modeq.modeq_and_modeq_iff_modeq_mul cp).mp ⟨f_mod_3 n,f_mod_8 n⟩,
end

/- ----------- Part (ii) ------------- -/

def h {R : Type} [comm_ring R] (a b c d : R) : R := 
 (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) 

lemma h_shift {R : Type} [comm_ring R] (a b c d : R) : 
 h a b c d = h (a - d) (b - d) (c - d) 0 := 
begin
 have e : ∀ x y z : R, (x + -z) + -(y + -z) = x + -y := 
  by {intros, ring},
 dsimp[h],
 rw[neg_zero,add_zero,add_zero,add_zero],
 rw[e,e,e],
end

lemma h_zero_shift {R : Type} [comm_ring R] : 
 (∀ a b c : R, h a b c 0 = 0) → (∀ a b c d : R, h a b c d = 0) := 
  λ p a b c d, (h_shift a b c d).trans (p (a - d) (b - d) (c - d))

lemma h_zero_3 : ∀ a b c d : zmod 3, h a b c d = 0 := 
 h_zero_shift dec_trivial

lemma h_zero_4 : ∀ a b c d : zmod 4, h a b c d = 0 :=
 h_zero_shift dec_trivial

lemma h_map {R S : Type} [comm_ring R] [comm_ring S] 
 (φ : R → S) [is_ring_hom φ] (a b c d : R) :
  φ (h a b c d) = h (φ a) (φ b) (φ c) (φ d) := 
begin
 dsimp[h],
 let em := @is_ring_hom.map_mul R S _ _ φ _,
 let ea := @is_ring_hom.map_add R S _ _ φ _,
 let en := @is_ring_hom.map_neg R S _ _ φ _,
 rw[em,em,em,em,em],
 rw[ea,ea,ea,ea,ea,ea],
 rw[en,en,en],
end

lemma h_zero_mod (p : ℕ+) :
 (∀ a b c d : zmod p, h a b c d = 0) → 
  (∀ a b c d : ℤ, h a b c d ≡ 0 [ZMOD p]) := 
begin
 intros e a b c d,
 apply (@zmod.eq_iff_modeq_int p _ _).mp,
 let π : ℤ → (zmod p) := int.cast,
 exact calc 
  π (h a b c d) = h (π a) (π b) (π c) (π d) : 
   by rw[@h_map ℤ (zmod p) _ _ π _]
  ... = 0 : e (π a) (π b) (π c) (π d),
end

lemma h_zero_12 : ∀ (a b c d : ℤ), h a b c d ≡ 0 [ZMOD 12] := 
begin
 intros,
 let i3 : ℤ := 3,
 let i4 : ℤ := 4,
 let h3 := h_zero_mod 3 h_zero_3 a b c d,
 let h4 := h_zero_mod 4 h_zero_4 a b c d,
 have : (12 : ℤ) = i3 * i4 := rfl,
 rw[this],
 have cp : nat.coprime i3.nat_abs i4.nat_abs := dec_trivial,
 exact (int.modeq.modeq_and_modeq_iff_modeq_mul cp).mp ⟨h3,h4⟩,
end

/-
 Here are partial results for a more general case
-/

def π (m : ℕ+) : ℤ → (zmod m) := int.cast

instance π_hom (m : ℕ+) : is_ring_hom (π m) :=
 by { dsimp[π], apply_instance }

def F (n : ℕ) := { ij : (fin n) × (fin n) // ij.1.val < ij.2.val }

instance (n : ℕ) : fintype (F n) := by { dsimp[F], apply_instance,}

def g (n : ℕ) (u : (fin n) → ℤ) : ℤ := 
 (@finset.univ (F n) _).prod (λ ij, (u ij.val.2) - (u ij.val.1))

def g_mod (n : ℕ) (m : ℕ+) (u : (fin n) → ℤ) : zmod m := 
 (@finset.univ (F n) _).prod (λ ij, (π m (u ij.val.2)) - (π m (u ij.val.1)))

lemma g_mod_spec (n : ℕ) (m : ℕ+) (u : (fin n) → ℤ) : 
 π m (g n u) = g_mod n m u := 
begin
 dsimp[g,g_mod],
 let mn := @is_ring_hom.map_neg ℤ (zmod m) _ _ (π m) _,
 let ma := @is_ring_hom.map_add ℤ (zmod m) _ _ (π m) _,
 conv
 begin
  to_rhs,congr,skip,funext,rw[← mn,← ma],
 end,
 apply (finset.prod_hom (π m)).symm,
end

lemma must_repeat (n : ℕ) (m : ℕ+) (m_lt_n : m.val < n)
 (u : fin n → ℤ) : ∃ i j : fin n, (i.val < j.val ∧ (π m (u i)) = (π m (u j))) := 
begin
 let P := { ij : (fin n) × (fin n) // ij.1 ≠ ij.2 },
 let p : P → Prop := λ ij, π m (u ij.val.1) = π m (u ij.val.2),
 let q := exists ij, p ij,
 by_cases h : q,
 {
  rcases h with ⟨⟨⟨i,j⟩,i_ne_j⟩,eq_mod⟩,
  change i ≠ j at i_ne_j,
  let i_ne_j_val : i.val ≠ j.val := λ e,i_ne_j (fin.eq_of_veq e),
  change (π m (u i)) = (π m (u j)) at eq_mod,
  by_cases hij : i.val < j.val,
  {use i,use j,exact ⟨hij,eq_mod⟩},
  {let hij' := lt_of_le_of_ne (le_of_not_gt hij) i_ne_j_val.symm,
   use j,use i,exact ⟨hij',eq_mod.symm⟩ 
  } 
 },{
  exfalso,
  let v : fin n → zmod m := λ i, π m (u i),
  have v_inj : function.injective v := 
  begin 
   intros i j ev,
   by_cases hij : i = j,
   {exact hij},
   {exfalso,exact h ⟨⟨⟨i,j⟩,hij⟩,ev⟩,
   }
  end,  
  let e := calc
   n = fintype.card (fin n) : (fintype.card_fin n).symm
   ... ≤ fintype.card (zmod m) : fintype.card_le_of_injective v v_inj
   ... = m.val : fintype.card_fin m
   ... < n : m_lt_n,
  exact lt_irrefl _ e,
 }
end

lemma g_mod_zero (n : ℕ) (m : ℕ+) (m_lt_n : m.val < n)
 (u : fin n → ℤ) : g_mod n m u = 0 := 
begin
 rcases must_repeat n m m_lt_n u with ⟨i,j,i_lt_j,e⟩,
 dsimp[π] at e,
 let ij : F n := ⟨⟨i,j⟩,i_lt_j⟩,
 dsimp[g_mod],
 apply finset.prod_eq_zero (finset.mem_univ ij),
 dsimp[ij],
 change π m (u i) = π m (u j) at e,
 rw[e,add_right_neg],
end

end Q19
end exercises_1
end MAS114