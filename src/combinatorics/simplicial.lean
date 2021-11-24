/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.nat.choose data.fintype.basic
import data.fin_extra
import tactic.squeeze tactic.linarith

namespace simplicial

namespace infinite 

def δ (i j : ℕ) : ℕ := if j < i then j else j + 1

def σ (i j : ℕ) : ℕ := if j ≤ i then j else j - 1

lemma δ_zero (j : ℕ) : δ 0 j = j + 1 := if_neg (nat.not_lt_zero j)

lemma σ_zero (j : ℕ) : σ 0 j = j - 1 := 
by { cases j, refl, exact if_neg (nat.not_succ_le_zero j) }

lemma δ_ge (i j : ℕ) : j ≤ δ i j := 
by { dsimp[δ], split_ifs with h, exact le_refl j, exact le_of_lt j.lt_succ_self }

lemma σ_le (i j : ℕ) : σ i j ≤ j := 
by { dsimp[σ], split_ifs with h, exact le_refl j, exact j.pred_le }

lemma δδ (i j : ℕ) (hji : j ≤ i) : (δ j) ∘ (δ i) = δ (i + 1) ∘ (δ j) := 
begin
  ext k, 
  simp only [function.comp_app, δ],
  { by_cases hkj : k < j,
    { have hki : k < i := lt_of_lt_of_le hkj hji, 
      rw [if_pos hki, if_pos hkj, if_pos (lt_trans hki i.lt_succ_self)] },
    { by_cases hki : k < i, 
      { rw [if_pos hki, if_neg hkj, if_pos (nat.succ_lt_succ hki)] }, 
      { rw [if_neg hki, if_neg hkj, if_neg (λ h, hki (nat.lt_of_succ_lt_succ h))],
        rw [if_neg (λ h, hkj (lt_trans k.lt_succ_self h))] } } }
end

lemma σσ (i j : ℕ) (hij : i ≤ j) : (σ j) ∘ (σ i) = (σ  i) ∘ (σ (j + 1)) := 
begin
  ext k,
  simp only [function.comp_app, σ],
  { by_cases hki : k ≤ i,
    { have hkj : k ≤ j := le_trans hki hij, 
      rw [if_pos hki, if_pos hkj, if_pos (le_trans hkj (le_of_lt j.lt_succ_self)), if_pos hki] },
    { rw [if_neg hki],
      have hki' := lt_of_not_ge hki,
      cases k with k₀, {exfalso, exact nat.not_lt_zero i hki'},
      have hk : k₀.succ - 1 = k₀ := nat.pred_succ k₀, rw [hk],
      by_cases hkj : k₀ ≤ j, 
      { rw [if_pos hkj, if_pos (nat.succ_le_succ hkj), if_neg hki, hk] }, 
      { rw [if_neg hkj, if_neg (λ h, hkj (nat.le_of_succ_le_succ h))],
        rw [if_neg (not_le_of_gt (lt_of_le_of_lt hij (lt_of_not_ge hkj)))] } } }
end

lemma σδ₀ (i j : ℕ) (hij : i + 1 < j) : (σ i) ∘ (δ j) = (δ (j - 1)) ∘ (σ i) := 
begin
  ext k,
  simp only [function.comp_app, σ, δ],
  by_cases hki : k ≤ i,
  { rw [if_pos hki, if_pos (lt_trans (lt_of_le_of_lt hki i.lt_succ_self) hij), if_pos hki],
    rw [if_pos (lt_of_le_of_lt hki (nat.lt_pred_iff.mpr hij) : k < j - 1)] },
  { rw [if_neg hki], 
    have hk : k ≠ 0 := λ h, (h ▸ hki) (nat.zero_le i),
    have hj : j ≠ 0 := λ h, nat.not_lt_zero (i + 1) (h ▸ hij),
    have hj' : (j - 1).succ = j := nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hj),
    have hk' : (k - 1).succ = k := nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hk),
    by_cases hkj : k < j,
    { have hkj' : k - 1 < j - 1 := nat.pred_lt_pred hk hkj,
      rw [if_pos hkj, if_neg hki, if_pos hkj'] },
    { rw [if_neg hkj, if_neg (λ h, hki (le_trans (le_of_lt k.lt_succ_self) h))],
      have : ¬ (k - 1 < j - 1) := λ h, 
      begin 
       replace h := nat.succ_lt_succ h,
       rw [hj', hk'] at h, exact hkj h,
      end,
      rw [if_neg this, nat.add_sub_cancel],
      have : k - 1 + 1 = k := hk', rw [this] } }
end

lemma σδ₁ (i : ℕ) : (σ i) ∘ (δ i) = id := 
begin
  ext k,
  simp only [function.comp_app, σ, δ, id],
  by_cases hk : k < i,
  { rw [if_pos hk, if_pos (le_of_lt hk)] }, 
  { rw [if_neg hk], 
    rw [if_neg (λ h, hk (lt_of_lt_of_le k.lt_succ_self h)), nat.add_sub_cancel] }  
end

lemma σδ₂ (i : ℕ) : (σ i) ∘ (δ (i + 1)) = id := 
begin
  ext k,
  simp only [function.comp_app, σ, δ, id],
  by_cases hk : k < i + 1,
  { rw [if_pos hk, if_pos (nat.le_of_lt_succ hk)] }, 
  { rw [if_neg hk], 
    have : ¬ (k + 1 ≤ i) := λ h, 
      hk (lt_trans (lt_of_lt_of_le k.lt_succ_self h) i.lt_succ_self),
    rw [if_neg this, nat.add_sub_cancel] }  
end

lemma σδ₃ (i j : ℕ) (hji : j < i) : (σ i) ∘ (δ j) = (δ j) ∘ (σ (i - 1)) := 
begin
  cases i with i₀, { cases hji },
  replace hji := nat.le_of_lt_succ hji,
  ext k,
  simp only [function.comp_app, σ, δ, nat.succ_eq_add_one, nat.add_sub_cancel],
  by_cases hkj : k < j,
  { have hki : k < i₀ := lt_of_lt_of_le hkj hji,
    rw [if_pos hkj, if_pos (le_of_lt (lt_trans hki i₀.lt_succ_self)), 
        if_pos (le_of_lt hki), if_pos hkj] },
  { rw [if_neg hkj, nat.add_sub_cancel], 
    by_cases hki : k ≤ i₀,
    { rw [if_pos hki, if_pos (nat.succ_le_succ hki), if_neg hkj], },
    { rw [if_neg hki, if_neg (λ h, hki (nat.le_of_succ_le_succ h))],
      cases k with k₀, {exfalso, exact hki (nat.zero_le i₀)},
      have : k₀.succ - 1 = k₀ := nat.pred_succ k₀, rw [this],
      have : ¬ (k₀ < j) := λ h, hki (lt_of_lt_of_le h hji),
      rw [if_neg this] } }
end

lemma σδ (i j : ℕ) : (σ i) ∘ (δ j) = 
  if (j < i) then (δ j) ∘ (σ (i - 1)) 
  else ( if j ≤ i + 1 then id
  else δ (j - 1) ∘ (σ i)) := 
begin
  split_ifs with h₀ h₁,
  { exact σδ₃ i j h₀ },
  { by_cases h₂ : j ≤ i, 
    { rw [le_antisymm h₂ (le_of_not_gt h₀), σδ₁] },
    { rw [le_antisymm h₁ (lt_of_not_ge h₂), σδ₂] } },
  { exact σδ₀ i j (lt_of_not_ge h₁) }
end

lemma σδ_pred (i : ℕ) : (σ i.pred) ∘ (δ i) = id := 
begin
  cases i with i₀,
  { simp[σδ, lt_irrefl], },
  { have : ¬ (1 < 0) := dec_trivial,
    simp[σδ, nat.succ_eq_add_one, le_refl i₀, this] }
end

lemma δσ_pred {i k : ℕ} (h : k ≠ i) : δ i (σ i.pred k) = k := 
begin
  cases i with i₀,
  { cases k with k₀, { exfalso, exact h rfl },
    rw [nat.pred_zero, 
        simplicial.infinite.δ_zero, simplicial.infinite.σ_zero,
        nat.succ_eq_add_one, nat.add_sub_cancel] },
  { rw [nat.pred_succ, simplicial.infinite.σ, simplicial.infinite.δ],
    by_cases h' : k ≤ i₀,
    { rw [if_pos h', if_pos (nat.lt_succ_of_le h')] },
    { rw [if_neg h'],
      rw [if_neg (not_lt_of_ge (nat.le_pred_of_lt (lt_of_le_of_ne 
             (nat.succ_le_of_lt (lt_of_not_ge h')) h.symm)))],
      cases k with k₀,
      { exfalso, exact h' (nat.zero_le i₀) },
      { rw [nat.succ_eq_add_one, nat.add_sub_cancel] } } } 
end

lemma δ_bound {n i k : ℕ} (hi : i < n + 1) (hk : k < n) : δ i k < n + 1 := 
begin
  rw [δ], split_ifs, 
  { exact lt_trans hk n.lt_succ_self },
  { exact nat.succ_lt_succ hk }
end

lemma δ_bound' (i k : ℕ) : k ≤ δ i k ∧ δ i k ≤ k + 1 := 
begin
  dsimp [δ],
  by_cases h : k < i,
  { rw [if_pos h], exact ⟨le_refl k,le_of_lt k.lt_succ_self⟩  },
  { rw [if_neg h], exact ⟨le_of_lt k.lt_succ_self, le_refl _⟩ }
end

lemma σ_bound {n i k : ℕ} (hi : i < n) (hk : k < n + 1) : σ i k < n := 
begin
  rw [σ], split_ifs,
  { exact lt_of_le_of_lt h hi },
  { have : k ≠ 0 := λ hz, (hz ▸ h) (nat.zero_le i),
    exact nat.pred_lt_pred this hk }
end

lemma σ_bound' (i k : ℕ) : k - 1 ≤ σ i k ∧ σ i k ≤ k := 
begin
  dsimp [σ],
  by_cases h : k ≤ i,
  { rw [if_pos h], exact ⟨nat.pred_le k,le_refl k⟩ },
  { rw [if_neg h], exact ⟨le_refl _, nat.pred_le k⟩ }
end

lemma δ_inj (i : ℕ) : function.injective (δ i) := λ j₀ j₁ e, 
begin
  replace e := congr_arg (σ i) e, 
  have := function.comp_app (σ i) (δ i),
  rw [← this, ← this, σδ₁, id] at e, exact e
end

lemma σ_surj (i : ℕ) : function.surjective (σ i) := λ j, 
begin
  use δ i j, rw [← function.comp_app (σ i) (δ i), σδ₁, id]
end

lemma δ_ne (i k : ℕ) : δ i k ≠ i :=
begin
  rw [δ], split_ifs with h; intro e; rw [← e] at h,
  { exact lt_irrefl k h }, { exact h k.lt_succ_self }
end

lemma δ_image (i j : ℕ) : (∃ k, δ i k = j) ↔ j ≠ i := 
begin
  split,
  { rintro ⟨k,e⟩, rw [← e], intro e', exact δ_ne i k e' },
  { intro hne, 
    by_cases hle : j ≤ i,
    { use j, rw [δ, if_pos (lt_of_le_of_ne hle hne)] }, 
    { have hlt := lt_of_not_ge hle,
      cases j with j₀, { exfalso, exact nat.not_lt_zero i hlt },
      replace hlt := nat.le_of_lt_succ hlt,
      use j₀, 
      rw [δ, if_neg (not_lt_of_ge hlt)] } }
end

lemma σ_ker_aux (i j k : ℕ) : j < k ∧ (σ i j = σ i k) → j = i ∧ k = i + 1 := 
begin
 rintro ⟨hlt,he⟩,
 dsimp [σ] at he, split_ifs at he with h₀ h₁ h₃,
 { exfalso, rw[he] at hlt, exact lt_irrefl k hlt },
 { rw [he] at *, 
   rw [le_antisymm (nat.le_pred_of_lt (lt_of_not_ge h₁)) h₀] at *,
   cases k with k₀, {cases hlt},
   have : k₀.succ - 1 = k₀ := nat.add_sub_cancel k₀ 1,
   rw [this] at *, split; refl },
 { exfalso, rw[← he] at hlt, exact (not_le_of_gt hlt) (nat.sub_le j 1) },
 { exfalso,
   cases j with j₀, { exfalso, exact h₀ i.zero_le },
   cases k with k₀, { exfalso, exact h₃ i.zero_le },
   simp only [nat.succ_eq_add_one, nat.add_sub_cancel] at he,
   rw [he] at hlt, exact lt_irrefl _ hlt }
end

lemma σ_ker {i j k : ℕ} : (σ i j = σ i k) ↔ 
  (j = k ∨ (j = i ∧ k = i + 1) ∨ (j = i + 1 ∧ k = i)) := 
begin
  split,
  { intro he, 
    by_cases h₀ : j = k, 
    { left, exact h₀ },
    { by_cases h₁ : j < k,
      { right, left, exact σ_ker_aux i j k ⟨h₁,he⟩, },
      { change j ≠ k at h₀, 
        have h₂ : k < j := lt_of_le_of_ne (le_of_not_gt h₁) h₀.symm,
        right, right, exact (σ_ker_aux i k j ⟨h₂,he.symm⟩).symm } } },
  { rintro (h₀ | ⟨h₁,h₂⟩ | ⟨h₃,h₄⟩),
    { rw [h₀] }, 
    { rw [h₁, h₂, σ, σ, if_pos (le_refl i), 
          if_neg (not_le_of_gt i.lt_succ_self), nat.add_sub_cancel] },
    { rw [h₃, h₄, σ, σ, if_pos (le_refl i), 
          if_neg (not_le_of_gt i.lt_succ_self), nat.add_sub_cancel] } }
end

lemma σ_pred_inj {i j k : ℕ} (hj : j ≠ i) (hk : k ≠ i)
  (he : σ i.pred j = σ i.pred k) : j = k := 
begin
  rcases σ_ker.mp he with ⟨⟨h₀⟩⟩ | ⟨⟨h₁⟩,⟨h₂⟩⟩ | ⟨⟨h₃⟩,⟨h₄⟩⟩;
  try { refl }; exfalso; cases i with i₀; 
  try { exact hj rfl }; try { exact hk rfl }
end

example (p q : Prop) (h : ¬ (p ∨ q)) : ¬ p ∧ ¬ q := by library_search

lemma σ_pred_nodup {i : ℕ} {l : list ℕ} (hl : l.nodup) (hm : i ∉ l) :
  (l.map (σ i.pred)).nodup := 
begin
  induction l with j l ih,
  { exact list.nodup_nil },
  { rw [list.map_cons],
    rw [list.nodup_cons] at hl ⊢,
    rw [list.mem_cons_iff] at hm,
    replace hm : i ≠ j ∧ i ∉ l := or_imp_distrib.mp hm,
    split,
    { intro h,
      exfalso,
      rcases list.mem_map.mp h with ⟨k,⟨hkm,hke⟩⟩,
      have hki : k ≠ i := λ e, hm.right (e ▸ hkm),
      have hjk : j ≠ k := λ e, hl.left (e.symm ▸ hkm),
      exact hjk (σ_pred_inj hm.left.symm hki hke.symm) },
    { exact ih hl.right hm.right } }
end

end infinite

def δ {n : ℕ} (i : fin n.succ) : fin n → fin n.succ := 
  λ j, if (j : ℕ) < (i : ℕ) then j.inc else j.succ

lemma δ_infinite {n : ℕ} (i : fin n.succ) (k : fin n) : 
  (δ i k : ℕ) = infinite.δ i k := 
begin
  simp only [δ, infinite.δ],
  split_ifs, { rw [fin.coe_inc] }, { exact fin.coe_succ k }
end

@[simp] lemma δ_val {n : ℕ} (i : fin n.succ) (j : fin n) : (δ i j : ℕ) = 
  if (j : ℕ) < (i : ℕ) then (j : ℕ) else (j : ℕ).succ := 
by { rw [δ]; split_ifs, { rw [fin.coe_inc] }, { exact fin.coe_succ j } }

lemma δ_val_lt {n : ℕ} {i : fin n.succ} {j : fin n} (h : (j : ℕ) < (i : ℕ)) :
  (δ i j : ℕ) = j := by { rw [δ_val, if_pos h] }

lemma δ_val_ge {n : ℕ} {i : fin n.succ} {j : fin n} (h : (i : ℕ) ≤ (j : ℕ)) :
  (δ i j : ℕ) = (j : ℕ).succ := by { rw [δ_val, if_neg (not_lt_of_ge h)] }

def σ {n : ℕ} (i : fin n) : fin n.succ → fin n := 
  λ j, dite ((j : ℕ) ≤ (i : ℕ))
         (λ h, fin.res h) 
         (λ h, j.pred (λ e, by { cases e, exact h (nat.zero_le _)}))

lemma σ_infinite {n : ℕ} (i : fin n) (k : fin n.succ) : 
  (σ i k : ℕ) = infinite.σ i k := 
begin
  simp only [σ, infinite.σ],
  split_ifs, 
  { rw [fin.coe_res] }, 
  { exact fin.coe_pred k _ }
end

@[simp] lemma σ_val {n : ℕ} (i : fin n) (j : fin n.succ) : (σ i j : ℕ) = 
  if (j : ℕ) ≤ (i : ℕ) then (j : ℕ) else (j : ℕ).pred := 
begin
 rw [σ]; split_ifs, 
 { rw [fin.coe_res] }, 
 { exact fin.coe_pred j _ }
end

lemma ite.map {α β : Type} (f : α → β) (a a' : α) (h : Prop) [decidable h] :
  f (ite h a a') = ite h (f a) (f a') := by { split_ifs; refl } 

lemma ite.fin_val {n : ℕ} (a a' : fin n) (h : Prop) [decidable h] :
  (ite h a a' : ℕ) = ite h (a : ℕ) (a' : ℕ)  := by { split_ifs; refl } 

lemma le_iff_not_gt {α : Type*} [linear_order α] (x y : α) : x ≤ y ↔ ¬ x > y :=
⟨not_lt_of_ge, le_of_not_gt⟩

lemma δδ {n : ℕ} (i : fin (n + 1)) (j : fin (n + 2)) (hji : (j : ℕ) ≤ (i : ℕ)) : 
  (δ j) ∘ (δ i) = (δ i.succ) ∘ (δ (fin.res hji)) :=
begin
  ext k,
  let hi := congr_fun (infinite.δδ (i : ℕ) (j : ℕ) hji) k,
  simp only [function.comp_app, δ_infinite, fin.coe_succ, fin.coe_res] at hi ⊢,
  exact hi 
end

lemma σσ {n : ℕ} (i : fin (n + 1)) (j : fin n) (hij : (i : ℕ) ≤ (j : ℕ)) : 
  (σ j) ∘ (σ i) = (σ (fin.res hij)) ∘ (σ j.succ) :=
begin
  ext k,
  let hi := congr_fun (infinite.σσ (i : ℕ) (j : ℕ) hij) k,
  simp only [function.comp_app, σ_infinite, fin.coe_succ, fin.coe_res] at hi ⊢,
  exact hi
end

lemma σδ₀ {n : ℕ} (i : fin (n + 1)) (j : fin (n + 2)) (hij : (i : ℕ) + 1 < (j : ℕ)) : 
  (σ i) ∘ (δ j) = (δ (j.pred (λ h, by { rw[h] at hij, exact nat.not_lt_zero _ hij}))) ∘ 
                  (σ ⟨i.val, nat.lt_of_succ_lt_succ (lt_of_lt_of_le hij (nat.le_of_lt_succ j.is_lt))⟩ ) :=  
begin
  ext k,
  let hi := congr_fun (infinite.σδ₀ (i : ℕ) (j : ℕ) hij) k,
  simp only [function.comp_app, σ_infinite, δ_infinite, fin.coe_pred, fin.coe_res] at hi ⊢,
  exact hi
end

lemma σδ₁ {n : ℕ} (i : fin n) : (σ i) ∘ δ (fin.inc i) = id := 
begin
  ext k,
  let hi := congr_fun (infinite.σδ₁ (i : ℕ)) k,
  simp only [function.comp_app, σ_infinite, δ_infinite, fin.coe_inc] at hi ⊢,
  exact hi
end

lemma σδ₂ {n : ℕ} (i : fin n) : (σ i) ∘ δ (i.succ) = id := 
begin
  ext k,
  let hi := congr_fun (infinite.σδ₂ (i : ℕ)) k,
  simp only [function.comp_app, σ_infinite, δ_infinite, fin.coe_succ] at hi ⊢,
  exact hi
end

lemma σδ₃ {n : ℕ} (i : fin (n + 1)) (j : fin (n + 2)) (hij : (j : ℕ) < (i : ℕ)) : 
  (σ i) ∘ (δ j) = (δ ⟨j.val, lt_trans hij i.is_lt ⟩) ∘ 
                  (σ (i.pred (λ h, by { rw[h] at hij, exact nat.not_lt_zero (j : ℕ) hij})) ) :=  
begin
  ext k,
  let hi := congr_fun (infinite.σδ₃ (i : ℕ) (j : ℕ) hij) k.val,
  simp only [function.comp_app, σ_infinite, δ_infinite, fin.coe_pred, fin.coe_res] at hi ⊢,
  exact hi
end

lemma σδ_pred {n : ℕ} (i : fin (n + 2)) : (σ i.pred') ∘ (δ i) = id := 
begin
  ext k,
  let hi := congr_fun (infinite.σδ_pred (i : ℕ)) k,
  simp only [function.comp_app, σ_infinite, δ_infinite, fin.coe_pred'] at hi ⊢,
  exact hi
end

lemma δ_inj {n : ℕ} (i : fin (n + 1)): function.injective (δ i) := λ j₀ j₁ e, 
begin
  replace e := congr_arg (coe : fin _ → ℕ) e,
  rw [δ_infinite, δ_infinite] at e, 
  exact fin.eq_of_veq (infinite.δ_inj (i : ℕ) e) 
end

lemma σ_surj {n : ℕ} (i : fin n) : function.surjective (σ i) := 
begin
  have : function.right_inverse (δ i.succ) (σ i) := 
   λ j, begin change ((σ i) ∘ (δ i.succ)) j = _, simp[σδ₂], end,
  exact function.right_inverse.surjective this
end

/-  ⟨δ i.succ,λ j, by { rw [← function.comp_app (σ i), σδ₂, id]}⟩ -/

lemma δ_ne {n : ℕ} (i : fin (n + 1)) (k : fin n) : δ i k ≠ i := 
begin
 intro e, replace e := congr_arg (coe : fin (n + 1) → ℕ) e,
 simp only  [δ_infinite] at e, exact infinite.δ_ne _ _ e
end

lemma δ_image {n : ℕ} (i j : fin (n + 1)) : (∃ k, δ i k = j) ↔ j ≠ i := 
begin
  split,
  { rintro ⟨k,e⟩, rw [← e], apply δ_ne },
  { intro hne, 
    have hne' : (j : ℕ) ≠ (i : ℕ) := λ h, hne (fin.eq_of_veq h),
    by_cases hji : (j : ℕ) ≤ (i : ℕ),
    { replace hji := lt_of_le_of_ne hji hne',
      have hj : (j : ℕ) < n := lt_of_lt_of_le hji (nat.le_of_lt_succ i.is_lt),
      let j' : fin n := ⟨j,hj⟩,
      let hji' : (j' : ℕ) < (i : ℕ) := hji,
      use j', simp only [δ, if_pos hji'],
      apply fin.coe_inj, rw [fin.coe_inc], refl }, 
    { have : j ≠ 0 := λ h, 
       begin
         replace h : (j : ℕ) = 0 := congr_arg coe h, 
         rw [h] at hji, exact hji (nat.zero_le _) 
       end,
      let j₀ := j.pred this, use j₀, apply fin.coe_inj,
      have : j = j₀.succ := (fin.succ_pred j _).symm,
      rw [this, fin.coe_succ] at hne' hji,
      rw [this, δ_infinite, fin.coe_succ, infinite.δ],
      have hlt := lt_of_not_ge hji,
      have : ¬ ((j₀ : ℕ) < (i : ℕ)) := λ h, hji (nat.succ_le_of_lt h),
      rw [if_neg this] } }
end

lemma σ_inj {n : ℕ} {i j k : fin (n + 2)} (hj : j ≠ i) (hk : k ≠ i) 
 (he : σ i.pred' j = σ i.pred' k) : j = k := 
begin
  replace he := congr_arg (coe : fin _ → ℕ) he,
  replace hj : (j : ℕ) ≠ (i : ℕ) := λ e, hj (fin.coe_inj e),
  replace hk : (k : ℕ) ≠ (i : ℕ) := λ e, hk (fin.coe_inj e),
  simp only [σ_infinite, fin.coe_pred'] at he,
  exact fin.coe_inj (simplicial.infinite.σ_pred_inj hj hk he)
end

end simplicial