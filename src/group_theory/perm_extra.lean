import group_theory.perm.cycles
import data.vector data.equiv.basic 
import data.fin_extra
import group_theory.cyclic

open int.modeq

variables {α : Type*} [decidable_eq α]

def finperm (n : ℕ) := equiv.perm (fin n)

namespace finperm

variable (n : ℕ)

instance : group (finperm n)          := by { dsimp[finperm], apply_instance }
instance : decidable_eq (finperm n)   := by { dsimp[finperm], apply_instance }
instance : has_coe_to_fun (finperm n) (λ _, (fin n) → (fin n)) := by { dsimp[finperm], apply_instance }

variable {n}

@[ext] lemma ext {s t : finperm n} : s = t ↔ ∀ (i : fin n), s i = t i :=
begin
  split, 
  { rintro ⟨_⟩ i, refl },
  { intro h, ext i, rw[h i] }
end

lemma ext' {s t : finperm n} 
 (h : ∀ (i : ℕ) (hi : i < n), ((s ⟨i,hi⟩) : ℕ) = ((t ⟨i,hi⟩) : ℕ)) : s = t := 
begin
  ext i, rcases i with ⟨i,hi⟩, exact h i hi,
end

variable (n)

lemma fin_coe_int_inj {n : ℕ} {i₀ i₁ : fin n} (h : (i₀ : ℤ) = (i₁ : ℤ)) : i₀ = i₁ := 
  fin.coe_inj (int.coe_nat_inj h)

def fin_of_int (i : ℤ) : fin (n + 1) := 
⟨i.nat_mod n.succ, 
begin
  cases i; let j := i % n.succ; have hj : j < n.succ := i.mod_lt n.succ_pos,
  { exact hj },
  { change int.to_nat (int.sub_nat_nat n.succ j.succ) < n.succ,
    rw [int.sub_nat_nat_eq_coe, ← int.coe_nat_sub (hj)],
    change n.succ - j.succ < n.succ,
    rw [nat.succ_sub_succ],
    exact lt_of_le_of_lt (n.sub_le j) n.lt_succ_self }
end⟩

lemma coe_fin_of_int  (i : ℤ) : ((fin_of_int n i) : ℕ) = i.nat_mod n.succ := rfl

lemma coe_fin_of_int' (i : ℤ) : ((fin_of_int n i) : ℤ) = i % n.succ := 
begin
  have : (n.succ : ℤ) ≠ 0 := λ h, by { cases h },
  exact int.to_nat_of_nonneg (i.mod_nonneg this),
end

def shift : ℤ → (fin (n + 1)) → (fin (n + 1)) := 
  λ k i, fin_of_int n (k + (i : ℤ))

lemma shift_zero (i : fin (n + 1)) : shift n 0 i = i := 
begin
  apply fin_coe_int_inj, 
  dsimp [shift, fin_of_int, int.nat_mod],
  have : (n + 1 : ℤ) = n.succ := rfl,  
  rw [this, zero_add, int.of_nat_mod],
  congr' 1, exact nat.mod_eq_of_lt i.is_lt,
end

lemma shift_shift (k₀ k₁ : ℤ) (i : fin (n + 1)) : 
  shift n k₀ (shift n k₁ i) = shift n (k₀ + k₁) i := 
begin
  apply fin_coe_int_inj, 
  simp only [shift, coe_fin_of_int'],
  rw [add_assoc k₀ k₁],
  change _ ≡ _ [ZMOD _],
  apply int.modeq.add, refl, apply int.mod_modeq,
end

lemma shift_of_zero (i : fin (n + 1)) : shift n i 0 = i := 
begin
  apply fin_coe_int_inj, 
  have : ((0 : fin (n + 1)) : ℤ) = 0 := rfl,
  simp only [shift, coe_fin_of_int', this, add_zero],
  change ((i : ℕ) : ℤ) % n.succ = (i : ℕ),
  rw [int.of_nat_mod], rw[nat.mod_eq_of_lt i.is_lt], refl,
end

/-
def p {l₀ l₁ : list α} (h : list.perm l₀ l₁) : equiv.perm (fin l₀.length) :=
by {
  let n := l₀.length, change equiv.perm (fin n),
  induction l₀ with a₀ m₀ ih generalizing l₁ h,
  { exact equiv.refl _ },
  { rcases (list.cons_perm_iff_perm_erase.mp h) with ⟨hm,hp⟩ }
} 
--/

end finperm