import data.real.basic data.real.sqrt tactic.fin_cases

namespace loh

lemma real_sq_nonneg (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

lemma no_nat_half : ¬ ∃ (n : ℕ), 2 * n = 1 := 
begin 
  rintro ⟨n,hn⟩,
  cases n; cases hn
end

lemma int_domain : ∀ (n m : ℤ), n * m = 0 → n = 0 ∨ m = 0 := 
  λ n m h, int.eq_zero_or_eq_zero_of_mul_eq_zero h

section root_set 

variables {u : ℝ} (hu : u > 0)
include hu

def root_set := { x : ℝ | x ^ 2 = u }
noncomputable def pos_root : root_set hu := 
  ⟨real.sqrt u, real.sq_sqrt (le_of_lt hu)⟩ 
noncomputable def neg_root : root_set hu := 
  ⟨- real.sqrt u, by { change _ ^ 2  = _, rw[neg_sq, real.sq_sqrt (le_of_lt hu)] } ⟩ 

lemma coe_pos_root : ((pos_root hu) : ℝ) = real.sqrt u := rfl
lemma coe_neg_root : ((neg_root hu) : ℝ) = - real.sqrt u := rfl

lemma pos_root_pos : (pos_root hu : ℝ) > 0 := real.sqrt_pos.mpr hu
lemma neg_root_neg : ¬ ((neg_root hu : ℝ) > 0) := 
  not_lt_of_gt (neg_neg_of_pos (pos_root_pos hu))

lemma sq_pos_root : (pos_root hu : ℝ) ^ 2 = u := (pos_root hu).property
lemma sq_neg_root : (neg_root hu : ℝ) ^ 2 = u := (neg_root hu).property

noncomputable def root_set_to : root_set hu → fin 2 := λ u, ite ((u : ℝ) > 0) 0 1
noncomputable def root_set_of : fin 2 → root_set hu := λ i, ite (i = 0) (pos_root hu) (neg_root hu)

lemma coe_root_set_of : ∀ (i : fin 2), ((root_set_of hu i) : ℝ) = ite (i = 0) (real.sqrt u) (- real.sqrt u) := 
begin
  intro i, dsimp[root_set_of], split_ifs; refl
end

lemma root_set_els : ∀ (x : root_set hu), x = (pos_root hu) ∨ x = (neg_root hu) := 
begin
  rintro ⟨x, hx : x ^ 2 = u⟩,
  let v := real.sqrt u,
  rw[← sub_eq_zero, ← (real.sq_sqrt (le_of_lt hu))] at hx,
  have : x ^ 2 - v ^ 2 = (x - v) * (x - (- v)) := by ring, 
  rw[this] at hx,
  replace hx := eq_zero_or_eq_zero_of_mul_eq_zero hx,
  rw[sub_eq_zero, sub_eq_zero] at hx,
  cases hx with hx hx,
  { left , ext, change x = _, rw[coe_pos_root], exact hx },
  { right, ext, change x = _, rw[coe_neg_root], exact hx }
end

noncomputable def root_set.equiv : (root_set hu) ≃ (fin 2) := {
  to_fun := root_set_to hu,
  inv_fun := root_set_of hu,
  left_inv := begin
    intro x,
    cases root_set_els hu x with hp hn,
    { rw[hp], dsimp[root_set_to], rw[if_pos (pos_root_pos hu)], refl },
    { rw[hn], dsimp[root_set_to], rw[if_neg (neg_root_neg hu)], refl }
  end,
  right_inv := begin
    intro i,
    dsimp[root_set_of],
    split_ifs,
    { dsimp[root_set_to], rw[h, if_pos (pos_root_pos hu)] },
    { dsimp[root_set_to], rw[if_neg (neg_root_neg hu)], 
      fin_cases i; trivial,
    }
  end
}
end root_set 

example (x : ℝ) (h : 0 ≤ x) : (abs x) = x := by library_search

noncomputable def abs_cases (x : ℝ) : { u : ℝ // 0 ≤ u ∧ (abs x) = u ∧ (x = u ∨ x = -u) } := 
begin 
  use (abs x), split, exact (abs_nonneg x), split, refl,
  by_cases h : x ≥ 0,
  {left, rw[abs_eq_self.mpr h]},
  {right, rw[abs_eq_neg_self.mpr (le_of_not_ge h), neg_neg] }
end

lemma tri_ineq (x y : ℝ) : abs (x + y) ≤ (abs x) + (abs y) := sorry

def conv_to (x : ℕ → ℝ) (a : ℝ) : Prop := 
  ∀ (ε : ℝ) (hε : ε > 0), ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → (abs (x n - a) < ε)

section jective

variables {X Y : Type*} (f : X → Y)

def inj (f : X → Y) := ∀ x₀ x₁ : X, f x₀ = f x₁ → x₀ = x₁

def surj (f : X → Y) := ∀ y : Y, ∃ x : X, f x = y

def bij (f : X → Y) := (inj f) ∧ (surj f)

lemma inj_of_bij {f : X → Y} (h : bij f) : inj f := h.1

lemma surj_of_bij {f : X → Y} (h : bij f) : surj f := h.2

lemma bij_of_inj_of_surj {f : X → Y} (hi : inj f) (hs : surj f) : bij f := ⟨hi, hs⟩



end jective

end loh
