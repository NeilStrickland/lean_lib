import data.finset
import data.real.basic
import algebra.group.basic
import algebra.order.floor

#check finset.sum_range_induction

section commutators

variables {G H : Type*} [group G] [group H]

def γ (a b : G) : G := a * b * a⁻¹ * b⁻¹ 

lemma map_γ (f : monoid_hom G H) (a b : G) : f (γ a b) = γ (f a) (f b) := by {
  dsimp[γ], simp[f.map_mul, f.map_inv]
}

lemma cube_γ (a b : G) : (γ a b) ^ 3 = 
   (γ (a * b * a⁻¹) (b⁻¹ * a * b * (a⁻¹ ^ 2))) * (γ (b⁻¹ * a * b) (b ^ 2)) := 
begin
  dsimp[γ], repeat { rw[pow_succ] }, repeat { rw[pow_zero] },
  repeat { rw[mul_inv_rev] }, repeat { rw[inv_inv] }, repeat { rw[one_inv] },
  repeat { rw[mul_one] }, repeat { rw[one_mul] },
  repeat { rw[mul_assoc] },
  simp,
end

end commutators

lemma sandwich {c x : ℝ} (h : ∀ n : ℕ+, (abs x) ≤ c / n) : x = 0 := 
begin
  by_cases hc : c > 0,
  { by_contra hx,
    replace hx : abs x > 0 := abs_pos.mpr hx,
    rcases (archimedean.arch (c + 1) hx) with ⟨n,hn⟩,
    cases n with n,
    { rw[zero_smul] at hn, 
      exact lt_asymm (lt_of_lt_of_le (lt_add_one c) hn) hc },
    rw[nsmul_eq_mul, mul_comm] at hn,
    have np : (n.succ : ℝ) > 0 := nat.cast_pos.mpr n.succ_pos,
    have h' : abs x ≤ c / n.succ := h ⟨n.succ, n.succ_pos⟩,
    exact not_lt_of_ge (le_trans hn ((le_div_iff np).mp h')) (lt_add_one c)
  },
  { have h' := (h 1), 
    have : (1 : ℝ) = (1 : ℕ+) := by norm_num, rw[← this, div_one] at h',
    exact abs_nonpos_iff.mp (le_trans h' (le_of_not_gt hc))
  }
end