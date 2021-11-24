import data.real.basic data.real.sqrt

namespace MAS114
namespace exercises_1
namespace Q38

noncomputable def r3 : ℝ := real.sqrt 3
noncomputable def r5 : ℝ := real.sqrt 5
noncomputable def r7 : ℝ := real.sqrt 7

lemma p3 : (3 : ℝ) ≥ 0 := by { norm_cast, exact dec_trivial }
lemma p5 : (5 : ℝ) ≥ 0 := by { norm_cast, exact dec_trivial }
lemma p7 : (7 : ℝ) ≥ 0 := by { norm_cast, exact dec_trivial }

lemma h3 : r3 * r3 = 3 := real.mul_self_sqrt p3
lemma h5 : r5 * r5 = 5 := real.mul_self_sqrt p5
lemma h7 : r7 * r7 = 7 := real.mul_self_sqrt p7

noncomputable def u := r3 + r5 + r7 

noncomputable def v := (u ^ 7 - 60 * u^5 + 841 * u ^ 3 - 4950 * u) / 472

lemma u2 : u ^ 2 = 15 + 2 * r3 * r5 + 2 * r3 * r7 + 2 * r5 * r7 := 
calc 
 u ^ 2 = r3 * r3 + r5 * r5 + r7 * r7 + 2 * r3 * r5 + 2 * r3 * r7 + 2 * r5 * r7 : 
          by { dsimp[u], ring}
 ... = 3 + 5 + 7 + 2 * r3 * r5 + 2 * r3 * r7 + 2 * r5 * r7 : 
          by { rw[h3, h5, h7] }
 ... = 15 + 2 * r3 * r5 + 2 * r3 * r7 + 2 * r5 * r7 : by { ring }

lemma v_sq : v * v = 3 * 5 * 7 := sorry

lemma v_irrational : ¬ ∃ v_Q : ℚ, v = v_Q := sorry

lemma u_irrational : ¬ ∃ u_Q : ℚ, u = u_Q := sorry

end Q38
end exercises_1
end MAS114