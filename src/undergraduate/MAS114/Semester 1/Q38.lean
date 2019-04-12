import data.real.basic

namespace MAS114
namespace exercises_1
namespace Q38

noncomputable def r3 : ℝ := real.sqrt 3
noncomputable def r5 : ℝ := real.sqrt 5
noncomputable def r7 : ℝ := real.sqrt 7

noncomputable def u := r3 + r5 + r7 

noncomputable def v := (u ^ 7 - 60 * u^5 + 841 * u ^ 3 - 4950 * u) / 472

lemma v_sq : v * v = 3 * 5 * 7 := sorry

lemma v_irrational : ¬ ∃ v_Q : ℚ, v = v_Q := sorry

lemma u_irrational : ¬ ∃ u_Q : ℚ, u = u_Q := sorry

end Q38
end exercises_1
end MAS114