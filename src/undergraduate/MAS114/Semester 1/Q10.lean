import data.real.basic data.fintype algebra.big_operators data.nat.modeq
import tactic.find tactic.squeeze 

namespace MAS114
namespace exercises_1
namespace Q10 

def f : ℝ → ℝ := λ x, x ^ 2 - 7 * x + 10 
def f_alt : ℝ → ℝ := λ x, (x - 2) * (x - 5)

lemma f_eq (x : ℝ) : f x = f_alt x := by {dsimp[f,f_alt],ring}
lemma f_two  : f 2 = 0 := by {dsimp[f],ring}
lemma f_five : f 5 = 0 := by {dsimp[f],ring}
lemma two_ne_five : (2 : ℝ) ≠ (5 : ℝ) := 
begin
 intro e,
 have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by {simp}, 
 have h5 : (5 : ℝ) = ((5 : ℕ) : ℝ) := by {simp}, 
 rw[h5,h2] at e,
 exact (dec_trivial : 2 ≠ 5) (nat.cast_inj.mp e),
end

def P1 (x : ℝ) : Prop := f x = 0 → x = 2 ∧ x = 5
def P2 (x : ℝ) : Prop := f x = 0 → x = 2 ∨ x = 5

lemma L1 : ¬ (∀ x : ℝ, P1 x) := 
begin
 intro h_P1,
 exact two_ne_five (h_P1 2 f_two).right,
end

lemma L2 : ∀ x : ℝ, P2 x := 
begin
 intros x fx,
 rw[f_eq x] at fx,
 dsimp[f_alt] at fx,
 rcases eq_zero_or_eq_zero_of_mul_eq_zero fx with x_eq_2 | x_eq_5,
 {rw[← sub_eq_add_neg] at x_eq_2,
  exact or.inl (sub_eq_zero.mp x_eq_2),
 },{
  rw[← sub_eq_add_neg] at x_eq_5,
  exact or.inr (sub_eq_zero.mp x_eq_5),
 }
end

end Q10 

end exercises_1
end MAS114