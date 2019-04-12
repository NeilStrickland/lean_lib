import data.real.basic data.fintype algebra.big_operators data.nat.modeq
import tactic.find tactic.squeeze 
import MAS114.fiber

namespace MAS114
namespace exercises_1
namespace Q12

def f : ℚ → ℚ := λ x, x * (x + 1) * (2 * x + 1) / 6

lemma f_step (x : ℚ) : f (x + 1) = (x + 1) ^ 2 + f x := 
begin
 dsimp[f],
 apply sub_eq_zero.mp,
 rw[pow_two],
 ring,
end

lemma sum_of_squares : ∀ (n : ℕ), 
 (((finset.range n.succ).sum (λ i, i ^ 2)) : ℚ) = f n
| 0 := rfl
| (n + 1) := begin
  rw[finset.sum_range_succ,sum_of_squares n],
  have : (((n + 1) : ℕ) : ℚ) = ((n + 1) : ℚ ) := by simp, 
  rw[this,f_step n]
 end

end Q12
end exercises_1
end MAS114