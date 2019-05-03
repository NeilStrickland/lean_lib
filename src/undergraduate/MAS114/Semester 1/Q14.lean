import data.real.basic data.fintype algebra.big_operators data.nat.modeq
import tactic.find tactic.squeeze 

namespace MAS114
namespace exercises_1
namespace Q14

def f : ℚ → ℚ := λ x, (x + 1) / (2 * x)

lemma f_step (x : ℚ) : x > 1 → (1 - 1 / (x ^ 2)) * f (x - 1) = f x := 
begin
 intro x_big,
 let d := 2 * (x - 1) * (x ^ 2) ,
 /- Prove that all relevant denominators are nonzero -/
 let nz_x  : x ≠ 0     := (ne_of_lt (by linarith using [x_big])).symm,
 let nz_2x : 2 * x ≠ 0 := mul_ne_zero dec_trivial nz_x,
 let nz_x2 : x ^ 2 ≠ 0 := by {rw[pow_two], exact mul_ne_zero nz_x nz_x},
 let nz_y  : x - 1 ≠ 0 := (ne_of_lt (by linarith using [x_big])).symm,
 let nz_2y : 2 * (x - 1) ≠ 0 := mul_ne_zero dec_trivial nz_y,
 let nz_d : d ≠ 0 := mul_ne_zero nz_2y nz_x2,
 let e0 := calc
  (x ^ 2) * (1 - 1 / (x ^ 2)) = (x ^ 2) * 1 - (x ^ 2) * (1 / (x ^ 2)) : 
   by rw[mul_sub] 
  ... = x ^ 2 - 1 : by rw[mul_one,mul_div_cancel' 1 nz_x2],
 let e1 := calc 
  d * (1 - 1 / (x ^ 2)) = (2 * (x - 1)) * ((x ^ 2) * (1 - 1 / (x ^ 2))) :
   by rw[mul_assoc]
  ... = (2 * (x - 1)) * (x ^ 2 - 1) : by rw[e0]
  ... = (x ^ 2 - 1) * (2 * (x - 1)) : by rw[mul_comm],
 let e2 : (x - 1) + 1 = x := by ring,
 let e3 := calc 
  (2 * (x - 1)) * f (x - 1) = (2 * (x - 1)) * (((x - 1) + 1) / (2 * (x - 1))) : rfl
  ... = (2 * (x - 1)) * (x / (2 * (x - 1))) : by rw[e2]
  ... = x * (2 * (x - 1) / (2 * (x - 1))) : mul_div_comm (2 * (x - 1)) x (2 * (x - 1))
  ... = x : by rw[div_self nz_2y,mul_one],
 let e4 := calc
  d * ((1 - 1 / (x ^ 2)) * f (x - 1)) = (d * (1 - 1 / (x ^ 2))) * f (x - 1) :
   by rw[← mul_assoc]
  ... = (x ^ 2 - 1) * (2 * (x - 1)) * f (x - 1) : by rw[e1]
  ... = (x ^ 2 - 1) * x : by rw[mul_assoc,e3]
  ... = (x ^ 2) * x - 1 * x : by rw[sub_mul]
  ... = x ^ 3 - x : by rw[← pow_succ',one_mul],
 let e5 : d = (x * x - x) * (2 * x) := by {dsimp[d],ring},
 let e6 := calc 
  d * f x = d * ((x + 1) / (2 * x)) : rfl 
  ... = ((x * x - x) * (2 * x)) * ((x + 1) / (2 * x)) : by rw[e5]
  ... = (x * x - x) * ((2 * x) * ((x + 1) / (2 * x))) : by rw[mul_assoc]
  ... = (x * x - x) * (x + 1) : by rw[mul_div_comm,div_self nz_2x,mul_one]
  ... = x ^ 3 - x : by ring,
 exact eq_of_mul_eq_mul_left nz_d (e4.trans e6.symm),
end

lemma product_formula : ∀ (n : ℕ), 
 (finset.range n).prod (λ k, ((1 - 1 / ((k + 2) ^ 2)) : ℚ)) = f (n + 1)
| 0 := rfl
| (n + 1) := begin
 have e0 : 1 < n + 2 := by linarith,
 have e1 : (1 : ℚ) < ((n + 2) : ℕ) := nat.cast_lt.mpr e0, 
 rw[nat.cast_add,nat.cast_bit0,nat.cast_one] at e1,
 rw[finset.prod_range_succ,product_formula n],
 let e2 := f_step (n + 2) e1,
 have e3 : (n : ℚ) + 2 - 1 = n + 1 := by ring,
 have e4 : (((n + 1) : ℕ) : ℚ) + 1 = (n : ℚ) + 2 :=
  by { rw[nat.cast_add,nat.cast_one],ring},
 rw[e3] at e2,
 rw[e2,e4],
end

end Q14

end exercises_1
end MAS114