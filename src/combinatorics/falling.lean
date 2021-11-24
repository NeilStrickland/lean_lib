/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This is about the function falling n k = n (n - 1) ... (n - k + 1)
Note that the above formula involves subtraction but we give a
different recursive definition that only involves addition and
so works more smoothly as a map ℕ → ℕ → ℕ.

-/

import data.nat.choose

open nat

def falling : ℕ → ℕ → ℕ 
| 0 0 := 1
| 0 (k + 1) := 0
| (n + 1) 0 := 1
| (n + 1) (k + 1) := (n + 1) * falling n k

@[simp]
lemma falling_zero (n : ℕ) : falling n 0 = 1 := begin
 cases n; refl,
end

@[simp]
lemma falling_succ (n k : ℕ) : falling (n + 1) (k + 1) = 
 (n + 1) * falling n k := rfl

@[simp]
lemma falling_zero_succ (k : ℕ) : falling 0 (k + 1) = 0 := rfl

/- falling n n = n! -/
lemma falling_factorial : ∀ n : ℕ, falling n n = factorial n 
| 0 := rfl
| (n + 1) := by {rw[falling,factorial,falling_factorial n]}

/- falling p n = p ! / (p - n)! for p ≥ n.  
   We formalise this with p = n + m rather than with an inequality.
-/
lemma falling_factorial_quot : ∀ n m : ℕ, (falling (n + m) n) * factorial m = factorial (n + m)
| n 0 := by {rw[add_zero,factorial,mul_one,falling_factorial n]}
| 0 (m + 1) := by {rw[zero_add,falling,one_mul]}
| (n + 1) (m + 1) := calc 
   falling ((n + 1) + (m + 1)) (n + 1) * factorial (m + 1) = 
    ((n + 1) + (m + 1)) * (falling ((n + 1) + m) n) * factorial (m + 1) : rfl
   ... = ((n + 1) + (m + 1)) * ((falling (n + (m + 1)) n) * factorial (m + 1)) :
    by rw[mul_assoc,add_assoc n 1 m,add_comm 1 m]
   ... = ((n + 1) + (m + 1)) * factorial (n + (m + 1)) :
    by {rw[falling_factorial_quot n (m + 1)]}
   ... = (n + (m + 1) + 1) * factorial (n + (m + 1)) : 
    by {rw[add_assoc n 1 (m + 1),add_comm 1 (m + 1),← add_assoc n (m + 1) 1]}
   ... = factorial (n + (m + 1) + 1) : rfl
   ... = factorial ((n + 1) + (m + 1)) : 
    by {rw[add_assoc n (m + 1) 1,add_assoc n 1 (m + 1),add_comm (m + 1) 1],}

