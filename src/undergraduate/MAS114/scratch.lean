def half_Q : ℚ := 1 / 2
def neg_half_Q : ℚ := - half_Q
noncomputable def half_R : ℝ := half_Q
noncomputable def neg_half_R : ℝ := neg_half_Q

/-
 Even basic identities like 1/2 - 1 = -1/2 cannot easily be 
 proved directly in ℝ, because there are no general algorithms
 for exact calculation in ℝ.  We need to work in ℚ and then 
 apply the cast map.
-/


/-
 Here is a small identity that could in principle be proved 
 by a long string of applications of the commutative ring axioms.
 The "ring" tactic automates the process of finding this string.

 For reasons that I do not fully understand, the ring tactic
 seems to work more reliably if we do it in a separate lemma 
 so that the terms are just free variables.  We can then 
 substitute values for this variables as an extra step.  In 
 particular, we will substitute h = 1/2, and then give a 
 separate argument that the final term 2 * h - 1 is zero.
-/
lemma misc_identity (m n h : ℝ) :
 (m + h) - (2 * m + 1 - n) = - ((m + h) - n) + (2 * h - 1) := 
  by ring 

/-
 We now prove that there is no closest integer to m + 1/2.
 The obvious approach would be to focus attention on the 
 candidates n = m and n = m + 1, but it turns out that that
 creates more work than necessary.  It is more efficient to 
 prove that for all n, the integer k = 2 m + 1 - n is different
 from n and lies at the same distance from m + 1/2, so 
 n does not have the required property.  
-/
lemma no_closest_integer (n m : ℤ) : 
 ¬ (is_closest_integer n ((m : ℝ) + half_R)) := 
begin
 intro h0,
 let x_Q : ℚ := (m : ℚ) + half_Q, 
 let x_R : ℝ := (m : ℝ) + half_R, 
 let k := 2 * m + 1 - n,
 by_cases e0 : k = n,
 {-- In this block we consider the possibility that k = n, and 
  -- show that it is impossible.
  exfalso,
  dsimp[k] at e0,
  let e1 := calc 
   (1 : ℤ) = (2 * m + 1 + -n) + n - 2 * m : by ring
   ... = n + n - 2 * m : by rw[e0]
   ... = 2 * (n - m) : by ring,
  have e2 := calc 
   (1 : ℤ) = int.mod 1 2 : rfl
   ... = int.mod (2 * (n - m)) 2 : congr_arg (λ x, int.mod x 2) e1
   ... = 0 : int.mul_mod_right 2 (n - m),
  exact (dec_trivial : (1 : ℤ) ≠ 0) e2,
 },{
  let h1 := ne_of_gt (h0 k e0),
  let u_R := x_R - n,
  let v_R := x_R - k,
  have h2 : v_R = - u_R + (2 * half_R - 1) := begin
   dsimp[u_R,v_R,x_R,k],
   rw[int.cast_add,int.cast_add,int.cast_mul,int.cast_bit0],
   rw[int.cast_one,int.cast_neg],
   exact misc_identity (↑ m) (↑ n) half_R,
  end,
  have h3 : 2 * half_Q - 1 = 0 := dec_trivial,
  have h4 : 2 * half_R - 1 = (((2 * half_Q - 1) : ℚ) : ℝ) := 
  begin
   dsimp[half_R],
   rw[rat.cast_add,rat.cast_mul,rat.cast_bit0,rat.cast_neg,rat.cast_one],
  end,
  have h5 : 2 * half_R - 1 = 0 := by rw[h4,h3,rat.cast_zero],
  rw[h5,add_zero] at h2,
  have h6 : abs v_R = abs u_R := by rw[h2,abs_neg],
  exact h1 h6,
 }
end





def fibonacci_step_mod (p : ℕ+) : ℕ × ℕ → ℕ × ℕ := 
 λ ⟨a,b⟩, ⟨b,(a + b) % p⟩ 



#eval fibonacci_pair_mod 89 44

def fibonacci_mod (p : ℕ+): ℕ → ℕ 
| 0 := 0 % p
| 1 := 1 % p
| (n + 2) := ((fibonacci_mod n) + (fibonacci_mod (n + 1))) % p

lemma fibonacci_mod_mod (p : ℕ+) (n : ℕ) : 
 fibonacci_mod p n = (fibonacci_mod p n) % p := 
begin
 rcases n with _ | _ | n;
 rw[fibonacci_mod,nat.mod_mod],
end

lemma fibonacci_mod_spec (p : ℕ+) : ∀ n,
 fibonacci_mod p n = (fibonacci n) % p 
| 0 := rfl
| 1 := rfl
| (n + 2) := 
begin
 rw[fibonacci_mod_mod],
 change fibonacci_mod p (n + 2) ≡ fibonacci (n + 2) [MOD p],
 rw[fibonacci,fibonacci_mod],
 let h0 := calc 
  fibonacci n ≡ (fibonacci n) % p [MOD p] :
                (nat.modeq.mod_modeq (fibonacci n) p).symm 
  ... ≡ fibonacci_mod p n [MOD p] : by rw[fibonacci_mod_spec n],
 let h1 := calc 
  fibonacci n.succ ≡ (fibonacci n.succ) % p [MOD p] :
                     (nat.modeq.mod_modeq (fibonacci n.succ) p).symm 
  ... ≡ fibonacci_mod p n.succ [MOD p] : by rw[fibonacci_mod_spec n.succ],
 let h2 := nat.modeq.modeq_add h0 h1,
 rw[nat.modeq,nat.mod_mod,← nat.modeq],
 exact h2.symm
end

lemma fibonacci_period (p : ℕ+) (m : ℕ)
 (h0 : (fibonacci m) ≡ 0 [MOD p]) 
 (h1 : (fibonacci (m + 1)) ≡ 1 [MOD p]) :
  ∀ n, fibonacci (m + n) ≡ (fibonacci n) [MOD p] 
| 0 := by {simp[zero_add,h0,fibonacci],}
| 1 := by {simp[zero_add,h1,fibonacci],}
| (n + 2) := begin
 rw[← add_assoc,fibonacci,fibonacci],
 apply nat.modeq.modeq_add,
 apply fibonacci_period n,
 apply fibonacci_period n.succ,
end
