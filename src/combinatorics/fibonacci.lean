/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file defines Fibonacci numbers and their reductions mod `n`.
It was intended to make computation efficient, but does not
succeed very well.  Some better approaches were discussed on
Zulip by Mario and Kenny; they should be incorporated here.
-/

import data.real.basic data.fintype.basic algebra.big_operators data.nat.modeq
import tactic.find tactic.squeeze tactic.norm_num tactic.ring

namespace combinatorics

/- This is the basic definition of fibonacci numbers.  It 
   is not good for efficient evaluation.
-/

def fibonacci : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n + 2) := (fibonacci n) + (fibonacci (n + 1))

/- We now do a more efficient version, and prove that it is 
   consistent with the original one.
-/

def fibonacci_step : ℕ × ℕ → ℕ × ℕ := 
 λ ⟨a,b⟩, ⟨b, a + b⟩

def fibonacci_pair : ℕ → ℕ × ℕ 
| 0 := ⟨0,1⟩ 
| (n + 1) := fibonacci_step (fibonacci_pair n)

lemma fibonacci_pair_spec : ∀ n , 
 fibonacci_pair n = ⟨fibonacci n,fibonacci n.succ⟩ 
| 0 := rfl
| (nat.succ n) := begin
 rw[fibonacci_pair,fibonacci_pair_spec n,fibonacci_step,fibonacci],
 ext,refl,refl,
end

lemma fibonacci_from_pair (n : ℕ) : 
 fibonacci n = (fibonacci_pair n).fst := 
  by rw[fibonacci_pair_spec n].

/- We now prove a fact about the fibonacci numbers mod 2.
   Later we will generalise this for an arbitrary modulus.
-/

lemma fibonacci_bodd_step (n : ℕ) : 
 (fibonacci (n + 3)).bodd = (fibonacci n).bodd := 
begin
 rw[fibonacci,fibonacci,nat.bodd_add,nat.bodd_add],
 cases (fibonacci (n + 1)).bodd;
 cases (fibonacci n).bodd;
 refl,
end

lemma fibonacci_bodd : ∀ n, (fibonacci n).bodd = bnot (n % 3 = 0)
| 0 := rfl
| 1 := rfl
| 2 := rfl
| (n + 3) := begin
 rw[fibonacci_bodd_step n,fibonacci_bodd n,nat.add_mod_right]
end

/-
 We now do a more general theory of modular periodicity
 of fibonacci numbers.  For computational efficiency, we
 give an inductive definition of modular fibonacci numbers
 that does not require us to calculate the non-modular ones.
 We then prove that it is consistent with the original 
 definition.
-/

def pair_mod (p : ℕ) : ℕ × ℕ → ℕ × ℕ := 
 λ ⟨a,b⟩, ⟨a % p,b % p⟩ 

lemma pair_mod_mod (p : ℕ) : ∀ (c : ℕ × ℕ), 
 pair_mod p (pair_mod p c) = pair_mod p c := 
λ ⟨a,b⟩, by {simp[pair_mod,nat.mod_mod],}

def fibonacci_pair_mod (p : ℕ) : ℕ → ℕ × ℕ 
| 0 := pair_mod p ⟨0,1⟩ 
| (n + 1) := pair_mod p (fibonacci_step (fibonacci_pair_mod n))

lemma fibonacci_pair_mod_mod (p : ℕ) : ∀ n,
 pair_mod p (fibonacci_pair_mod p n) = fibonacci_pair_mod p n
| 0 := by {rw[fibonacci_pair_mod,pair_mod_mod],} 
| (n + 1) := by {rw[fibonacci_pair_mod,pair_mod_mod],} 

lemma mod_step_mod (p : ℕ) : ∀ (c : ℕ × ℕ), 
 pair_mod p (fibonacci_step c) = 
  pair_mod p (fibonacci_step (pair_mod p c)) :=
λ ⟨a,b⟩, begin
 change (⟨b % p,(a + b) % p⟩ : ℕ × ℕ) = 
  ⟨b % p % p,(a % p + b % p) % p⟩,
 have e0 : b % p % p = b % p := nat.mod_mod b p,
 have e1 : (a % p + b % p) % p = (a + b) % p :=
  nat.modeq.add (nat.mod_mod a p) (nat.mod_mod b p),
 rw[e0,e1],
end

lemma fibonacci_pair_mod_spec (p : ℕ) : ∀ n, 
 fibonacci_pair_mod p n = pair_mod p (fibonacci_pair n) 
| 0 := rfl
| (n + 1) := begin
 rw[fibonacci_pair_mod,fibonacci_pair,fibonacci_pair_mod_spec n],
 rw[← mod_step_mod],
end

lemma fibonacci_mod_spec (p : ℕ) (n : ℕ) :
 (fibonacci_pair_mod p n).fst = (fibonacci n) % p := 
begin
 rw[fibonacci_pair_mod_spec,fibonacci_pair_spec,pair_mod],
 refl,
end

lemma fibonacci_pair_period₀ {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) :
  ∀ n, fibonacci_pair_mod p (n + d) = fibonacci_pair_mod p n
| 0 := by {rw[zero_add,h,fibonacci_pair_mod],}
| (n + 1) := by {
  rw[add_assoc,add_comm 1 d,← add_assoc],
  rw[fibonacci_pair_mod,fibonacci_pair_mod],
  rw[fibonacci_pair_period₀ n],
}

lemma fibonacci_pair_period₁ {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) (m : ℕ) :
  ∀ n, fibonacci_pair_mod p (m + d * n) = fibonacci_pair_mod p m
| 0 := by {rw[mul_zero,add_zero]}
| (n + 1) := by {
  have : m + d * (n + 1) = (m + d * n) + d := by ring,
  rw[this,fibonacci_pair_period₀ h,fibonacci_pair_period₁],
}

lemma fibonacci_pair_period {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) (n : ℕ) : 
  fibonacci_pair_mod p n = fibonacci_pair_mod p (n % d) := 
calc 
 fibonacci_pair_mod p n = fibonacci_pair_mod p (n % d + d * (n / d)) :
  congr_arg (fibonacci_pair_mod p) (nat.mod_add_div n d).symm
  ... = fibonacci_pair_mod p (n % d) : fibonacci_pair_period₁ h (n % d) (n / d)

lemma fibonacci_period  {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) (n : ℕ) : 
  (fibonacci n) ≡ (fibonacci (n % d)) [MOD p] := 
begin
 rw[nat.modeq,← fibonacci_mod_spec,← fibonacci_mod_spec],
 rw[fibonacci_pair_period],
 exact h,
end

/-
 Prove the identity

 (fibonacci n) = (choose n 0) + (choose n-1 1) + (choose n-2 2) + ...
-/

end combinatorics