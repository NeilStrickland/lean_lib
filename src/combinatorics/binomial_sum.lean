/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.nat.choose
import algebra.prod_equiv
import tactic.squeeze

/-
 Consider the identity
 (choose n k) =  (choose k-1 k-1) + (choose k k-1) + ... + (choose n-1 k-1)

 or 
 (choose n+1 k+1) = (choose k k) + (choose k+1 k) + ... + (choose n k)
 This can be proved algebraically by induction.   
 Alternatively, we can consider the set (P n k) of 
 subsets A of size k in {0,..,n-1}, so |(P n k)| = (choose n k).
 We can split this set up according to the value of (max A),
 and recover a combinatorial proof of the identity.

-/

lemma choose_sum' (k m : ℕ) : 
 nat.choose (k + m) (k + 1) = 
  (finset.range m).sum (λ i, nat.choose (k + i) k) := 
begin
 induction m with m ih,
 {rw[finset.range_zero,finset.sum_empty,add_zero,nat.choose_succ_self]},
 {rw[finset.sum_range_succ,← ih,nat.add_succ,nat.choose, add_comm],}
end

lemma choose_sum (n k : ℕ) : 
 nat.choose n.succ k.succ = (finset.Ico k n.succ).sum (λ i, nat.choose i k) :=
begin
 by_cases h : k ≤ n.succ,
 { let m := n.succ - k,
   have : n.succ = k + m := by rw [add_comm, nat.sub_add_cancel h],
   rw [this] at h ⊢, 
   rw [choose_sum' k m],
   let f : ℕ → ℕ := λ p, nat.choose p k,
   let g : ℕ → ℕ := has_add.add k,
   change (finset.range m).sum (λ i, f (g i)) = (finset.Ico k (k + m)).sum f,
   rw [← @finset.sum_image ℕ ℕ ℕ f _ _ (finset.range m) g
       (λ _ _ _ _, nat.add_left_cancel)],
   have : finset.range m = finset.Ico 0 m := 
   begin
     ext i,
     simp only [finset.mem_range, finset.mem_Ico, nat.zero_le i, true_and]
   end,
   rw [this], 
   have := finset.image_add_left_Ico 0 m k,
   rw[add_zero] at this, rw[← this]},
  { have : finset.Ico k n.succ = ∅ := 
     finset.Ico_eq_empty_iff.mpr (λ h₀, h (le_of_lt h₀)),
    rw[this, finset.sum_empty],
    rw [nat.choose_eq_zero_of_lt (lt_trans (lt_of_not_ge h) k.lt_succ_self)] }
end