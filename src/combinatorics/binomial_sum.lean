/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.nat.choose
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
 choose (k + m) (k + 1) = 
  (finset.range m).sum (λ i, choose (k + i) k) := 
begin
 induction m with m ih,
 {rw[finset.range_zero,finset.sum_empty,add_zero,choose_succ_self]},
 {rw[finset.sum_range_succ,← ih,nat.add_succ,choose],}
end

lemma choose_sum (n k : ℕ) : 
 choose n.succ k.succ = (finset.Ico k n.succ).sum (λ i, choose i k)
  := sorry 