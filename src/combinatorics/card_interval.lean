/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.fintype.intervals

namespace combinatorics

/- @latex: defn_intervals -/
def Ico (n m : ℕ) : finset ℕ := (finset.Ico n m)
def Icc (n m : ℕ) : finset ℕ := Ico n m.succ
def Ioo (n m : ℕ) : finset ℕ := Ico n.succ m
def Ioc (n m : ℕ) : finset ℕ := Ico n.succ m.succ

lemma mem_Ico { n m k : ℕ } : k ∈ (Ico n m) ↔ (n ≤ k ∧ k < m) := 
 finset.Ico.mem

lemma mem_Icc { n m k : ℕ } : k ∈ (Icc n m) ↔ (n ≤ k ∧ k ≤ m) := 
by { rw[Icc, ← @nat.lt_succ_iff k m], exact finset.Ico.mem }

lemma mem_Ioo { n m k : ℕ } : k ∈ (Ioo n m) ↔ (n < k ∧ k < m) := 
by { rw[Ioo, ← @nat.succ_le_iff n k], exact finset.Ico.mem }

lemma mem_Ioc { n m k : ℕ } : k ∈ (Ioc n m) ↔ (n < k ∧ k ≤ m) := 
by { rw[Ioc, ← @nat.lt_succ_iff k m, ← @nat.succ_le_iff n k],
      exact finset.Ico.mem } 

lemma Ico_card (n m : ℕ) : (Ico n m).card = m - n := 
 finset.Ico.card n m

lemma Icc_card (n m : ℕ) : (Icc n m).card = m.succ - n := 
by { rw[Icc, Ico_card] }

lemma Ioo_card (n m : ℕ) : (Ioo n m).card = (m - n).pred := 
by { rw[Ioo, Ico_card, nat.sub_succ] }

lemma Ioc_card (n m : ℕ) : (Ioc n m).card = m - n := 
by { rw[Ioc, Ico_card, nat.succ_sub_succ] }

end combinatorics
