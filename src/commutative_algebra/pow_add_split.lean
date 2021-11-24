import algebra.ring algebra.group_power
import tactic.ring

variables {A : Type*} [comm_ring A] (a b : A) (n m : ℕ)

namespace pow_add_split 

def α : ℕ → ℕ → A → A → A 
| 0 m a b := 0
| (n + 1) 0 a b := (a + b) ^ n
| (n + 1) (m + 1) a b := (α (n + 1) m a b) + (α n (m + 1) a b) * b

end pow_add_split

open pow_add_split

/-
 It looks like the induction needs to be generalised for this to work

lemma pow_add_split : ∀ (p n m : ℕ) (hp : p + 1 = n + m) (a b : A), 
 (a + b) ^ p = (α m n a b) * a ^ n + (α n m b a) * b ^ m 
| 0 0 0 hp a b := by {exfalso, exact nat.zero_ne_one hp.symm,}
| 0 0 1 _ a b := by {rw[α,α,zero_mul,add_zero,pow_zero,pow_zero,mul_one],}
| 0 1 0 _ a b := by {rw[α,α,zero_mul,zero_add,pow_zero,pow_zero,pow_zero,mul_one],}
| 0 (n + 1) (m + 1) hp a b := by {
   rw[zero_add,add_assoc,add_comm 1,add_assoc m,← add_assoc] at hp,
   cases hp,
  }
| (p + 1) 0 0 hp a b := by {cases hp}
| (p + 1) 0 (m + 1) hp a b := by {
    rw[zero_add] at hp,let hp' := nat.succ_inj hp,
    rw[α,α,hp',pow_zero,mul_one,zero_mul,add_zero],
  }
| (p + 1) (n + 1) 0 hp a b := by {
    rw[add_zero] at hp,let hp' := nat.succ_inj hp,
    rw[α,α,hp',pow_zero,mul_one,zero_mul,zero_add,add_comm],
  }
| (p + 1) (n + 1) (m + 1) hp a b := by {
    rw[add_assoc,add_assoc,add_comm 1 (m + 1),add_assoc,← add_assoc n m] at hp,
    let hp' : p = n + m := nat.succ_inj (nat.succ_inj hp),
    have hn : p + 1 = n + (m + 1) := by {rw[hp',add_assoc],},
    have hm : p + 1 = (n + 1) + m := by {rw[hp',add_assoc,add_assoc,add_comm 1],},
    let en := congr_arg (λ x, x * b) (pow_add_split p n (m + 1) hn a b),
    let em := congr_arg (λ x, x * a) (pow_add_split p (n + 1) m hm a b),
    simp only [] at en em,
    rw[α,α], repeat {rw[pow_add,pow_one]}, rw[mul_add,en,em], ring,
    sorry
}

-/
