import algebra.ring algebra.group_power data.zmod.basic data.nat.prime
import data.finset algebra.big_operators
import tactic.ring tactic.linarith

namespace MAS114
namespace exercises_1
namespace Q21

def u (n : ℕ) : ℕ := 2 ^ n
def a (n : ℕ) : ℕ := 2 ^ (u n) + 1

lemma u_ge_1 (n : ℕ) : u n ≥ 1 := 
 by {
  let e := @nat.pow_le_pow_of_le_right 2 dec_trivial 0 n (nat.zero_le n),
  rw[nat.pow_zero] at e,
  exact e,
 }

lemma u_step (n : ℕ) : u (n + 1) = (u n) * 2 := 
 by {dsimp[u],rw[nat.pow_succ],}

def a_pos (n : ℕ) : ℕ+ := ⟨a n,nat.zero_lt_succ _⟩

lemma a_step (n : ℕ) : a (n + 1) + 2 * (a n) = 2 + (a n) * (a n) := 
begin
 have h : ∀ (x : ℕ), x ^ 2 + 1 + 2 * (x + 1) 
   = 2 + (x + 1) * (x + 1) := by {intro, ring,}, 
 rw[a,a,u_step,nat.pow_mul,h (2 ^ (u n))],
end

lemma a_ge_3 (n : ℕ) : a n ≥ 3 := 
begin
 let e := @nat.pow_le_pow_of_le_right 2 dec_trivial _ _ (u_ge_1 n),
 rw[nat.pow_one] at e,
 exact nat.succ_le_succ e,
end

lemma a_ne_1 (n : ℕ) : a n ≠ 1 := ne_of_gt (lt_trans dec_trivial (a_ge_3 n))

lemma a_odd (n : ℕ) : (a n) % 2 = 1 := 
begin
 dsimp[a],
 rw[← nat.add_sub_of_le (u_ge_1 n),nat.pow_add,nat.pow_one],
 rw[add_comm _ 1,nat.add_mul_mod_self_left],
 refl,
end

lemma a_mod_a : ∀ (n m : ℕ), a (n + m + 1) ≡ 2 [MOD (a n)] 
| n 0 := begin 
   rw[add_zero n],
   let e : (a (n + 1) + 2 * (a n)) % (a n) = 
           (2 + (a n) * (a n)) % (a n) :=
            congr_arg (λ i, i % (a n)) (a_step n),
   rw[nat.add_mul_mod_self_right] at e,
   rw[nat.add_mul_mod_self_right] at e,
   exact e,
  end
| n (m + 1) := begin
   rw[← (add_assoc n m 1)],
   let e := a_step (n + m + 1),
   replace e : (a (n + m + 1 + 1) + 2 * a (n + m + 1)) % (a n) = 
             (2 + a (n + m + 1) * a (n + m + 1)) % (a n) := by {rw[e]},
   let ih := a_mod_a n m,
   let ih1 : 2 * a (n + m + 1) ≡ 4 [MOD (a n)] := 
    nat.modeq.modeq_mul rfl ih,
   let ih2 : a (n + m + 1) * a (n + m + 1) ≡ 4 [MOD (a n)] := 
    nat.modeq.modeq_mul ih ih,
   let ih3 : a (n + m + 1 + 1) + 2 * a (n + m + 1) ≡
             a (n + m + 1 + 1) + 4 [MOD (a n)] := nat.modeq.modeq_add rfl ih1, 
   let ih4 : 2 + a (n + m + 1) * a (n + m + 1) ≡ 2 + 4 [MOD (a n)] := 
    nat.modeq.modeq_add rfl ih2,
   let e1 := (ih3.symm.trans e).trans ih4,
   exact nat.modeq.modeq_add_cancel_right rfl e1,
  end

lemma a_coprime_aux (n m : ℕ) : nat.coprime (a n) (a (n + m + 1)) := 
begin
 let u := a n,
 let v := a (n + m + 1),
 change (nat.gcd u v) = 1,
 let q := v / u,
 let r := v % u,
 have e0 : r + u * q = v := nat.mod_add_div (a (n + m + 1)) (a n),
 have e1 : r = 2 % (a n) := a_mod_a n m,
 have e2 : 2 % (a n) = 2 := @nat.mod_eq_of_lt 2 (a n) (a_ge_3 n),
 rw[e2] at e1,
 have e3 : nat.gcd u v = nat.gcd r u := nat.gcd_rec u v,
 rw[e1] at e3,
 have e4 : nat.gcd 2 u = nat.gcd (u % 2) 2 := nat.gcd_rec 2 u,
 have e5 : u % 2 = 1 := a_odd n,
 rw[e5] at e4,
 rw[e4] at e3,
 exact e3
end

lemma a_coprime {n m : ℕ} : n ≠ m → nat.coprime (a n) (a m) := 
begin
 rcases (lt_or_ge n m) with h,
 {let k := m - n.succ,
  have e0 : (n + 1) + k = m := nat.add_sub_of_le h,
  have : (n + 1) + k = n + k + 1 := by ring,
  rw[this] at e0,
  rw[← e0],
  intro,
  exact a_coprime_aux n k,  
 },{
  intro h0,   
  let h1 := lt_of_le_of_ne h h0.symm,
  let k := n - m.succ,
  have e0 : (m + 1) + k = n := nat.add_sub_of_le h1,
  have : (m + 1) + k = m + k + 1 := by ring,
  rw[this] at e0,
  rw[← e0],
  exact (a_coprime_aux m k).symm,  
 }
end

def b (n : ℕ) : ℕ := nat.min_fac (a n)

def b_prime (n : ℕ) : nat.prime (b n) := nat.min_fac_prime (a_ne_1 n)

lemma b_inj : function.injective b := begin
 intros i j e0,
 by_cases e1 : i = j,
 {assumption},
 {exfalso,
  have e2 : nat.gcd (a i) (a j) = 1 := a_coprime e1,
  have e3 : (b i) ∣ (a i) := nat.min_fac_dvd (a i),
  have e4 : (b j) ∣ (a j) := nat.min_fac_dvd (a j),
  rw[← e0] at e4,
  let e5 := nat.dvd_gcd e3 e4,
  rw[e2] at e5,
  exact nat.prime.not_dvd_one (b_prime i) e5
 }
end

end Q21
end exercises_1
end MAS114