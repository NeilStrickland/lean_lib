import data.real.basic data.fintype algebra.big_operators data.nat.modeq
import tactic.find tactic.squeeze 

namespace MAS114
namespace exercises_1
namespace Q16

lemma nat.bodd_even (n : ℕ) : (2 * n).bodd = ff := 
 by {rw[nat.bodd_mul,nat.bodd_two,band],} 

lemma nat.bodd_odd (n : ℕ) : (2 * n + 1).bodd = tt := 
 by {rw[nat.bodd_add,nat.bodd_even],refl} 

lemma nat.div2_even : ∀ (n : ℕ), (2 * n).div2 = n 
| 0 := rfl
| (n + 1) := begin 
 have : 2 * (n + 1) = (2 * n + 1).succ := by ring,
 rw[this,nat.div2_succ,nat.bodd_odd,bool.cond_tt],
 rw[nat.div2_succ,nat.bodd_even,bool.cond_ff],
 rw[nat.div2_even n],
end

lemma nat.div2_odd (n : ℕ) : (2 * n + 1).div2 = n := 
by {rw[nat.div2_succ,nat.bodd_even,bool.cond_ff,nat.div2_even]}

lemma wf_lemma : ∀ (m : ℕ), m.succ.div2 < m.succ 
| 0 := dec_trivial
| (nat.succ m) := begin
 rw[nat.div2_succ],
 cases m.succ.bodd; simp only[bool.cond_tt,bool.cond_ff],
 exact lt_trans (wf_lemma m) m.succ.lt_succ_self,
 exact nat.succ_lt_succ (wf_lemma m)
end

lemma wf_lemma' (m : ℕ) :
 cond (nat.bodd m) (nat.succ (nat.div2 m)) (nat.div2 m) < nat.succ m :=
begin
 cases m,
 {exact dec_trivial,},
 let u := wf_lemma m,
 cases m.succ.bodd; simp only[bool.cond_tt,bool.cond_ff],
 exact lt_trans u m.succ.lt_succ_self,
 exact nat.succ_lt_succ u,
end

def f : bool → ℕ → ℕ 
| ff u := 4 * u + 1
| tt u := 9 * u + 2

def a : ℕ → ℕ 
| 0 := 0 
| (nat.succ m) := 
   have cond (nat.bodd m) (nat.succ (nat.div2 m)) (nat.div2 m) < nat.succ m := wf_lemma' m,
   f m.succ.bodd (a m.succ.div2)

lemma a_even (n : ℕ) : n > 0 → a (2 * n) = 4 * (a n) + 1 := 
begin
 intro n_pos,
 let k := n.pred,
 have e0 : n = k + 1 := (nat.succ_pred_eq_of_pos n_pos).symm,
 let m := 2 * k + 1,
 have e1 : 2 * n = m.succ := calc
  2 * n = 2 * (k + 1) : by rw[e0]
  ... = 2 * k + 2 : by rw[mul_add,mul_one]
  ... = m.succ : rfl,
 rw[e1,a,← e1,nat.bodd_even,nat.div2_even,f],
end

lemma a_odd (n : ℕ) : a (2 * n + 1) = 9 * (a n) + 2 := 
begin
 change a (2 * n).succ = 9 * (a n) + 2,
 rw[a,nat.bodd_odd,nat.div2_odd,f],
end

lemma a_even_step (n : ℕ) : n > 0 → n ^ 2 ≤ a n → (2 * n) ^ 2 ≤ a (2 * n) := 
begin
 intros n_pos ih,
 rw[a_even n n_pos],
 exact calc
  (2 * n) ^ 2 = 4 * n ^ 2 : by ring
  ... ≤ 4 * a n : nat.mul_le_mul_left 4 ih
  ... ≤ 4 * a n + 1 : nat.le_succ _ 
end

lemma a_odd_step (n : ℕ) : n ^ 2 ≤ a n → (2 * n + 1) ^ 2 ≤ a (2 * n + 1) := 
begin
 intro ih,
 rw[a_odd n],
 exact calc
  (2 * n + 1) ^ 2 = 4 * n + (4 * n ^ 2 + 1) : by ring
   ... ≤ 4 * n ^ 2 + (4 * n ^ 2 + 1) : 
      by {apply (nat.add_le_add_iff_le_right _ _ _).mpr,
          rw[nat.pow_two],
          exact nat.mul_le_mul_left 4 (nat.le_mul_self n),} 
   ... = 8 * n ^ 2 + 1 : by ring
   ... ≤ 9 * n ^ 2 + 2 : by linarith
   ... ≤ 9 * a n + 2 : 
      by {apply (nat.add_le_add_iff_le_right _ _ _).mpr,
          exact nat.mul_le_mul_left 9 ih,}  
end

lemma square_le : ∀ n, n ^ 2 ≤ a n 
| 0 := le_refl 0
| (nat.succ m) := 
   have cond (nat.bodd m) (nat.succ (nat.div2 m)) (nat.div2 m) < nat.succ m := wf_lemma' m,
   begin
    let e := nat.bodd_add_div2 m.succ,
    rw[nat.bodd_succ] at e,
    rw[← e],
    rcases m.bodd;
    simp only[bnot,bool.cond_ff,bool.cond_tt,zero_add],
    {intros u0 u1,
     rw[nat.add_comm 1],
     exact a_odd_step m.succ.div2 (square_le m.succ.div2),
    },{
     intros u0 u1,
     by_cases h : m.succ.div2 = 0,
     {exfalso,rw[h,mul_zero] at u0,exact nat.succ_ne_zero m u0.symm},
     exact a_even_step m.succ.div2 (nat.pos_of_ne_zero h) (square_le m.succ.div2),
    }
   end

end Q16


end exercises_1
end MAS114