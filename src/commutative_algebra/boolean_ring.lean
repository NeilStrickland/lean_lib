import algebra.ring
import order.boolean_algebra

universe u

variable (α : Type u)

class boolean_ring (α : Type u) extends (ring α) := 
(mul_self : ∀ a : α, a * a = a)

namespace boolean_ring

variable {α}
variables [boolean_ring α]

lemma add_self (a : α) : a + a = 0 := 
begin
  have := mul_self (a + a),
  rw [add_mul, mul_add, mul_self a] at this,
  exact calc
    a + a = (a + a) + (a + a) - (a + a) : (add_sub_cancel _ _).symm
    ... = 0 : by rw [this, sub_self]
end

lemma neg_self (a : α) : - a = a := 
 (eq_neg_of_add_eq_zero (add_self a)).symm

instance : comm_ring α := 
{ mul_comm := λ a b,
  begin
    have h0 := mul_self (a + b),
    rw [mul_add, add_mul, add_mul, mul_self a, mul_self b, add_assoc] at h0,
    have h1 := congr_arg (has_add.add (b * a)) (add_left_cancel h0),
    rw [← add_assoc, add_self (b * a), zero_add] at h1,
    exact add_right_cancel h1
  end,
  .. (by {apply_instance} : ring α) }

open lattice

instance : has_le  α := ⟨λ a b, a * b = a⟩
instance : has_bot α := ⟨0⟩
instance : has_top α := ⟨1⟩
instance : has_sup α := ⟨λ a b, a + b + a * b⟩ 
instance : has_inf α := ⟨λ a b, a * b⟩ 

instance : boolean_algebra α := 
{ le := has_le.le,
  bot := has_bot.bot,
  top := has_top.top,
  sup := has_sup.sup,
  inf := has_inf.inf,
  le_refl := λ a, mul_self a,
  le_antisymm := λ a b (hab : a * b = a) (hba : b * a = b), 
    (hab.symm.trans (mul_comm a b)).trans hba,
  le_trans := λ a b c (hab : a * b = a) (hbc : b * c = b), 
    calc a * c = a * b * c : by {rw[hab],}
      ... = a : by {rw[mul_assoc,hbc,hab]},
  bot_le := λ a, (zero_mul a),
  le_top := λ a, (mul_one a),
  sup_le := λ a b c (hac : a * c = a) (hbc : b * c = b), 
  show (a + b + a * b) * c = (a + b + a * b),
  by rw [add_mul, add_mul, mul_assoc, hac, hbc],
  le_sup_left := λ a b, show a * (a + b + a * b) = a, 
  by rw [mul_add,mul_add,← mul_assoc,mul_self a,add_assoc,
         add_self (a * b),add_zero],
  le_sup_right := λ a b, show b * (a + b + a * b) = b, 
  by rw[mul_comm a b,
        mul_add,mul_add,← mul_assoc,mul_self b,
        add_comm (b * a) b,add_assoc,
        add_self (b * a),add_zero],
  le_inf := λ a b c (hab : a * b = a) (hac : a * c = a), 
  show a * (b * c) = a, by rw [← mul_assoc, hab, hac], 
  inf_le_left := λ a b, show (a * b) * a = a * b, 
  by rw [mul_assoc, mul_comm b a, ← mul_assoc, mul_self a], 
  inf_le_right := λ a b, show (a * b) * b = a * b, 
  by rw [mul_assoc,mul_self b], 
  le_sup_inf := λ a b c, show
    (a + b + a * b) * (a + c + a * c) * (a + b * c + a * (b * c)) = 
    (a + b + a * b) * (a + c + a * c),
  begin
    let ha := mul_self a,
    let hb := mul_self b,
    let hc := mul_self c,
    let u := (a + b + a * b),
    let v := (a + c + a * c),
    let w := (a + b * c + a * (b * c)),
    change u * v * w = u * v,
    have hua : u * a = a :=
    by {rw [mul_comm], dsimp[u],
        rw [mul_add, mul_add, ← mul_assoc, ha,
            add_assoc, add_self, add_zero] },
    have huc : u * c = a * c + b * c + a * b * c := 
    by {dsimp[u],rw[add_mul,add_mul]},
    have huv : u * v = a + b * c + b * c * a := 
    by {dsimp [v],
       rw [mul_add, mul_add, ← mul_assoc u, hua, add_assoc, add_comm (u * c)],
       rw [huc, ← add_assoc (a * c), ← add_assoc (a * c), 
           add_self (a * c), zero_add],
       rw [add_assoc,mul_assoc a,mul_comm a]},
  have haw : a * w = a :=
    by {dsimp [w],
        rw [mul_add, mul_add, ← mul_assoc a, ← mul_assoc a, ← mul_assoc a],
        rw [ha, add_assoc, add_self, add_zero]},
  rw [huv, add_mul, add_mul, mul_assoc (b * c), haw],
  congr' 2,
  dsimp [w],
  rw [mul_add, mul_add, mul_comm a (b * c), ← mul_assoc (b * c) (b * c)],
  rw [mul_self (b * c), add_comm (b * c * a), add_assoc, add_self, add_zero], 
 end,
 compl := λ a, 1 + a,
 sdiff := λ a b, a + a * b,
 sdiff_eq := λ a b, show a + a * b = a * (1 + b), by rw[mul_add,mul_one],
 sup_inf_sdiff := λ a b, show a * b + (a + a * b) + (a * b) * (a + a * b) = a,
  by rw[mul_add,mul_comm (a * b) a,← mul_assoc,mul_self a,mul_self (a * b),
     add_self (a * b),add_zero,add_comm a,← add_assoc,add_self (a * b),zero_add],
  inf_inf_sdiff := λ a b, show a * b * (a + a * b) = 0,
   by rw[mul_add,mul_self (a * b),mul_comm (a * b),← mul_assoc,mul_self a,
          add_self],
  inf_compl_le_bot := λ a, show a * (1 + a) * 0 = a * (1 + a), 
   by rw[mul_zero,mul_add,mul_one,mul_self,add_self],
  top_le_sup_compl := λ a, show 1 * (a + (1 + a) + a * (1 + a)) = 1,
  by rw[one_mul,mul_add,mul_one,mul_self,add_self,add_zero,
           add_comm 1 a,← add_assoc,add_self,zero_add]
}

end boolean_ring