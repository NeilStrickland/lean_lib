import data.SL2N data.prat

def smul_num (m : SL2N) (q r : ℚ+) : ℚ+ := 
 ⟨m.a * (q : ℚ) + m.b * (r : ℚ),
  add_pos_of_pos_of_nonneg
   (mul_pos (nat.cast_pos.mpr m.a_pos) q.property)  
   (mul_nonneg (nat.cast_nonneg m.b) (le_of_lt r.property))⟩

def smul_den (m : SL2N) (q r : ℚ+) : ℚ+ := 
 ⟨m.c * (q : ℚ) + m.d * (r : ℚ),
  add_pos_of_nonneg_of_pos
   (mul_nonneg (nat.cast_nonneg m.c) (le_of_lt q.property))  
   (mul_pos (nat.cast_pos.mpr m.d_pos) r.property)⟩

instance : has_scalar SL2N ℚ+ := ⟨λ m q,
 (smul_num m q 1) * (smul_den m q 1)⁻¹ 
⟩ 

theorem smul_num_coe (m : SL2N) (q r : ℚ+) : 
 ((smul_num m q r) : ℚ) = m.a * q + m.b * r := rfl

theorem smul_den_coe (m : SL2N) (q r : ℚ+) : 
 ((smul_den m q r) : ℚ) = m.c * q + m.d * r := rfl

/-
theorem smul_coe (m : SL2N) (q : ℚ+) : 
 ((m • q : ℚ+) : ℚ) = (m.a * (q : ℚ) + m.b) / (m.c * (q : ℚ) + m.d) :=
begin
  change ((m.a : ℚ) * (q : ℚ) + m.b * ((1 : ℚ+) : ℚ)  * 
            (m.c * (q : ℚ) + m.d * ((1 : ℚ+) : ℚ))⁻¹
          = (m.a * (q : ℚ) + m.b) / (m.c * (q : ℚ) + m.d),
 rw[pnat.one_coe,mul_one,mul_one,div_eq_mul_inv],
end

theorem smul_to_prat (m : SL2N) (u : P2) : 
 m • u.to_prat = (m • u).to_prat := by {
 have hn : (smul_num m (u.x / u.y) 1) * u.y = smul_num m u.x u.y := 
  by {apply subtype.eq,
      rw[mul_val,smul_num_val,smul_num_val,one_val,mul_one,
         add_mul,mul_val,inv_val,mul_assoc,mul_assoc],
      rw[inv_mul_cancel (ne_of_gt r.property),mul_one],},
}

theorem smul_div (m : SL2N) (q r : ℚ+) : 
 m • (q * r⁻¹) = (smul_num m q r) * (smul_den m q r)⁻¹ := 
by {
 have hn : (smul_num m (q * r⁻¹) 1) * r = smul_num m q r := 
  by {apply subtype.eq,
      rw[mul_val,smul_num_val,smul_num_val,one_val,mul_one,
         add_mul,mul_val,inv_val,mul_assoc,mul_assoc],
      rw[inv_mul_cancel (ne_of_gt r.property),mul_one],},
 have hd : (smul_den m (q * r⁻¹) 1) * r = smul_den m q r := 
  by {apply subtype.eq,
      rw[mul_val,smul_den_val,smul_den_val,one_val,mul_one,
         add_mul,mul_val,inv_val,mul_assoc,mul_assoc],
      rw[inv_mul_cancel (ne_of_gt r.property),mul_one],},
 rw[← hn,← hd,mul_inv,mul_assoc,mul_comm r,mul_assoc],
 rw[inv_mul_self r,mul_one],refl,
}

instance : mul_action SL2N ℚ+ := {
 smul := has_scalar.smul,
 one_smul := λ q,
  by {apply subtype.eq,
      rw[smul_val,one_a,one_b,one_c,one_d,
         nat.cast_zero,nat.cast_one,zero_mul,one_mul,
         add_zero,zero_add,div_one],},
 mul_smul := λ m n q,
  by {
   let u := (smul_num m (smul_num n q 1) (smul_den n q 1)),
   let v := (smul_den m (smul_num n q 1) (smul_den n q 1)),
   let x := smul_num (m * n) q 1,
   let y := smul_den (m * n) q 1,
   suffices huyvx : u * y = v * x,
   {exact calc
     (m * n) • q = x * y⁻¹ : rfl
      ... = (v⁻¹ * (v * x)) * y⁻¹ : 
       by {rw[← mul_assoc v⁻¹,inv_mul_self v,one_mul]}
      ... = (v⁻¹ * (u * y)) * y⁻¹ : by {rw[← huyvx]}
      ... = u * v⁻¹ : by {rw[mul_assoc,mul_assoc,mul_inv_self y,mul_one,mul_comm]}
      ... = m • (n • q) : (smul_div m _ _).symm
    },
    apply subtype.eq,rw[mul_val,mul_val],
    dsimp[u,v,x,y],
    simp only [smul_num_val,smul_den_val,one_val,mul_a,mul_b,mul_c,mul_d],
    simp only [mul_one,one_mul,mul_add,add_mul,nat.cast_add,nat.cast_mul],
    repeat {rw[mul_assoc]},
    ring,
  }
}

theorem S_smul_val (q : ℚ+) : (S • q).val = q.val + 1 := 
by {
 change (1 * q.val + 1 * (1 : ℚ+).val) * 
        (0 * q.val + 1 * (1 : ℚ+).val)⁻¹ = 
          q.val + 1,
 rw[one_val,zero_mul,zero_add,one_mul,one_mul],
 have : (1 : ℚ)⁻¹ = 1 := rfl, rw[this,mul_one],
}

theorem T_smul_val (q : ℚ+) : (T • q).val = q.val / (q.val + 1) := 
by {
 change (1 * q.val + 0 * (1 : ℚ+).val) * 
        (1 * q.val + 1 * (1 : ℚ+).val)⁻¹ = 
          q.val / (q.val + 1),
 rw[div_eq_mul_inv],
 rw[one_val,zero_mul,add_zero,one_mul,one_mul]
}

end prat

namespace P2

def to_prat (u : P2) : ℚ+ := 
 ⟨u.x / u.y,by {
  have hx : (u.x : ℚ) > 0 := nat.cast_pos.mpr u.x_pos,
  have hy : (u.y : ℚ) > 0 := nat.cast_pos.mpr u.y_pos,
  exact div_pos hx hy,}⟩

theorem to_prat_val (u : P2) : u.to_prat.val = u.x / u.y := rfl

def of_prat (q : ℚ+) : P2 := 
 { x := q.val.num.nat_abs,
   y := q.val.denom,
   x_pos := int.nat_abs_pos_of_ne_zero (ne_of_gt (rat.num_pos_iff_pos.mpr q.property)),
   y_pos := q.val.pos
 }


theorem to_of_prat (q : ℚ+) : to_prat (of_prat q) = q := 
begin
 symmetry,apply subtype.eq,
 change q.val = (q.val.num.nat_abs) / (q.val.denom),
 have n_pos : q.val.num > 0 := rat.num_pos_iff_pos.mpr q.property,
 have hn := int.eq_nat_abs_of_zero_le (le_of_lt n_pos),
 have : (q.val.num : ℚ) = q.val.num.nat_abs := 
  by {rw[← int.cast_coe_nat,← hn],},
 rw[← this,← rat.num_denom'' q.val],
end

end P2

-/
