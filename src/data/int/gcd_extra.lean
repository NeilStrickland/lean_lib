import data.int.gcd algebra.gcd_domain

namespace int

def gcd_a (x y : ℤ) : ℤ := 
 x.sign * (nat.gcd_a x.nat_abs y.nat_abs)

def gcd_b (x y : ℤ) : ℤ := 
 y.sign * (nat.gcd_b x.nat_abs y.nat_abs)

lemma nat_abs_eq_sign_mul_self : ∀ (x : ℤ),
 (x.nat_abs : ℤ) = x.sign * x
| (0 : ℕ) := rfl
| ((n + 1) : ℕ) := by {rw[int.nat_abs_of_nat,int.sign,_root_.one_mul],}
| (-[1+ m]) := by {rw[int.nat_abs,int.sign,← neg_eq_neg_one_mul],refl}

lemma gcd_eq_gcd_ab (x y : ℤ) : 
 (gcd_domain.gcd x y) = x * (gcd_a x y) + y * (gcd_b x y) := 
begin
 let d := nat.gcd x.nat_abs y.nat_abs,
 let a := nat.gcd_a x.nat_abs y.nat_abs,
 let b := nat.gcd_b x.nat_abs y.nat_abs,
 change (d : ℤ) = x * (x.sign * a) + y * (y.sign * b),
 let h : (d : ℤ) = x.nat_abs * a + y.nat_abs * b := 
  by {dsimp[d,a,b],exact nat.gcd_eq_gcd_ab x.nat_abs y.nat_abs},
 rw[← _root_.mul_assoc,← _root_.mul_assoc,mul_comm x,mul_comm y],
 rw[← nat_abs_eq_sign_mul_self x,← nat_abs_eq_sign_mul_self y],
 exact h,
end

end int