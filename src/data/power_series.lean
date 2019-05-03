import algebra.ring algebra.pi_instances algebra.big_operators
import data.birange

universes u v

variables (α : Type u) (β : Type v)

def power_series := ℕ → α 

namespace power_series

@[extensionality]
lemma ext {a b : power_series α} : a = b ↔ ∀ k, (a k) = (b k) := 
 ⟨λ e, congr_fun e,λ e,funext e⟩ 

section add_comm_monoid

variable [add_comm_monoid α]
variables a b c : power_series α 
variables i j k n m : ℕ 

instance : add_comm_monoid (power_series α) := 
 by {unfold power_series, apply_instance}

variable {α}

def C (x : α) : power_series α 
| 0 := x
| (n + 1) := 0

lemma C_coeff_zero {x : α} : (C x) 0 = x := rfl
lemma C_coeff_succ {x : α} (k : ℕ) : (C x) (k + 1) = (0 : α) := rfl
lemma C_coeff {x : α} : ∀ (k : ℕ), (C x) k = ite (k = 0) x (0 : α) 
| 0 := by {rw[C_coeff_zero,if_pos rfl],} 
| (k + 1) := by {rw[C_coeff_succ,if_neg (nat.succ_ne_zero k)],}

@[simp]
lemma zero_coeff : (0 : power_series α) k = 0 := rfl

@[simp]
lemma add_coeff : (a + b) k = (a k) + (b k) := rfl

lemma C_zero : C (0 : α) = 0 := 
 by {ext n, rw[zero_coeff],cases n,rw[C_coeff_zero],rw[C_coeff_succ]}

lemma C_add {x y : α} : C (x + y) = C x + C y := 
 by {ext n, rw[add_coeff],cases n,repeat{rw[C_coeff_zero]},
     repeat{rw[C_coeff_succ]},rw[add_zero]}

end add_comm_monoid

section semiring

variable [semiring α] 

variable {α}
variables a b c : power_series α 
variables x y z : α
variables i j k n m : ℕ 

def one : (power_series α)
| 0 := 1
| (k + 1) := 0

instance : has_one (power_series α) := ⟨one⟩ 

lemma one_coeff_zero : (1 : power_series α) 0 = (1 : α) := rfl
lemma one_coeff_succ (k : ℕ) : (1 : power_series α) (k + 1) = (0 : α) := rfl
lemma one_coeff : ∀ (k : ℕ), (1 : power_series α) k = ite (k = 0) (1 : α) (0 : α) 
| 0 := by {rw[one_coeff_zero,if_pos rfl],} 
| (k + 1) := by {rw[one_coeff_succ,if_neg (nat.succ_ne_zero k)],}

lemma C_one : C (1 : α) = 1 :=
 by {ext n,cases n,rw[one_coeff_zero,C_coeff_zero],rw[one_coeff_succ,C_coeff_succ]}

def X : (power_series α)
| 0 := 0
| 1 := 1
| (k + 2) := 0

lemma X_coeff_zero      : (X : power_series α) 0       = 0 := rfl
lemma X_coeff_one       : (X : power_series α) 1       = 1 := rfl
lemma X_coeff_succ_succ : (X : power_series α) (k + 2) = 0 := rfl
lemma X_coeff : ∀ (k : ℕ), (X : power_series α) k = ite (k = 1) 1 0
| 0 := by {rw[X_coeff_zero, if_neg (dec_trivial : 0 ≠ 1)]}
| 1 := by {rw[X_coeff_one, if_pos rfl]}
| (k + 2) := by {have : k + 2 ≠ 1 := λ h, by {cases h},
                 rw[X_coeff_succ_succ,if_neg this],}

def shift : power_series α → power_series α := λ a k, (a (k + 1))

lemma shift_coeff : (shift a) k = a (k + 1) := rfl

lemma shift_zero : shift (0 : power_series α)  = 0 := by { ext, refl, }
lemma shift_one  : shift (1 : power_series α)  = 0 := by { ext, refl, }
lemma shift_C {x : α} : shift (C x) = 0 := by {ext, refl,}
lemma shift_add : shift (a + b) = shift a + shift b := by {ext, refl}

lemma shift_X : shift (X : power_series α) = 1 := 
 by { ext i, cases i with i, 
     {rw[shift_coeff,one_coeff_zero,zero_add,X_coeff_one],},
     {rw[shift_coeff,one_coeff_succ,X_coeff_succ_succ]}}

def smul (x : α) (a : power_series α) : power_series α := λ k, x * (a k)
def rmul (a : power_series α) (x : α) : power_series α := λ k, (a k) * x

@[simp] lemma smul_coeff : smul x a k = x * (a k) := rfl
@[simp] lemma rmul_coeff : rmul a x k = (a k) * x := rfl

lemma shift_smul : shift (smul x a) = smul x (shift a) := by { ext, refl, }
lemma shift_rmul : shift (rmul a x) = rmul (shift a) x := by { ext, refl, }

lemma smul_C : smul x (C y) = C (x * y) := 
by { ext n, cases n, refl, dsimp[smul,C],rw[mul_zero],}

lemma C_smul : rmul (C x) y = C (x * y) := 
by { ext n, cases n, refl, dsimp[rmul,C],rw[zero_mul],}

lemma zero_smul : smul (0 : α) a = 0 := by { ext n, simp only[smul,zero_coeff,zero_mul],} 
lemma rmul_zero : rmul a (0 : α) = 0 := by { ext n, simp only[rmul,zero_coeff,mul_zero],} 
lemma smul_zero : smul x 0 = 0 :=  by { ext n, simp only[smul,zero_coeff,mul_zero],} 
lemma zero_rmul : rmul 0 x = 0 :=  by { ext n, simp only[rmul,zero_coeff,zero_mul],} 

lemma one_smul : smul (1 : α) a = a := by { ext n,rw[smul_coeff,one_mul],}
lemma rmul_one : rmul a (1 : α) = a := by { ext n,rw[rmul_coeff,mul_one],}

lemma add_smul : smul (x + y) a = (smul x a) + (smul y a) := 
 by {ext n, simp only[smul_coeff,add_coeff,add_mul],}
lemma rmul_add : rmul a (x + y) = (rmul a x) + (rmul a y) := 
 by {ext n, simp only[rmul_coeff,add_coeff,mul_add],}
lemma smul_add : smul x (a + b) = smul x a + smul x b := 
 by {ext n, simp only[smul_coeff,add_coeff,mul_add],}
lemma add_rmul : rmul (a + b) x = rmul a x + rmul b x := 
 by {ext n, simp only[rmul_coeff,add_coeff,add_mul],}

def mul : ∀ (a b : power_series α), power_series α 
| a b 0 := (a 0) * (b 0)
| a b (n + 1) := (a (n + 1)) * (b 0) + (mul a b.shift) n

instance : has_mul (power_series α) := ⟨mul⟩ 

lemma mul_coeff_zero : (a * b) 0 = (a 0) * (b 0) := rfl 

lemma mul_coeff_succ :
 (a * b) (n + 1) = (a (n + 1)) * (b 0) + (a * b.shift) n := rfl 

lemma mul_coeff_succ' : 
 (a * b) (n + 1) = (a 0) * (b (n + 1)) + (a.shift * b) n := 
begin
 induction n with n ih generalizing a b,
 {rw[mul_coeff_succ,mul_coeff_zero,mul_coeff_zero,shift_coeff,shift_coeff,zero_add,add_comm],},
 {rw[mul_coeff_succ,ih a b.shift,mul_coeff_succ,shift_coeff,shift_coeff],
  rw[← add_assoc,← add_assoc,add_comm ((a 0) * (b (n + 2)))],
 }
end

lemma mul_eq_sum : 
 (a * b) n = (finset.range (n + 1)).sum (λ i, (a i) * (b (n - i))) := 
begin
 induction n with n ih generalizing a b,
 {rw[mul_coeff_zero,finset.sum_range_succ,finset.range_zero,finset.sum_empty,add_zero],},
 {rw[mul_coeff_succ,finset.sum_range_succ,nat.sub_self,ih a b.shift],
  congr' 1,apply finset.sum_congr rfl,intros i hi,rw[shift_coeff],
  congr,
  exact (nat.succ_sub (nat.le_of_lt_succ (finset.mem_range.mp hi))).symm,
 }
end

lemma C_mul : (C x) * a = smul x a := 
 by {
  ext n, induction n with n ih generalizing a, 
  {rw[mul_coeff_zero,C_coeff_zero,smul]},
  {rw[mul_coeff_succ,ih,C_coeff_succ,_root_.zero_mul (a 0),zero_add,← shift_smul,shift_coeff],}
 }

lemma zero_mul : (0 : power_series α) * a = 0 := 
 by { rw[← C_zero,C_mul,zero_smul,C_zero],}

lemma one_mul : (1 : power_series α) * a = a := 
 by { rw[← C_one,C_mul,one_smul],}

lemma mul_zero : a * (0 : power_series α) = 0 := 
 by {
  ext n, induction n with n ih generalizing a, 
  {rw[mul_coeff_zero,zero_coeff,mul_zero]},
  {rw[mul_coeff_succ,shift_zero,ih,zero_coeff,zero_coeff,zero_coeff,mul_zero,zero_add],}
 }

lemma mul_C : a * (C x) = rmul a x := 
 by {
  ext n, cases n, 
  {rw[mul_coeff_zero,C_coeff_zero,rmul]},
  {rw[mul_coeff_succ,C_coeff_zero,shift_C,mul_zero,zero_coeff,add_zero,rmul],}
 }

lemma mul_one : a * (1 : power_series α) = a := 
 by { rw[← C_one,mul_C,rmul_one] }

lemma add_mul : (a + b) * c = a * c + b * c := 
 by {
  ext n,induction n with n ih generalizing c,
  {simp only [mul_coeff_zero,add_coeff,_root_.add_mul],},
  {rw[add_coeff,mul_coeff_succ,mul_coeff_succ,mul_coeff_succ],
   rw[ih c.shift,add_coeff,add_coeff,_root_.add_mul],
   simp only[add_comm,add_left_comm],}
 }

lemma mul_add : a * (b + c) = a * b + a * c := 
 by {
  ext n,induction n with n ih generalizing b c,
  {simp only [mul_coeff_zero,add_coeff,_root_.mul_add],},
  {rw[add_coeff,mul_coeff_succ,mul_coeff_succ,mul_coeff_succ],
   rw[shift_add,ih b.shift c.shift,add_coeff,add_coeff,_root_.mul_add],
   simp only[add_comm,add_left_comm],}
 }

lemma shift_mul : shift (a * b) = smul (a 0) b.shift + (a.shift * b) := 
 by {
  ext n,rw[shift_coeff,mul_coeff_succ',add_coeff,smul_coeff,shift_coeff],
 }

lemma smul_mul : (smul x a) * b = smul x (a * b) := 
 by {
  ext n,induction n with n ih generalizing b,
  {simp only[mul_coeff_zero,smul_coeff,_root_.mul_assoc]},
  {simp only[mul_coeff_succ,ih,smul_coeff,_root_.mul_add,_root_.mul_assoc],}
 }

lemma mul_rmul : a * rmul b x = rmul (a * b) x := 
 by {
  ext n,induction n with n ih generalizing b,
  {simp only[mul_coeff_zero,rmul_coeff,_root_.mul_assoc]},
  {simp only[mul_coeff_succ,shift_rmul,ih,rmul_coeff,_root_.add_mul,_root_.mul_assoc],}
 }

lemma mul_assoc : a * b * c = a * (b * c) := 
by {
  ext n,
  induction n with n ih generalizing a b c,
  {repeat{rw[mul_coeff_zero]},rw[_root_.mul_assoc]},
  {rw[mul_coeff_succ',mul_coeff_succ',mul_coeff_succ',shift_mul],
   rw[add_mul,add_coeff,smul_mul,smul_coeff,ih,_root_.mul_add],
   rw[mul_coeff_zero,mul_assoc,add_assoc],
  }  
}

variable (α)

instance : semiring (power_series α) := {
  one := (1),
  mul := (*),
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  left_distrib := mul_add,
  right_distrib := add_mul,
  .. (power_series.add_comm_monoid α) 
 }

end semiring

end power_series