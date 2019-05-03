import algebra.ring data.rat data.real.basic data.complex.basic
import data.nat.prime ring_theory.subring
import tactic.ring

def local_denom (p : ℕ) (b : ℤ) := (p : ℤ) * b + 1

def denom_prod (p : ℕ) (b₀ b₁ : ℤ) := (p : ℤ) * b₀ * b₁ + b₀ + b₁ 

def is_local (p : ℕ) (q : ℚ) : Prop :=
 ∃ a b : ℤ, q * (local_denom p b) = a

def local_integers (p : ℕ) : Type := { q : ℚ // is_local p q }

namespace local_integers

def local_denom' (p : ℕ) (b : ℤ) : ℚ := (local_denom p b)

variables (p : ℕ) 
include p

lemma denom_prod_eq (b₀ b₁ : ℤ) : 
 local_denom p (denom_prod p b₀ b₁) = (local_denom p b₀) * (local_denom p b₁) := 
  by {dsimp[denom_prod,local_denom],ring,}

lemma denom_prod_eq' (b₀ b₁ : ℤ) : 
 local_denom' p (denom_prod p b₀ b₁) = (local_denom' p b₀) * (local_denom' p b₁) := 
  by {dsimp[local_denom'],rw[← int.cast_mul,denom_prod_eq],}

lemma int_mem (a : ℤ) : is_local p a := 
 ⟨a,⟨0,by {rw[local_denom,mul_zero,zero_add,← int.cast_mul,mul_one],}⟩⟩

lemma local_zero : is_local p 0 := int_mem p 0
lemma local_one  : is_local p 1 := int_mem p 1

def local_neg : ∀ q, is_local p q → is_local p (- q) := 
λ q ⟨a,⟨b,e⟩⟩, ⟨- a,⟨b,by rw[neg_mul_eq_neg_mul_symm,e,int.cast_neg]⟩⟩ 

def local_mul : ∀ q₀ q₁, is_local p q₀ → is_local p q₁ → 
 is_local p (q₀ * q₁) := 
 λ q₀ q₁ ⟨a₀,⟨b₀,e₀⟩⟩ ⟨a₁,⟨b₁,e₁⟩⟩,
begin
  let a := a₀ * a₁,
  let b := denom_prod p b₀ b₁,
  have e := calc
   (q₀ * q₁) * (local_denom' p b)
    = (q₀ * q₁) * (local_denom' p b₀) * (local_denom' p b₁) :
     by {rw[denom_prod_eq',← mul_assoc],}
    ... = (q₀ * (local_denom' p b₀)) * (q₁ * (local_denom' p b₁)) : 
     by ring
    ... = a : by {rw[local_denom',local_denom',e₀,e₁,int.cast_mul]},
  exact ⟨a,⟨b,e⟩⟩
end

def local_add : ∀ q₀ q₁, is_local p q₀ → is_local p q₁ → 
 is_local p (q₀ + q₁) := 
 λ q₀ q₁ ⟨a₀,⟨b₀,e₀⟩⟩ ⟨a₁,⟨b₁,e₁⟩⟩,
begin
  let a := a₀ * (local_denom p b₁) + (local_denom p b₀) * a₁,
  let b := denom_prod p b₀ b₁,
  have e := calc
   (q₀ + q₁) * (local_denom' p b)
    = (q₀ + q₁) * (local_denom' p b₀) * (local_denom' p b₁) :
     by {rw[denom_prod_eq',← mul_assoc],}
    ... = (q₀ * (local_denom' p b₀)) * (local_denom' p b₁) + 
          (local_denom' p b₀) * (q₁ * (local_denom' p b₁)) : 
     by ring
    ... = a : by {rw[local_denom',local_denom',e₀,e₁,
                     ← int.cast_mul,← int.cast_mul,← int.cast_add],},
  exact ⟨a,⟨b,e⟩⟩
end

instance : is_subring (is_local p) := {
 zero_mem := local_zero p, one_mem := local_one p, neg_mem := local_neg p,
 add_mem := local_add p, mul_mem := local_mul p
}

instance : comm_ring (local_integers p) :=
 by {dsimp[local_integers]; apply_instance}



end local_integers


