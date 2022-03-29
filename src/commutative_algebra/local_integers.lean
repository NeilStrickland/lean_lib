import algebra.ring data.rat data.real.basic data.complex.basic
import data.nat.prime ring_theory.subring.basic
import tactic.ring tactic.squeeze

namespace local_integers

def to_denom (p : ℕ) (b : ℤ) := (p : ℤ) * b + 1

def to_denom' (p : ℕ) (b : ℤ) : ℚ := (to_denom p b)

def denom_prod (p : ℕ) (b₀ b₁ : ℤ) := (p : ℤ) * b₀ * b₁ + b₀ + b₁ 

lemma denom_prod_eq (p : ℕ) (b₀ b₁ : ℤ) : 
 to_denom p (denom_prod p b₀ b₁) = (to_denom p b₀) * (to_denom p b₁) := 
  by { dsimp[denom_prod, to_denom], ring,}

lemma denom_prod_eq' (p : ℕ) (b₀ b₁ : ℤ) : 
 to_denom' p (denom_prod p b₀ b₁) = (to_denom' p b₀) * (to_denom' p b₁) := 
  by { dsimp[to_denom'], rw[← int.cast_mul, denom_prod_eq] }

def is_local (p : ℕ) (q : ℚ) : Prop :=
 ∃ a b : ℤ, q * (to_denom p b) = a

lemma int_mem (p : ℕ) (a : ℤ) : is_local p a := 
 ⟨a,⟨0,by { rw[to_denom, mul_zero, zero_add, ← int.cast_mul, mul_one]}⟩⟩

end local_integers

def local_integers (p : ℕ) : subring ℚ := {
  carrier := { q : ℚ | local_integers.is_local p q },
  zero_mem' := local_integers.int_mem p 0,
  one_mem' := by { rw[← int.cast_one], exact local_integers.int_mem p 1}, 
  add_mem' := λ q₀ q₁  ⟨a₀,⟨b₀,e₀⟩⟩ ⟨a₁,⟨b₁,e₁⟩⟩, begin 
   let a := a₀ * (local_integers.to_denom p b₁) + (local_integers.to_denom p b₀) * a₁,
   let b := local_integers.denom_prod p b₀ b₁,
   have e := calc
    (q₀ + q₁) * (local_integers.to_denom' p b)
     = (q₀ + q₁) * (local_integers.to_denom' p b₀) * (local_integers.to_denom' p b₁) :
      by {rw[local_integers.denom_prod_eq',← mul_assoc],}
     ... = (q₀ * (local_integers.to_denom' p b₀)) * (local_integers.to_denom' p b₁) + 
           (local_integers.to_denom' p b₀) * (q₁ * (local_integers.to_denom' p b₁)) : 
      by ring
     ... = a : by {rw[local_integers.to_denom',local_integers.to_denom',e₀,e₁,
                      ← int.cast_mul,← int.cast_mul,← int.cast_add],},
   exact ⟨a,⟨b,e⟩⟩
  end,
  neg_mem' := λ q ⟨a,⟨b,e⟩⟩, ⟨- a,⟨b,by rw[neg_mul,e,int.cast_neg]⟩⟩,
  mul_mem' := λ q₀ q₁  ⟨a₀,⟨b₀,e₀⟩⟩ ⟨a₁,⟨b₁,e₁⟩⟩, begin 
   let a := a₀ * a₁,
   let b := local_integers.denom_prod p b₀ b₁,
   have e := calc
    (q₀ * q₁) * (local_integers.to_denom' p b)
     = (q₀ * q₁) * (local_integers.to_denom' p b₀) * (local_integers.to_denom' p b₁) :
      by { rw[local_integers.denom_prod_eq', ← mul_assoc] }
     ... = (q₀ * (local_integers.to_denom' p b₀)) * (q₁ * (local_integers.to_denom' p b₁)) : 
      by ring
     ... = a : by {rw[local_integers.to_denom',local_integers.to_denom',e₀,e₁,int.cast_mul]},
   exact ⟨a,⟨b,e⟩⟩
  end
}

namespace local_integers 

instance (p : ℕ) : comm_ring (local_integers p) :=
 by {dsimp[local_integers]; apply_instance}

end local_integers

