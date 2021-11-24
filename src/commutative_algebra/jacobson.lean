import algebra.ring ring_theory.ideals
import tactic.ring
import commutative_algebra.nilpotent algebra.geom_sum

open commutative_algebra

variables (A : Type*) [comm_ring A]

def is_local := (1 : A) ≠ 0 ∧ ∀ (a : A), (is_unit a) ∨ (is_unit (1 - a))

def is_jacobson (a : A) :=  ∀ (x : A), is_unit (1 + a * x)

def jacobson_radical : ideal A := {
  carrier := λ (a : A), ∀ (x : A), is_unit (1 + a * x),
  zero := λ x, by { rw[zero_mul, add_zero], exact is_unit_one },
  add := λ a b ha hb x, 
  begin
   rcases is_unit_iff_exists_inv.mp (ha x) with ⟨u,hu⟩,
   rcases is_unit_iff_exists_inv.mp (hb (x * u)) with ⟨v,hv⟩,
   apply is_unit_iff_exists_inv.mpr, use (u * v),
   exact calc
    (1 + (a + b) * x) * (u * v) = 
     ((1 + a * x) * u) * v + (b * (x * u)) * v : by ring
    ... = (1 + b * (x * u)) * v : by { rw [hu], ring }
    ... = 1 : hv
  end,
  smul := λ a b hb x, by {
   have : a • b * x = a * b * x := rfl,
   rw [this, mul_comm a b, mul_assoc],
   exact hb (a * x)
  }
}

theorem nilradical_le_jacobson : (nilradical A) ≤ (jacobson_radical A) := 
λ a ⟨⟨n,h⟩⟩ x, 
begin
  apply is_unit_iff_exists_inv.mpr, 
  let u := geom_series (- (a * x)) n, use u,
  have h' : u * _ = _ := geom_sum_mul_neg (- (a * x)) n,
  rw[sub_neg_eq_add, mul_comm, mul_comm a, neg_mul_eq_neg_mul,
     mul_pow, h, mul_zero, sub_zero, mul_comm x] at h',
  exact h'
end