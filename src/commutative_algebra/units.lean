import algebra.ring algebra.group_power group_theory.submonoid order.boolean_algebra
import commutative_algebra.nilpotent commutative_algebra.regular
import tactic.ring

universe u
variables {A : Type u} [comm_ring A]

namespace commutative_algebra 

def as_unit (a : A) := {b : A // a * b = 1}

instance inverse_unique (a : A) : subsingleton (as_unit a) := 
 ⟨λ ⟨b₀,h₀⟩ ⟨b₁,h₁⟩ , begin apply subtype.eq, change b₀ = b₁,
  rw[← mul_one b₀,← h₁,← mul_assoc,mul_comm b₀,h₀,one_mul],
 end ⟩ 

inductive is_unit (a : A) : Prop
| mk : as_unit a → is_unit

noncomputable def inv (a : A) (h : is_unit a) : as_unit a := 
 classical.choice $ by { rcases h, exact ⟨h⟩ }

def mk_unit {a : A} (ha : as_unit a) : units A := {
 val := a, inv := ha.val,
 val_inv := ha.property,
 inv_val := by {rw[mul_comm],exact ha.property}
}

theorem val_mk_unit {a : A} (h : as_unit a) : (mk_unit h).val = a := rfl

end commutative_algebra