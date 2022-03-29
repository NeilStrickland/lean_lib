import algebra.ring data.rat data.real.basic data.complex.basic
import data.nat.prime ring_theory.subring.basic number_theory.zsqrtd.gaussian_int data.zmod.basic
import topology.constructions topology.continuous_function.algebra topology.instances.real
import data.mv_polynomial
import tactic.ring

import commutative_algebra.local_integers 
import commutative_algebra.galois_field_4
import commutative_algebra.ring_of_subsets

namespace sec_rings

variable (n : ℕ+)

/- -------------------------------------------------------- -/
/- defn-ring -/
#print comm_ring

/- eg-numbers -/
#check (by apply_instance : comm_ring ℤ)
#check (by apply_instance : comm_ring ℚ)
#check (by apply_instance : comm_ring ℝ)
#check (by apply_instance : comm_ring ℂ)

#check (by apply_instance : comm_semiring ℕ)
-- #check (by apply_instance : comm_ring ℕ) -- fails

/- -------------------------------------------------------- -/
/- eg-tw-local -/
#check (by apply_instance : comm_ring (local_integers 2))
#check (by apply_instance : comm_ring gaussian_int)

/- -------------------------------------------------------- -/
/- defn-subring -/
#print subring

/- -------------------------------------------------------- -/
/- eg-subrings -/
-- TO DO

/- -------------------------------------------------------- -/
/- eg-modular -/
#check (by apply_instance : comm_ring (zmod n))

/- -------------------------------------------------------- -/
/- eg-trivial-ring -/
def unit_comm_ring : comm_ring unit := by { apply_instance }

/- -------------------------------------------------------- -/
/- eg-square-matrices -/
-- TO DO

/- -------------------------------------------------------- -/
/- eg-F-four -/
#check F4
#check (by apply_instance : field F4) -- from galois_field_4.lean

/- -------------------------------------------------------- -/
/- eg-boolean -/
namespace eg_boolean
universes uS
variables (S : Type uS)
#check (by apply_instance : comm_ring (ring_of_subsets S))
end eg_boolean

/- -------------------------------------------------------- -/
/- defn-binary-product -/

namespace defn_binary_product 

universes uA uB
variables (A : Type uA) (B : Type uB) [comm_ring A] [comm_ring B]

#check (by apply_instance : comm_ring (A × B))
example (a a' : A) (b b' : B) :
 (prod.mk a b) * (prod.mk a' b') = prod.mk (a * a') (b * b')  := rfl

end defn_binary_product 

/- -------------------------------------------------------- -/
/- rem axis-not_subring -/

namespace axis_not_subring

lemma axis_not_subring (A B : Type*) [comm_ring A] [comm_ring B]
 (hB : (1 : B) ≠ 0) {S : subring (A × B)}
 (hS : S.carrier = (λ ab : (A × B), ab.snd = 0)) : false := 
begin
 let h := S.one_mem,
 rw[← subring.mem_carrier, hS] at h,
 exact hB h,
end

end axis_not_subring

/- -------------------------------------------------------- -/
/- rem-infinite-product -/
-- TO DO

/- -------------------------------------------------------- -/
/- defn-map-ring -/

namespace defn_map_ring

universes uA uS
variables (A : Type uA) [comm_ring A] (S : Type uS)

#check (by apply_instance : comm_ring (S → A))

end defn_map_ring

/- -------------------------------------------------------- -/
/- rem-function-rings -/
namespace rem_function_rings
universe uX 
variables (X : Type uX) [topological_space X]

noncomputable def R : (comm_ring (continuous_map X ℝ)) := 
 continuous_map.comm_ring

end rem_function_rings

/- -------------------------------------------------------- -/
/- eg-sunset -/
namespace eg_sunset

def X := { xy : ℝ × ℝ // (xy.1 ^ 2 + xy.2 ^ 2 - 1) * xy.2 = 0 }

noncomputable instance :
 topological_space X := by { unfold X, apply_instance }

@[reducible ]
def CX := continuous_map X ℝ 

noncomputable instance CX_comm_ring : comm_ring CX :=
 by { unfold CX, exact continuous_map.comm_ring }

noncomputable def CX.x : CX := ⟨prod.fst ∘ subtype.val,
 continuous.comp continuous_fst continuous_subtype_val⟩

noncomputable def CX.y : CX := ⟨prod.snd ∘ subtype.val,
 continuous.comp continuous_snd continuous_subtype_val⟩

lemma CX.x_def (xy : X) : CX.x xy = xy.val.1 := rfl
lemma CX.y_def (xy : X) : CX.y xy = xy.val.2 := rfl

lemma CX.rel : (CX.x ^ 2 + CX.y ^2 - 1) * CX.y = 0 := 
begin
 ext ab, rcases ab with ⟨⟨a,b⟩,e⟩, exact e
end

@[derive decidable_eq]
inductive A_gens
| x : A_gens
| y : A_gens

def PX := mv_polynomial A_gens ℝ 
noncomputable instance PX_comm_ring :
 comm_ring PX := by {unfold PX, apply_instance}

noncomputable def PX.x : PX := @mv_polynomial.X ℝ A_gens _ A_gens.x
noncomputable def PX.y : PX := @mv_polynomial.X ℝ A_gens _ A_gens.y

noncomputable def PX.relator : PX := (PX.x ^ 2 + PX.y ^ 2 - 1) * PX.y

noncomputable def φ₀ : ℝ →+* CX := {
 to_fun := λ c, ⟨(λ u, c),continuous_const⟩,
 map_zero' := by { ext, refl },
 map_add' := λ c d, by { ext, refl },
 map_one' := by { ext, refl },
 map_mul' := λ c d, by { ext, refl }
}

noncomputable def φ₁ : A_gens → CX
| A_gens.x := CX.x
| A_gens.y := CX.y

noncomputable def φ : PX →+* CX :=
 mv_polynomial.eval₂_hom φ₀ φ₁

end eg_sunset

/- -------------------------------------------------------- -/
/- defn-general-product -/

-- TO DO

/- -------------------------------------------------------- -/
/- rem-product-subring -/

-- TO DO

/- -------------------------------------------------------- -/
/- eg-padic -/

namespace eg_padic

variables (p : ℕ) [fact (p > 0)]

lemma p_pow_pos (k : ℕ) : fact (p ^ k > 0) := fact.mk begin
 have h : p > 0 := fact.elim (by apply_instance),
 exact pow_pos h k
end

local attribute [instance] p_pow_pos

def P := ∀ (k : ℕ), (zmod (p ^ k))
instance P_ring : comm_ring (P p) := by { unfold P, apply_instance }

def π (k : ℕ) : zmod (p ^ (k + 1)) →+* zmod (p ^ k) := 
 zmod.cast_hom (pow_dvd_pow p (le_of_lt (nat.lt_succ_self k))) (zmod (p ^ k))

def is_coherent (a : P p) := ∀ (k : ℕ), π p k (a (k + 1)) = (a k)

def p_adic_integers : subring (P p) := {
 carrier := is_coherent p,
 zero_mem' := by { intro k, change π p k 0 = 0,
                   exact ring_hom.map_zero _ },
 add_mem'  := by { intros a b ha hb k,
                   change π p k ((a (k + 1)) + (b (k + 1))) = (a k) + (b k),
                   rw[ring_hom.map_add, ha k, hb k],
                 },
 neg_mem'  := by { intros a ha k,
                  change π p k (- (a (k + 1))) = - (a k),
                  rw[ring_hom.map_neg,ha k],
                 },
 one_mem'  := by { intro k, change π p k 1 = 1,
                  exact ring_hom.map_one _ },
 mul_mem'  := by { intros a b ha hb k,
                  change π p k ((a (k + 1)) * (b (k + 1))) = (a k) * (b k),
                  rw[ring_hom.map_mul, ha k, hb k],
                }
}

variables (q : ℕ) [fact q.prime] 

lemma q_pos : fact (q > 0) :=
 ⟨nat.prime.pos (fact.elim (by { apply_instance }))⟩

lemma q_pred (k : ℕ) : (q.pred : (zmod (q ^ k))) = (q : (zmod (q ^ k))) - 1 := 
begin
 have h : q.pred + 1 = q := 
  nat.succ_pred_eq_of_pos (fact.elim (by {apply_instance})),
 symmetry, rw[sub_eq_iff_eq_add, ← nat.cast_one, ← nat.cast_add, h]
end

local attribute [instance] q_pos

def a₀ : ℕ → ℕ
| 0 := 0
| (k + 1) := (a₀ k) + q ^ k

lemma a₀_step (k : ℕ) : a₀ q (k + 1) = 1 + q * (a₀ q k) := 
begin 
 induction k with k ih,
 { dsimp[a₀], rw[pow_zero, mul_zero, zero_add] },
 { have h₀ : 1 + q * (a₀ q (k + 1)) = 1 + q * (a₀ q k) + q ^ (k + 1) := 
    by { rw[a₀, mul_add, add_assoc, pow_succ] },
   have h₁ : a₀ q (k + 2) = a₀ q (k + 1) + q ^ (k + 1) := rfl,
   rw[h₀, h₁, ih]
 }
end

def a : p_adic_integers q := ⟨
 λ k, (a₀ q k), 
begin 
 intro k,
 change π q k (a₀ q (k + 1)) = a₀ q k,
 rw[map_nat_cast,a₀],
 rw[nat.cast_add,zmod.nat_cast_self,add_zero]
end
⟩ 

def b : p_adic_integers q := ⟨λ k, (q : zmod (q ^ k)) - 1,
begin
 intro k,
 change π q k (q - 1) = (q - 1),
 rw[← q_pred, ← q_pred, map_nat_cast],
end
⟩ 

lemma ab : (a q) * (b q) = - 1 := 
begin
 rw[mul_comm],
 ext k,
 change ((q : zmod (q ^ k)) - 1) * (a₀ q k) = - (1 : (zmod (q ^ k))),
 rw[sub_mul, one_mul, sub_eq_iff_eq_add', ← sub_eq_add_neg],
 symmetry,
 rw[sub_eq_iff_eq_add', ← nat.cast_one, ← nat.cast_mul, ← nat.cast_add],
 rw[← a₀_step, a₀, nat.cast_add, zmod.nat_cast_self, add_zero]
end

end eg_padic

end sec_rings