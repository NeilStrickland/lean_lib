import algebra.ring algebra.pi_instances data.rat data.real.basic data.complex.basic
import data.nat.prime ring_theory.subring data.zsqrtd.gaussian_int data.zmod.basic
import ring_theory.subring 
import topology.constructions topology.algebra.continuous_functions topology.instances.real
import data.mv_polynomial
import tactic.ring

import commutative_algebra.local_integers 
import commutative_algebra.galois_field_4
import commutative_algebra.ring_of_subsets
import commutative_algebra.zmod_extra
import commutative_algebra.ring_hom_extra

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
#print is_subring

/- -------------------------------------------------------- -/
/- eg-subrings -/
-- TO DO

/- -------------------------------------------------------- -/
/- eg-modular -/
#check (by apply_instance : comm_ring (zmod n))

/- -------------------------------------------------------- -/
/- eg-trivial-ring -/
def unit_comm_ring : comm_ring unit := begin 
 refine_struct {..}; repeat { rintro ⟨_⟩ }; try {exact unit.star}; refl,
end

/- -------------------------------------------------------- -/
/- eg-square-matrices -/
-- TO DO

/- -------------------------------------------------------- -/
/- eg-F-four -/
#check (by apply_instance : comm_ring F4) -- from galois_field_4.lean

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

lemma axis_not_subring (A B : Type*) [comm_ring A] [comm_ring B]:
 (1 : B) ≠ 0 → (is_subring (λ ab : (A × B), ab.snd = 0)) → false := 
begin
 intros h_ne h_subring,
 let h := h_subring.one_mem,
 dsimp[has_mem.mem,set.mem] at h,
 exact h_ne h,
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

noncomputable def R : (comm_ring {f : X → ℝ // continuous f}) := continuous_comm_ring

end rem_function_rings

/- -------------------------------------------------------- -/
/- eg-sunset -/
namespace eg_sunset

def X := { xy : ℝ × ℝ // (xy.1 ^ 2 + xy.2 ^ 2 - 1) * xy.2 = 0 }

noncomputable instance :
 topological_space X := by { unfold X, apply_instance }

def C := { f : X → ℝ // continuous f }

noncomputable instance C_comm_ring : comm_ring C :=
 by { unfold C, exact continuous_comm_ring }

def C.x : C := ⟨prod.fst ∘ subtype.val,
 continuous.comp continuous_fst continuous_subtype_val⟩

def C.y : C := ⟨prod.snd ∘ subtype.val,
 continuous.comp continuous_snd continuous_subtype_val⟩

lemma C.x_def (xy : X) : C.x.val xy = xy.val.1 := rfl
lemma C.y_def (xy : X) : C.y.val xy = xy.val.2 := rfl

lemma C.rel : (C.x ^ 2 + C.y ^2 - 1) * C.y = 0 := 
begin
 apply subtype.eq,funext u,
 rcases u with ⟨⟨x,y⟩,e⟩, exact e,
end

@[derive decidable_eq]
inductive A_gens
| x : A_gens
| y : A_gens

def P := mv_polynomial A_gens ℝ 
noncomputable instance P_comm_ring :
 comm_ring P := by {unfold P, apply_instance}

noncomputable def P.x : P := @mv_polynomial.X ℝ A_gens _ A_gens.x
noncomputable def P.y : P := @mv_polynomial.X ℝ A_gens _ A_gens.y

noncomputable def P.relator : P := (P.x ^ 2 + P.y ^ 2 - 1) * P.y

def φ₀ : ℝ → C := λ c, ⟨(λ u, c),continuous_const⟩

instance φ₀_hom : is_ring_hom φ₀ := {
 map_one := by {apply subtype.eq,funext u,refl,},
 map_add := λ c d, by {apply subtype.eq,funext u,refl,},
 map_mul := λ c d, by {apply subtype.eq,funext u,refl,},
}

def φ₁ : A_gens → C
| A_gens.x := C.x
| A_gens.y := C.y

noncomputable def φ : P → C := mv_polynomial.eval₂ φ₀ φ₁  
instance φ_hom : is_ring_hom φ := by {unfold φ, apply_instance}

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

variables {p : ℕ} (hp : nat.prime p)

def p_pow : ℕ → ℕ+ := 
 λ k, ⟨p ^ (k + 1),nat.pow_pos hp.pos (k + 1)⟩

lemma p_pow_coe (k : ℕ) : ((p_pow hp k) : ℕ) = p ^ (k + 1) := rfl 

lemma p_pow_dvd (k : ℕ) : ((p_pow hp k) : ℕ) ∣ ((p_pow hp (k + 1)) : ℕ) := 
by { change p ^ (k + 1) ∣ p ^ (k + 2),
     let h0 : k + 1 ≤ k + 2 := le_of_lt (nat.lt_succ_self (k + 1)), 
     let h1 := dvd_refl (p ^ (k + 2)),
     exact nat.pow_dvd_of_le_of_pow_dvd h0 h1,}

lemma p_pow_mod_self (k : ℕ) : ((p ^ (k + 1) : ℕ) : zmod (p_pow hp k)) = 0 := 
 by { have := @zmod.self_eq_zero (p_pow hp k), rw[p_pow_coe] at this,exact this}

lemma p_pow_mod_self' (k : ℕ) : (((p ^ (k + 1) : ℕ) : ℤ) : zmod (p_pow hp k)) = 0 := 
 by { rw[int.cast_coe_nat,p_pow_mod_self], }

lemma p_pow_mod_self'' (k : ℕ) : ((p ^ (k + 1) : ℤ) : zmod (p_pow hp k)) = 0 := 
 by { 
  let e0 := congr_arg (int.cast : ℤ → (zmod (p_pow hp k))) (int.coe_nat_pow p (k + 1)),
  exact e0.symm.trans (p_pow_mod_self' hp k),
 }

def Q (k : ℕ) := zmod (p_pow hp k)

instance (k : ℕ) : comm_ring (Q hp k) := by {unfold Q, apply_instance}

def P := ∀ (k : ℕ), (zmod (p_pow hp k))
instance P_ring : comm_ring (P hp) := by { unfold P, apply_instance }

def π (k : ℕ) : zmod (p_pow hp (k + 1)) → zmod (p_pow hp k) := 
 zmod.cast

instance π_hom (k : ℕ) : is_ring_hom (π hp k) := 
 by { unfold π, 
      exact zmod.zmod_cast_is_ring_hom (p_pow_dvd hp k),
    }

def is_coherent (a : P hp) := ∀ (k : ℕ), π hp k (a (k + 1)) = (a k)

instance : is_subring (is_coherent hp) := {
 zero_mem := by { intro k, change π hp k 0 = 0,
                  exact is_ring_hom.map_zero (π hp k), },
 one_mem  := by { intro k, change π hp k 1 = 1,
                  exact is_ring_hom.map_one (π hp k), },
 neg_mem  := by { intros a ha k,
                  change π hp k (- (a (k + 1))) = - (a k),
                  rw[is_ring_hom.map_neg (π hp k),ha k],
                },
 add_mem  := by { intros a b ha hb k,
                  change π hp k ((a (k + 1)) + (b (k + 1))) = (a k) + (b k),
                  rw[is_ring_hom.map_add (π hp k),ha k,hb k],
                },
 mul_mem  := by { intros a b ha hb k,
                  change π hp k ((a (k + 1)) * (b (k + 1))) = (a k) * (b k),
                  rw[is_ring_hom.map_mul (π hp k),ha k,hb k],
                }
}

def padic_integers := { a : P hp // is_coherent hp a }

instance padic_ring : comm_ring (padic_integers hp) := 
 by { unfold padic_integers, apply_instance }

def a₀ {p : ℕ} (hp : p.prime) : ℕ → ℤ 
| 0 := 1
| (k + 1) := (a₀ k) + p ^ (k + 1)

def a : padic_integers hp := ⟨λ k, (a₀ hp k), 
begin 
 intro k,
 change π hp k (a₀ hp (k + 1)) = a₀ hp k,
 rw[is_ring_hom.map_cast (π hp k),a₀],
 rw[int.cast_add,p_pow_mod_self'',add_zero],
end
⟩ 

def b₀ {p : ℕ} (hp : p.prime) : ℤ := (p : ℤ) - 1

def b : padic_integers hp := ⟨λ k, b₀ hp,
begin
 intro k,
 change π hp k (b₀ hp) = b₀ hp,
 rw[is_ring_hom.map_cast (π hp k)],
end
⟩ 

lemma ab₀ (k : ℕ) : (b₀ hp) * (a₀ hp k) = p ^ (k + 1) - 1 := 
begin
 induction k with k ih,
 {dsimp[a₀,b₀],rw[mul_one,zero_add,pow_one],},
 {dsimp[a₀],rw[mul_add (b₀ hp),ih,b₀,nat.succ_eq_add_one],
  rw[pow_add _ (k + 1) 1,pow_one,sub_mul,mul_comm (p : ℤ)],simp,
 }
end

lemma ab : (a hp) * (b hp) + 1 = 0 := 
begin
 rw[mul_comm],
 apply subtype.eq,ext k,
 let a'  : ℤ := a₀ hp k,
 let b'  : ℤ := b₀ hp,
 have e' : b' * a' + 1 = p ^ (k + 1) := by {dsimp[a',b'],rw[ab₀ hp k],simp,},
 let a'' : zmod (p_pow hp k) := a',
 let b'' : zmod (p_pow hp k) := b',
 change b'' * a'' + 1 = 0,
 exact calc 
  b'' * a'' + 1 = (((b' * a' + 1) : ℤ) : zmod (p_pow hp k)) 
   : by {dsimp[a'',b''],rw[int.cast_add,int.cast_mul,int.cast_one],}
   ... = (p ^ (k + 1) : ℤ) : by {rw[e'],}
   ... = 0 : by rw[p_pow_mod_self''],
end

end eg_padic

end sec_rings