import algebra.ring data.equiv.basic
import commutative_algebra.bool_field
import tactic.pi_instances tactic.squeeze

universes u v
variables (U : Type u) (V : Type v)

def ring_of_bool_subsets := (U → bool)

instance : comm_ring (ring_of_bool_subsets U) := 
 by { unfold ring_of_bool_subsets, pi_instance, }

lemma val_zero (x : U) : (0 : ring_of_bool_subsets U) x = ff := rfl
lemma val_one  (x : U) : (1 : ring_of_bool_subsets U) x = tt := rfl
lemma val_neg  (f : ring_of_bool_subsets U) (x : U) : (- f) x = f x := rfl
lemma val_add  (f g : ring_of_bool_subsets U) (x : U) : (f + g) x = bxor (f x) (g x) := rfl
lemma val_mul  (f g : ring_of_bool_subsets U) (x : U) : (f * g) x = band (f x) (g x) := rfl

open classical 

def ring_of_subsets := set V

namespace ring_of_subsets

local attribute [instance] classical.dec

instance : has_zero (ring_of_subsets V) := ⟨(∅ : set V)⟩ 

instance : has_one  (ring_of_subsets V) := ⟨(set.univ : set V)⟩ 

instance : has_neg  (ring_of_subsets V) := ⟨(λ s, s)⟩ 

instance : has_add  (ring_of_subsets V) :=
 ⟨(λ s t : set V, (s \ t ∪ t \ s : set V))⟩ 

instance : has_mul (ring_of_subsets V) :=
 ⟨(λ s t : set V, (s ∩ t : set V))⟩ 

instance : has_mem V (ring_of_subsets V) := 
 ⟨λ (x : V) (s : set V), x ∈ s⟩  

variable (x : V)

lemma mem_zero_iff : x ∈ (0 : ring_of_subsets V) ↔ false := 
 (iff_false _).mpr (set.not_mem_empty x)

lemma mem_one_iff : x ∈ (1 : ring_of_subsets V) ↔ true := 
 (iff_true _).mpr (set.mem_univ x)

lemma mem_neg_iff (s : ring_of_subsets V) : x ∈ (- s) ↔ x ∈ s := 
 by { change x ∈ s ↔ x ∈ s, refl }

lemma mem_add_iff (s t : ring_of_subsets V) : 
 x ∈ s + t ↔ ((x ∈ s ∧ x ∉ t) ∨ (x∈ t ∧ x ∉ s)) := 
 by { unfold has_add.add, rw[set.mem_union,set.mem_diff,set.mem_diff],} 
 
lemma mem_mul_iff (s t : ring_of_subsets V) : 
 x ∈ s * t ↔ (x ∈ s ∧ x ∈ t) := 
 by { unfold has_mul.mul, rw[set.mem_inter_iff], }

instance : comm_ring (ring_of_subsets V) := {
  zero := (0 : ring_of_subsets V), one := 1, 
  neg := has_neg.neg, add := (+), mul := (*),
  add_zero := λ a, by { ext x, rw[mem_add_iff, mem_zero_iff], simp },
  zero_add := λ a, by { ext x, rw[mem_add_iff, mem_zero_iff], simp },
  add_left_neg := λ a, begin 
    ext x, rw[mem_add_iff, mem_neg_iff, mem_zero_iff], 
    by_cases ha : x ∈ a;
    simp[ha]
  end,
  add_comm := λ a b, begin 
    ext x, rw[mem_add_iff, mem_add_iff],
    by_cases ha : x ∈ a; by_cases hb : x ∈ b;
    simp[ha,hb]
  end,
  add_assoc := λ a b c, begin 
    ext x, repeat { rw[mem_add_iff] },
    by_cases ha : x ∈ a; by_cases hb : x ∈ b; by_cases hc : x ∈ c; 
    simp[ha,hb,hc],
  end,
  mul_one := λ a, by { ext x, rw[mem_mul_iff, mem_one_iff], simp },
  one_mul := λ a, by { ext x, rw[mem_mul_iff, mem_one_iff], simp },
  mul_comm := λ a b, begin 
    ext x, rw[mem_mul_iff, mem_mul_iff, and_comm],
  end,
  mul_assoc := λ a b c, begin
    ext x, repeat { rw[mem_mul_iff] }, rw[and_assoc],
  end,
  left_distrib := λ a b c, begin
    ext x, rw[mem_add_iff, mem_mul_iff, mem_add_iff, mem_mul_iff, mem_mul_iff],
    by_cases ha : x ∈ a; by_cases hb : x ∈ b;
    simp[ha,hb]
  end,
  right_distrib := λ a b c, begin 
    ext x, rw[mem_add_iff, mem_mul_iff, mem_add_iff, mem_mul_iff, mem_mul_iff],
    by_cases ha : x ∈ a; by_cases hb : x ∈ b;
    simp[ha,hb]
  end
 }

variable {V}

noncomputable def indicator : ring_of_subsets V →+* ring_of_bool_subsets V := { 
 to_fun := λ s x, (if x ∈ s then tt else ff), 
 map_zero' := by { ext x, rw[mem_zero_iff V x,if_false], refl },
 map_add' := λ s t, by { 
  ext x, 
  rw[mem_add_iff, val_add],
  by_cases hs : x ∈ s; by_cases ht : x ∈ t; simp[hs,ht],
 },
 map_one' := by { ext x, rw[mem_one_iff V x,if_true], refl },
 map_mul' := λ s t, by { 
  ext x, 
  rw[mem_mul_iff, val_mul],
  by_cases hs : x ∈ s; by_cases ht : x ∈ t;
  simp[hs, ht],
 }
}

end ring_of_subsets

namespace ring_of_bool_subsets

variable {U}

def support : (ring_of_bool_subsets U) →+* (ring_of_subsets U) := {
 to_fun := λ (f : U → bool), (λ x, f x = tt),
 map_zero' := begin 
  ext x, rw[set.mem_def, val_zero, ring_of_subsets.mem_zero_iff], simp only [],
 end,
 map_add' := λ s t, begin
  ext x, rw[ring_of_subsets.mem_add_iff],
  repeat { rw[set.mem_def] },
  rw[val_add],
  cases (s x); cases (t x); rw[bxor]; exact dec_trivial,
 end,
 map_one' := begin 
  ext x, rw[set.mem_def, val_one, ring_of_subsets.mem_one_iff, eq_self_iff_true]
 end,
 map_mul' := λ s t, begin
  ext x, rw[ring_of_subsets.mem_mul_iff],
  repeat { rw[set.mem_def] },
  rw[val_mul],
  cases (s x); cases (t x); rw[band]; exact dec_trivial,
 end,
}

end ring_of_bool_subsets

namespace ring_of_subsets

noncomputable def bool_equiv : (ring_of_subsets U) ≃ (ring_of_bool_subsets U) := {
 to_fun := @indicator U,
 inv_fun := @ring_of_bool_subsets.support U,
 left_inv := λ s, begin
  haveI := classical.dec,
  rw[ring_of_bool_subsets.support,indicator],
  ext x,dsimp[has_mem.mem,set.mem],
  split_ifs;simp only [h,iff_self,eq_self_iff_true],
 end,
 right_inv := λ f, begin
  ext x,
  dsimp[indicator,ring_of_bool_subsets.support,has_mem.mem,set.mem],
  cases f x; simp,
 end
}


end ring_of_subsets
