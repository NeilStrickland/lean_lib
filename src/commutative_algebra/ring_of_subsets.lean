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

instance : comm_ring (ring_of_subsets V) := begin
 refine_struct {
  zero := (0 : ring_of_subsets V), one := 1, 
  neg := has_neg.neg, add := (+), mul := (*) 
 }; intros;ext x;
 repeat{rw[mem_add_iff]};repeat{rw[mem_mul_iff]};repeat{rw[mem_neg_iff]};
 repeat{rw[mem_add_iff]};repeat{rw[mem_mul_iff]};repeat{rw[mem_neg_iff]};
 repeat{rw[mem_zero_iff]};repeat{rw[mem_one_iff]};
 try {by_cases ha : x ∈ a};
 try {by_cases hb : x ∈ b};
 try {by_cases hc : x ∈ c};
 try{simp[ha,hb,hc]};
 try{simp[ha,hb]};
 try{simp[ha]},
end

variable {V}

noncomputable def indicator : ring_of_subsets V → ring_of_bool_subsets V := 
 λ s x, (if x ∈ s then tt else ff) 

lemma indicator_val (s : ring_of_subsets V) (x : V) : 
 indicator s x = (if x ∈ s then tt else ff) := rfl

instance : is_ring_hom (@indicator V) := {
 map_one := by { ext x, dsimp[indicator], rw[mem_one_iff V x,if_true], refl,},
 map_mul := λ s t, by { 
  ext x, 
  change indicator (s * t) x = band (indicator s x) (indicator t x),
  dsimp[indicator],rw[mem_mul_iff],
  by_cases hs : x ∈ s; by_cases ht : x ∈ t; simp[hs,ht],
 },
 map_add := λ s t, by { 
  ext x, 
  change indicator (s + t) x = bxor (indicator s x) (indicator t x),
  dsimp[indicator],rw[mem_add_iff],
  by_cases hs : x ∈ s; by_cases ht : x ∈ t; simp[hs,ht],
 },
}

end ring_of_subsets

namespace ring_of_bool_subsets

variable {U}

def support : (ring_of_bool_subsets U) → (ring_of_subsets U) := 
 λ (f : U → bool), (λ x, f x = tt)

lemma mem_support {f : ring_of_bool_subsets U} {x : U} : 
 x ∈ (support f) ↔ f x = tt := by {dsimp[support], refl}

instance : is_ring_hom (@support U) := {
 map_one := begin 
  ext x, rw[mem_support,val_one,ring_of_subsets.mem_one_iff,eq_self_iff_true], 
 end,
 map_mul := λ s t, begin
  ext x, rw[ring_of_subsets.mem_mul_iff],
  repeat{rw[mem_support]},rw[val_mul],
  cases (s x); cases (t x); rw[band]; exact dec_trivial,
 end,
 map_add := λ s t, begin
  ext x, rw[ring_of_subsets.mem_add_iff],
  repeat{rw[mem_support]},rw[val_add],
  cases (s x); cases (t x); rw[bxor]; exact dec_trivial,
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
