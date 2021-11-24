/-
Copyright (c) 2020 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

It is known that epimorphisms in the category of groups
are always surjective, and monomorphisms are always regular.  
These facts are also useful for giving Lean-friendly proofs of 
various facts that do not explicitly involve category theory.
The tidiest proof (which we learned from Todd Trimble via the
nLab) involves the construction that we formalize here.  
It is the semidirect product for the evident action of a 
group `G` on `(G → bool)`.  Here we treat `bool` as a group 
under `bxor`, so it is morally `ℤ/2`, but `bool` is more
natural in the Lean context. 
-/

import algebra.group.hom 
import group_theory.subgroup.basic
import tactic.interactive tactic.squeeze tactic.suggest

namespace group_theory

variables (G : Type*) [group G]

/- Elements of the subgroup classifier are represented as 
   `T g u` with `g : G` and `u : G → bool`. 
-/
inductive subgroup_classifier
| T : G → (G → bool) → subgroup_classifier

namespace subgroup_classifier

instance : group (subgroup_classifier G) := {
  one := T 1 (λ _,ff),
  mul := λ ⟨g,u⟩ ⟨h,v⟩, T (g * h) (λ x, bxor (u (h * x)) (v x)),
  inv := λ ⟨g,u⟩, T g⁻¹ (λ x, u (g⁻¹ * x)), 
  one_mul := λ ⟨g,u⟩, 
  begin
    change T (1 * g) _ = T g u, rw [one_mul], congr' 1,
    funext x, exact ff_bxor _
  end,
  mul_one := λ ⟨g,u⟩,
  begin
    change T (g * 1) _ = T g u, rw [mul_one], congr' 1,
    funext x, rw [one_mul], exact bxor_ff _
  end,
  mul_assoc := λ ⟨g,u⟩ ⟨h,v⟩ ⟨k,w⟩, 
  begin 
    change T ((g * h) * k) _ = T (g * (h * k)) _, rw [mul_assoc], congr' 1,
    funext x, simp only [], rw [mul_assoc, bool.bxor_assoc] 
  end,
  mul_left_inv := λ ⟨g,u⟩, 
  begin
    change T (g⁻¹ * g) _ = T 1 _, rw[mul_left_inv], congr' 1,
    funext x, change bxor (u (g⁻¹ * (g * x))) (u x) = ff,
    rw [← mul_assoc, mul_left_inv, one_mul, bxor_self]
  end
}

def proj : (subgroup_classifier G) →* G := {
  to_fun := λ ⟨g,u⟩, g,
  map_one' := rfl,
  map_mul' := λ ⟨g,u⟩ ⟨h,v⟩, rfl
}

def inc : G →* (subgroup_classifier G) := {
  to_fun := λ g, T g (λ _, ff),
  map_one' := rfl,
  map_mul' := λ g h,
  begin
    change T (g * h) _ = T (g * h) _, congr' 1
  end
}

variable {G}

/- A decidable subset `S ⊆ G` can be represented by the  
   boolean characteristic function `G → bool` or the 
   corresponding predicate `G → Prop` together with a
   decidability instance.  We will make some constructions
   with the boolean version first and then translate to 
   the propositional case.

   For any such `S` we define a subgroup `core S` of `G`.
   This is just the stabiliser of `S` with respect to the 
   obvious action of `G` on subsets of `G`, although we 
   choose not to formulate it that way.  

   We also define a homomorphism `δ S` from `G` to 
   `subgroup_classifier G` such that the equaliser of `δ S`
   and the trivial inclusion is just the core of `S`.  
   This is the main ingredient in applications of this 
   construction.
-/

def δ₀ (m : G → bool) : G →* (subgroup_classifier G) := {
  to_fun := λ g, T g (λ x, bxor (m (g * x)) (m x) ),
  map_one' := 
  begin 
    change T (1 : G) _ = T (1 : G) _, congr' 1,
    funext x, rw [one_mul, bxor_self] 
  end,
  map_mul' := λ g h,
  begin
    change T (g * h) _ = T (g * h) _, congr' 1,
    funext x, rw [mul_assoc],
    let a := m x, let b := m (h * x), let c := m (g * (h * x)),
    change bxor c a = bxor (bxor c b) (bxor b a),
    rw [bool.bxor_assoc, ← bool.bxor_assoc b, bxor_self b, 
        bool.bxor_comm ff, bxor_ff]
  end
}

def core₀ (m : G → bool) : subgroup G := {
 carrier := { g | ∀ y, m (g * y) = m y },
 one_mem' := by { intro a, rw[one_mul] },
 mul_mem' := by { intros a b ha hb c, rw[mul_assoc,ha,hb] },
 inv_mem' := by { intros a ha b, rw [← ha (a⁻¹ * b), ← mul_assoc, mul_right_inv, one_mul]}
}

def δ (S : set G) [decidable_pred S] : G →* (subgroup_classifier G) := 
  δ₀ (λ x, to_bool (S x))

def core (S : set G) [decidable_pred S] : subgroup G := 
  core₀ (λ x, to_bool (S x))

lemma to_bool_eq_iff_iff {p q : Prop} [decidable p] [decidable q] : 
  (to_bool p = to_bool q) ↔ (p ↔ q) := 
by { by_cases hp : p; by_cases hq : q; simp [hp, hq] }

lemma bxor_eq_ff_iff {a b : bool} : bxor a b = ff ↔ a = b := 
  by { cases a; cases b; simp only [bxor, eq_true_intro rfl] }

lemma mem_core_iff (g : G) (S : set G) [dS : decidable_pred S] : 
  g ∈ core S ↔ (∀ y, g * y ∈ S ↔ y ∈ S) := 
begin
  change g ∈ core S ↔ (∀ y, S (g * y) ↔ S y), 
  dsimp [core, core₀], split; intros h y,
  { rw [← to_bool_eq_iff_iff], exact h y },
  { rw [  to_bool_eq_iff_iff], exact h y }
end

lemma core_of_subgroup (H : subgroup G) [decidable_pred (H : set G)] : 
  core (H : set G) = H := 
begin
  ext a, rw [mem_core_iff],
  split,
  { intro h, replace h := (h 1).mpr H.one_mem,
    rw [mul_one] at h, exact h },
  { intros h y, apply H.mul_mem_cancel_left h }
end

lemma core_from_δ (S : set G) [decidable_pred S] : 
  core S = monoid_hom.eq_locus (δ S) (inc G) := 
begin
  ext a, rw [mem_core_iff],
  change _ ↔ (T a _) = (T a _),
  split, 
  { intro h, congr' 1, funext y,
    rw [bxor_eq_ff_iff, to_bool_eq_iff_iff], exact h y },
  { intro h, 
    have : ∀ {u v : G → bool}, T a u = T a v → u = v := 
      λ u v e, by { injection e },
    intro y,
    exact to_bool_eq_iff_iff.mp (bxor_eq_ff_iff.mp (congr_fun (this h) y)) }
end

end subgroup_classifier
end group_theory

