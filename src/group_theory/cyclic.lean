/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

We define finite cyclic groups, in multiplicative notation.
The elements of `Cₙ` are denoted by `r i` for `i : zmod n`.
We prove that an element `g ∈ G` with `gⁿ = 1` gives rise to
a homomorphism `Cₙ → G`.  We also do the case n = ∞ separately.
-/

import data.fintype.basic algebra.power_mod

namespace group_theory

variables (n : ℕ) [fact (n > 0)]

@[derive decidable_eq]
inductive cyclic
| r : (zmod n) → cyclic

namespace cyclic

variable {n}

def log : cyclic n → zmod n := λ ⟨i⟩, i

def log_equiv : (cyclic n) ≃ (zmod n) :=
{ to_fun := log,
  inv_fun := r,
  left_inv := λ ⟨i⟩, rfl,  right_inv := λ i, rfl }

instance : fintype (cyclic n) := fintype.of_equiv (zmod n) log_equiv.symm

lemma card : fintype.card (cyclic n) = n :=
by { rw [fintype.card_congr log_equiv], exact zmod.card n }

def one : cyclic n := r 0

def inv : ∀ (g : cyclic n)  , cyclic n | (r i) := r (-i)

def mul : ∀ (g h : cyclic n), cyclic n | (r i) (r j) := r (i + j)

instance : has_one (cyclic n) := ⟨r 0⟩
lemma one_eq : (1 : cyclic n) = r 0 := rfl

instance : has_inv (cyclic n) := ⟨cyclic.inv⟩
lemma r_inv (i : zmod n) : (r i)⁻¹ = r (- i) := rfl

instance : has_mul (cyclic n) := ⟨cyclic.mul⟩
lemma rr_mul (i j : zmod n) : (r i) * (r j) = r (i + j) := rfl

instance : group (cyclic n) :=
{ one := 1,
  mul := (*),
  inv := has_inv.inv,
  one_mul := λ ⟨i⟩, by rw [one_eq, rr_mul, zero_add],
  mul_one := λ ⟨i⟩, by rw [one_eq, rr_mul, add_zero],
  mul_left_inv := λ ⟨i⟩, by rw [r_inv, rr_mul, neg_add_self, one_eq],
  mul_assoc := λ ⟨i⟩ ⟨j⟩ ⟨k⟩, by simp only [rr_mul, add_assoc] }

section hom_from_gens

variables {M : Type*} [monoid M] {g : M} (hg : g ^ (n : ℕ) = 1)
include g hg

def hom_from_gens₀ : (cyclic n) → M
| (r i) := g ^ i

def hom_from_gens : (cyclic n) →* M := {
   to_fun := hom_from_gens₀ hg,
   map_one' := begin 
    change hom_from_gens₀ hg (r 0) = 1, rw[hom_from_gens₀,pow_mod_zero]
   end,
   map_mul' := λ ⟨i⟩ ⟨j⟩, pow_mod_add hg i j,
 }

lemma hom_from_gens_r  (i : zmod n) : 
  hom_from_gens hg (r i) = g ^ i := rfl

end hom_from_gens
end cyclic

@[derive decidable_eq]
inductive infinite_cyclic
| r : ℤ → infinite_cyclic

namespace infinite_cyclic

def log : infinite_cyclic → ℤ := λ ⟨i⟩, i

def log_equiv : infinite_cyclic ≃ ℤ :=
{ to_fun := log,
  inv_fun := r,
  left_inv := λ ⟨i⟩, rfl,  right_inv := λ i, rfl }

def one : infinite_cyclic := r 0

def inv : ∀ (g : infinite_cyclic)  , infinite_cyclic | (r i) := r (-i)

def mul : ∀ (g h : infinite_cyclic), infinite_cyclic | (r i) (r j) := r (i + j)

instance : has_one (infinite_cyclic) := ⟨r 0⟩
lemma one_eq : (1 : infinite_cyclic) = r 0 := rfl

instance : has_inv (infinite_cyclic) := ⟨infinite_cyclic.inv⟩
lemma r_inv (i : ℤ) : (r i)⁻¹ = r (- i) := rfl

instance : has_mul (infinite_cyclic) := ⟨infinite_cyclic.mul⟩
lemma rr_mul (i j : ℤ) : (r i) * (r j) = r (i + j) := rfl

instance : group (infinite_cyclic) :=
{ one := 1,
  mul := (*),
  inv := has_inv.inv,
  one_mul := λ ⟨i⟩, by rw [one_eq, rr_mul, zero_add],
  mul_one := λ ⟨i⟩, by rw [one_eq, rr_mul, add_zero],
  mul_left_inv := λ ⟨i⟩, by rw [r_inv, rr_mul, neg_add_self, one_eq],
  mul_assoc := λ ⟨i⟩ ⟨j⟩ ⟨k⟩, by simp only [rr_mul, add_assoc] }

def hom_from_gens₀ {G : Type*} [group G] (g : G) : infinite_cyclic → G
| (r i) := g ^ i

def hom_from_gens {G : Type*} [group G] (g : G) : infinite_cyclic →* G := {
  to_fun := hom_from_gens₀ g,
  map_one' := by { rw[one_eq], exact zpow_zero g, },
  map_mul' := λ ⟨i⟩ ⟨j⟩, by { rw[rr_mul], apply zpow_add g, } 
}

def monoid_hom_from_gens₀ {M : Type*} [monoid M] (g : units M) : infinite_cyclic → M
| (r i) := ((g ^ i) : units M)

def monoid_hom_from_gens {M : Type*} [monoid M] (g : units M) : infinite_cyclic →* M := {
  to_fun := monoid_hom_from_gens₀ g,
  map_one' := by { rw[one_eq], refl, },
  map_mul' := λ i j, by { rcases i, rcases j,
   change
    ((g ^ (i + j) : units M) : M) = (g ^ i : units M) * (g ^ j : units M) ,
   rw [← units.coe_mul, zpow_add] 
  }
}

end infinite_cyclic

end group_theory
