/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

We define finite cyclic groups, in multiplicative notation.
We prove that an element `g ∈ G` with `gⁿ = 1` gives rise to
a homomorphism `Cₙ → G`.
-/

import data.fintype group_theory.group_action 
 algebra.group_power algebra.big_operators data.zmod.basic
import tactic.ring
import group_theory.pow_mod

namespace group_theory

variable n : ℕ+ 

@[derive decidable_eq]
inductive cyclic 
| r : (zmod n) → cyclic

namespace cyclic 

variable {n}

def log : cyclic n → zmod n := λ ⟨i⟩, i

def log_equiv : (cyclic n) ≃ (zmod n) := {
  to_fun := log,
  inv_fun := r,
  left_inv := λ ⟨i⟩, rfl,  right_inv := λ i, rfl
}

instance : fintype (cyclic n) := 
 fintype.of_equiv (zmod n) log_equiv.symm

lemma card : fintype.card (cyclic n) = n := 
 by {rw[fintype.card_congr log_equiv], exact fintype.card_fin n}

def one : cyclic n := r 0

def inv : ∀ (g : cyclic n), cyclic n 
| (r i) := r (-i)

def mul : ∀ (g h : cyclic n), cyclic n
| (r i) (r j) := r (i + j)

instance : has_one (cyclic n) := ⟨r 0⟩ 
lemma one_eq : (1 : cyclic n) = r 0 := rfl

instance : has_inv (cyclic n) := ⟨cyclic.inv⟩
lemma r_inv (i : zmod n) : (r i)⁻¹ = r (- i) := rfl

instance : has_mul (cyclic n) := ⟨cyclic.mul⟩
lemma rr_mul (i j : zmod n) : (r i) * (r j) = r (i + j) := rfl

instance : group (cyclic n) := {
  one := 1,
  mul := (*),
  inv := has_inv.inv,
  one_mul := λ g, by {cases g, simp[one_eq,r_inv,rr_mul],},
  mul_one := λ g, by {cases g, simp[one_eq,r_inv,rr_mul],},
  mul_left_inv := λ g, by {cases g, simp[one_eq,r_inv,rr_mul],},
  mul_assoc := λ g h k,
   by {cases g, cases h, cases k; simp[rr_mul],},
}

def hom_from_gens 
 {G : Type*} [group G] {g : G}
  (hg : monoid.pow g n = 1) : 
  (cyclic n) → G
| (r i) := pow_mod n hg i

def is_hom_from_gens 
 {G : Type*} [group G] {g : G}
  (hg : g ^ (n : ℕ) = 1) : is_monoid_hom (hom_from_gens hg) := 
begin
 split,
 {dsimp[has_one.one,monoid.one,group.one],refl},
 {rintros ⟨i⟩ ⟨j⟩, 
  change (g ^ (i + j).val) = (g ^ i.val) * (g ^ j.val),
  rw[← pow_add,← nat.mod_add_div (i.val + j.val) n],
  rw[pow_add,pow_mul,hg,one_pow,mul_one,zmod.add_val],
 }
end

end cyclic 

end group_theory