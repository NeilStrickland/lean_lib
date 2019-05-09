/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file defines a typeclass for biadditive maps, i.e. maps
`m : α → β → γ` (where α, β and γ are commutative additive monoids)
such that `m a b` is an additive function of `a` and also an 
additive function of `b`.  In other words, `m` should be bilinear
over `ℕ`.
-/

import algebra.group algebra.big_operators algebra.module

variables {ι : Type*} {α : Type*} {β : Type*} {γ : Type*}
variables [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]

class is_biadditive (m : α → β → γ) : Prop := 
(zero_mul : ∀ b, m 0 b = 0)
(add_mul  : ∀ a₁ a₂ b, m (a₁ + a₂) b = m a₁ b + m a₂ b)
(mul_zero : ∀ a, m a 0 = 0)
(mul_add  : ∀ a b₁ b₂, m a (b₁ + b₂) = m a b₁ + m a b₂)

namespace is_biadditive

variables (m : α → β → γ) [is_biadditive m]

instance is_hom_right (a : α) : is_add_monoid_hom (m a) := {
 map_zero := is_biadditive.mul_zero m a,
 map_add  := is_biadditive.mul_add m a 
}

instance is_hom_left (b : β) : is_add_monoid_hom (λ a, m a b) := {
 map_zero := is_biadditive.zero_mul m b,
 map_add  := λ a₁ a₂, is_biadditive.add_mul m a₁ a₂ b 
}

lemma sum_mul (s : finset ι) (a : ι → α) (b : β) : 
 m (s.sum a) b = s.sum (λ x, m (a x) b) := 
  (@finset.sum_hom ι α γ s a _ _ (λ a' : α, m a' b) _).symm

lemma mul_sum (s : finset ι) (a : α) (b : ι → β) : 
 m a (s.sum b) = s.sum (λ x, m a (b x)) := 
  (@finset.sum_hom ι β γ s b _ _ (m a) _).symm

end is_biadditive

namespace semiring

variables (R : Type*) [semiring R]

instance : is_biadditive ((*) : R → R → R) := {
 zero_mul := λ b, by {rw[_root_.zero_mul]},
 mul_zero := λ b, by {rw[_root_.mul_zero]},
 add_mul  := λ a₁ a₂ b, by {rw[_root_.add_mul]},
 mul_add  := λ a b₁ b₂, by {rw[_root_.mul_add]},
}

end semiring 

namespace semimodule

variables (R : Type*) [semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]

instance : is_biadditive ((•) : R → M → M) := {
 zero_mul := λ b, by {rw[_root_.zero_smul]},
 mul_zero := λ b, by {rw[_root_.smul_zero]},
 add_mul  := λ a₁ a₂ b, by {rw[_root_.add_smul]},
 mul_add  := λ a b₁ b₂, by {rw[_root_.smul_add]},
}

end semimodule 