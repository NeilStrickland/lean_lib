/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Some additional typeclass instances:

* A set with decidable linear order and top and bottom 
  elements is a bounded distributive lattice
* If we take a set with decidable linear order and 
  adjoin top and bottom elements, we again get a 
  bounded distributive lattice
* A sup-semilattice becomes a monoid under the 
  sup operation.
* Dually, an inf-semilattice becomes a monoid under the
  inf operation.
-/

import data.fin.basic
import order.bounded_lattice

namespace lattice
open lattice 

instance bounded_distrib_lattice_of_linear_order 
  {α : Type*} [linear_order α]
  (top : α) (le_top : ∀ a, a ≤ top)
  (bot : α) (bot_le : ∀ a, bot ≤ a) :
  bounded_distrib_lattice α := {
   top          := top,     bot          := bot,
   le_top       := le_top,  bot_le       := bot_le,
   .. (distrib_lattice_of_linear_order)
  }

instance wtb_bdl_of_dlo (α : Type*) [linear_order α] :
 bounded_distrib_lattice (with_top (with_bot α)) := 
  @lattice.bounded_distrib_lattice_of_linear_order 
   (with_top (with_bot α)) _ 
    has_top.top (λ _, le_top)
    has_bot.bot (λ _, bot_le)

instance inf_monoid {α : Type*} [semilattice_inf_top α] :
 comm_monoid α := {
    mul := has_inf.inf,
    one := has_top.top,
    one_mul := @top_inf_eq α _,
    mul_one := @inf_top_eq α _,
    mul_comm := @inf_comm α _,
    mul_assoc := @inf_assoc α _,
}

instance sup_monoid {α : Type*} [semilattice_sup_bot α] :
 comm_monoid α := {
    mul := has_sup.sup,
    one := has_bot.bot,
    one_mul := @bot_sup_eq α _,
    mul_one := @sup_bot_eq α _,
    mul_comm := @sup_comm α _,
    mul_assoc := @sup_assoc α _,
}

end lattice

namespace fin

instance (n : ℕ) : bounded_distrib_lattice (fin n.succ) := 
 lattice.bounded_distrib_lattice_of_linear_order
 (fin.mk n n.lt_succ_self) (λ i, nat.le_of_lt_succ i.is_lt)
 (fin.mk 0 n.zero_lt_succ) (λ i, nat.zero_le i)

end fin

