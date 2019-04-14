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

import order.bounded_lattice

namespace lattice
open lattice 

instance bounded_distrib_lattice_of_decidable_linear_order 
  {α : Type*} [decidable_linear_order α]
  (top : α) (le_top : ∀ a, a ≤ top)
  (bot : α) (bot_le : ∀ a, bot ≤ a) :
  bounded_distrib_lattice α := {
   top          := top,     bot          := bot,
   le_top       := le_top,  bot_le       := bot_le,
   .. (lattice.distrib_lattice_of_decidable_linear_order)
  }

instance wtb_bdl_of_dlo (α : Type*) [decidable_linear_order α] :
 bounded_distrib_lattice (with_top (with_bot α)) := 
  @lattice.bounded_distrib_lattice_of_decidable_linear_order 
   (with_top (with_bot α)) _ 
    (has_top.top _) (@lattice.le_top _ _)
    (has_bot.bot _) (@lattice.bot_le _ _)

instance inf_monoid {α : Type*} [semilattice_inf_top α] :
 comm_monoid α := {
    mul := has_inf.inf,
    one := has_top.top α,
    one_mul := @top_inf_eq α _,
    mul_one := @inf_top_eq α _,
    mul_comm := @inf_comm α _,
    mul_assoc := @inf_assoc α _,
}

instance sup_monoid {α : Type*} [semilattice_sup_bot α] :
 comm_monoid α := {
    mul := has_sup.sup,
    one := has_bot.bot α,
    one_mul := @bot_sup_eq α _,
    mul_one := @sup_bot_eq α _,
    mul_comm := @sup_comm α _,
    mul_assoc := @sup_assoc α _,
}

end lattice
