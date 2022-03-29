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
import order.lattice

namespace lattice
open lattice 

instance wtb_dl_of_dlo (α : Type*) [linear_order α] :
 distrib_lattice (with_top (with_bot α)) := 
 begin 
  exact linear_order.to_distrib_lattice,
 end

instance wtb_bo_of_dlo (α : Type*) [linear_order α] :
 bounded_order (with_top (with_bot α)) := {
  top := ⊤,
  bot := ⊥,
  le_top := λ a, by { exact le_top, },
  bot_le := λ a, by { exact bot_le } 
 }

instance inf_monoid {α : Type*} [semilattice_inf α] [order_top α]:
 comm_monoid α := {
    mul := has_inf.inf,
    one := has_top.top,
    one_mul := λ a, top_inf_eq,
    mul_one := λ a, inf_top_eq,
    mul_comm := @inf_comm α _,
    mul_assoc := @inf_assoc α _,
}

instance sup_monoid {α : Type*} [semilattice_sup α] [order_bot α]:
 comm_monoid α := {
    mul := has_sup.sup,
    one := has_bot.bot,
    one_mul := λ a, bot_sup_eq,
    mul_one := λ a, sup_bot_eq,
    mul_comm := @sup_comm α _,
    mul_assoc := @sup_assoc α _,
}

end lattice

namespace fin

instance (n : ℕ) : distrib_lattice (fin n.succ) := 
 linear_order.to_distrib_lattice

end fin

