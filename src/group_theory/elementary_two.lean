/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

If `G` is a group in which all elements `g` stisfy `g² = 1`, then 
`G` is automatically abelian.  We prove this, and encode the proof
as a typeclass instance.
-/

import algebra.group_power

namespace group_theory

class elementary_two_group (G : Type*) extends (group G) := 
 (square_one : ∀ a : G, a ^ 2 = 1)

instance elementary_two_group_commutes
 (G : Type*) [e : elementary_two_group G] : comm_group G := 
 { mul_comm := 
   begin
    intros a b,
    let h := e.square_one,
    let ea : a * a = 1 := (pow_two a).symm.trans (h a),
    let eb : b * b = 1 := (pow_two b).symm.trans (h b),
    let eab : (a * b) * (a * b) = 1 :=
      (pow_two (a * b)).symm.trans (h (a * b)),
    exact calc
     a * b = (a * 1) * b : by rw[mul_one]
     ... = (a * ((a * b) * (a * b))) * b : by rw[← eab]
     ... = ((a * (a * b)) * (a * b)) * b : by rw[← (mul_assoc a (a * b) (a * b))]
     ... = (b * (a * b)) * b : by rw[← (mul_assoc a a b),ea,one_mul b]
     ... = b * (a * (b * b)) : by rw[mul_assoc b (a * b) b,mul_assoc a b b]
     ... = b * a : by rw[eb,mul_one a]
   end,
   ..e
 }

end group_theory
