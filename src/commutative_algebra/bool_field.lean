import algebra.ring

instance : discrete_field bool := 
begin 
 refine_struct {
  zero := ff, one := tt,
  neg := id, inv := id,
  add := bxor, mul := band,
  zero_ne_one := λ e, by {cases e},
  has_decidable_eq := by { apply_instance }
 };
 try { repeat { intro a, cases a }; exact dec_trivial, },
end

