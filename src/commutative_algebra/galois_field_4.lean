import algebra.ring

@[derive decidable_eq]
inductive F4 : Type 
| zero  : F4
| one   : F4
| alpha : F4
| beta  : F4 

namespace F4 

def add : F4 → F4 → F4 
| zero  y     := y
| x     zero  := x
| one   one   := zero
| one   alpha := beta
| one   beta  := alpha 
| alpha one   := beta
| alpha alpha := zero
| alpha beta  := one
| beta  one   := alpha
| beta  alpha := one
| beta  beta  := zero

def mul : F4 → F4 → F4 
| zero  y     := zero 
| one   y     := y 
| x     zero  := zero 
| x     one   := x
| alpha alpha := beta
| alpha beta  := one
| beta  alpha := one
| beta  beta  := alpha

def inv : F4 → F4
| zero  := zero 
| one   := one
| alpha := beta
| beta  := alpha

instance : discrete_field F4 := 
begin 
 refine_struct {
  zero := F4.zero, one := F4.one,
  neg := id, inv := F4.inv,
  add := F4.add, mul := F4.mul,
  zero_ne_one := λ e, by {cases e},
  has_decidable_eq := by { apply_instance }
 };
 try { repeat { intro a, cases a }; exact dec_trivial, },
end

end F4
