import algebra.ring algebra.field.basic

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

instance : field F4 := 
begin 
 letI : has_zero F4 := ⟨F4.zero⟩,
 letI : has_add F4 := ⟨F4.add⟩,
 letI : has_neg F4 := ⟨id⟩,
 letI : has_one F4 := ⟨F4.one⟩,
 letI : has_mul F4 := ⟨F4.mul⟩,
 letI : has_inv F4 := ⟨F4.inv⟩,
 refine_struct {
  zero := F4.zero, add := (+), neg := id, sub := (+), 
  one := F4.one, mul := (*), inv := F4.inv, div := λ a b, a * b⁻¹,
  nsmul := nsmul_rec, npow := npow_rec, 
  zsmul := zsmul_rec, zpow := zpow_rec,
  nsmul_succ' := λ n x, rfl, 
  npow_succ' := λ n x, rfl,
  zsmul_succ' := λ n x, rfl, zsmul_neg' := λ n x, rfl,
  zpow_succ' := λ n x, rfl, zpow_neg' := λ n x, rfl,
  exists_pair_ne := by { use F4.zero, use F4.one }
 };
 try { repeat { intro a, cases a }; exact dec_trivial, },
end

end F4
