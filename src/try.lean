import algebra.ring 
import data.list.min_max data.polynomial
import order.lattice_extra

set_option pp.all false

instance R0 : comm_ring bool := begin
 letI : has_zero bool := ⟨ff⟩,
 letI : has_add bool := ⟨bxor⟩,
 letI : has_neg bool := ⟨id⟩,
 letI : has_one bool := ⟨tt⟩,
 letI : has_mul bool := ⟨band⟩,
 refine_struct {
  zero := (0 : bool),
  add  := (+),
  neg  := id,
  one  := (1 : bool),
  mul  := (*),
  sub  := (+), 
  nsmul := nsmul_rec, npow := npow_rec, zsmul := zsmul_rec
 };
 repeat { rintro ⟨_⟩ }; 
 refl
end
  
instance R1 : comm_ring bool := {
  zero := ff,
  add := bxor,
  neg := id,
  one := tt,
  mul := band,
  zero_add      := by { repeat { rintro ⟨_⟩ };  refl },
  add_zero      := by { repeat { rintro ⟨_⟩ };  refl },
  one_mul       := by { repeat { rintro ⟨_⟩ };  refl },
  mul_one       := by { repeat { rintro ⟨_⟩ };  refl },
  add_left_neg  := by { repeat { rintro ⟨_⟩ };  refl },
  add_comm      := by { repeat { rintro ⟨_⟩ };  refl },
  mul_comm      := by { repeat { rintro ⟨_⟩ };  refl },
  add_assoc     := by { repeat { rintro ⟨_⟩ };  refl },
  mul_assoc     := by { repeat { rintro ⟨_⟩ };  refl },
  left_distrib  := by { repeat { rintro ⟨_⟩ };  refl },
  right_distrib := by { repeat { rintro ⟨_⟩ };  refl }
}