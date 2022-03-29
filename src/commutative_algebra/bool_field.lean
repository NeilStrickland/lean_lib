import algebra.field.basic

instance : field bool := {
  zero := ff, one := tt,
  neg := id, inv := id,
  add := bxor, mul := band,
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
  right_distrib := by { repeat { rintro ⟨_⟩ };  refl },
  mul_inv_cancel := λ a ha, by {  cases a, { exact false.elim (ha rfl) }, { refl }},
  inv_zero := rfl,
  exists_pair_ne := by { use tt, use ff }
 }
