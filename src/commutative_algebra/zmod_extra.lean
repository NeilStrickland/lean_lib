import data.zmod.basic algebra.char_p

namespace zmod

universe u
variables {α : Type u} [ring α] {n : ℕ+} 

lemma self_eq_zero : ((n : ℕ) : (zmod n)) = 0 := by {
 apply fin.eq_of_veq, rw[@zmod.val_cast_nat n n,nat.mod_self],refl,
}

lemma cast_eq_cast_mod (h : (n : α) = 0) (k : ℕ) :
 (k : α) = ((k % n) : ℕ) := 
 by {
  change ((n : ℕ) : α) = 0 at h, 
  let k' : ℕ := k % n + n * (k / n),
  exact calc 
   (k : α) = k' : by rw[← nat.mod_add_div k n]
   ... = ((k % n) : ℕ) : by rw[nat.cast_add,nat.cast_mul,h,zero_mul,add_zero],
 }

lemma cast_eq_of_modeq (h : (n : α) = 0) (j k : ℕ) :
  j ≡ k [MOD n] → (j : α) = (k : α) := 
 λ e, by { change j % n = k % n at e, rw[cast_eq_cast_mod h j,cast_eq_cast_mod h k,e], }

instance cast_is_ring_hom' (h : (n : α) = 0) : is_ring_hom (cast : zmod n → α) :=
{ map_one := by {
    let h0 : (1 : zmod n).val = 1 % n := @zmod.one_val n,
    exact calc
     cast 1 = nat.cast (1 : zmod n).val : rfl
     ... = nat.cast (1 % n) : congr_arg nat.cast h0
     ... = nat.cast 1 : (cast_eq_cast_mod h 1).symm
     ... = 1 : nat.cast_one
  },
  map_mul := assume x y : zmod n, show ↑((x * y).val) = ↑(x.val) * ↑(y.val),
    by {rw [zmod.mul_val,← cast_eq_cast_mod h,nat.cast_mul],},
  map_add := assume x y : zmod n, show ↑((x + y).val) = ↑(x.val) + ↑(y.val),
    by {rw [zmod.add_val,← cast_eq_cast_mod h,nat.cast_add] }}

instance zmod_cast_is_ring_hom {n m : ℕ+} (h : (m : ℕ) ∣ (n : ℕ)) : 
 is_ring_hom (cast : (zmod n) → (zmod m)) := 
  zmod.cast_is_ring_hom' (by { 
    let d := (n : ℕ) / (m : ℕ),
    have e : (n : ℕ) = d * (m : ℕ) := nat.eq_mul_of_div_eq_left h rfl,
    change ((n : ℕ) : (zmod m)) = 0,
    rw[e,nat.cast_mul,self_eq_zero,mul_zero],
  })

end zmod