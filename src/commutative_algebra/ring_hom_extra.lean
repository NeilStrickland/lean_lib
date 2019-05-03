import algebra.ring data.nat.cast data.int.basic

universes u v
variables {α : Type u} {β : Type v} [semiring α] [semiring β]
variables (f : α → β) [is_semiring_hom f] 

lemma is_semiring_hom.map_cast (n : ℕ) : f (n : α) = (n : β) :=
begin 
 apply nat.eq_cast (λ n, f (n : α)),
 {change f ((0 : ℕ) : α) = 0,rw[nat.cast_zero,is_semiring_hom.map_zero f], }, 
 {change f ((1 : ℕ) : α) = 1,rw[nat.cast_one ,is_semiring_hom.map_one  f], }, 
 {intros n m, change f((n + m : ℕ) : α) = f n + f m,
  rw[nat.cast_add,is_semiring_hom.map_add f],}
end

variables {γ : Type u} {δ : Type v} [ring γ] [ring δ]
variables (g : γ → δ) [is_ring_hom g]

lemma is_ring_hom.map_cast (n : ℤ) : g (n : γ) = (n : δ) :=
begin 
 apply int.eq_cast (λ n, g (n : γ)),
 {change g ((1 : ℤ) : γ) = 1,rw[int.cast_one ,is_ring_hom.map_one  g], }, 
 {intros n m, change g((n + m : ℤ) : γ) = g n + g m,
  rw[int.cast_add,is_ring_hom.map_add g],}
end

 