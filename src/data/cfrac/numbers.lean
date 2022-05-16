import data.pnat.basic data.setoid.basic

namespace pnat

instance : covariant_class pnat pnat (+) (≤) := {
  elim := begin
   rintro ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩ (hyz : y ≤ z),
   change x + y ≤ x + z,
   exact add_le_add_left hyz x
  end
}

instance : covariant_class pnat pnat (+) (<) := {
  elim := begin
   rintro ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩ (hyz : y < z),
   change x + y < x + z,
   exact add_lt_add_left hyz x
  end
}

end pnat

inductive spread (α : Type*)
| zero : spread
| ps : α → spread
| ng : α → spread

namespace spread

instance {α : Type*} : has_zero (spread α) := ⟨zero⟩ 

lemma zero_def {α : Type*} : (0 : spread α) = zero := rfl

instance {α : Type*} [has_one α] : has_one (spread α) := ⟨ps 1⟩ 

lemma one_def {α : Type*} [has_one α] : (1 : spread α) = ps 1 := rfl

def is_sub {α : Type*} [has_add α] (x y : α) : spread α → Prop
| zero := x = y
| (ps z) := x = y + z
| (ng z) := x + z = y

def neg {α : Type*} : (spread α) → (spread α)
| zero := zero
| (ps x) := ng x
| (ng x) := ps x

instance {α : Type*} : has_neg (spread α) := ⟨neg⟩ 

@[simp]
def mul {α : Type*} [has_mul α] : (spread α) → (spread α) → (spread α)
| (zero)  _     := zero
| (ps x) (zero) := zero 
| (ps x) (ps y) := ps (x * y)
| (ps x) (ng y) := ng (x * y)
| (ng x) (zero) := zero
| (ng x) (ps y) := ng (x * y)
| (ng x) (ng y) := ps (x * y) 

instance {α : Type*} [has_mul α] : has_mul (spread α) := ⟨mul⟩

instance {α : Type*} [comm_monoid α] : comm_monoid (spread α) := {
  one_mul := λ a, begin
    change mul 1 a = a, rw[one_def], cases a; simp[one_mul] 
  end,
  mul_one := λ a, begin
    change mul a 1 = a, rw[one_def], cases a; simp[mul_one] 
  end,
  mul_comm := λ a b, begin
    change mul a b = mul b a, cases a; cases b; simp[mul_comm],
  end,
  mul_assoc := λ a b c, begin
    change mul (mul a b) c = mul a (mul b c), 
    cases a; cases b; cases c; simp[mul_assoc],
  end,
  .. (by { apply_instance } : has_one (spread α)),
  .. (by { apply_instance } : has_mul (spread α))
}

def is_add {α : Type*} [has_add α] : (spread α) → (spread α) → (spread α) → Prop
| (zero) (zero) (zero) := true
| (zero) (zero) (ps z) := false
| (zero) (zero) (ng z) := false
| (zero) (ps y) (zero) := false
| (zero) (ps y) (ps z) := (y = z)
| (zero) (ps y) (ng z) := false
| (zero) (ng y) (zero) := false
| (zero) (ng y) (ps z) := false
| (zero) (ng y) (ng z) := (y = z)
| (ps x) (zero) (zero) := false
| (ps x) (zero) (ps z) := (x = z)
| (ps x) (zero) (ng z) := false
| (ps x) (ps y) (zero) := false
| (ps x) (ps y) (ps z) := (x + y = z)
| (ps x) (ps y) (ng z) := false
| (ps x) (ng y) (zero) := (x = y)
| (ps x) (ng y) (ps z) := (y + z = x)
| (ps x) (ng y) (ng z) := (x + z = y)
| (ng x) (zero) (zero) := false
| (ng x) (zero) (ps z) := false
| (ng x) (zero) (ng z) := (x = z)
| (ng x) (ps y) (zero) := (x = y)
| (ng x) (ps y) (ps z) := (x + z = y)
| (ng x) (ps y) (ng z) := (y + z = x)
| (ng x) (ng y) (zero) := false
| (ng x) (ng y) (ps z) := false
| (ng x) (ng y) (ng z) := (x + y = z)

@[simp]
def le {α : Type*} [has_le α] : (spread α) → (spread α) → Prop
| (zero) (zero) := true
| (zero) (ps y) := true
| (zero) (ng y) := false
| (ps x) (zero) := false
| (ps x) (ps y) := (x ≤ y) 
| (ps x) (ng y) := false
| (ng x) (zero) := true
| (ng x) (ps y) := true
| (ng x) (ng y) := (y ≤ x)

instance {α : Type*} [has_le α] : has_le (spread α) := ⟨le⟩ 

instance {α : Type*} [linear_order α] : linear_order (spread α) := {
  le_refl := λ a, begin
   cases a with a, trivial, exact (le_refl a), exact (le_refl a)
  end,
  le_trans := λ a b c hab hbc, begin
   cases a; cases b; cases c; 
   try { cases hab }; try { cases hbc }; try { trivial };
   try { exact le_trans hab hbc };
   try { exact le_trans hbc hab }
  end,
  le_antisymm := λ a b hab hba, begin
   cases a; cases b; 
   try { cases hab }; try { cases hba };
   try { cases (le_antisymm (hab : a ≤ b) (hba : b ≤ a)) };
   try { cases (le_antisymm (hab : b ≤ a) (hba : a ≤ b)) };
   refl,
  end,
  le_total := λ a b, begin
   cases a; cases b; 
   try { cases (le_total a b) with h };
   try { left, trivial }; try { right, trivial };
   try { left, assumption }; try { right, assumption }
  end,
  decidable_le := λ a b, begin 
   cases a; cases b;
   try { exact decidable.true }; try { exact decidable.false };
   try { exact (by apply_instance : decidable (a ≤ b)) };
   try { exact (by apply_instance : decidable (b ≤ a)) },
  end,
  .. (by { apply_instance } : has_le (spread α))
}

end spread

@[derive decidable_eq]
structure prat_f : Type := 
(num : pnat) (den : pnat) 

namespace prat_f

@[ext]
lemma ext {x y : prat_f} (hn : x.num = y.num) (hd : x.den = y.den) : x = y := 
begin
 cases x with a b, cases y with c d, cases (hn : a = c), cases (hd : b = d), refl
end

def one' (a : pnat) : prat_f := ⟨a,a⟩

instance : comm_monoid prat_f := {
  one := ⟨1,1⟩,
  mul := λ x y,⟨x.num * y.num, x.den * y.den⟩,
  one_mul := λ x, begin 
    ext1, exact one_mul x.num, exact one_mul x.den,
  end,
  mul_one := λ x, begin 
    ext1, exact mul_one x.num, exact mul_one x.den,
  end,
  mul_comm := λ x y, begin
   ext1, exact mul_comm x.num y.num, exact mul_comm x.den y.den
  end,
  mul_assoc := λ x y z, begin
   ext1, exact mul_assoc _ _ _,  exact mul_assoc _ _ _ 
  end
}

instance : has_inv prat_f := ⟨λ x, ⟨x.den, x.num⟩⟩

lemma inv_inv (x : prat_f) : (x⁻¹)⁻¹ = x := by { ext1; refl }

lemma inv_mul (x y : prat_f) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by { ext1; refl }

instance : add_comm_semigroup prat_f := {
  add := λ x y, ⟨x.num * y.den + x.den * y.num, x.den * y.den⟩,
  add_comm := λ x y, begin
   cases x with a b, cases y with c d,
   ext1,
   { change a * d + b * c = c * b + d * a, rw[add_comm, mul_comm b c, mul_comm a d] },
   { exact mul_comm b d }
  end,
  add_assoc := λ x y z, begin
   cases x with a b, cases y with c d, cases z with e f,
   ext1,
   { change (a * d + b * c) * f + (b * d) * e  = a * (d * f) + b * (c * f + d * e),
     rw[add_mul, mul_add, ← add_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
   },{
     exact mul_assoc b d f
   }
  end
}

lemma mul_add (x y z : prat_f) : x * (y + z) * (one' x.den) = x * y + x * z := 
begin
  cases x with a b, cases y with c d, cases z with e f,
  ext1,
  { change a * (c * f + d * e) * b = (a * c) * (b * f) + (b * d) * (a * e),
    rw[mul_add, add_mul, mul_comm b f, mul_comm d e, mul_comm (b * d) (a * e), mul_comm b d],
    repeat { rw[← mul_assoc] },
  },{
    change b * (d * f) * b = (b * d) * (b * f),
    rw[mul_comm b f],
    repeat { rw[← mul_assoc] }
  }
end

instance : preorder prat_f := {
  le := λ x y, x.num * y.den ≤ y.num * x.den,
  le_refl := λ x, le_refl _,
  le_trans := begin
    rintro ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩ (hxy : a * d ≤ c * b) (hyz : c * f ≤ e * d),
    change a * f ≤ e * b, 
    replace hxy := (mul_le_mul_iff_right f).mpr hxy, 
    replace hyz := (mul_le_mul_iff_left b).mpr hyz,
    rw[← mul_assoc b c f, mul_comm b c] at hyz, 
    have hxz := le_trans hxy hyz,
    rw[mul_assoc a d f, mul_comm d f, ← mul_assoc, ← mul_assoc, mul_comm b e] at hxz,
    exact (mul_le_mul_iff_right d).mp hxz,
  end
}

instance : decidable_rel ((≤) : prat_f → prat_f → Prop) := 
  by { apply_instance }

lemma add_le_add_iff_left (x : prat_f) {y z : prat_f} : x + y ≤ x + z ↔ y ≤ z := 
begin
 cases x with a b, cases y with c d, cases z with e f,
 change (a * d + b * c) * (b * f) ≤ (a * f + b * e) * (b * d) ↔ c * f ≤ e * d,
 rw[add_mul, add_mul, mul_comm b d, mul_assoc a f (d * b), mul_comm f (d * b)],
 repeat { rw[mul_assoc] }, 
 rw[add_le_add_iff_left, mul_le_mul_iff_left, mul_comm b f],
 repeat { rw[← mul_assoc] }, 
 rw[mul_le_mul_iff_right]
end

lemma mul_le_mul_iff_left (x : prat_f) {y z : prat_f} : x * y ≤ x * z ↔ y ≤ z := 
begin
 cases x with a b, cases y with c d, cases z with e f,
 change (a * c) * (b * f) ≤ (a * e) * (b * d) ↔ c * f ≤ e * d,
 rw[mul_comm b f, mul_comm b d, mul_assoc a c, mul_assoc a e, ← mul_assoc c, ← mul_assoc e],
 rw[mul_le_mul_iff_left a, mul_le_mul_iff_right b],
end

def fraceq : setoid prat_f := {
 r := λ x y, x.num * y.den = y.num * x.den,
 iseqv := begin
   split,
   { intro x, refl },
   split,
   { rintro x y (h : x.num * y.den = y.num * x.den), exact h.symm },
   { rintro ⟨a,b⟩ ⟨c,d⟩ ⟨e,f⟩ (hxy : a * d = c * b) (hyz : c * f = e * d),
     change a * f = e * b,
     replace hxy : (a * d) * f = (c * b) * f := congr_fun (congr_arg (*) hxy) f,
     replace hyz : b * (c * f) = b * (e * d) := congr_arg ((*) b) hyz,
     rw[← mul_assoc b c f, mul_comm b c] at hyz, 
     have hxz := hxy.trans hyz,
     rw[mul_assoc a d f, mul_comm d f, ← mul_assoc, ← mul_assoc, mul_comm b e] at hxz,
     exact (mul_left_inj d).mp hxz,
   }
 end
}

lemma fraceq.rel_def (x y : prat_f) : fraceq.rel x y ↔ x.num * y.den = y.num * x.den := 
  by { refl }

instance : decidable_rel fraceq.rel := λ x y, by { rw[fraceq.rel_def], apply_instance }

lemma mul_lift {x₀ y₀ x₁ y₁ : prat_f} (hx : fraceq.rel x₀ x₁) (hy : fraceq.rel y₀ y₁) : 
  fraceq.rel (x₀ * y₀) (x₁ * y₁) :=
begin
  cases x₀ with a₀ b₀, cases x₁ with a₁ b₁, 
  cases y₀ with c₀ d₀, cases y₁ with c₁ d₁, 
  change a₀ * b₁ = a₁ * b₀ at hx,
  change c₀ * d₁ = c₁ * d₀ at hy,
  change (a₀ * c₀) * (b₁ * d₁) = (a₁ * c₁) * (b₀ * d₀),
  rw[mul_assoc a₀ c₀, ← mul_assoc c₀, mul_comm c₀,mul_assoc b₁, ← mul_assoc a₀],
  rw[hx, hy, mul_assoc a₁, ← mul_assoc b₀, mul_comm b₀ c₁],
  repeat { rw[mul_assoc] }
end

lemma add_lift {x₀ y₀ x₁ y₁ : prat_f} (hx : fraceq.rel x₀ x₁) (hy : fraceq.rel y₀ y₁) : 
  fraceq.rel (x₀ + y₀) (x₁ + y₁) :=
begin
  cases x₀ with a₀ b₀, cases x₁ with a₁ b₁, 
  cases y₀ with c₀ d₀, cases y₁ with c₁ d₁, 
  change a₀ * b₁ = a₁ * b₀ at hx,
  change c₀ * d₁ = c₁ * d₀ at hy,
  change (a₀ * d₀ + b₀ * c₀) * (b₁ * d₁) = (a₁ * d₁ + b₁ * c₁) * (b₀ * d₀),
  rw[add_mul, add_mul], 
  rw[mul_assoc a₀ d₀, ← mul_assoc d₀, mul_comm d₀ b₁,mul_assoc b₁, ← mul_assoc a₀, hx],
  rw[mul_assoc b₀ c₀, ← mul_assoc c₀, mul_comm c₀ b₁,mul_assoc b₁, hy],
  rw[mul_comm d₀ d₁, mul_assoc a₁ b₀, ← mul_assoc b₀, mul_comm b₀ d₁],
  rw[mul_comm b₀, mul_assoc b₁, mul_assoc c₁, mul_comm d₀ b₀],
  repeat { rw[mul_assoc] }
end

lemma le_lift {x₀ y₀ x₁ y₁ : prat_f} (hx : fraceq.rel x₀ x₁) (hy : fraceq.rel y₀ y₁) : 
  x₀ ≤ y₀ ↔ x₁ ≤ y₁ :=
begin
  cases x₀ with a₀ b₀, cases x₁ with a₁ b₁, 
  cases y₀ with c₀ d₀, cases y₁ with c₁ d₁, 
  change a₀ * b₁ = a₁ * b₀ at hx,
  change c₀ * d₁ = c₁ * d₀ at hy,
  change (a₀ * d₀ ≤ c₀ * b₀) ↔ (a₁ * d₁ ≤ c₁ * b₁),
  conv { to_lhs, rw[← mul_le_mul_iff_right (b₁ * d₁)], 
         rw[mul_assoc a₀, ← mul_assoc d₀, mul_comm d₀ b₁, mul_assoc b₁, ← mul_assoc a₀, hx],
         rw[mul_comm c₀, mul_assoc b₀ c₀, ← mul_assoc c₀ b₁, mul_comm c₀ b₁], },
  conv { to_rhs, rw[← mul_le_mul_iff_right (b₀ * d₀)],
         rw[mul_comm _ (b₀ * d₀), mul_assoc c₁ b₁, mul_comm b₁, mul_comm b₀],
         rw[mul_assoc d₀ b₀ b₁, ← mul_assoc c₁, ← hy],
         rw[mul_comm d₀ b₀, mul_comm (b₀ * d₀), mul_assoc a₁, ← mul_assoc d₁, mul_comm d₁ b₀],
         rw[mul_assoc b₀, mul_comm d₁ d₀, mul_comm (c₀ * d₁)], },
  repeat { rw[mul_assoc] },
end

lemma mul_one' (x : prat_f) (n : pnat): fraceq.rel x (x * (one' n)) := 
begin 
  cases x with a b, 
  change a * (b * n) = (a * n) * b,
  rw[mul_comm b n, mul_assoc],
end

end prat_f

def prat_r := quotient prat_f.fraceq

namespace prat_r

local attribute [instance] prat_f.fraceq

instance : ordered_comm_monoid prat_r := {
  one := quotient.mk' 1,
  mul := quotient.map₂ (*) (λ x₀ x₁ hx y₀ y₁ hy, prat_f.mul_lift hx hy),
  one_mul := λ x, begin rcases x, change quot.mk setoid.r (1 * x) = _, rw[one_mul] end,
  mul_one := λ x, begin rcases x, change quot.mk setoid.r (x * 1) = _, rw[mul_one] end,
  mul_comm := λ x y, begin
    rcases x, rcases y,
    change quot.mk setoid.r (x * y) = quot.mk setoid.r (y * x),
    rw[mul_comm x y]
  end,
  mul_assoc := λ x y z, begin
    rcases x, rcases y, rcases z,
    change quot.mk setoid.r ((x * y) * z) = quot.mk setoid.r (x * (y * z)),
    rw[mul_assoc]
  end,
  le := quotient.lift₂ (≤) (λ x₀ y₀ x₁ y₁ hx hy, (begin 
    rw[← iff_eq_eq], exact prat_f.le_lift hx hy
    end)),
  le_refl := by { rintro ⟨x⟩, exact le_refl x },
  le_trans := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ (hxy : x ≤ y) (hyz : y ≤ z), exact le_trans hxy hyz },
  le_antisymm := begin
    rintro ⟨⟨a,b⟩⟩ ⟨⟨c,d⟩⟩ (hxy : a * d ≤ c * b) (hyx : c * b ≤ a * d),
    have h : prat_f.fraceq.rel ⟨a,b⟩ ⟨c,d⟩ := le_antisymm hxy hyx,
    exact quot.sound h 
  end,
  mul_le_mul_left := begin
    rintro ⟨x⟩ ⟨y⟩ (hxy : x ≤ y) ⟨z⟩, 
    exact (prat_f.mul_le_mul_iff_left z).mpr hxy
  end
}

instance : add_comm_semigroup prat_r := {
  add := quotient.map₂ (+) (λ x₀ x₁ hx y₀ y₁ hy, prat_f.add_lift hx hy),
  add_comm := λ x y, begin
    rcases x, rcases y,
    change quot.mk setoid.r (x + y) = quot.mk setoid.r (y + x),
    rw[add_comm x y]
  end,
  add_assoc := λ x y z, begin
    rcases x, rcases y, rcases z,
    change quot.mk setoid.r ((x + y) + z) = quot.mk setoid.r (x + (y + z)),
    rw[add_assoc]
  end
}

lemma mul_add (x y z : prat_r) : x * (y + z) = (x * y) + (x * z) := 
begin
  rcases x, rcases y, rcases z,
  change quot.mk setoid.r (x * (y + z)) = quot.mk setoid.r ((x * y) + (x * z)),
  rw[← prat_f.mul_add],
  apply quot.sound,
  change prat_f.fraceq.rel _ _,
  apply prat_f.mul_one'
end

lemma add_mul (x y z : prat_r) : (x + y) * z = (x * z) + (y * z) := 
  by { rw[mul_comm (x + y), mul_comm x, mul_comm y, mul_add] }

instance : linear_order prat_r := {
  le_total := begin
    rintro ⟨⟨a,b⟩⟩ ⟨⟨c,d⟩⟩,
    change a * d ≤ c * b ∨ c * b ≤ a * d,
    apply le_total
  end,
  decidable_le := λ x y, begin
    apply quotient.rec_on_subsingleton₂ x y,
    { intros u v, change decidable (u ≤ v), apply_instance },
    { intros u v, change subsingleton (decidable (u ≤ v)), apply_instance } 
  end,
  .. (by { apply_instance } : ordered_comm_monoid prat_r)
}

end prat_r

