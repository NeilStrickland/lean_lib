import data.pnat.basic data.setoid.basic

inductive spread (α : Type*)
| zero : spread
| ps : α → spread
| ng : α → spread

namespace spread

instance {α : Type*} : has_zero (spread α) := ⟨zero⟩ 

lemma zero_def {α : Type*} : (0 : spread α) = zero := rfl

instance {α : Type*} [has_one α] : has_one (spread α) := ⟨ps 1⟩ 

lemma one_def {α : Type*} [has_one α] : (1 : spread α) = ps 1 := rfl

def is_sub {α : Type*} [add_comm_semigroup α] (x y : α) : spread α → Prop
| zero := x = y
| (ps z) := x = y + z
| (ng z) := x + z = y

lemma is_sub_unique {α : Type*} [add_comm_semigroup α]
 (hp : ∀ {x y : α}, x + y ≠ x)
 (hc : ∀ {x y z : α}, x + y = x + z → y = z)
 {x y : α} {z₀ z₁ : spread α} (h₀ : is_sub x y z₀) (h₁ : is_sub x y z₁) : z₀ = z₁ := 
begin
  cases z₀; cases z₁; dsimp[is_sub] at h₀ h₁,
  { refl, },
  { rw[h₀] at h₁, exact (hp h₁.symm).elim },
  { rw[h₀] at h₁, exact (hp h₁).elim },
  { rw[h₁] at h₀, exact (hp h₀.symm).elim },
  { rw[h₀] at h₁, rw[hc h₁] },
  { rw[h₀, add_assoc] at h₁, exact (hp h₁).elim },
  { rw[h₁] at h₀, exact (hp h₀).elim },
  { rw[h₁, add_assoc] at h₀, exact (hp h₀).elim },
  { rw[← h₁] at h₀, rw[hc h₀]}
end

def neg {α : Type*} : (spread α) → (spread α)
| zero := zero
| (ps x) := ng x
| (ng x) := ps x

instance {α : Type*} : has_neg (spread α) := ⟨neg⟩ 

lemma is_sub_swap {α : Type*} [add_comm_semigroup α] {x y : α} {z : spread α}:
 is_sub y x z ↔ is_sub x y (neg z) := 
begin
 cases z; dsimp[neg, is_sub]; exact comm
end

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

section add

variables {α : Type*} [add_comm_semigroup α]
variables (hp : ∀ {x y : α}, x + y ≠ x)
variables (hc : ∀ {x y z : α}, x + y = x + z → y = z) 

def is_add : (spread α) → (spread α) → (spread α) → Prop
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

include hp hc

lemma is_add_unique {a b c₀ c₁ : spread α}
 (h₀ : is_add a b c₀) (h₁ : is_add a b c₁) : c₀ = c₁ := 
begin
 cases a; cases b; 
 cases c₀; dsimp[is_add] at h₀; 
 try { exfalso, assumption }; 
 cases c₁; dsimp[is_add] at h₁;
 try { exfalso, assumption }; 
 try { match_hyp h₀ : _ = _, 
       fail_if_success { match_hyp h₀ : _ = _ + _},
       fail_if_success { match_hyp h₀ : _ + _ = _},
       cases h₀ };
 try { match_hyp h₁ : _ = _, 
       fail_if_success { match_hyp h₁ : _ = _ + _},
       fail_if_success { match_hyp h₁ : _ + _ = _},
       cases h₁ };
  try { refl };
  try { exact (hp h₀).elim };
  try { exact (hp h₁).elim };
  try { rw[← h₀] at h₁, rw[hc h₁] };
  try { rw[← h₀, add_assoc] at h₁, exact (hp h₁).elim, };
  try { rw[← h₀, ← h₁] }
end

omit hp hc

lemma is_add_zero (a a' : spread α) : 
 is_add a zero a' ↔ a = a' :=
begin
 split,
 { cases a; cases a'; dsimp[is_add]; intro h;
   try { exfalso, assumption }; try { cases h ; refl } 
 },{
  intro h, cases h, cases a; dsimp[is_add]; trivial
 }
end 

lemma is_zero_add (a a' : spread α) : 
 is_add zero a a' ↔ a = a' :=
begin
 split,
 { cases a; cases a'; dsimp[is_add]; intro h;
   try { exfalso, assumption }; try { cases h ; refl } 
 },{
  intro h, cases h, cases a; dsimp[is_add]; trivial
 }
end 

include hp

lemma is_add_neg (a z : spread α) : is_add a (- a) z ↔ z = zero := 
begin
 change is_add a (neg a) z ↔ z = zero,
 split,
 { cases a; cases z; intro h; dsimp[neg, is_add] at h;
   try { replace h := hp h };
   try { exfalso, assumption }; 
   try { refl }
 },
 { intro h, rw[h], 
   change is_add a (neg a) zero, cases a; dsimp[neg, is_add]; trivial 
 }
end

omit hp

lemma is_add_comm (a b ab : spread α) : 
 is_add a b ab ↔ is_add b a ab := 
begin
 cases a; cases b; cases ab; dsimp[is_add]; 
 try { trivial };
 try { rw[add_comm b a] };
 try { exact comm }
end

include hp hc

lemma is_add_assoc {a b c ab bc abc : spread α} 
 (hab : is_add a b ab) (hbc : is_add b c bc) (habc : is_add ab c abc) :
 is_add a bc abc :=
begin
 have hp₁ : ∀ {x y : α}, y + x ≠ x := 
   λ x y h, by { rw[add_comm] at h, exact hp h}, 
 have hp₂ : ∀ {x y z : α}, x + (y + z) ≠ y := 
   λ x y z h, by { rw[add_comm x, add_assoc] at h, exact hp h },
 have hc₁ : ∀ { x y z : α}, x + y = z + x → y = z := 
   λ x y z h, by { rw[add_comm z x] at h, exact hc h }, 
 have hc₂ : ∀ { w x y z : α}, w + x = y + (w + z) → x = y + z := 
   λ w x y z h, by { rw[add_comm y, add_assoc, add_comm z] at h, exact hc h }, 
 cases a; cases b; cases c;
 try { rw[is_add_zero] at * }; try { rw[is_zero_add] at * };
 try { match_hyp habc : _ = _, cases habc };
 try { match_hyp hbc : _ = _, cases hbc };
 try { match_hyp hab : _ = _, cases hab }; 
 try { rw[is_add_zero] at * }; try { rw[is_zero_add] at * };
 try { rw[is_add_unique @hp @hc hab habc] };
 try { rw[is_add_unique @hp @hc hbc habc] };
 try { exact is_add_unique @hp @hc hbc habc }; 
 try { refl }; try { assumption };
 cases ab; dsimp[is_add] at hab; try { exfalso, assumption };
 try { rw[is_add_zero] at * }; try { rw[is_zero_add] at * }; 
 rw[← hab] at *; 
 cases bc; dsimp[is_add] at hbc; try { exfalso, assumption };   
 try { rw[is_add_zero] at * }; try { rw[is_zero_add] at * }; 
 rw[← hbc] at *; 
 cases abc;
 try { dsimp[is_add] at habc };
 try { exfalso, assumption };
 try { injection habc with habc'; replace habc := habc' };
 try { dsimp[is_add] };
 rw[← habc] at *;
 repeat { rw[add_assoc] at * };
 try { rw[add_comm], done }; 
 try { exact (hp₁ habc).elim };
 try { exact (hp₁ habc.symm).elim };
 try { exact (hp₂ habc).elim };
 try { exact (hp₂ habc.symm).elim };
 try { rw[hc₁ habc] }; 
 try { rw[hc₁ habc.symm] };
 try { rw[hc₁ hbc] }; 
 try { rw[hc₁ hbc.symm] };
 try { rw[(hc₁ hbc).symm, add_comm], done };
 try { rw[hc₂ habc] }; 
 try { rw[hc₂ habc.symm] };
 try { rw[hc₂ hbc] }; 
 try { rw[add_comm b, add_assoc, add_comm b] }; 
 try { rw[add_comm c, add_assoc, add_comm _ c] }
end

omit hp hc

@[simp]
def add₀ (s : α → α → spread α) : 
  spread α → spread α → spread α
| (zero) (zero) := zero 
| (zero) (ps a) := ps a
| (zero) (ng b) := ng b
| (ps a) (zero) := ps a
| (ps a) (ps b) := ps (a + b)
| (ps a) (ng b) := s a b
| (ng a) (zero) := ng a
| (ng a) (ps b) := s b a
| (ng a) (ng b) := ng (a + b)

include hp hc

lemma add₀_is_add
 (s : α → α → spread α)
 (hs : ∀ a b : α, is_sub a b (s a b)) : 
  ∀ (a b : spread α), is_add a b (add₀ s a b) := 
begin
 have hs' : ∀ {x y : α} {z : spread α} (h : is_sub x y z), 
   is_add (ps x) (ng y) z := 
 λ x y z, begin
  cases z; dsimp[is_sub, is_add]; intro h; rw[h]
 end,
 intros a b, 
 cases a; cases b; dsimp[add₀, is_add]; 
 try { refl }; try { trivial }, 
 { exact hs' (hs a b) },
 { rw[is_add_comm], exact hs' (hs b a) }
end 

lemma add₀_is_add'
 (hp : ∀ {x y : α}, x + y ≠ x)
 (hc : ∀ {x y z : α}, x + y = x + z → y = z) 
 (s : α → α → spread α)
 (hs : ∀ a b : α, is_sub a b (s a b)) 
 {a b c : spread α} : 
 is_add a b c ↔ c = add₀ s a b :=
begin
 have h : is_add a b (add₀ s a b) := add₀_is_add @hp @hc s hs a b,
 split,
 { intro h', exact is_add_unique @hp @hc h' h },
 { intro h', rw[h'], exact h }
end

end add

section mul 

variables {α : Type*} [add_comm_semigroup α] [comm_monoid α]
variable (hp : ∀ {x y : α}, x + y ≠ x)
variable (hc : ∀ {x y z : α}, x + y = x + z → y = z) 
variables (s : α → α → spread α) (hs : ∀ a b : α, is_sub a b (s a b)) 
variable (hd : ∀ a b c : α, a * (b + c) = a * b + a * c) 

include hd

lemma mul_ps_is_sub 
 (x : α) {y z : α} {u : spread α} (h : is_sub y z u) : 
 is_sub (x * y) (x * z) (mul (ps x) u) :=
begin
 cases u; dsimp[is_sub] at h; dsimp[mul, is_sub], 
 { rw[h] }, { rw[h,hd] }, { rw[← h, hd] }
end

lemma mul_ng_is_sub 
 (x : α) {y z : α} {u : spread α} (h : is_sub y z u) : 
 is_sub (x * z) (x * y) (mul (ng x) u) :=
begin
 cases u; dsimp[is_sub] at h; dsimp[mul, is_sub], 
 { rw[h] }, { rw[h,hd] }, { rw[← h, hd] }
end

omit hd 
include s hs hp hc hd

lemma mul_add₀ (a b c : spread α) : 
  a * (add₀ s b c) = add₀ s (a * b) (a * c) :=
begin
    change mul a (add₀ s b c) = add₀ s (mul a b) (mul a c),
    cases a; cases b; cases c;
    dsimp[add₀, mul]; try { rw[hd] }; try { refl }, 
    { have := (mul_ps_is_sub hd a (hs b c)),
      exact is_sub_unique @hp @hc this (hs (a * b) (a * c)) }, 
    { have := (mul_ps_is_sub hd a (hs c b)),
      exact is_sub_unique @hp @hc this (hs (a * c) (a * b)) }, 
    { have := (mul_ng_is_sub hd a (hs b c)),
      exact is_sub_unique @hp @hc this (hs (a * c) (a * b)) }, 
    { have := (mul_ng_is_sub hd a (hs c b)),
      exact is_sub_unique @hp @hc this (hs (a * b) (a * c)) }, 
end

lemma add₀_mul (a b c : spread α) : 
  (add₀ s a b) * c = add₀ s (a * c) (b * c) := 
  by { repeat { rw[mul_comm _ c] }, apply mul_add₀ @hp @hc s hs hd }

variable (α) 

def comm_ring₀ : comm_ring (spread α) := {
   add := add₀ s,
   zero_add := λ a, by { cases a; refl },
   add_zero := λ a, by { cases a; refl },
   add_left_neg := λ a, begin
    have hu := @is_sub_unique α (by apply_instance) @hp @hc,
    cases a,
    { refl },
    { have hz : is_sub a a zero := rfl, exact hu (hs a a) hz },
    { have hz : is_sub a a zero := rfl, exact hu (hs a a) hz }
   end,
   add_comm := λ a b, begin 
     cases a; cases b; change add₀ s _ _ = add₀ s _ _;
     dsimp[add₀]; try { rw add_comm a b }; refl
   end,
   add_assoc := λ a b c, begin
    change add₀ s (add₀ s a b) c = add₀ s a (add₀ s b c),
    set ab := add₀ s a b with hab,
    set bc := add₀ s b c with hbc,
    set abc := add₀ s ab c with habc,
    have hab'  := (add₀_is_add' @hp @hc s hs).mpr hab,
    have hbc'  := (add₀_is_add' @hp @hc s hs).mpr hbc,
    have habc' := (add₀_is_add' @hp @hc s hs).mpr habc,
    rw[← add₀_is_add' @hp @hc s hs], 
    exact is_add_assoc @hp @hc hab' hbc' habc',
   end,
   left_distrib := λ a b c, begin
    apply mul_add₀ @hp @hc s hs hd,
   end,
   right_distrib := λ a b c, begin
    apply add₀_mul @hp @hc s hs hd,
   end,
   .. (by apply_instance : has_neg (spread α)),
   .. (by apply_instance : has_zero (spread α)),
   .. (by apply_instance : comm_monoid (spread α))
 }

end mul 

section le

variables {α : Type*} [linear_order α]

@[simp]
def le : (spread α) → (spread α) → Prop
| (zero) (zero) := true
| (zero) (ps y) := true
| (zero) (ng y) := false
| (ps x) (zero) := false
| (ps x) (ps y) := (x ≤ y) 
| (ps x) (ng y) := false
| (ng x) (zero) := true
| (ng x) (ps y) := true
| (ng x) (ng y) := (y ≤ x)


instance : has_le (spread α) := ⟨le⟩ 

instance : linear_order (spread α) := {
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

end le

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

lemma add_def (x y : prat_f) :
  x + y = ⟨x.num * y.den + x.den * y.num, x.den * y.den⟩ := rfl

lemma add_def' (a b c d : pnat) : 
  (prat_f.mk a b) + (prat_f.mk c d) = (prat_f.mk (a * d + b * c) (b * d)) := 
   by { rw[add_def] }

lemma num_add (x y : prat_f) : (x + y).num = x.num * y.den + x.den * y.num := rfl

lemma den_add (x y : prat_f) : (x + y).den = x.den * y.den := rfl

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

instance : add_left_cancel_semigroup prat_r := {
  add_left_cancel := begin
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h,
    change quot.mk setoid.r (x + y) = quot.mk setoid.r (x + z) at h,
    replace h := quotient.exact h, apply quot.sound,
    rcases x with ⟨a,b⟩, rcases y with ⟨c,d⟩, rcases z with ⟨e,f⟩,
    change c * f = e * d, 
    change (a * d + b * c)  * (b * f) = (a * f + b * e) * (b * d) at h,
    rw[mul_comm b f, mul_comm b d, ← mul_assoc, ← mul_assoc] at h,
    replace h := mul_right_cancel h,
    rw[add_mul, add_mul, mul_assoc a f d, mul_comm f d, ← mul_assoc a d f] at h,
    replace h := _root_.add_left_cancel h,
    rw[mul_assoc, mul_assoc] at h,
    exact mul_left_cancel h
  end,
  .. (by apply_instance : add_comm_semigroup prat_r)
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

lemma lt_add_right (x y : prat_r) : x < x + y := 
begin
 apply lt_of_not_ge, intro h,
 rcases x with ⟨x⟩, rcases y with ⟨y⟩, change x + y ≤ x at h,
 rcases x with ⟨a,b⟩, rcases y with ⟨c,d⟩,
 change (a * d + b * c) * b ≤ a * (b * d) at h,
 rw[_root_.add_mul, mul_assoc a d b, mul_comm d b] at h,
 exact (not_le_of_gt (pnat.lt_add_right (a * (b * d)) (b * c * b))) h,
end

end prat_r

def rat_r := spread prat_r

#check spread.comm_ring₀ prat_r 
 (λ x y, ne_of_gt (prat_r.lt_add_right x y))
 (λ x y z h, add_left_cancel h)