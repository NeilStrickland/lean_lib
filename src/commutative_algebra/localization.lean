import algebra.ring group_theory.submonoid ring_theory.ideals linear_algebra.basic
import tactic.ring tactic.abel

namespace localization_alt

universes u v w x

structure prelog_semiring := 
(A : Type u)
(S : Type v)
(i : S → A)
(A_comm_semiring : comm_semiring A)
(S_comm_monoid : comm_monoid S)
(i_hom : is_monoid_hom i)

namespace prelog_semiring
open prelog_semiring 

instance to_comm_semiring (P : prelog_semiring) : comm_semiring P.A :=
 P.A_comm_semiring

instance to_comm_monoid_S (P : prelog_semiring) : comm_monoid P.S :=
 P.S_comm_monoid

instance to_comm_monoid_A (P : prelog_semiring) : comm_monoid P.A := 
 @comm_semiring.to_comm_monoid P.A P.A_comm_semiring

instance to_monoid_S (P : prelog_semiring) : monoid P.S := 
 @comm_monoid.to_monoid P.S (@prelog_semiring.to_comm_monoid_S P)

instance to_monoid_A (P : prelog_semiring) : monoid P.A := 
 @comm_monoid.to_monoid P.A (@prelog_semiring.to_comm_monoid_A P)

instance to_monoid_hom (P : prelog_semiring) : is_monoid_hom P.i := P.i_hom

structure preloc (P : prelog_semiring) :=
(numer : P.A) (denom : P.S)

namespace preloc
open preloc

variable {P : prelog_semiring}

notation a `/₀` s := preloc.mk a s

@[extensionality]
lemma ext : ∀ (a₁ a₂ : P.A) (s₁ s₂ : P.S), a₁ = a₂ → s₁ = s₂ →
 (a₁ /₀ s₁) = (a₂ /₀ s₂) := 
 by { intros; congr; assumption } 

lemma ext' : ∀ {x₁ x₂ : preloc P},
 x₁ = x₂ ↔ (x₁.numer = x₂.numer) ∧ (x₁.denom = x₂.denom) 
| ⟨_,_⟩ ⟨_,_⟩ := by { simp }

instance : comm_monoid (preloc P) := begin
 let one : (preloc P) := (1 /₀ 1),
 let mul : (preloc P) → (preloc P) → (preloc P) := 
  λ x y, ((x.numer * y.numer) /₀ (x.denom * y.denom)),
 let one_mul : ∀ (x : preloc P), mul one x = x := 
 begin
  intro x,cases x with a s,
  exact congr (congr_arg preloc.mk (one_mul a)) (one_mul s),
 end,
 let mul_one : ∀ (x : preloc P), mul x one = x := 
 begin
  intro x,cases x with a s,
  exact congr (congr_arg preloc.mk (mul_one a)) (mul_one s),
 end,
 let mul_comm : ∀ x y, mul x y = mul y x := 
 begin
  intros x y,cases x with a s,cases y with b t,
  exact @congr P.S (preloc P) _ _ _ _ 
    (congr_arg (@preloc.mk P) (mul_comm a b)) (mul_comm s t),
 end,
 let mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z) := 
 begin
  intros x y z,cases x with a s, cases y with b t, cases z with c u,
  exact @congr P.S (preloc P) _ _ _ _ 
    (congr_arg (@preloc.mk P) (mul_assoc a b c)) (mul_assoc s t u),
 end,
 exact {
     one := one, mul := mul,
     mul_one := mul_one, one_mul := one_mul,
     mul_comm := mul_comm, mul_assoc := mul_assoc
 }
end

instance : add_comm_monoid (preloc P) := begin 
 let zero : (preloc P) := (0 /₀ 1),
 let add : (preloc P) → (preloc P) → (preloc P) := 
  λ x y, ((x.numer * (P.i y.denom) + (P.i x.denom) * y.numer) /₀ 
          (x.denom * y.denom)),
 let zero_add : ∀ (x : preloc P), add zero x = x := 
 begin
  intro x,cases x with a s,
  let h0 := (congr_fun (congr_arg P.A_comm_semiring.mul P.i_hom.map_one) a),
  let h1 := congr (congr_arg P.A_comm_semiring.add (zero_mul (P.i s))) h0,
  let h2 := h1.trans ((zero_add (1 * a)).trans (one_mul a)),
  exact congr (congr_arg preloc.mk h2) (one_mul s),
 end,
 let add_zero : ∀ (x : preloc P), add x zero = x := 
 begin
  intro x,cases x with a s,
  dsimp[zero,add],
  let h0 := (congr_arg ((*) a) P.i_hom.map_one).trans (mul_one a),
  let h1 := (congr (congr_arg (+) h0) (mul_zero (P.i s))).trans (add_zero a),
  exact congr (congr_arg preloc.mk h1) (mul_one s),
 end,
 let add_comm : ∀ x y, add x y = add y x := 
 begin
  intros x y,cases x with a s,cases y with b t,
  dsimp[add],
  rw[mul_comm s t,mul_comm a (P.i t),mul_comm (P.i s) b,add_comm],
 end,
 let add_assoc : ∀ x y z, add (add x y) z = add x (add y z) := 
 begin
  intros x y z,cases x with a s, cases y with b t, cases z with c u,
  dsimp[add],
  rw[P.i_hom.map_mul,P.i_hom.map_mul,add_mul,mul_add],
  rw[add_assoc,mul_assoc s t u,mul_assoc a (P.i t) (P.i u),
     mul_assoc (P.i s) b (P.i u),mul_assoc (P.i s) (P.i t) c],
 end,
 exact {
     zero := zero, add := add,
     add_zero := add_zero, zero_add := zero_add,
     add_comm := add_comm, add_assoc := add_assoc
 },
end

lemma numer_def (a : P.A) (s : P.S) : (a /₀ s).numer = a := rfl
lemma denom_def (a : P.A) (s : P.S) : (a /₀ s).denom = s := rfl
lemma numer_zero : @preloc.numer P 0 = 0 := rfl
lemma denom_zero : @preloc.denom P 0 = 1 := rfl
lemma numer_one  : @preloc.numer P 1 = 1 := rfl
lemma denom_one  : @preloc.denom P 1 = 1 := rfl

lemma one_def  : (1 : preloc P) = (1 /₀ 1) := rfl
lemma mul_def (x y : preloc P) : 
 x * y = ((x.numer * y.numer) /₀ (x.denom * y.denom)) := rfl
lemma mul_def' (a b : P.A) (s t : P.S) : 
 (a /₀ s) * (b /₀ t) = ((a * b) /₀ (s * t)) := rfl
lemma zero_def : (0 : preloc P) = (0 /₀ 1) := rfl
lemma add_def (x y : preloc P) :
 x + y = (((x.numer * (P.i y.denom) + (P.i x.denom) * y.numer):P.A) /₀
          (x.denom * y.denom)) := rfl
lemma add_def' (a b : P.A) (s t : P.S) : 
 (a /₀ s) + (b /₀ t) = (((a * (P.i t) + (P.i s) * b)) /₀ (s * t)) := rfl

def η₀ (a : P.A) : preloc P := a /₀ 1

lemma numer_eta (a : P.A) : (η₀ a).numer = a := rfl 
lemma denom_eta (a : P.A) : (η₀ a).denom = 1 := rfl 

lemma eta_map_zero : @η₀ P 0 = 0 := rfl
lemma eta_map_one  : @η₀ P 1 = 1 := rfl

lemma eta_map_mul (a b : P.A) : η₀ (a * b) = (η₀ a) * (η₀ b) := 
begin
 ext, 
 rw[numer_eta,numer_eta],
 rw[denom_eta,denom_eta,mul_one]
end

lemma eta_map_add (a b : P.A) : η₀ (a + b) = (η₀ a) + (η₀ b) := 
begin
 ext, 
 rw[numer_eta,numer_eta,denom_eta,denom_eta,
    P.i_hom.map_one,mul_one,one_mul],
 rw[denom_eta,denom_eta,mul_one],
end

structure R (x x' : preloc P) := 
 (s : P.S)
 (e : P.i (s * x'.denom) * x.numer = P.i (s * x.denom) * x'.numer)

def R_refl (x : preloc P) : R x x := 
 {s := 1, e := rfl}

def R_symm {x x' : preloc P} (m : R x x') : R x' x := 
 {s := m.s, e := m.e.symm}

def R_trans {x x' x'' : preloc P} (m : R x x') (n : R x' x'') : R x x'' := 
begin
  rcases x with ⟨a,u⟩, rcases x' with ⟨a',u'⟩, rcases x'' with ⟨a'',u''⟩,
  let ss := m.s * n.s * u',
  let ee := calc
   P.i (ss * u'') * a = P.i (n.s * u'') * (P.i (m.s * u') * a)
    : by {repeat {rw[P.i_hom.map_mul]}, ring,}
   ... = P.i (n.s * u'') * (P.i (m.s * u) * a') : by rw[m.e]
   ... = P.i (m.s * u) * (P.i (n.s * u'') * a') : by ring
   ... = P.i (m.s * u) * (P.i (n.s * u') * a'') : by rw[n.e]
   ... = P.i (ss * u) * a'' 
    : by {repeat {rw[P.i_hom.map_mul]}, ring,},
   exact { s := ss, e := ee }
end

def R_zero : (R 0 0) := R_refl (0 : preloc P)

def R_one : (R 1 1) := R_refl (1 : preloc P)

def R_add {x y x' y' : preloc P} (m : R x x') (n : R y y') :
 R (x + y) (x' + y') := 
begin
 rcases x with ⟨a,u⟩, rcases x' with ⟨a',u'⟩,
 rcases y with ⟨b,v⟩, rcases y' with ⟨b',v'⟩,
 let ss := m.s * n.s,
 let ee := calc
     (P.i (ss * (u' * v'))) * (a * (P.i v) + (P.i u) * b)
       = P.i (n.s * v * v') * (P.i (m.s * u') * a) + 
         P.i (m.s * u * u') * (P.i (n.s * v') * b) 
         : by {repeat {rw[P.i_hom.map_mul]}, ring,}
   ... = P.i (n.s * v * v') * (P.i (m.s * u) * a') + 
         P.i (m.s * u * u') * (P.i (n.s * v) * b')
         : by rw[m.e,n.e] 
   ... = (P.i (ss * (u * v))) * (a' * (P.i v') + (P.i u') * b')
         : by {repeat {rw[P.i_hom.map_mul]}, ring,},
  exact { s := ss, e := ee },
end

def R_mul {x y x' y' : preloc P} (m : R x x') (n : R y y') :
 R (x * y) (x' * y') := 
begin
 rcases x with ⟨a,u⟩, rcases x' with ⟨a',u'⟩,
 rcases y with ⟨b,v⟩, rcases y' with ⟨b',v'⟩,
 let ss := m.s * n.s,
 let ee := calc
     (P.i (ss * (u' * v'))) * (a * b)
       = (P.i (m.s * u') * a) * (P.i (n.s * v') * b)
         : by {repeat {rw[P.i_hom.map_mul]}, ring,}
   ... =  (P.i (m.s * u) * a') * (P.i (n.s * v) * b')
         : by rw[m.e,n.e] 
   ... = (P.i (ss * (u * v))) * (a' * b')
         : by {repeat {rw[P.i_hom.map_mul]}, ring,},
  exact { s := ss, e := ee },
end

def R_zero_mul : ∀ (x : preloc P), R (0 * x) 0
| ⟨a,u⟩ := {s := 1,e := begin 
  show (P.i (1 * 1)) * (0 * a) = (P.i (1 * (1 * u))) * 0,
  rw[_root_.zero_mul,_root_.mul_zero,_root_.mul_zero],
end}

def R_mul_zero : ∀ (x : preloc P), R (x * 0) 0
| ⟨a,u⟩ := {s := 1,e := begin 
  show (P.i (1 * 1)) * (a * 0) = (P.i (1 * (u * 1))) * 0,
  repeat {rw[_root_.mul_zero]},
end}

def R_mul_add (x y z : preloc P) : R (x * (y + z)) (x * y + x * z) := 
begin
 rcases x with ⟨a,u⟩, rcases y with ⟨b,v⟩, rcases z with ⟨c,w⟩,
 have e : (P.i (1 * ((u * v) * (u * w)))) * 
            (a * (b * (P.i w) + (P.i v) * c)) =
          (P.i (1 * (u * (v *w)))) * 
            ((a * b) * P.i (u * w) + P.i (u * v) * (a * c)) :=  
  by {repeat {rw[P.i_hom.map_mul]}, ring,},
  exact {s := 1, e := e},
end

def R_add_mul (x y z : preloc P) : R ((x + y) * z) (x * z + y * z) := 
begin
 rcases x with ⟨a,u⟩, rcases y with ⟨b,v⟩, rcases z with ⟨c,w⟩,
 have e : (P.i (1 * ((u * w) * (v * w)))) * 
            ((a * (P.i v) + (P.i u) * b) * c) =
          (P.i (1 * (u * v *w))) * 
            ((a * c) * P.i (v * w) + P.i (u * w) * (b * c)) :=  
  by {repeat {rw[P.i_hom.map_mul]}, ring,},
  exact {s := 1, e := e},
end

variable (P)

instance loc_equiv : setoid (preloc P) := {
 r := λ x x', nonempty (R x x'),
 iseqv := ⟨λ x,⟨R_refl x⟩,
  λ x x',by {rintro ⟨m⟩,exact ⟨R_symm m⟩},
  λ x x' x'',by {rintros ⟨m⟩ ⟨n⟩, exact ⟨R_trans m n⟩}⟩ 
}

lemma r_add {x y x' y' : preloc P} : ∀ (m : x ≈ x') (n : y ≈ y'),
 (x + y) ≈ (x' + y')
| ⟨m⟩ ⟨n⟩ := ⟨R_add m n⟩

lemma r_mul {x y x' y' : preloc P} : ∀ (m : x ≈ x') (n : y ≈ y'),
 (x * y) ≈ (x' * y')
| ⟨m⟩ ⟨n⟩ := ⟨R_mul m n⟩

end preloc

def loc (P : prelog_semiring) := quotient (preloc.loc_equiv P)

namespace loc

variable {P : prelog_semiring}

def mk0 : (preloc P) → (loc P) := quotient.mk
def mk (a : P.A) (s : P.S) : loc P := mk0 (a /₀ s)

notation a `/₁` s := loc.mk a s

instance : comm_semiring (loc P) := {
  zero := mk0 0,
  one := mk0 1,
  add := quotient.lift₂ 
          (λ x y, mk0 (x + y)) 
          (λ x y x' y' m n, quotient.sound (@preloc.r_add P x y x' y' m n)),
  mul := quotient.lift₂ 
          (λ x y, mk0 (x * y)) 
          (λ x y x' y' m n, quotient.sound (@preloc.r_mul P x y x' y' m n)),
  zero_add := λ x,by {rcases x,exact congr_arg mk0 (zero_add x),},
  add_zero := λ x,by {rcases x,exact congr_arg mk0 (add_zero x),},
  one_mul  := λ x,by {rcases x,exact congr_arg mk0 (one_mul x),},
  mul_one  := λ x,by {rcases x,exact congr_arg mk0 (mul_one x),},
  zero_mul := λ x,by {rcases x,exact quotient.sound ⟨preloc.R_zero_mul x⟩,},
  mul_zero := λ x,by {rcases x,exact quotient.sound ⟨preloc.R_mul_zero x⟩,},
  add_comm := λ x y,by {rcases x, rcases y, exact congr_arg mk0 (add_comm x y)},
  mul_comm := λ x y,by {rcases x, rcases y, exact congr_arg mk0 (mul_comm x y)},
  add_assoc := λ x y z,by {rcases x,rcases y,rcases z,
                           exact congr_arg mk0 (add_assoc x y z)},
  mul_assoc := λ x y z,by {rcases x,rcases y,rcases z,
                           exact congr_arg mk0 (mul_assoc x y z)},
  left_distrib := λ x y z,by {rcases x,rcases y,rcases z,
    exact quotient.sound ⟨@preloc.R_mul_add P x y z⟩,
  },
  right_distrib := λ x y z,by {rcases x,rcases y,rcases z,
    exact quotient.sound ⟨@preloc.R_add_mul P x y z⟩,
  },
}

def η (a : P.A) : loc P := a /₁ 1

instance (P : prelog_semiring) : is_semiring_hom (@η P) := {
 map_zero := rfl,
 map_one := rfl,
 map_add := λ a b,congr_arg mk0 (preloc.eta_map_add a b),
 map_mul := λ a b,congr_arg mk0 (preloc.eta_map_mul a b),
}

def ζ (s : P.S) : units (loc P) := begin
  let val : loc P := ((P.i s) /₁ 1),
  let inv : loc P := (1 /₁ s),
  let val_inv : val * inv = 1 := begin 
   show mk0 (((P.i s) * 1) /₀ (1 * s)) = mk0 (1 /₀ 1),
   let h : (((P.i s) * 1) /₀ (1 * s)) ≈ (1 /₀ 1) := 
    ⟨{ s := 1 , e := by {simp[P.i_hom.map_one],}}⟩ ,
   exact quotient.sound h,
  end,
  let inv_val := (mul_comm inv val).trans val_inv,
  exact { val := val, inv := inv, val_inv := val_inv, inv_val := inv_val },
end

end loc

end prelog_semiring

end localization_alt
