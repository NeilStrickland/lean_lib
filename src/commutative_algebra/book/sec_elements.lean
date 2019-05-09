import algebra.ring data.equiv.basic data.complex.basic data.zmod.basic 
import data.nat.prime data.int.gcd data.nat.choose algebra.gcd_domain data.finsupp
import data.list.min_max data.polynomial
import order.lattice_extra data.nat.square_free
import tactic.ring tactic.squeeze
namespace sec_elements

universe u
variables {A : Type u} [comm_ring A]

/- -------------------------------------------------------- -/
/- defn-el-props -/

def inverse (a : A) := {b : A // a * b = 1}

def is_invertible (a : A) := nonempty (inverse a)

noncomputable def inv (a : A) (h : is_invertible a) := 
 classical.choice h 

def is_regular (a : A) : Prop := ∀ (x : A) (e : a * x = 0), x = 0

def is_zero_divisor (a : A) := ¬ (is_regular a)

def nilpotent_witness (a : A) := {n : ℕ // a ^ n = 0}

def is_nilpotent (a : A) := nonempty (nilpotent_witness a)

def is_idempotent (a : A) := a ^ 2 = a

lemma is_idempotent' (a : A) : is_idempotent a ↔ a * (1 - a) = 0 := 
by { dsimp[is_idempotent],
 rw[pow_two,mul_add,mul_one,mul_neg_eq_neg_mul_symm],
 rw[← sub_eq_add_neg,sub_eq_zero],
 split; intro e; exact e.symm}

/- -------------------------------------------------------- -/
/- prop-inv-unique -/

instance inverse_unique (a : A) : subsingleton (inverse a) := 
 ⟨λ ⟨b₀,h₀⟩ ⟨b₁,h₁⟩ , begin apply subtype.eq, change b₀ = b₁,
  rw[← mul_one b₀,← h₁,← mul_assoc,mul_comm b₀,h₀,one_mul],
 end ⟩ 

/- -------------------------------------------------------- -/
/- eg-C-el-props -/

namespace integral_domain 

variables {D : Type*} [integral_domain D] (a : D)

lemma is_regular_iff : (is_regular a ↔ a ≠ 0) := 
begin 
 split,
 {rintro h_reg a_eq_0, exact zero_ne_one (h_reg 1 (a_eq_0.symm ▸ (zero_mul 1))).symm},
 {intros a_ne_0 b e,
  rcases eq_zero_or_eq_zero_of_mul_eq_zero e with ha | hb,
  {exact (a_ne_0 ha).elim},{exact hb}}
end

lemma is_nilpotent_iff : (is_nilpotent a ↔ a = 0) := 
begin
 split,
 {rintro ⟨⟨n,e⟩⟩,induction n with n ih,
  {rw[pow_zero] at e,exact (zero_ne_one e.symm).elim},
  {rw[pow_succ] at e,rcases eq_zero_or_eq_zero_of_mul_eq_zero e with h | h,
   {exact h},{exact ih h}
  }
 },{
  intro h,rw[h],exact ⟨⟨1,pow_one 0⟩⟩ 
 }
end

lemma is_idempotent_iff : (is_idempotent a ↔ a = 0 ∨ a = 1) := 
begin
 rw[is_idempotent'],split,
 {intro e,rcases eq_zero_or_eq_zero_of_mul_eq_zero e with h0 | h1,
  {exact or.inl h0},
  {exact or.inr (sub_eq_zero_iff_eq.mp h1).symm,}
 },{
  rintro (h | h); rw[h],rw[zero_mul],rw[sub_self,mul_zero],  
 }
end

end integral_domain 

namespace field 

variables {F : Type*} [field F] (a : F)

lemma is_invertible_iff : (is_invertible a ↔ a ≠ 0) := 
begin 
 split,
 {rintro ⟨⟨ai,ai_prop⟩⟩ a_eq_0,rw[a_eq_0,zero_mul] at ai_prop,
  exact zero_ne_one ai_prop
 },{intro a_ne_0,use a⁻¹,exact mul_inv_cancel a_ne_0,}
end

lemma is_regular_iff : (is_regular a ↔ a ≠ 0) := 
begin 
 split,
 {rintro h_reg a_eq_0, exact zero_ne_one (h_reg 1 (a_eq_0.symm ▸ (zero_mul 1))).symm},
 {intros a_ne_0 b e,exact calc
   b = 1 * b : (one_mul b).symm
   ... = 0 : by rw[← inv_mul_cancel a_ne_0,mul_assoc,e,mul_zero],}
end

end field

namespace C_el_props

lemma ℂ_el_props (z : ℂ) : 
 (is_invertible z ↔ z ≠ 0) ∧ 
 (is_regular z ↔ z ≠ 0) ∧ 
 (is_nilpotent z ↔ z = 0) ∧ 
 (is_idempotent z ↔ (z = 0 ∨ z = 1)) := 
begin
 split,exact field.is_invertible_iff z,
 split,exact integral_domain.is_regular_iff z,
 split,exact integral_domain.is_nilpotent_iff z,
       exact integral_domain.is_idempotent_iff z,
end

end C_el_props

/- -------------------------------------------------------- -/
/- eg-Zn-el-props -/

namespace zmod_el_props

variable (n : ℕ+)

namespace int

def gcd_a (x y : ℤ) : ℤ := 
 x.sign * (nat.gcd_a x.nat_abs y.nat_abs)

def gcd_b (x y : ℤ) : ℤ := 
 y.sign * (nat.gcd_b x.nat_abs y.nat_abs)

lemma nat_abs_eq_sign_mul_self : ∀ (x : ℤ),
 (x.nat_abs : ℤ) = x.sign * x
| (0 : ℕ) := rfl
| ((n + 1) : ℕ) := by {rw[int.nat_abs_of_nat,int.sign,_root_.one_mul],}
| (-[1+ m]) := by {rw[int.nat_abs,int.sign,← neg_eq_neg_one_mul],refl}

lemma gcd_eq_gcd_ab (x y : ℤ) : 
 (gcd x y) = x * (gcd_a x y) + y * (gcd_b x y) := 
begin
 let d := nat.gcd x.nat_abs y.nat_abs,
 let a := nat.gcd_a x.nat_abs y.nat_abs,
 let b := nat.gcd_b x.nat_abs y.nat_abs,
 change (d : ℤ) = x * (x.sign * a) + y * (y.sign * b),
 let h : (d : ℤ) = x.nat_abs * a + y.nat_abs * b:= 
  by {dsimp[d,a,b],exact nat.gcd_eq_gcd_ab x.nat_abs y.nat_abs},
 rw[← _root_.mul_assoc,← _root_.mul_assoc,mul_comm x,mul_comm y],
 rw[← nat_abs_eq_sign_mul_self x,← nat_abs_eq_sign_mul_self y],
 exact h,
end

end int

namespace nat

def sup_monoid : add_comm_monoid ℕ := {
  zero := 0,
  add := λ (a b : ℕ), ite (a ≤ b) b a,
  add_zero := λ a, by
   {dsimp[has_add.add],split_ifs,exact (nat.eq_zero_of_le_zero h).symm,refl},
  zero_add := λ a, by
   {dsimp[has_add.add],split_ifs,refl,exact (h (nat.zero_le a)).elim},
  add_comm := λ a b, by 
   {change ℕ at a,
     dsimp[has_add.add],split_ifs with hab hba,
    {exact le_antisymm hba hab},{refl},{refl},
     {exact (h (le_of_lt (lt_of_not_ge hab))).elim},
   },
  add_assoc := λ a b c, by {
    dsimp[has_add.add],split_ifs with hab hbc hac hac hbc; try {refl},
    {exact (hac (le_trans hab hbc)).elim},
    {replace hbc := lt_of_not_ge hbc,
     replace hab := lt_of_not_ge hab,
     exact (not_le_of_gt (lt_trans hbc hab) hac).elim,
    }  
  },
}

end nat

lemma is_invertible_iff (a : ℤ) : 
 (is_invertible (a : zmod n)) ↔ gcd a n = 1 := 
begin
 let en : ((n : ℕ) : ℤ) = n := rfl,
 split,
 {  
  rintro ⟨b₀,hab⟩,
  let d := gcd a n,change d = 1,
  have : d = d.nat_abs :=
   ((int.coe_nat_abs_eq_normalize d).trans (normalize_gcd a n)).symm,
  rw[this,← int.coe_nat_one],congr,
  let b : ℤ := b₀.val,
  have : (b : zmod n) = b₀ := by {rw[int.cast_coe_nat,zmod.cast_val b₀],},
  rw[← this,← int.cast_mul] at hab,
  have : (((a * b - 1) : ℤ) : (zmod n)) = 0 :=
   by {rw[int.cast_sub,hab,int.cast_one,sub_self],},
  rcases (zmod.eq_zero_iff_dvd_int.mp this) with ⟨c,e⟩,
  change a * b - 1 = n * c at e,
  replace e : a * b = n * c + 1 := by {rw[← e,sub_add,sub_self,sub_zero],},
  let ha : d ∣ a := by {dsimp[d],rw[en], exact gcd_dvd_left a n},
  let hn : d ∣ n := by {dsimp[d],rw[en], exact gcd_dvd_right a n},
  let hab : d ∣ (n * c + 1) := e ▸ (dvd_mul_of_dvd_left ha b),
  rcases ((dvd_add_iff_right (dvd_mul_of_dvd_left hn c)).mpr hab) with ⟨u,eu⟩,
  replace eu := congr_arg int.nat_abs eu,
  change 1 = (d * u).nat_abs at eu,rw[int.nat_abs_mul] at eu,
  exact (nat.mul_eq_one_iff.mp eu.symm).left,
 },{
  let d := gcd a n,
  let b := int.gcd_a a n,
  let q := int.gcd_b a n,
  have e : d = a * b + n * q := int.gcd_eq_gcd_ab a n,
  intro h, change d = 1 at h,rw[e,← en] at h,
  replace h := eq_sub_of_add_eq h,
  have : (a : zmod n) * (b : zmod n) = 1 := 
  by {rw[← int.cast_mul,h,int.cast_sub,int.cast_mul,int.cast_coe_nat],
      rw[zmod.cast_self_eq_zero,zero_mul,sub_zero,int.cast_one],},
  exact ⟨⟨(b : zmod n),this⟩⟩
 }
end

lemma is_invertible_iff' (a : ℕ) : 
 (is_invertible (a : zmod n)) ↔
  (∀ (p : ℕ), (nat.prime p) → (p ∣ n) → ¬ (p ∣ a)) := 
begin
 rw[← int.cast_coe_nat,is_invertible_iff],
 dsimp[gcd,int.gcd],rw[← int.coe_nat_one,int.coe_nat_inj'],
 split,
 {intros h p p_prime p_dvd_n p_dvd_a,
  have : p ∣ 1 := h ▸ (nat.dvd_gcd p_dvd_a p_dvd_n),
  exact nat.prime.not_dvd_one p_prime this,
 },
 {intro h,by_contradiction h',
  let d := nat.gcd a n,
  let p := nat.min_fac d,
  let p_prime : p.prime := nat.min_fac_prime h',
  let p_dvd_d : p ∣ d := nat.min_fac_dvd d,
  let p_dvd_a : p ∣ a := dvd_trans p_dvd_d (nat.gcd_dvd_left a n),
  let p_dvd_n : p ∣ n := dvd_trans p_dvd_d (nat.gcd_dvd_right a n),
  exact h p p_prime p_dvd_n p_dvd_a,
 }
end

lemma is_regular_iff (a : ℕ) : 
 (is_regular (a : zmod n)) ↔ (is_invertible (a : zmod n)) := 
begin
 split,
 {intro h,
  let f : (zmod n) → (zmod n) := λ x, a * x,
  have : function.injective f := λ x₁ x₂ e, 
   by {rw[← sub_eq_zero_iff_eq] at e ⊢,
    dsimp[f] at e,rw[neg_mul_eq_mul_neg,← mul_add] at e,
    replace e := h _ e,rw[sub_eq_add_neg],exact e,
   },
  rcases (fintype.injective_iff_surjective.mp this 1) with ⟨b,e⟩,
  dsimp[f] at e,exact ⟨⟨b,e⟩⟩,
 },{
  rintros ⟨⟨b,eab⟩⟩ x eax,rw[mul_comm] at eab,
  exact calc 
   x = 1 * x : (one_mul x).symm
    ... = 0 : by rw[← eab,mul_assoc,eax,mul_zero b],
 }
end

lemma is_nilpotent_iff (a : ℕ) : 
 (is_nilpotent (a : zmod n)) ↔
  (∀ (p : ℕ), (nat.prime p) → (p ∣ n) → (p ∣ a)) := 
begin
 split,
 {rintro ⟨⟨k,e⟩⟩ p p_prime p_dvd_n,
  rw[← nat.cast_pow] at e,
  replace e := dvd_trans p_dvd_n (zmod.eq_zero_iff_dvd_nat.mp e),
  exact nat.prime.dvd_of_dvd_pow p_prime e,
 },{
  rcases n with ⟨n,hn⟩,
  rcases nat.dvd_square_free_radical hn with ⟨k,⟨q,hq⟩⟩,
  intro h,
  rcases (nat.square_free_radical_dvd_iff hn a).mpr h with ⟨r,hr⟩,
  have ha : a ^ k = n * (q * r ^ k) :=
    by {rw[hr,nat.mul_pow,hq,mul_assoc]},
  have hz : (n : zmod ⟨n,hn⟩) = 0 := zmod.cast_self_eq_zero,
  have := calc
   (a : zmod ⟨n,hn⟩) ^ k = (((a ^ k) : ℕ) : zmod ⟨n,hn⟩) : by rw[nat.cast_pow]
  ... = 0 : by {rw[ha,nat.cast_mul,nat.cast_mul,nat.cast_pow,hz,zero_mul]},
  exact ⟨⟨k,this⟩⟩,
 }
end

end zmod_el_props

/- -------------------------------------------------------- -/
/- prop-inv-prod -/

variable (A)
def inverse_one : inverse (1 : A) := ⟨1,mul_one 1⟩
variable {A}

def inverse_prod_equiv (a b : A) :
 inverse (a * b) ≃ ((inverse b) × (inverse a)) := {
  to_fun := λ ⟨u,e⟩, ⟨⟨a * u,by {rw[← e],ring}⟩,
                     ⟨b * u,by {rw[← e],ring}⟩⟩ ,
  inv_fun := λ ⟨⟨v,ev⟩,⟨u,eu⟩⟩,
   ⟨v * u, calc (a * b) * (v * u) = (a * u) * (b * v) : by ring
           ... = 1 : by rw[eu,ev,mul_one],
   ⟩,
  left_inv := λ u, by {apply subsingleton.elim},
  right_inv := λ ⟨v,u⟩, by {apply prod.ext;apply subsingleton.elim},
}

def inverse_inv (a : A) (u : inverse a) : inverse u.val := 
 ⟨a,by {rw[mul_comm,u.property]}⟩ 

variable (A)
lemma is_invertible_one : is_invertible (1 : A) := 
 ⟨inverse_one A⟩ 
variable {A}

lemma is_invertible_mul_iff (a b : A) : 
 is_invertible (a * b) ↔ (is_invertible a) ∧ (is_invertible b) := 
begin
 split,
 {rintro ⟨uv⟩,let uv' := (inverse_prod_equiv a b).to_fun uv,
  exact ⟨⟨uv'.2⟩,⟨uv'.1⟩⟩},
 {rintro ⟨⟨u⟩,⟨v⟩⟩, exact ⟨(inverse_prod_equiv a b).inv_fun ⟨v,u⟩⟩,}
end

/- -------------------------------------------------------- -/
/- prop-regular-prod -/

variable (A)
def is_regular_one : is_regular (1 : A) := 
 λ x h, by {rw[one_mul] at h, exact h}
variable {A}

def is_regular_mul_iff {a b : A} :
  is_regular (a * b) ↔ (is_regular a) ∧ (is_regular b) := 
begin
 split, 
 {intro hab,split,
  {intros x e,
   have e' : (a * b) * x = b * (a * x) := by ring,
   rw[e,mul_zero] at e',exact hab _ e',},
  {intros x e,
   have e' : (a * b) * x = a * (b * x) := by ring,
   rw[e,mul_zero] at e',exact hab _ e',},
  },
  {rintro ⟨ha,hb⟩ x e,rw[mul_assoc] at e,
   replace e := ha (b * x) e,replace e := hb x e,exact e,   
  }
end

def is_regular_of_invertible {a : A} : is_invertible a → is_regular a := 
 λ ⟨u⟩ x e, calc
   x = (1 : A) * x : (one_mul x).symm
   ... = (a * u.val) * x : by rw[u.property]
   ... = u.val * (a * x) : by ring 
   ... = 0 : by rw[e,mul_zero]

/- -------------------------------------------------------- -/
/- prop-finite-regular -/

lemma invertible_of_regular_of_finite [fintype A]
 {a : A} : (is_regular a) → (is_invertible a) := 
begin
 intro ha,
 let f : A → A := λ x, a * x,
 have hf : function.injective f := 
  λ x₀ x₁ e, begin
   let e' := calc 
    a * (x₀ - x₁) = (a * x₀) - (a * x₁) : mul_sub _ _ _
    ... = (f x₀) - (f x₁) : rfl
    ... = 0 : by rw[e,sub_self],
   exact sub_eq_zero.mp (ha _ e')
  end,
  let hf' := fintype.injective_iff_surjective.mp hf,
  rcases (hf' 1) with ⟨u,hu⟩,
  exact ⟨⟨u,hu⟩⟩
end

/- -------------------------------------------------------- -/
/- prop-nilpotent-sum -/

lemma is_nilpotent_zero : is_nilpotent (0 : A) := 
 ⟨⟨1,pow_one 0⟩⟩ 

lemma is_nilpotent_add {a b : A} : 
 is_nilpotent a → is_nilpotent b → is_nilpotent (a + b) := 
begin 
 intros ha hb,
 rcases ha with ⟨_|n,ea⟩,
 {exact ⟨⟨0,by {rw[pow_zero] at ea ⊢,exact ea} ⟩⟩},
 rcases hb with ⟨_|m,eb⟩,
 {exact ⟨⟨0,by {rw[pow_zero] at eb ⊢,exact eb} ⟩⟩},
 constructor,
 use n + m + 1,rw[add_pow],
 rw[← @finset.sum_const_zero ℕ A (finset.range (n + m + 1).succ)],
 congr,ext i,
 by_cases hi : i ≥ n + 1,
 {rw[← nat.add_sub_of_le hi,pow_add,ea],repeat {rw[zero_mul]},},
 {replace hi := le_of_not_gt hi,
  have := nat.add_sub_of_le hi,
  have : n + m + 1 - i = (m + 1) + (n - i) := by {
   rw[← this,add_comm i,add_assoc,nat.add_sub_cancel],
   rw[add_assoc,add_comm i,← add_assoc,nat.add_sub_cancel,add_comm],
  },
  rw[this,pow_add,eb,zero_mul,mul_zero,zero_mul],
 }
end

lemma is_nilpotent_smul (a : A) {b : A} : 
 is_nilpotent b → is_nilpotent (a * b) := 
λ ⟨⟨n,e⟩⟩, by { 
 have e' : (a * b) ^ n = 0 := by { rw[mul_pow,e,mul_zero],},
 exact ⟨⟨n,e'⟩⟩
}

lemma is_nilpotent_neg {b : A} : 
 is_nilpotent b → is_nilpotent (-b) := 
  λ h, by {rw[neg_eq_neg_one_mul],exact is_nilpotent_smul (-1) h}

lemma is_nilpotent_sub {a b : A} : 
 is_nilpotent a → is_nilpotent b → is_nilpotent (a - b) := 
  λ ha hb, by {rw[sub_eq_add_neg],apply is_nilpotent_add,
              exact ha,apply is_nilpotent_neg,exact hb}

/- -------------------------------------------------------- -/
/- prop-nilpotent-inv -/

def geometric_series (a : A) (n : ℕ) :=
 (finset.range n).sum (λ i, a ^ i)

lemma geometric_sum (a : A) (n : ℕ) :
 (1 - a) * (geometric_series a n) = 1 - a ^ n := 
begin
 induction n with n ih,
 {change (1 - a) * 0 = 1 - a ^ 0,rw[mul_zero,pow_zero,sub_self],},
 {have : geometric_series a n.succ = a ^ n + geometric_series a n := 
   by {dsimp[geometric_series],rw[finset.sum_range_succ]},
  rw[this,mul_add,ih,nat.succ_eq_add_one,pow_add,pow_one],
  rw[sub_mul,one_mul,mul_comm a],
  repeat {rw[sub_eq_add_neg]},
  rw[add_comm,add_assoc,← add_assoc (- (a^n)),neg_add_self,zero_add],
 }
end

def one_add_nilp_inv {a : A} :
 ∀ (h : nilpotent_witness a), inverse (1 + a) 
| ⟨n,e⟩ := ⟨geometric_series (-a) n, by {
 let u := geometric_series (-a) n, change (1 + a) * u = 1, 
 let e' : (1 - (- a)) * u = 1 - (- a) ^ n := 
  by {dsimp[u],exact geometric_sum (- a) n}, 
 rw[sub_neg_eq_add,neg_eq_neg_one_mul,mul_pow,e,mul_zero,sub_zero] at e',
 exact e' 
} ⟩ 

lemma one_add_nilp_inv' {a : A} :
 is_nilpotent a → is_invertible (1 + a) := 
λ ⟨h⟩, ⟨one_add_nilp_inv h⟩ 

/- -------------------------------------------------------- -/
/- cor-nilp-inv -/

lemma inv_add_nilp_inv {u a : A} : 
 is_invertible u → is_nilpotent a → is_invertible (u + a) := 
λ ⟨⟨v,euv⟩⟩ ea,
begin
 have : u + a = u * (1 + v * a) := 
  by { rw[mul_add,← mul_assoc,euv,mul_one,one_mul], },
 rw[this,is_invertible_mul_iff],
 split,
 {exact ⟨⟨v,euv⟩⟩},
 {exact one_add_nilp_inv' (is_nilpotent_smul v ea)}
end

/- -------------------------------------------------------- -/
/- prop-idempotent-ops -/

namespace idempotent
variable (A)

lemma zero_mem : is_idempotent (0 : A) := 
 by {dsimp[is_idempotent],rw[pow_two,mul_zero]}

lemma one_mem : is_idempotent (1 : A) := 
 by {dsimp[is_idempotent],rw[pow_two,mul_one]}

variable {A}

def not (a : A) := 1 - a
def and (a b : A) := a * b
def or  (a b : A) := a + b - a * b
def xor (a b : A) := a + b - 2 * a * b

lemma one_sub_mem {a : A} : 
 is_idempotent a → is_idempotent (1 - a) := 
by {
 dsimp[is_idempotent],rw[pow_two,pow_two],intro e,
 rw[mul_add,mul_one,add_mul,one_mul,neg_mul_neg,e,neg_add_self,add_zero],
}

lemma mul_mem {a b : A} : 
 is_idempotent a → is_idempotent b → is_idempotent (a * b) := 
by {
 intros ea eb, dsimp[is_idempotent] at *,
 rw[pow_two] at *,
 rw[mul_assoc,mul_comm b,mul_assoc a,eb,← mul_assoc,ea],
}

lemma add_sub_mul_mem {a b : A} : 
 is_idempotent a → is_idempotent b → is_idempotent (a + b - a * b) := 
by {
 intros ea eb,
 have : a + b - a * b = 1 - (1 - a) * (1 - b) := by ring,
 rw[this],
 apply one_sub_mem, apply mul_mem; apply one_sub_mem; assumption,
}

def invol (a : A) := 1 - 2 * a

lemma invol_square {a : A} (ha : is_idempotent a) :
 (invol a) ^ 2 = 1 := 
begin
 dsimp[invol,is_idempotent] at ha,
 have : (1 - 2 * a) ^ 2 = 1 - 4 * (a - a ^ 2) := 
  by {rw[pow_two,pow_two],ring},
 rw[ha,sub_self,mul_zero,sub_zero] at this,
 exact this,
end

lemma eq_of_sub_nilp {e₀ e₁ : A}
 (h₀ : is_idempotent e₀) (h₁ : is_idempotent e₁)
  (h : is_nilpotent (e₀ - e₁)) : e₀ = e₁ := 
begin
 dsimp[is_idempotent] at h₀ h₁,rw[pow_two] at h₀ h₁,
 let x := e₀ - e₁,
 let u := 1 - 2 * e₀,
 let v := 1 + u * x, 
 have hv : is_invertible v := one_add_nilp_inv' (is_nilpotent_smul u h),
 have hvx := calc
  v * x = (e₀ * e₀ - e₀) * (4 * e₁ - 2 * e₀ - 1) +
          (e₁ * e₁ - e₁) * (1 - 2 * e₀) : 
    by {dsimp[v,u,x],ring}
   ... = 0 : by {rw[h₀,h₁,sub_self,sub_self,zero_mul,zero_mul,zero_add],},
 have hx : x = 0 := (is_regular_of_invertible hv) x hvx,
 rw[← sub_eq_zero],
 exact hx,
end

def lift : ∀ (e : A) (h : nilpotent_witness (e * (1 - e))), A := 
 λ e ⟨n,hx⟩, e ^ (n + 2) * geometric_series (1 - e ^ (n + 2) - (1 - e) ^ (n + 2)) n

lemma lift_spec (e : A) (h : nilpotent_witness (e * (1 - e))) :
 pprod (is_idempotent (lift e h)) (nilpotent_witness ((lift e h) - e)) :=
begin 
 rcases h with ⟨n,hx⟩,
 let x := e * (1 - e), change x ^ n = 0 at hx,
 let y := 1 - e ^ (n + 2) - (1 - e) ^ (n + 2),
 let u := geometric_series y n,
 let e₁ := e ^ (n + 2) * u,
 have : lift e ⟨n,hx⟩ = e₁ := rfl,
 rw[this],
 let f := λ (i : ℕ), e ^ i * (1 - e) ^ (n + 2 - i) * nat.choose (n + 2) i,
 let z := (finset.range (n + 1)).sum 
            (λ j, e ^ j * (1 - e) ^ (n - j) * (nat.choose (n + 2) (j + 1))),
 let xz := (finset.range (n + 1)).sum (f ∘ nat.succ),
 have hxz : x * z = xz := by {
   dsimp[xz,x],rw[finset.mul_sum],apply finset.sum_congr rfl,intros i hi,
   replace hi : i ≤ n := nat.le_of_lt_succ (finset.mem_range.mp hi),
   have : (f ∘ nat.succ) i = f (i + 1) := rfl, rw[this], dsimp[f],
   have : n + 2 - (i + 1) = (n - i) + 1 := calc 
    n + 2 - (i + 1) = n + 1 - i : by {rw[nat.succ_sub_succ]}
    ... = (i + (n - i)) + 1 - i : by {rw[nat.add_sub_of_le hi]}  
    ... = (n - i) + 1 : by {simp only [add_comm,add_assoc,nat.add_sub_cancel_left],}, 
   rw[this,pow_succ,pow_succ],repeat {rw[mul_assoc]},congr' 1,
   repeat {rw[← mul_assoc]},rw[mul_comm (1 + - e) (e ^ i)],   
 },
 have hf₀ : f 0 = (1 - e) ^ (n + 2) :=
  by {dsimp[f],rw[nat.choose,nat.cast_one,one_mul,mul_one],},
 have hf₁ : f (n + 2) = e ^ (n + 2) := 
  by {dsimp[f],rw[nat.choose_self,nat.cast_one,nat.sub_self,pow_zero,mul_one,mul_one],},
 have := calc
  (1 : A) = (1 : A) ^ (n + 2) : (one_pow (n + 2)).symm
  ... = (e + (1 - e)) ^ (n + 2) :
   by {congr,rw[add_sub,add_comm,add_sub_cancel]}
  ... = (finset.range (n + 2).succ).sum f : add_pow e (1 - e) (n + 2) 
  ... = e ^ (n + 2) + (finset.range (n + 2)).sum f : 
         by {rw[finset.sum_range_succ,hf₁],}
  ... = e ^ (n + 2) + (xz + (1 - e) ^ (n + 2)) : 
         by {rw[finset.sum_range_succ',hf₀]} 
  ... = e ^ (n + 2) + (x * z + (1 - e) ^ (n + 2)) : by {rw[hxz]},
 have hxyz := calc 
  y = 1 - e ^ (n + 2) - (1 - e) ^ (n + 2) : rfl 
  ... = (e ^ (n + 2) + (x * z + (1 - e) ^ (n + 2))) - e ^ (n + 2) - (1 - e) ^ (n + 2) : 
   by {congr' 2,exact this}
  ... = x * z : by {simp only [sub_eq_add_neg,add_comm,add_left_comm,
                               add_neg_cancel_left,add_neg_cancel_right],},
 have hy : y ^ n = 0 := by {rw[hxyz,mul_pow,hx,zero_mul],},
 have hu : (1 - y) * u = 1 := by {rw[geometric_sum y n,hy,sub_zero]},
 have : 1 - y = e ^ (n + 2) + (1 - e) ^ (n + 2) := 
  calc 1 - y = 1 - (1 - e ^ (n + 2) - (1 - e) ^ (n + 2)) : by {simp only [y]}
   ... = e ^ (n + 2) + (1 - e) ^ (n + 2) : by rw[sub_sub,sub_sub_cancel],
 let hu' := hu, rw[this] at hu',
 have := calc
  1 - e₁ = (e ^ (n + 2) + (1 - e) ^ (n + 2)) * u - e₁ : by {rw[hu'],}
  ... = e ^ (n + 2) * u + (1 - e) ^ (n + 2) * u - e ^ (n + 2) * u :
   by {rw[add_mul],}
  ... = (1 - e) ^ (n + 2) * u : by {rw[add_comm,add_sub_cancel]},
 have := calc 
  e₁ * (1 - e₁) = (e ^ (n + 2) * u) * (1 - e₁) : rfl
  ... = u * (e ^ (n + 2) * (1 - e₁)) : by {rw[mul_comm (e ^ (n + 2))],rw[← mul_assoc],}
  ... = u * (e ^ (n + 2) * (1 - e) ^ (n + 2) * u) : by {rw[this,mul_assoc]}
  ... = u * (x ^ (n + 2) * u) : by {rw[mul_pow,pow_add],}
  ... = 0 : by {rw[pow_add,hx,zero_mul,zero_mul,mul_zero],},
 split, exact (is_idempotent' e₁).mpr this,
 let w := geometric_series e (n + 1), 
 have hw : x * w = e - e ^ (n + 2) := calc 
  x * w = e * ((1 - e) * w) : by {dsimp[x],rw[mul_assoc]}
  ... = e * (1 - e ^ (n + 1)) : by {rw[geometric_sum e (n + 1)],}
  ... = e - e ^ (n + 2) : by {rw[mul_sub,mul_one,pow_succ e (n + 1)],},
 have hu'' : u = 1 + x * z * u := by {
   rw[sub_mul,hxyz,one_mul] at hu,rw[← hu,sub_add_cancel],
 },
 have := calc
  e₁ - e = e ^ (n + 2) * u - e : rfl
  ... = e ^ (n + 2) * (1 + x * z * u) - e : by {congr' 2,exact hu''}
  ... = (e ^ (n + 2) * (x * z * u) + e ^ (n + 2)) - e : 
         by {rw[mul_add,mul_one,add_comm],}
  ... = x * (e ^ (n + 2) * z * u) - (e - e ^ (n + 2)) : 
         by {rw[← sub_add,sub_eq_add_neg,sub_eq_add_neg],
             rw[← mul_assoc,← mul_assoc,mul_comm (e ^ (n + 2))],
             repeat {rw[add_assoc]},rw[add_comm (e ^ (n + 2))],
             repeat {rw[mul_assoc]},}
  ... = x * (e ^ (n + 2) * z * u - w) : by {rw[mul_sub,hw],},
 have : (e₁ - e) ^ n = 0 := by {rw[this,mul_pow,hx,zero_mul],},
 exact ⟨n,this⟩,
end

lemma lift_unique (e e₁ : A) 
 (h : nilpotent_witness (e * (1 - e))) (hi : is_idempotent e₁)
 (hn : is_nilpotent (e₁ - e)) : e₁ = lift e h := 
begin
 rcases lift_spec e h with ⟨hi',hn'⟩,
 apply eq_of_sub_nilp hi hi',
 have : e₁ - lift e h = (e₁ - e) - (lift e h - e) := 
  by {rw[sub_sub_sub_cancel_right],},
 rw[this],apply is_nilpotent_sub hn ⟨hn'⟩
end

/- -------------------------------------------------------- -/
/- rem-lifting -/

def lift' : ∀ (e : A) (h : nilpotent_witness (e * (1 - e))), A := 
 λ e ⟨n,hx⟩,
  let x := e * (1 - e) in 
   let b := (finset.range n).sum (λ k, ((x ^ k) * nat.choose (2 * k + 1) k)) in 
    e + (2 * e - 1) * b * x

lemma lift_eq (e : A) (h : nilpotent_witness (e * (1 - e))) : 
 lift' e h = lift e h := sorry

end idempotent

/- -------------------------------------------------------- -/
/- prop-poly-el-props -/

namespace poly_el_props
open polynomial

variables [decidable_eq A] (p : polynomial A)

lemma is_invertible_iff : 
 is_invertible p ↔
  (is_invertible (coeff p 0)) ∧ (∀ n : ℕ, (is_nilpotent (coeff p n.succ))) :=
sorry

lemma is_regular_bot (n : ℕ)
 (h₀ : ∀ i, i < n → coeff p i = 0) (h₁ : is_invertible (coeff p n)) : 
  is_regular p := sorry

lemma is_regular_top (n : ℕ)
 (h₀ : ∀ i, i > n → coeff p i = 0) (h₁ : is_invertible (coeff p n)) : 
  is_regular p := sorry

lemma is_nilpotent_iff : 
 is_nilpotent p ↔ (∀ n, is_nilpotent (coeff p n)) := sorry

lemma is_idempotent_iff : 
 is_idempotent p ↔ 
  (is_idempotent (coeff p 0)) ∧ (∀ n : ℕ, (coeff p n.succ) = 0) :=
  sorry
 
end poly_el_props

/- -------------------------------------------------------- -/
/- prop-idempotent-splitting -/

namespace idempotent

variables {e : A} (he : is_idempotent e)
include he

def axis := {b : A // b * e = b}

namespace axis 

def mk (b : A) (hb : b * e = b) : axis he := ⟨b,hb⟩

instance : has_zero (axis he) := ⟨⟨(0 : A),zero_mul e⟩⟩

instance : has_one (axis he) := ⟨⟨e,by {rw[← pow_two],exact he}⟩⟩

instance : has_neg (axis he) := 
 ⟨λ b, axis.mk he (- b.val) (by {rw[← neg_mul_eq_neg_mul,b.property]})⟩

instance : has_add (axis he) := 
 ⟨λ b₁ b₂, axis.mk he (b₁.val + b₂.val) (by {rw[add_mul,b₁.property,b₂.property]})⟩ 

instance : has_mul (axis he) := 
 ⟨λ b₁ b₂, axis.mk he (b₁.val * b₂.val) (by {rw[mul_assoc,b₂.property]})⟩

@[simp] lemma val_zero : (0 : axis he).val = 0 := rfl

@[simp] lemma val_one : (1 : axis he).val = e := rfl

@[simp] lemma val_neg (b : axis he) : (- b).val = - (b.val) := rfl

@[simp] lemma val_add (b₁ b₂ : axis he) : (b₁ + b₂).val = b₁.val + b₂.val := rfl

@[simp] lemma val_mul (b₁ b₂ : axis he) : (b₁ * b₂).val = b₁.val * b₂.val := rfl

instance : comm_ring (axis he) := by { 
  refine_struct {
  zero := has_zero.zero _,
  one  := has_one.one _,
  neg  := has_neg.neg,
  add  := has_add.add,
  mul  := has_mul.mul,
  ..
 };
 try { rintro ⟨a,ha⟩ }; 
 try { rintro ⟨b,hb⟩ }; 
 try { rintro ⟨c,hc⟩ }; 
 apply subtype.eq, 
 {repeat {rw[val_add]},apply add_assoc},
 {rw[val_add,val_zero,zero_add]},
 {rw[val_add,val_zero,add_zero]},
 {rw[val_add,val_neg,val_zero,neg_add_self]},
 {rw[val_add,val_add,add_comm]},
 {repeat {rw[val_mul]},rw[mul_assoc]},
 {rw[val_mul,val_one,mul_comm,ha]},
 {rw[val_mul,val_one,ha]},
 {rw[val_mul,val_add,val_add,val_mul,val_mul,mul_add]},
 {rw[val_mul,val_add,val_add,val_mul,val_mul,add_mul]},
 {rw[val_mul,val_mul,mul_comm]}
}

def proj : A → axis he :=
 λ a, ⟨a * e,by {dsimp[is_idempotent] at he, rw[mul_assoc,← pow_two,he]}⟩

instance proj_ring_hom : is_ring_hom (proj he) := {
 map_one := by { apply subtype.eq, change 1 * e = e, rw[one_mul] },
 map_add := λ a b, by { apply subtype.eq, 
                        change (a + b) * e = a * e + b * e,
                        rw[add_mul]},
 map_mul := λ a b, by { dsimp[is_idempotent] at he, rw[pow_two] at he,
                        apply subtype.eq,
                        change (a * b) * e = (a * e) * (b * e),
                        rw[mul_assoc a e,← mul_assoc e b e,mul_comm e b,
                           mul_assoc b e,he,mul_assoc]}
}

def split : A → (axis he) × (axis (one_sub_mem he)) := 
 λ a, ⟨(proj he a),(proj (one_sub_mem he) a)⟩

instance split_ring_hom : is_ring_hom (split he) := 
 let he' := one_sub_mem he in {
 map_one := by { 
  ext, 
  exact is_ring_hom.map_one (proj he),
  exact is_ring_hom.map_one (proj he'),},
 map_add := λ a b, by {
  dsimp[split],ext,
  exact @is_ring_hom.map_add _ _ _ _ (proj he ) _ a b,
  exact @is_ring_hom.map_add _ _ _ _ (proj he') _ a b,},
 map_mul := λ a b, by {
  dsimp[split],ext,
  exact @is_ring_hom.map_mul _ _ _ _ (proj he ) _ a b,
  exact @is_ring_hom.map_mul _ _ _ _ (proj he') _ a b,},
}

lemma mul_eq_zero (b : axis he) (c : axis (one_sub_mem he)) : 
 b.val * c.val = 0 := by {
  rcases b with ⟨b,hb⟩,
  rcases c with ⟨c,hc⟩,
  change b * c = 0,
  exact calc
   b * c = (b * e) * (c * (1 - e)) : by rw[hb,hc]
   ... = b * (e * (1 - e)) * c : by {rw[mul_comm c,mul_assoc,mul_assoc,mul_assoc]}
   ... = 0 : by {rw[(is_idempotent' e).mp he,mul_zero,zero_mul]}
}

def combine : (axis he) × (axis (one_sub_mem he)) → A := 
 λ bc, bc.1.val + bc.2.val

instance combine_ring_hom : is_ring_hom (combine he) := {
 map_one := by {change e + (1 - e) = 1,rw[add_sub_cancel'_right]},
 map_add := λ bc₁ bc₂, by {
  rcases bc₁ with ⟨⟨b₁,hb₁⟩,⟨c₁,hc₁⟩⟩,
  rcases bc₂ with ⟨⟨b₂,hb₂⟩,⟨c₂,hc₂⟩⟩,
  change (b₁ + b₂) + (c₁ + c₂) = (b₁ + c₁) + (b₂ + c₂),
  rw[add_assoc,← add_assoc b₂,add_comm b₂ c₁,add_assoc,add_assoc],
 },
 map_mul := λ bc₁ bc₂, by {
  rcases bc₁ with ⟨⟨b₁,hb₁⟩,⟨c₁,hc₁⟩⟩,
  rcases bc₂ with ⟨⟨b₂,hb₂⟩,⟨c₂,hc₂⟩⟩,
  change (b₁ * b₂) + (c₁ * c₂) = (b₁ + c₁) * (b₂ + c₂),
  have ebc : b₁ * c₂ = 0 := mul_eq_zero he ⟨b₁,hb₁⟩ ⟨c₂,hc₂⟩,
  have ecb : b₂ * c₁ = 0 := mul_eq_zero he ⟨b₂,hb₂⟩ ⟨c₁,hc₁⟩,
  rw[mul_comm] at ecb,
  rw[mul_add,add_mul,add_mul,ebc,ecb,zero_add,add_zero],
 }
}

lemma combine_split (a : A) : combine he (split he a) = a := 
by { change a * e + a * (1 - e) = a, 
     rw[mul_sub,mul_one,add_sub_cancel'_right]}

lemma split_combine (bc : (axis he) × (axis (one_sub_mem he))) : 
 split he (combine he bc) = bc := 
by {
 have he' : e * (1 - e) = 0 := (is_idempotent' e).mp he,
 rcases bc with ⟨⟨b,hb⟩,⟨c,hc⟩⟩,
 ext; apply subtype.eq,
 {change (b + c) * e = b,
  rw[← hc,add_mul,hb,mul_assoc,mul_comm (1 - e),he',mul_zero,add_zero],},
 {change (b + c) * (1 - e) = c,
  rw[← hb,add_mul,hc,mul_assoc,he',mul_zero,zero_add],}
}

end axis

end idempotent

end sec_elements