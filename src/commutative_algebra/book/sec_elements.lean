import algebra.ring data.equiv.basic data.complex.basic data.zmod.basic
import data.nat.prime data.int.gcd data.nat.choose
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

lemma ℂ_el_props : ∀ z : ℂ, 
 (is_invertible z ↔ z ≠ 0) ∧ 
 (is_regular z ↔ z ≠ 0) ∧ 
 (is_nilpotent z ↔ z = 0) ∧ 
 (is_idempotent z ↔ (z = 0 ∨ z = 1)) := sorry

/- -------------------------------------------------------- -/
/- eg-Zn-el-props -/

namespace zmod_el_props

variable (n : ℕ+)

lemma is_inv (a : ℕ) : 
 (is_invertible (a : zmod n)) ↔ nat.coprime a n := sorry

lemma is_inv' (a : ℕ) : 
 (is_invertible (a : zmod n)) ↔
  (∀ (p : ℕ), (nat.prime p) → (p ∣ n) → ¬ (p ∣ a)) := sorry

lemma is_reg (a : ℕ) : 
 (is_regular (a : zmod n)) ↔ (is_invertible (a : zmod n)) := sorry 

lemma is_nilp (a : ℕ) : 
 (is_nilpotent (a : zmod n)) ↔
  (∀ (p : ℕ), (nat.prime p) → (p ∣ n) → (p ∣ a)) := sorry

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

lemma is_nilpotent_neg (a b : A) : 
 is_nilpotent b → is_nilpotent (-b) := 
  λ h, by {rw[neg_eq_neg_one_mul],exact is_nilpotent_smul (-1) h}

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

lemma one_add_nilp_inv {a : A} :
 is_nilpotent a → is_invertible (1 + a) := 
λ ⟨⟨n,e⟩⟩,
begin
 let u := geometric_series (-a) n,
 let e' : (1 - (- a)) * u = 1 - (- a) ^ n := 
  by {dsimp[u],exact geometric_sum (- a) n}, 
 rw[sub_neg_eq_add,neg_eq_neg_one_mul,mul_pow,e,mul_zero,sub_zero] at e',
 exact ⟨⟨u,e'⟩⟩ 
end

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
 {exact one_add_nilp_inv (is_nilpotent_smul v ea)}
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
 have hv : is_invertible v := one_add_nilp_inv (is_nilpotent_smul u h),
 have hvx := calc
  v * x = (e₀ * e₀ - e₀) * (4 * e₁ - 2 * e₀ - 1) +
          (e₁ * e₁ - e₁) * (1 - 2 * e₀) : 
    by {dsimp[v,u,x],ring}
   ... = 0 : by {rw[h₀,h₁,sub_self,sub_self,zero_mul,zero_mul,zero_add],},
 have hx : x = 0 := (is_regular_of_invertible hv) x hvx,
 rw[← sub_eq_zero],
 exact hx,
end


end idempotent

end sec_elements