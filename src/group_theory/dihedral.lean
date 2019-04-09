import data.fintype group_theory.group_action 
 algebra.group_power algebra.big_operators data.zmod.basic
import tactic.ring
import group_theory.pow_mod

namespace group_theory

variable n : ℕ+ 

@[derive decidable_eq]
inductive dihedral 
| r : (zmod n) → dihedral
| s : (zmod n) → dihedral

namespace dihedral

variable {n}

def log : dihedral n → (zmod n)
| (r i) := i
| (s i) := i

def is_s : dihedral n → bool
| (r _) := ff
| (s _) := tt

def to_bz : dihedral n → bool × (zmod n)
| (r i) := ⟨ff,i⟩
| (s i) := ⟨tt,i⟩

def of_bz : bool × (zmod n) → dihedral n
| ⟨ff,i⟩ := r i
| ⟨tt,i⟩ := s i

variable (n)
def bz_equiv : dihedral n ≃ (bool × (zmod n)) := 
{
 to_fun := to_bz,
 inv_fun := of_bz,
 left_inv := λ g, by {cases g; refl},
 right_inv := λ bi, by {rcases bi with ⟨_|_,i⟩ ; refl}
}

variable {n}

instance : fintype (dihedral n) := 
 fintype.of_equiv (bool × (zmod n)) (bz_equiv n).symm

lemma card : fintype.card (dihedral n) = 2 * n := calc 
 fintype.card (dihedral n) = fintype.card (bool × (zmod n)) :
  begin rw[fintype.card_congr (bz_equiv n)], end
 ... = (fintype.card bool) * (fintype.card (zmod n)) : by rw[fintype.card_prod]
 ... = (fintype.card bool) * (fintype.card (fin n)) : rfl
 ... = 2 * n : by rw[fintype.card_bool,fintype.card_fin]

def one : dihedral n := r 0

def inv : ∀ (g : dihedral n), dihedral n 
| (r i) := r (-i)
| (s i) := s i

def mul : ∀ (g h : dihedral n), dihedral n
| (r i) (r j) := r (i + j)
| (r i) (s j) := s (i + j)
| (s i) (r j) := s (i - j)
| (s i) (s j) := r (i - j)

instance : has_one (dihedral n) := ⟨r 0⟩ 
lemma one_eq : (1 : dihedral n) = r 0 := rfl

instance : has_inv (dihedral n) := ⟨dihedral.inv⟩
lemma r_inv (i : zmod n) : (r i)⁻¹ = r (- i) := rfl
lemma s_inv (i : zmod n) : (s i)⁻¹ = s i := rfl

instance : has_mul (dihedral n) := ⟨dihedral.mul⟩
lemma rr_mul (i j : zmod n) : (r i) * (r j) = r (i + j) := rfl
lemma rs_mul (i j : zmod n) : (r i) * (s j) = s (i + j) := rfl
lemma sr_mul (i j : zmod n) : (s i) * (r j) = s (i - j) := rfl
lemma ss_mul (i j : zmod n) : (s i) * (s j) = r (i - j) := rfl

instance : group (dihedral n) := {
 one := 1,
 mul := (*),
 inv := has_inv.inv,
 mul_one := λ g, begin cases g;
  simp only[one_eq,rr_mul,sr_mul,add_zero,sub_zero], end,
 one_mul := λ g, begin cases g;
  simp only[one_eq,rr_mul,rs_mul,zero_add], end,
 mul_left_inv := λ g, begin cases g;
  simp only[one_eq,r_inv,s_inv,rr_mul,ss_mul,sub_self,add_comm,add_neg_self],
 end,
 mul_assoc := λ f g h, begin 
  cases f; cases g; cases h;
  simp[rr_mul,rs_mul,sr_mul,ss_mul];
  ring,
 end,
}

section hom_from_gens
variables {M : Type*} [monoid M] {r0 s0: M} 
variables (hr : r0 ^ (n : ℕ) = 1)
          (hs : s0 * s0 = 1) 
          (hrs : r0 * s0 * r0 = s0) 

variable (n)

include r0 s0 hr hs hrs

def hom_from_gens :
 (dihedral n) → M
| (r i) := pow_mod n hr i
| (s i) := (pow_mod n hr i) * s0
variable {n}

lemma hom_from_gens_r (i : zmod n) :
 hom_from_gens n hr hs hrs (r i) = pow_mod n hr i := rfl

lemma hom_from_gens_s (i : zmod n) :
 hom_from_gens n hr hs hrs (s i) = (pow_mod n hr i) * s0 := rfl

lemma sr_rs : ∀ (i : ℕ), r0 ^ i * s0 * (r0 ^ i) = s0 
| 0 := by {rw[pow_zero,one_mul,mul_one]}
| (i + 1) := calc
   r0 ^ (i + 1) * s0 * r0 ^ (i + 1) = 
    r0 ^ (i + 1) * s0 * r0 ^ (1 + i) : by {rw[add_comm i 1]}
   ... = (r0 ^ i * r0) * s0 * (r0 * r0 ^ i) : by {rw[pow_add,pow_add,pow_one]}
   ... = (r0 ^ i) * ((r0 * s0) * (r0 * (r0 ^ i))) : 
    by rw[mul_assoc (r0 ^ i) r0 s0,mul_assoc (r0 ^ i)]
   ... = (r0 ^ i) * (((r0 * s0) * r0) * r0 ^ i) : 
    by rw[mul_assoc (r0 * s0) r0 (r0 ^ i)]
   ... = s0 : by rw[hrs,← mul_assoc,sr_rs i]

lemma sr_rs' : ∀ (i : zmod n), 
 s0 * (pow_mod n hr i) = (pow_mod n hr (- i)) * s0 := 
λ i, calc 
  s0 * (pow_mod n hr i) = 
   1 * (s0 * (pow_mod n hr i)) : (one_mul _).symm
  ... = (pow_mod n hr ((- i) + i))  * (s0 * (pow_mod n hr i)) :
   by rw[← pow_mod_zero,neg_add_self]
  ... = (pow_mod n hr (- i)) * ((pow_mod n hr i) * s0 * (pow_mod n hr i)) :
   by {rw[pow_mod_add,mul_assoc (pow_mod n hr (- i)),mul_assoc]}
  ... = (pow_mod n hr (- i)) * (r0 ^ i.val * s0 * r0 ^ i.val) : rfl
  ... = (pow_mod n hr (- i)) * s0 : by rw[sr_rs hr hs hrs i.val]

lemma is_hom_from_gens : 
 is_monoid_hom (hom_from_gens n hr hs hrs) := 
begin
 let h := sr_rs' hr hs hrs,
 split,
 {rw[one_eq,hom_from_gens_r],refl,},
 {intros a b,
  cases a with i i; cases b with j j;
  simp[rr_mul,rs_mul,sr_mul,ss_mul,hom_from_gens_r,hom_from_gens_s],
  {rw[pow_mod_add],},
  {rw[← mul_assoc,pow_mod_add],},
  {rw[mul_assoc,h j,← mul_assoc,pow_mod_add]},
  {rw[mul_assoc,← mul_assoc s0 _ s0,h j,mul_assoc,hs,mul_one,pow_mod_add]}
 }
end

end hom_from_gens
end dihedral

end group_theory