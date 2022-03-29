/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

We define finite dihedral groups, with elements denoted by
`r i` and `s i` for `i : zmod n`.  We show that a pair of elements
`r0, s0 ∈ G` satisfying appropriate relations gives rise to a
homomorphism `Dₙ → G`, sending `r i` to `r0 ^ i` and `s i` to
`(r0 ^ i) * s0`.  (We have chosen to formulate this in
a way that works when `G` is merely a monoid, as that makes
it easier to deal with `Dₙ`-actions as homomorphisms from
`Dₙ` to endomorphism monoids.  Thus, our relations are
`r0 ^ n = s0 * s0 = 1` and `r0 * s0 * r0 = s0`.)

We also do the case n = ∞ separately.
-/

import data.fintype.basic
import algebra.power_mod
import group_theory.subgroup.basic
import group_theory.group_action
import group_theory.action_instances
import group_theory.cyclic

namespace group_theory

variables (n : ℕ) [fact (n > 0)]

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
| (r i) := ⟨ff, i⟩
| (s i) := ⟨tt, i⟩

def of_bz : bool × (zmod n) → dihedral n
| ⟨ff, i⟩ := r i
| ⟨tt, i⟩ := s i

variable (n)
def bz_equiv : dihedral n ≃ (bool × (zmod n)) :=
{ to_fun := to_bz,
  inv_fun := of_bz,
  left_inv := λ g, by cases g; refl,
  right_inv := λ bi, by rcases bi with ⟨_|_, i⟩ ; refl }

variable {n}

instance : fintype (dihedral n) :=
fintype.of_equiv (bool × (zmod n)) (bz_equiv n).symm

lemma card : fintype.card (dihedral n) = 2 * n :=
by simp [fintype.card_congr (bz_equiv n), zmod.card]

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
  one := has_one.one,
  mul := has_mul.mul,
  inv := has_inv.inv,
  one_mul := λ a, by { rcases a with (i|i); simp only [one_eq,rr_mul,rs_mul,zero_add] },
  mul_one := λ a, by { rcases a with (i|i); simp only [one_eq,rr_mul,sr_mul,add_zero,sub_zero] },
  mul_left_inv := λ a, by { rcases a with (i|i); simp only [one_eq,r_inv,s_inv,rr_mul,ss_mul]; ring },
  mul_assoc := λ a b c, begin
   rcases a with (i|i); rcases b with (j|j); rcases c with (k|k);
   simp only [rr_mul,rs_mul,sr_mul,ss_mul]; ring, 
  end
}

def inc : cyclic n →* dihedral n := {
  to_fun := λ ⟨i⟩, r i,
  map_one' := rfl,
  map_mul' := λ ⟨i⟩ ⟨j⟩, rfl
}

lemma s_mul_self (i : zmod n) : (s i) * (s i) = 1 := 
by { rw [ss_mul, sub_self, one_eq] }

lemma r_pow_nat (i : zmod n) (j : ℕ) : (r i) ^ j = r (i * j) := 
begin
  induction j with j ih,
  { have : ((0 : ℕ) : zmod n) = 0 := rfl,
    rw [pow_zero, nat.cast_zero, mul_zero], refl },
  { rw [pow_succ, ih, rr_mul, add_comm, nat.succ_eq_add_one,
        nat.cast_add, nat.cast_one, mul_add, mul_one] }
end

lemma r_pow_int (i : zmod n) (j : ℤ) : (r i) ^ j = r (i * j) := 
begin
  cases j with j,
  { have : int.of_nat j = j := rfl, rw this,
    have : ((j : ℤ) : zmod n) = j := rfl, rw this,
    rw [zpow_coe_nat, r_pow_nat] },
  { rw [zpow_neg_succ_of_nat,r_pow_nat, r_inv, int.cast_neg_succ_of_nat,mul_neg],
    congr' 1, }
end

lemma r_pow_zmod (i j : zmod n) : (r i) ^ j = r (i * j) := 
begin
  change (r i) ^ j.val = _,
  rw [r_pow_nat i j.val, zmod.nat_cast_zmod_val]
end

lemma r_pow_n (i : zmod n) : (r i) ^ n = 1 := 
by rw[r_pow_nat,one_eq,zmod.nat_cast_self,mul_zero]

lemma s_pow_nat (i : zmod n) (j : ℕ) : (s i) ^ j = cond j.bodd (s i) 1 :=
begin
  induction j with j ih,
  refl,
  { rw [pow_succ, j.bodd_succ, ih],
    cases j.bodd; simp [bnot, cond, ss_mul], refl, }
end

lemma s_pow_int (i : zmod n) (j : ℤ) : (s i) ^ j = cond j.bodd (s i) 1 :=
begin
  cases j; simp [int.bodd, s_pow_nat],
  { cases j.bodd; simp [bnot, cond, s_inv] }
end

variable (n)

structure prehom (M : Type*) [monoid M] :=
(r s : M)
(hr : r ^ (n : ℕ) = 1)
(hs : s * s = 1)
(hrs : r * s * r = s)

variable {n}

namespace prehom

@[ext] 
lemma ext {M : Type*} [monoid M] {p q : prehom n M} : 
  p.r = q.r → p.s = q.s → p = q :=
begin
  cases p, cases q, rintro ⟨er⟩ ⟨es⟩, refl
end

variables {M : Type*} [monoid M] (p : prehom n M)

lemma sr_rs : ∀ (i : ℕ), p.r ^ i * p.s * (p.r ^ i) = p.s
| 0 := by rw [pow_zero, one_mul, mul_one]
| (i + 1) := calc
    p.r ^ (i + 1) * p.s * p.r ^ (i + 1) =
     p.r ^ (i + 1) * p.s * p.r ^ (1 + i) : by rw [add_comm i 1]
    ... = (p.r ^ i * p.r) * p.s * (p.r * p.r ^ i) : by rw [pow_add, pow_add, pow_one]
    ... = (p.r ^ i) * ((p.r * p.s) * (p.r * (p.r ^ i))) :
      by rw [mul_assoc (p.r ^ i) p.r p.s, mul_assoc (p.r ^ i)]
    ... = (p.r ^ i) * (((p.r * p.s) * p.r) * p.r ^ i) :
      by rw [mul_assoc (p.r * p.s) p.r (p.r ^ i)]
    ... = p.s : by rw [hrs, ← mul_assoc, sr_rs i]

lemma sr_rs' : ∀ (i : zmod n),
 p.s * p.r ^ i = p.r ^ (- i) * p.s :=
λ i, begin 
  exact calc
  p.s * p.r ^ i =
    1 * (p.s * p.r ^ i) : (one_mul _).symm
  ... = p.r ^ ((- i) + i)  * (p.s * p.r ^ i) :
    by { rw [← pow_mod_zero n], rw[neg_add_self] }
  ... = (p.r ^ (- i)) * (p.r ^ i * p.s * (p.r ^ i)) :
    by rw [pow_mod_add p.hr, mul_assoc (p.r ^ (- i)), mul_assoc]
  ... = (p.r ^ (- i)) * (p.r ^ i.val * p.s * p.r ^ i.val) : rfl
  ... = (p.r ^ (- i)) * p.s : by rw [p.sr_rs i.val]
end

include M p

def to_hom₀ : (dihedral n) → M 
| (dihedral.r i) := p.r ^ i
| (dihedral.s i) := p.r ^ i * p.s

def to_hom : (dihedral n) →* M := {
  to_fun := p.to_hom₀,
  map_one' := by { rw[one_eq,to_hom₀, pow_mod_zero] },
  map_mul' := λ a b,
  begin
    cases a with i i; cases b with j j; 
    simp only [rr_mul, rs_mul, sr_mul, ss_mul, to_hom₀],
    { rw [pow_mod_add p.hr], },
    { rw [← mul_assoc, pow_mod_add p.hr] },
    { rw [mul_assoc, p.sr_rs' j, ← mul_assoc, 
          sub_eq_add_neg, pow_mod_add p.hr] },
    { rw [mul_assoc, ← mul_assoc p.s _ p.s, p.sr_rs' j, mul_assoc, hs,
         mul_one, sub_eq_add_neg, pow_mod_add p.hr] }  
  end
}

@[simp] lemma to_hom.map_r (i : zmod n) :
  p.to_hom (dihedral.r i) = p.r ^ i := rfl

@[simp] lemma to_hom.map_s (i : zmod n) : 
  p.to_hom (dihedral.s i) = p.r ^ i * p.s := rfl

omit p
variable {n}

def of_hom (f : dihedral n →* M) : prehom n M := {
  r := f (dihedral.r 1),
  s := f (dihedral.s 0),
  hr := begin 
    let h := f.map_pow (dihedral.r 1) n,
    rw [r_pow_nat, one_mul, zmod.nat_cast_self, 
        ← dihedral.one_eq, f.map_one] at h,
    exact h.symm
  end,
  hs := by rw [← f.map_mul, s_mul_self, f.map_one],
  hrs := by
    rw [← f.map_mul, ← f.map_mul, rs_mul, sr_mul, add_zero, sub_self]
}

@[simp] lemma of_hom.r_def (f : dihedral n →* M) : 
  (of_hom f).r = f (dihedral.r 1) := rfl

@[simp] lemma of_hom.s_def (f : dihedral n →* M) : 
  (of_hom f).s = f (dihedral.s 0) := rfl

lemma of_to_hom : of_hom (to_hom p) = p :=
 by { ext; dsimp[to_hom,of_hom,to_hom₀],
  {exact pow_mod_one p.hr},
  {rw[pow_mod_zero,one_mul],}
  }  
/- ext (pow_mod_one p.hr) (one_mul p.s) -/

lemma to_of_hom (f : dihedral n →* M) : to_hom (of_hom f) = f :=
begin
  ext g, cases g with i i,
  { rw [to_hom.map_r, of_hom.r_def, ← f.map_pow_mod, r_pow_zmod, one_mul] },
  { rw [to_hom.map_s, of_hom.r_def, of_hom.s_def,
        ← f.map_pow_mod, ← f.map_mul, r_pow_zmod, rs_mul,
        add_zero, one_mul ] }
end

variables (n M)
def hom_equiv : prehom n M ≃ ((dihedral n) →* M) := {
  to_fun := to_hom,  inv_fun := of_hom,
  left_inv := of_to_hom,  right_inv := to_of_hom
}

end prehom

lemma generation {H : submonoid (dihedral n)}
  (hr : r 1 ∈ H) (hs : s 0 ∈ H) : H = ⊤ := 
begin
  ext g, simp only [submonoid.mem_top,iff_true],
  have hr' : ∀ (k : ℕ), r (k : zmod n) ∈ H := λ k, 
  begin
    induction k with k ih,
    { exact H.one_mem },
    { have : (r (k : zmod n)) * (r 1) = r (k.succ : zmod n) := 
      by { rw [rr_mul, nat.cast_succ] },
      rw [← this], exact H.mul_mem ih hr }
  end,
  cases g with i i; rw[← i.nat_cast_zmod_val] ,
  { exact hr' i.val },
  { have : ∀ (j : zmod n), s j = (r j) * (s 0) := 
      λ j, by { rw[rs_mul, add_zero] },
    rw [this], exact H.mul_mem (hr' _) hs  }
end

@[ext] lemma hom_ext {M : Type*} [monoid M] {f g : dihedral n →* M} : 
  f = g ↔ (f (dihedral.r 1) = g (dihedral.r 1)) ∧ 
          (f (dihedral.s 0) = g (dihedral.s 0)) := 
begin 
  split,
  { rintro ⟨_⟩, split; refl },
  { rintro ⟨hr,hs⟩, 
    exact (prehom.hom_equiv n M).symm.injective (prehom.ext hr hs) }
end

lemma map_smul_iff {X Y : Type*} [mul_action (dihedral n) X] 
  [mul_action (dihedral n) X] [mul_action (dihedral n) Y] (f : X → Y) :
(∀ (g : dihedral n) (x : X), f (g • x) = g • (f x)) ↔ 
  (∀ x : X, f ((s 0 : dihedral n) • x) = (s 0 : dihedral n) • (f x)) ∧ 
  (∀ x : X, f ((r 1 : dihedral n) • x) = (r 1 : dihedral n) • (f x)) :=
begin
  split, { intro h, exact ⟨h _, h _⟩ },
  rintro ⟨hs,hr⟩ g,
  let H : submonoid (dihedral n) := 
   mul_action.equivariantizer (dihedral n) f,
  change (s 0) ∈ H at hs,
  change (r 1) ∈ H at hr,
  change g ∈ H,
  rw[generation hr hs],
  apply submonoid.mem_top
end

end dihedral

@[derive decidable_eq]
inductive infinite_dihedral
| r : ℤ → infinite_dihedral
| s : ℤ → infinite_dihedral

namespace infinite_dihedral

variable {n}

def log : infinite_dihedral → ℤ
| (r i) := i
| (s i) := i

def is_s : infinite_dihedral → bool
| (r _) := ff
| (s _) := tt

def to_bz : infinite_dihedral → bool × ℤ
| (r i) := ⟨ff, i⟩
| (s i) := ⟨tt, i⟩

def of_bz : bool × ℤ → infinite_dihedral
| ⟨ff, i⟩ := r i
| ⟨tt, i⟩ := s i

variable (n)
def bz_equiv : infinite_dihedral ≃ (bool × ℤ) :=
{ to_fun := to_bz,
  inv_fun := of_bz,
  left_inv := λ g, by { cases g; refl },
  right_inv := λ bi, by { rcases bi with ⟨_|_, i⟩ ; refl } }

variable {n}

def one : infinite_dihedral := r 0

def inv : ∀ (g : infinite_dihedral), infinite_dihedral
| (r i) := r (-i)
| (s i) := s i

def mul : ∀ (g h : infinite_dihedral), infinite_dihedral
| (r i) (r j) := r (i + j)
| (r i) (s j) := s (i + j)
| (s i) (r j) := s (i - j)
| (s i) (s j) := r (i - j)

instance : has_one (infinite_dihedral) := ⟨r 0⟩
lemma one_eq : (1 : infinite_dihedral) = r 0 := rfl

instance : has_inv (infinite_dihedral) := ⟨infinite_dihedral.inv⟩
lemma r_inv (i : ℤ) : (r i)⁻¹ = r (- i) := rfl
lemma s_inv (i : ℤ) : (s i)⁻¹ = s i := rfl

instance : has_mul (infinite_dihedral) := ⟨infinite_dihedral.mul⟩
lemma rr_mul (i j : ℤ) : (r i) * (r j) = r (i + j) := rfl
lemma rs_mul (i j : ℤ) : (r i) * (s j) = s (i + j) := rfl
lemma sr_mul (i j : ℤ) : (s i) * (r j) = s (i - j) := rfl
lemma ss_mul (i j : ℤ) : (s i) * (s j) = r (i - j) := rfl

lemma srs (i : ℤ) : (s 0) * (r i) * (s 0) = r (- i) := by { simp [sr_mul,ss_mul] }

instance : group (infinite_dihedral) := {
 one := has_one.one, 
 mul := has_mul.mul,
 inv := has_inv.inv,
 one_mul := λ a, by { rcases a with (i|i); simp only [one_eq,rr_mul,rs_mul,zero_add] },
 mul_one := λ a, by { rcases a with (i|i); simp only [one_eq,rr_mul,sr_mul,add_zero,sub_zero] },
 mul_left_inv := λ a, by { rcases a with (i|i); simp only [one_eq,r_inv,s_inv,rr_mul,ss_mul]; ring },
 mul_assoc := λ a b c, begin
   rcases a with (i|i); rcases b with (j|j); rcases c with (k|k);
   simp only [rr_mul,rs_mul,sr_mul,ss_mul]; ring, 
 end
}

def inc : infinite_cyclic →* infinite_dihedral := {
  to_fun := λ ⟨i⟩, r i,
  map_one' := rfl,
  map_mul' := λ ⟨i⟩ ⟨j⟩, rfl
}

lemma s_mul_self (i : ℤ) : (s i) * (s i) = 1 := 
by { rw [ss_mul, sub_self, one_eq] }

lemma r_pow_nat (i : ℤ) (j : ℕ) : (r i) ^ j = r (i * j) := 
begin
  induction j with j ih,
  { rw [pow_zero, int.coe_nat_zero, mul_zero, one_eq] },
  { rw [pow_succ, ih, rr_mul, add_comm, nat.succ_eq_add_one,
        int.coe_nat_add, int.coe_nat_one, mul_add, mul_one] }
end

lemma r_pow_int (i j : ℤ) : (r i) ^ j = r (i * j) := 
begin
  cases j with j,
  { have : int.of_nat j = j := rfl, rw[this,zpow_coe_nat,r_pow_nat] },
  { have : int.neg_succ_of_nat j = - (j + 1) := rfl,
    rw [zpow_neg_succ_of_nat,r_pow_nat,r_inv,this,mul_neg],
    congr' 1, 
  }
end

lemma generation {H : submonoid infinite_dihedral}
  (hr : r 1 ∈ H) (hs : s 0 ∈ H) : H = ⊤ := 
begin
  ext g, simp only [submonoid.mem_top,iff_true],
  have h₀ : ∀ (k : ℕ), r k ∈ H := λ k, 
  begin
    induction k with k ih,
    { exact H.one_mem },
    { have : (r k) * (r 1) = r k.succ := 
      by { rw [rr_mul], refl },
      rw [← this], exact H.mul_mem ih hr }
  end,
  have h₁ : ∀ (k : ℕ), r (- k) ∈ H := λ k,
  begin 
   have := H.mul_mem (H.mul_mem hs (h₀ k)) hs,
   rw[srs] at this, exact this
  end,
  have h₂ : ∀ (k : ℤ), r k ∈ H := 
  begin
   rintro (k|k), exact h₀ k, exact h₁ k.succ,
  end,
  cases g with i i,
  { exact h₂ i },
  { have : (s i) = (r i) * (s 0) := by { rw[rs_mul,add_zero]},
    rw[this], exact H.mul_mem (h₂ i) hs,
  }
end

@[ext] lemma hom_ext {M : Type*} [monoid M] {f g : infinite_dihedral →* M} : 
  f = g ↔ (f (infinite_dihedral.r 1) = g (infinite_dihedral.r 1)) ∧ 
          (f (infinite_dihedral.s 0) = g (infinite_dihedral.s 0)) := 
begin 
 split, { intro h, cases h, split; refl },
 rintro ⟨hr,hs⟩,
 let H : submonoid infinite_dihedral := monoid_hom.eq_mlocus f g,
 change _ ∈ H at hr, change _ ∈ H at hs,
 have h := generation hr hs,
 ext x, change x ∈ H, rw[h], exact submonoid.mem_top x,
end

structure prehom (M : Type*) [monoid M] :=
(r s : M)
(hs : s * s = 1)
(hrs : r * s * r = s)

namespace prehom

@[ext] 
lemma ext {M : Type*} [monoid M] {p q : prehom M} : 
  p.r = q.r → p.s = q.s → p = q :=
begin
  cases p, cases q, rintro ⟨er⟩ ⟨es⟩, refl
end

variables {M : Type*} [monoid M] (p : prehom M)

def r_unit : units M :=
{ val := p.r, inv := p.s * p.r * p.s,
  val_inv := by rw [← mul_assoc, ← mul_assoc, p.hrs, p.hs],
  inv_val := by rw [mul_assoc, mul_assoc, ← mul_assoc p.r, p.hrs, p.hs] }

def s_unit : units M :=
{ val := p.s, inv := p.s, val_inv := p.hs, inv_val := p.hs }

@[simp] lemma r_unit_coe : (p.r_unit : M) = p.r := rfl
@[simp] lemma r_unit_val : p.r_unit.val = p.r := rfl
@[simp] lemma r_unit_inv : p.r_unit.inv = p.s * p.r * p.s := rfl
@[simp] lemma s_unit_coe : (p.s_unit : M) = p.s := rfl
@[simp] lemma s_unit_val : p.s_unit.val = p.s := rfl
@[simp] lemma s_unit_inv : p.s_unit.inv = p.s := rfl

theorem hs_unit : p.s_unit * p.s_unit = 1 := 
  units.ext p.hs

theorem hrs_unit : p.r_unit * p.s_unit * p.r_unit = p.s_unit := 
  units.ext p.hrs

lemma sr_rs : ∀ (i : ℕ), p.r ^ i * p.s * (p.r ^ i) = p.s
| 0 := by rw [pow_zero, one_mul, mul_one]
| (i + 1) := calc
    p.r ^ (i + 1) * p.s * p.r ^ (i + 1) =
     p.r ^ (i + 1) * p.s * p.r ^ (1 + i) : by rw [add_comm i 1]
    ... = (p.r ^ i * p.r) * p.s * (p.r * p.r ^ i) : by rw [pow_add, pow_add, pow_one]
    ... = (p.r ^ i) * ((p.r * p.s) * (p.r * (p.r ^ i))) :
      by rw [mul_assoc (p.r ^ i) p.r p.s, mul_assoc (p.r ^ i)]
    ... = (p.r ^ i) * (((p.r * p.s) * p.r) * p.r ^ i) :
      by rw [mul_assoc (p.r * p.s) p.r (p.r ^ i)]
    ... = p.s : by rw [hrs, ← mul_assoc, sr_rs i]

lemma sr_rs_unit : ∀ (i : ℤ), 
  p.r_unit ^ i * p.s_unit * (p.r_unit ^ i) = p.s_unit :=
begin
  suffices h : ∀ (i : ℕ), 
    p.r_unit ^ i * p.s_unit * (p.r_unit ^ i) = p.s_unit,
  { intro i, cases i with i i,
    { have : int.of_nat i = i := rfl, 
      rw [this, zpow_coe_nat, h i] },
    { rw[← h i.succ], 
      let u := p.r_unit ^ i.succ,
      let v := p.s_unit,
      change (u⁻¹ * (u * v * u)) * u⁻¹ = u * v * u,
      rw [mul_assoc, mul_assoc, mul_inv_self, mul_one],
      rw [← mul_assoc, inv_mul_self, one_mul],
      symmetry, exact h i.succ } },
  { intro i, apply units.ext,
    rw [units.coe_mul, units.coe_mul, units.coe_pow, 
      p.r_unit_coe, p.s_unit_coe, p.sr_rs] }
end

lemma sr_rs' (i : ℤ) : 
  p.s_unit * (p.r_unit ^ i) = (p.r_unit) ^ (- i) * p.s_unit :=
calc
  p.s_unit * p.r_unit ^ i = 1 * (p.s_unit * p.r_unit ^ i) : (one_mul _).symm
  ... = (p.r_unit ^ ((- i) + i))  * (p.s_unit * p.r_unit ^ i) :
     by { rw [← pow_zero p.r_unit, neg_add_self], refl }
  ... = (p.r_unit ^ (- i)) * ((p.r_unit ^ i) * p.s_unit * (p.r_unit ^ i)) :
     by { rw [zpow_add, mul_assoc (p.r_unit ^ (- i)), mul_assoc] }
  ... = p.r_unit ^ (- i) * p.s_unit : by { rw [p.sr_rs_unit] }

include M p

def to_hom₀ : infinite_dihedral → M 
| (infinite_dihedral.r i) := ((p.r_unit ^ i : units M) : M)
| (infinite_dihedral.s i) := ((p.r_unit ^ i * p.s_unit : units M) : M)

def to_hom : infinite_dihedral →* M := {
  to_fun := p.to_hom₀,
  map_one' := rfl,
  map_mul' := λ a b,
  begin
    cases a with i i; cases b with j j; 
    simp only [rr_mul, rs_mul, sr_mul, ss_mul, to_hom₀];
    rw [← units.coe_mul],
    { rw [zpow_add], },
    { rw [← mul_assoc, zpow_add] },
    { rw [mul_assoc, p.sr_rs' j, ← mul_assoc, 
          sub_eq_add_neg, zpow_add] },
    { rw [mul_assoc, ← mul_assoc p.s_unit _ p.s_unit], 
      rw [p.sr_rs' j, mul_assoc, p.hs_unit,
         mul_one, sub_eq_add_neg, zpow_add] }  
  end
}

lemma to_hom.map_r (i : ℤ) :
  p.to_hom (infinite_dihedral.r i) = (p.r_unit ^ i : units M) := rfl

lemma to_hom.map_r_nat (i : ℕ) :
  p.to_hom (infinite_dihedral.r i) = p.r ^ i := 
by { rw [to_hom.map_r, zpow_coe_nat, units.coe_pow], refl }

lemma to_hom.map_s (i : ℤ) : 
  p.to_hom (infinite_dihedral.s i) = (p.r_unit ^ i * p.s_unit : units M) := rfl

lemma to_hom.map_s_nat (i : ℕ) :
  p.to_hom (infinite_dihedral.s i) = p.r ^ i * p.s := 
by { rw [to_hom.map_s, zpow_coe_nat, units.coe_mul, units.coe_pow], refl }

omit p
variable {n}

def of_hom (f : infinite_dihedral →* M) : prehom M := {
  r := f (infinite_dihedral.r 1),
  s := f (infinite_dihedral.s 0),
  hs := by rw [← f.map_mul, s_mul_self, f.map_one],
  hrs := by
    rw [← f.map_mul, ← f.map_mul, rs_mul, sr_mul, add_zero, sub_self]
}

@[simp] lemma of_hom.r_def (f : infinite_dihedral →* M) : 
  (of_hom f).r = f (infinite_dihedral.r 1) := rfl

@[simp] lemma of_hom.s_def (f : infinite_dihedral →* M) : 
  (of_hom f).s = f (infinite_dihedral.s 0) := rfl

lemma of_to_hom : of_hom (to_hom p) = p := 
begin
  ext,
  { rw [of_hom.r_def, to_hom.map_r, zpow_one], refl },
  { rw [of_hom.s_def, to_hom.map_s, zpow_zero, one_mul], refl }
end

lemma units.pow_inv (M : Type*) [monoid M] (g : units M) (n : ℕ) : 
  (g ^ n).inv = g.inv ^ n := 
begin
  induction n with n ih,
  { rw [pow_zero,pow_zero], refl },
  { rw [pow_succ], change _ * _  = _, 
    rw [ih, n.succ_eq_add_one, pow_add, pow_one] }
end

lemma to_of_hom (f : infinite_dihedral →* M) : to_hom (of_hom f) = f :=
begin
  apply hom_ext.mpr, split,
  { have : (1 : ℤ) = (1 : ℕ) := rfl, 
    rw [this,to_hom.map_r_nat,pow_one,of_hom.r_def], refl },
  { rw [to_hom.map_s,zpow_zero,one_mul,s_unit_coe,of_hom.s_def] }
end

def hom_equiv : prehom M ≃ (infinite_dihedral →* M) := {
  to_fun := to_hom,  inv_fun := of_hom,
  left_inv := of_to_hom,  right_inv := to_of_hom
}

end prehom

end infinite_dihedral

end group_theory
