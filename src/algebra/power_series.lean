/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Given a semiring `R`, this file defines the power series semiring `R[[x]]`
-/

import data.fintype.basic data.finsupp algebra.big_operators data.pi
import data.list_extra algebra.biadditive algebra.prod_equiv algebra.convolution
import algebra.order.sub
import tactic.squeeze tactic.pi_instances

def power_series (R : Type*) := convolution.map ℕ R

namespace power_series

open finset 

variable {R : Type*}

def coeff₀ : ℕ → (power_series R) → R := λ n f, f n

instance [has_zero R] : has_zero (power_series R) := 
 by {dsimp[power_series], apply_instance}

instance [add_comm_monoid R] : add_comm_monoid (power_series R) := 
 by {dsimp[power_series], apply_instance}

instance [semiring R] : semiring (power_series R) := 
 by {dsimp[power_series], apply_instance}

instance [comm_semiring R] : comm_semiring (power_series R) := 
 by {dsimp[power_series], apply_instance}

instance [ring R] : ring (power_series R) := 
 by {dsimp[power_series], apply_instance}

instance [comm_ring R] : comm_ring (power_series R) := 
 by {dsimp[power_series], apply_instance}

/- `C a` is the constant power series with value `a`, so the zeroth 
   coefficient is `a` and the other coefficients are zero.
-/
def C [semiring R] : R →+* power_series R := {
 to_fun := convolution.map.delta,
 map_zero' := convolution.map.delta_zero,
 map_one' := by {dsimp[power_series,has_one.one,monoid.one,semiring.one],refl},
 map_add' := λ x y, by {apply convolution.map.delta_add},
 map_mul' := λ x y, by {symmetry,apply convolution.delta_convolve_delta}
}

/- `X` denotes the standard generator of the power series 
   semiring `R[[X]]`.
-/

def X [semiring R] : power_series R := convolution.map.single (1 : ℕ) (1 : R)

def coeff [add_comm_monoid R] (n : ℕ) : (power_series R →+ R) := {
  to_fun := λ f, f n,
  map_zero' := rfl,
  map_add' := λ f g, rfl,
}

@[ext]
lemma ext [add_comm_monoid R] : 
 ∀ {f g : power_series R}, (∀ n, coeff n f = coeff n g) → f = g := @funext _ _

lemma coeff_n_one [semiring R] (n : ℕ) :
 coeff n (1 : power_series R) = ite (0 = n) 1 0 := rfl

lemma coeff_zero_one [semiring R] : coeff 0 (1 : power_series R) = 1 := rfl
lemma coeff_succ_one [semiring R] (n : ℕ) : coeff (n + 1) (1 : power_series R) = 0 := rfl

lemma coeff_n_C [semiring R] (n : ℕ) (a : R) :
 coeff n (C a) = ite (0 = n) a 0 := rfl

lemma coeff_zero_C [semiring R] (a : R) : coeff 0 (C a) = a := rfl
lemma coeff_succ_C [semiring R] (n : ℕ) (a : R) : coeff (n + 1) (C a) = 0 := rfl

lemma coeff_n_X [semiring R] (n : ℕ) :
 coeff n (X : power_series R) = ite (1 = n) 1 0 := rfl

lemma coeff_zero_X [semiring R] : coeff 0 (X : power_series R) = 0 := rfl
lemma coeff_one_X  [semiring R] : coeff 1 (X : power_series R) = 1 := rfl
lemma coeff_ss_X   [semiring R] (n : ℕ) : coeff (n + 2) (X : power_series R) = 0 := rfl

lemma coeff_mul [semiring R] (n : ℕ) (f g : power_series R) : 
 coeff n (f * g) = (range n.succ).sum (λ i, (coeff i f) * (coeff (n - i) g)) := 
begin
 change convolution.convolve ((*) : R → R → R) f g n =
  (range n.succ).sum (λ i, (coeff i f) * (coeff (n - i) g)),
 dsimp[convolution.convolve,convolution.sum_set.els,coeff],
 let h_inj :
  ∀ (i₁ : ℕ) (h₁ : i₁ ∈ range n.succ)
    (i₂ : ℕ) (h₂ : i₂ ∈ range n.succ)
    (e : prod.mk i₁ (n - i₁) = prod.mk i₂ (n - i₂)), i₁ = i₂ := 
  by { intros,injection e, },
 have := @sum_image R (ℕ × ℕ) ℕ (λ x, (f x.1) * (g x.2)) _ _ 
  (range n.succ) (λ i, prod.mk i (n - i)) h_inj,
 simp only [] at this ⊢, rw[← this]
end

/- Left multiplication by `C a` is termwise left multiplication by `a` -/
lemma coeff_C_mul [semiring R] (n : ℕ) (a : R) (f : power_series R) : 
 coeff n ((C a) * f) = a * coeff n f := 
begin
 rw[coeff_mul],
 let h := @sum_eq_single R ℕ _ (range (n + 1)) 
  (λ i, coeff i (C a) * coeff (n - i) f) 0
   (λ i _ h, by { simp only[], rw[coeff_n_C i a,if_neg h.symm,zero_mul], })
   (λ h, by { exfalso, 
              exact h (mem_range_succ.mpr (nat.zero_le n)) }),
 rw[h],simp only[],rw[coeff_n_C,if_pos rfl,nat.sub_zero],
end

/- Right multiplication by `C a` is termwise right multiplication by `a` -/
lemma coeff_mul_C [semiring R] (n : ℕ) (f : power_series R) (a : R) : 
 coeff n (f * (C a)) = (coeff n f) * a := 
begin
 rw[coeff_mul],
 let h := @sum_eq_single R ℕ _ (range (n + 1)) 
  (λ i, coeff i f * coeff (n - i) (C a)) n
   (λ i h_le h_ne, by {
     replace h_le : i ≤ n := mem_range_succ.mp h_le,
     have h_lt : i < n := lt_of_le_of_ne h_le h_ne,
     have : n - i ≠ 0 := λ e, not_lt_of_ge (nat.sub_eq_zero_iff_le.mp e) h_lt, 
     simp only[], rw[coeff_n_C (n - i),if_neg this.symm,mul_zero],
    })
   (λ h, by { exfalso, exact h (mem_range_succ.mpr (le_refl n)),}),
 rw[h],simp only[],rw[nat.sub_self,coeff_n_C,if_pos rfl],
end

lemma coeff_X_mul_zero [semiring R] (f : power_series R) :
 coeff 0 (X * f) = 0 := 
begin
 rw[coeff_mul,sum_range_one,coeff_n_X,if_neg (dec_trivial : 1 ≠ 0),zero_mul],
end

lemma coeff_X_mul_succ [semiring R] (n : ℕ) (f : power_series R) :
 coeff (n + 1) (X * f) = coeff n f := 
begin
 rw[coeff_mul],
 let h₀ := @sum_eq_single R ℕ _ (range (n + 2)) 
  (λ i, coeff i X * coeff (n + 1 - i) f) 1
   (λ i _ h, by { simp only[], rw[coeff_n_X i,if_neg h.symm,zero_mul], })
   (λ h, by { have : 1 < n + 2 := nat.succ_lt_succ (nat.zero_lt_succ n),
              have : 1 ∈ range (n + 2) := mem_range.mpr this,
              exact (h this).elim}),
  rw[h₀],simp only[coeff_one_X],rw[one_mul],refl,
end

/- `E` is the homomorphism sending a power series to its constant term. -/
def E [semiring R] : (power_series R) →+* R := {
  to_fun := λ f, coeff 0 f,
  map_zero' := rfl,
  map_one' := rfl,
  map_add' := λ f g, rfl,
  map_mul' := λ f g, by { rw[coeff_mul,sum_range_one] }  
}

lemma E_C [semiring R] (a : R) : E (C a) = a := rfl

/- `val_ge n f` means that `f` has valuation at least `n`, or in other
   words that `f` is divisible by `X ^ n`.
-/
@[irreducible]
def val_ge [add_comm_monoid R] (n : ℕ) (f : power_series R) : Prop := 
 ∀ {i : ℕ} (hi : i < n), coeff i f = 0

lemma val_ge_zero_all [add_comm_monoid R] (f : power_series R) : val_ge 0 f := 
begin dsimp[val_ge],intros i hi, exact (nat.not_lt_zero i hi).elim end

lemma val_ge_all_zero [add_comm_monoid R] (n : ℕ) : val_ge n (0 : power_series R) := 
 by {dsimp[val_ge], intros i hi, refl}

lemma val_ge_one_iff [add_comm_monoid R] (f : power_series R) : 
 val_ge 1 f ↔ coeff 0 f = 0 := 
  by { dsimp[val_ge], split,
   {intro h,exact h (nat.lt_succ_self 0)},
   {intros h i i_lt,cases i with i,{exact h},
    {exact (nat.not_lt_zero i (nat.lt_of_succ_lt_succ i_lt)).elim,}}
  }

lemma val_ge_add [add_comm_monoid R] {n : ℕ} {f g : power_series R} : 
 val_ge n f → val_ge n g → val_ge n (f + g) := 
  by {dsimp[val_ge], intros hf hg i i_is_lt, 
      show coeff i f + coeff i g = 0,rw[hf i_is_lt,hg i_is_lt,zero_add],}

lemma val_ge_mul [semiring R] {n m : ℕ} {f g : power_series R} : 
 val_ge n f → val_ge m g → val_ge (n + m) (f * g) := 
  λ hf hg,
begin
 dsimp[val_ge] at hf hg ⊢,
 intros k k_is_lt,
 change (convolution.sum_set.els k).sum (λ ij, (f ij.1) * (g ij.2)) = 0,
 have : (convolution.sum_set.els k).sum (λ ij, (0 : R)) = (0 : R) := sum_const_zero,
 rw[← this],apply sum_congr rfl,
 rintros ⟨i,j⟩ ij_sum,
 replace ij_sum : i + j = k := (convolution.sum_set.mem_els _ _).mp ij_sum,
 change (coeff i f) * (coeff j g) = 0, 
 by_cases hi : i < n, {rw[hf hi,zero_mul],},
 by_cases hj : j < m, {rw[hg hj,mul_zero],},
 let hk : n + m ≤ k :=
  ij_sum ▸ (add_le_add (le_of_not_gt hi) (le_of_not_gt hj)),
 exact (not_le_of_gt k_is_lt hk).elim,
end

lemma val_ge_pow [semiring R] {n : ℕ} {f : power_series R} (hf : val_ge n f) (k : ℕ) : 
 val_ge (k * n) (f ^ k) := 
begin
 induction k with k ih,
 {rw[zero_mul],apply val_ge_zero_all},
 {rw[nat.succ_eq_add_one,pow_add,pow_one,add_mul,one_mul],
  exact val_ge_mul ih hf,
 }
end

lemma val_ge_pow' [semiring R] {f : power_series R} (hf : coeff 0 f = 0) (k : ℕ) : 
 val_ge k (f ^ k) := 
  by {have := val_ge_pow ((val_ge_one_iff f).mpr hf) k, 
      rw[mul_one] at this, exact this,}

lemma val_ge_X [semiring R] : val_ge 1 (X : power_series R) := 
 by {dsimp[val_ge,X,coeff],intros i hi,
     apply convolution.map.single_eq_of_ne  (ne_of_lt hi).symm,}

lemma coeff_X_pow [semiring R] (n i : ℕ) :
 coeff i ((X : power_series R) ^ n) = ite (n = i) 1 0 := 
begin
 induction n with n ih generalizing i,
 {rw[pow_zero,coeff_n_one]},
 {rw[pow_succ],cases i with i,
  {rw[coeff_X_mul_zero],rw[if_neg (nat.succ_ne_zero n)],},
  {rw[coeff_X_mul_succ,ih i],by_cases h : n = i,
   {rw[if_pos h,if_pos (congr_arg nat.succ h)]},
   {have : n.succ ≠ i.succ := λ e, h (nat.succ_inj'.mp e),
    rw[if_neg h,if_neg this]}}}
end

section compose

variable [comm_semiring R]

/-
 Note: this definition is only sensible with the side condition `coeff 0 g = 0`
-/

def compose (f g : power_series R) : power_series R := 
 λ n, ((range n.succ).sum (λ j, C (coeff j f) * (g ^ j))) n 

lemma coeff_compose (n : ℕ) (f g : power_series R) : 
 coeff n (compose f g) = 
  (range n.succ).sum (λ j, (coeff j f) * (coeff n (g ^ j))) := 
begin
 let hh := (coeff n : power_series R →+ R).map_sum,
 have := calc 
  coeff n (compose f g) = 
   coeff n ((range n.succ).sum (λ j, C (coeff j f) * (g ^ j))) : rfl
   ... = (range n.succ).sum (λ j, coeff n (C (coeff j f) * (g ^ j))) :
    by {rw[← hh]},
 rw[this],congr,funext j,rw[coeff_C_mul],
end

lemma coeff_compose_extra {n m : ℕ} (f g : power_series R) 
 (hg : coeff 0 g = 0) (hnm : n ≤ m) :
 coeff n (compose f g) = 
  (range m.succ).sum (λ j, (coeff j f) * (coeff n (g ^ j))) := 
begin 
 rw[coeff_compose],
 have : range n.succ = (range m.succ).filter (λ i, i ≤ n) := 
  by {ext i,rw[mem_filter,mem_range_succ,mem_range_succ],split,
      {intro hn,exact ⟨le_trans hn hnm,hn⟩,},{exact λ h,h.2}},
 rw[this,sum_filter],congr,ext j,split_ifs with h,refl,
 replace h : n < j := lt_of_not_ge h,
 have hv := val_ge_pow' hg j, dsimp[val_ge] at hv, rw[hv h,mul_zero],
end

lemma zero_compose (g : power_series R) : compose 0 g = 0 := 
begin
 ext n,rw[coeff_compose],
 apply sum_eq_zero_of_terms_eq_zero,
 intros i _,rw[(coeff i).map_zero,zero_mul],
end

/- `f ∘ g` is an additive function of `f`. -/
lemma add_compose (f₁ f₂ g : power_series R) : 
 compose (f₁ + f₂) g = compose f₁ g + compose f₂ g := 
begin
 ext n,rw[(coeff n).map_add,coeff_compose,coeff_compose,coeff_compose],
 rw[← sum_add_distrib],congr,ext j,
 rw[(coeff _).map_add,add_mul],
end

/- `f ∘ g` is a multiplicative function of `f`. -/
lemma mul_compose (f₁ f₂ g : power_series R) (hg : coeff 0 g = 0): 
 compose (f₁ * f₂) g = compose f₁ g * compose f₂ g := 
begin
 ext n,
 let r := range n.succ,
 let r2 := r.product r,
 let r3 := r.product r2,
 let r3' := r2.product r,
 let t₁ : (ℕ × ℕ × ℕ) → R := 
  λ jpq, coeff jpq.2.1 f₁ * coeff jpq.2.2 f₂ * 
          coeff jpq.1 (g ^ jpq.2.1) * coeff (n - jpq.1) (g ^ jpq.2.2), 
 let t'₁ := λ pqj : ((ℕ × ℕ) × ℕ), t₁ ⟨pqj.2,pqj.1⟩,
 let inc₁ : ∀ (k : ℕ), ℕ ↪ (ℕ × ℕ) := λ k, {
    to_fun := λ p, ⟨p,k - p⟩, inj' := λ p₁ p₂ e, congr_arg prod.fst e,
 },
 let r2' := r.bUnion (λ k, (range k.succ).map (inc₁ k)),
 have r2_filter : r2' = r2.filter (λ pq, pq.1 + pq.2 ≤ n) := by {
  ext ⟨p,q⟩,rw[mem_bUnion,mem_filter,mem_product,mem_range_succ,mem_range_succ],
  simp only [],split,
  {rintro ⟨k,k_le,hk⟩,rcases mem_map.mp hk with ⟨p',p_le,hpq⟩,
   injection hpq with hp hq,rw[hp] at p_le hq,
   replace k_le := mem_range_succ.mp k_le, 
   replace p_le := mem_range_succ.mp p_le,
   repeat {split}; apply le_trans _ k_le,
   {exact p_le},
   {rw[← hq],apply tsub_le_self},
   {rw[← hq,nat.add_sub_of_le p_le]}
  },
  {rintro ⟨⟨p_le,q_le⟩,k_le⟩,
   use p + q,use mem_range_succ.mpr k_le,
   apply mem_map.mpr,use p,use mem_range_succ.mpr (nat.le_add_right p q),
   show prod.mk p ((p + q) - p) = prod.mk p q,
   congr,rw[add_comm,nat.add_sub_cancel],
  }
 },
 let e₁ := calc
  coeff n (compose (f₁ * f₂) g) = 
    r.sum (λ k, coeff k (f₁ * f₂) * (coeff n (g ^ k))) : by rw[coeff_compose]
  ... = r.sum (λ k, (range k.succ).sum (λ p, coeff p f₁ * coeff (k - p) f₂ * coeff n (g ^ k))) : 
   by {apply sum_congr rfl,intros k k_le,rw[coeff_mul,sum_mul],}
  ... = r2'.sum (λ pq, coeff pq.1 f₁ * coeff pq.2 f₂ * coeff n (g ^ (pq.1 + pq.2))) : 
   by {rw[sum_bUnion],apply sum_congr rfl,intros k k_le,
       rw[sum_map],{
         apply sum_congr rfl,intros p p_le,dsimp[inc₁],
         replace p_le : p ≤ k := mem_range_succ.mp p_le,
         rw[nat.add_sub_of_le p_le],
       },{-- side condition for sum_map
         intros k₁ k₁_le k₂ k₂_le k_ne,
         change disjoint _ _, simp only [],
         rw [disjoint, le_bot_iff],
         apply eq_empty_iff_forall_not_mem.mpr,rintros ⟨p,q⟩ hpq,
         change _ ∈ _ ∩ _ at hpq,
         rw[mem_inter] at hpq,
         rcases mem_map.mp hpq.1 with ⟨p₁,p₁_le,hpq₁⟩,injection hpq₁ with hp₁ hq₁, 
         rcases mem_map.mp hpq.2 with ⟨p₂,p₂_le,hpq₂⟩,injection hpq₂ with hp₂ hq₂,
         replace p₁_le := mem_range_succ.mp p₁_le,  
         replace p₂_le := mem_range_succ.mp p₂_le,  
         rw[← nat.add_sub_of_le p₁_le,← nat.add_sub_of_le p₂_le,hq₁,hq₂,hp₁,hp₂] at k_ne,
         exact k_ne rfl,
       }
   }
  ... = r2.sum (λ pq, coeff pq.1 f₁ * coeff pq.2 f₂ * coeff n (g ^ (pq.1 + pq.2))) :
   by {
     rw[r2_filter,sum_filter],apply sum_congr rfl,rintros ⟨p,q⟩ hpq,
     split_ifs,refl,
     replace h : n < p + q := lt_of_not_ge h,
     have := val_ge_pow' hg (p + q),dsimp[val_ge] at this,rw[this h,mul_zero],
   }
  ... = r2.sum (λ pq,r.sum (λ j, t₁ ⟨j,pq⟩)) :
   by {dsimp[t₁],
       apply finset.sum_congr rfl,rintros ⟨p,q⟩ hpq,rw[pow_add,coeff_mul,mul_sum],
       apply finset.sum_congr rfl,rintros j hj,repeat {rw[mul_assoc]},}
  ... = r3'.sum t'₁ :
   by {dsimp[r3'],rw[@sum_product _ _ _ _ r2 r],} 
   ,rw[e₁],clear e₁, 
 let e₂ := calc
  coeff n (compose f₁ g * compose f₂ g) = 
   r.sum (λ j, coeff j (compose f₁ g) * coeff (n - j) (compose f₂ g)) :
    by rw[coeff_mul]
   ... = r.sum (λ j,   r.sum (λ p, coeff p f₁ * coeff j (g ^ p))
                     * r.sum (λ q, coeff q f₂ * coeff (n - j) (g ^ q))) :
    by {apply sum_congr rfl,intros j j_le,
     replace j_le := mem_range_succ.mp j_le,
     rw[coeff_compose_extra f₁ g hg j_le],
     have : n - j ≤ n := tsub_le_self,
     rw[coeff_compose_extra f₂ g hg this],
    }
   ... = r.sum (λ j, r.sum (λ p, coeff p f₁ * coeff j (g ^ p) * 
           r.sum (λ q, coeff q f₂ * coeff (n - j) (g ^ q)))) : 
    by {apply sum_congr rfl,intros j j_le,rw[sum_mul]}  
   ... = r.sum (λ j, r.sum (λ p, r.sum (λ q, 
          coeff p f₁ * coeff j (g ^ p) * (coeff q f₂ * coeff (n - j) (g ^ q))))) : 
    by {apply sum_congr rfl,intros j j_le,
        apply sum_congr rfl,intros k k_le,rw[mul_sum]}
   ... = r.sum (λ j, r.sum (λ p, r.sum (λ q, t₁ ⟨j,p,q⟩))) :
    by {apply sum_congr rfl,intros j j_le,
        apply sum_congr rfl,intros k k_le,
        apply sum_congr rfl,intros p p_le,
        rw[mul_assoc,← mul_assoc (coeff j (g ^ k)),mul_comm (coeff j (g ^ k))],
        rw[← mul_assoc,← mul_assoc],}
   ... = r.sum (λ j, r2.sum (λ pq, t₁ ⟨j,pq⟩)) : 
    by {apply sum_congr rfl,intros j j_le,rw[sum_product],}
   ... = r3.sum t₁ : by rw[← sum_product],
  rw[e₂], clear e₂,
  let s := λ (jpq : ℕ × ℕ × ℕ) (h : jpq ∈ r3), prod.mk jpq.2 jpq.1,
  let e := @sum_bij _ _ _ _ r3 r3' t₁ t'₁ s
   (λ ⟨j,p,q⟩ h, by {dsimp[s],repeat {rw[mem_product] at h ⊢},
                    rcases h with ⟨hj,hp,hq⟩,repeat {split}; assumption,})
   (λ ⟨j,p,q⟩ h, rfl)
   (λ ⟨j₁,p₁,q₁⟩ ⟨j₂,p₂,q₂⟩ h₁ h₂ e,
      by {dsimp[s] at e,injection e with epq ej,injection epq with ep eq,
          rw[ej,ep,eq],})
   (λ ⟨⟨p,q⟩,j⟩ h, 
      by {use ⟨j,p,q⟩,have : (⟨j,p,q⟩ : ℕ × ℕ × ℕ) ∈ r3,
           {repeat {rw[mem_product] at h ⊢},
            rcases h with ⟨⟨hp,hq⟩,hj⟩,repeat {split}; assumption,},
            use this}),
  exact e.symm,
end

lemma C_compose (a : R) (g : power_series R) : compose (C a) g = C a := 
begin
 ext n,rw[coeff_compose],
 let f := λ (j : ℕ), coeff j (C a) * coeff n (g ^ j),
 change (range n.succ).sum f = coeff n (C a),
 have : f 0 = coeff n (C a) := 
  by {dsimp[f],rw[pow_zero,coeff_zero_C,coeff_n_one,coeff_n_C],
      split_ifs,rw[mul_one],rw[mul_zero]},
 rw[← this],apply sum_eq_single,
 {intros j h_le h_ne,rw[coeff_n_C,if_neg h_ne.symm,zero_mul]},
 {intro h,exfalso,exact h (mem_range_succ.mpr (nat.zero_le n))}
end

lemma X_compose (a : R) (g : power_series R) (hg : coeff 0 g = 0) : compose X g = g := 
begin
 ext n,rw[coeff_compose],
 let f := λ (j : ℕ), coeff j X * coeff n (g ^ j),
 change (range n.succ).sum f = coeff n g,
 have : f 1 = coeff n g := 
  by {dsimp[f],rw[coeff_one_X,pow_one,one_mul]},
 rw[← this],apply sum_eq_single,
 {intros j h_le h_ne,rw[coeff_n_X,if_neg h_ne.symm,zero_mul]},
 {cases n with n,
  {intro h,rw[pow_one,hg,mul_zero]},
  {intro h,exfalso,
   exact h (mem_range_succ.mpr (nat.succ_le_succ (nat.zero_le n))),
  }}
end

end compose
end power_series