import data.nat.prime data.multiset
import data.list_extra data.multiset_extra

namespace nat

lemma list.coprime_prod {n : ℕ} {l : list ℕ} (h : list.all_prop (coprime n) l) : 
 coprime n l.prod := 
begin
 induction l with m l ih,
 {rw[list.prod_nil],exact coprime_one_right n},
 {rw[list.all_prop] at h,rw[list.prod_cons],
  exact coprime.mul_right h.left (ih h.right),
 }
end

lemma multiset.coprime_prod {n : ℕ} {s : multiset ℕ}
 (h : multiset.all_prop (coprime n) s) : coprime n s.prod := 
begin
 rcases s with ⟨l⟩,
 have : quot.mk setoid.r l = (l : multiset ℕ) := rfl, rw[this] at *,
 rw[multiset.all_prop_coe] at h,rw[multiset.coe_prod],
 exact list.coprime_prod h
end

lemma list.coprime_prod_dvd_of_dvd {l : list ℕ} (hc : l.pairwise coprime) 
 {n : ℕ} (hd : list.all_prop (λ p, p ∣ n) l) : l.prod ∣ n := 
begin
 induction l with m l ih,
 {rw[list.prod_nil],exact one_dvd n},
 {rw[list.pairwise_cons] at hc,
  rw[list.all_prop] at hd,rw[list.prod_cons],
  exact coprime.mul_dvd_of_dvd_of_dvd
   (list.coprime_prod (list.all_prop_iff.mpr hc.left)) 
    hd.left (ih hc.right hd.right),
 }
end

lemma multiset.coprime_prod_dvd_of_dvd {s : multiset ℕ} (hc : s.pairwise coprime) 
 {n : ℕ} (hd : multiset.all_prop (λ p, p ∣ n) s) : s.prod ∣ n := 
begin
 rcases s with ⟨l⟩,
 have : quot.mk setoid.r l = (l : multiset ℕ) := rfl, rw[this] at *,
 have : symmetric coprime := λ n m, coprime.symm,
 rw[multiset.pairwise_coe_iff_pairwise this] at hc,
 rw[multiset.all_prop_coe] at hd,
 rw[multiset.coe_prod],
 exact list.coprime_prod_dvd_of_dvd hc hd,
end

lemma list.nodup_prime_coprime 
 {l : list ℕ} (hd : l.nodup) (hp : list.all_prop nat.prime l) : 
  l.pairwise coprime := 
begin
 let hp' := list.all_prop_iff.mp hp,
 apply @list.pairwise.imp_of_mem ℕ ne coprime l _ hd,
 {intros p q hpl hql hpq,exact (coprime_primes (hp' p hpl) (hp' q hql)).mpr hpq,},
end

lemma multiset.nodup_prime_coprime 
 {s : multiset ℕ} (hd : s.nodup) (hp : multiset.all_prop nat.prime s) : 
  s.pairwise coprime := 
begin
 rcases s with ⟨l⟩,
 have : quot.mk setoid.r l = (l : multiset ℕ) := rfl, rw[this] at *,
 rw[multiset.coe_nodup] at hd,
 rw[multiset.all_prop_coe] at hp,
 have : symmetric coprime := λ n m, coprime.symm,
 rw[multiset.pairwise_coe_iff_pairwise this],
 exact list.nodup_prime_coprime hd hp,
end

def padic_valuation (p : ℕ) (n : ℕ) : ℕ := 
  multiset.count p n.factors

def unique_factors (n : ℕ) := (n.factors : multiset ℕ).dedup

lemma mem_unique_factors {n : ℕ} (h : n ≠ 0) (p : ℕ) :
 p ∈ unique_factors n ↔ p.prime ∧ p ∣ n := 
begin
 dsimp[unique_factors],rw[multiset.mem_coe,list.mem_dedup],
 split,
 {intro h0,
  let h1 := ((nat.mem_factors h).mp h0).1,
  let h2 := (nat.mem_factors_iff_dvd h h1).mp h0,
  exact ⟨h1,h2⟩
 },{
  rintro ⟨h1,h2⟩,exact (nat.mem_factors_iff_dvd h h1).mpr h2,
 }
end

lemma unique_factors_coprime (n : ℕ) :
 (unique_factors n).pairwise coprime := 
begin
 by_cases h : n = 0,
 {rw[h], 
  have : unique_factors 0 = 0 := 
   by { dsimp[unique_factors], rw[factors_zero], refl },
   rw[this],apply multiset.pairwise_zero},
 apply multiset.nodup_prime_coprime,
 {apply multiset.nodup_dedup},
 {rw[multiset.all_prop_iff],intros p hp,
  replace hp := multiset.mem_dedup.mp hp,
  rw[multiset.mem_coe] at hp,
  exact ((nat.mem_factors h).mp hp).1,
 }
end

def prime_power_factors (n : ℕ) := 
 (unique_factors n).map (λ p, p ^ (padic_valuation p n))

def prod_factors' (n : ℕ) (h : n ≠ 0) :
 (prime_power_factors n).prod = n := 
begin
 let f : multiset ℕ := n.factors,
 let f₁ := f.dedup,
 let u := λ p, multiset.prod (multiset.repeat p (multiset.count p f)),
 let v := λ p, p ^ (multiset.count p f),
 change (f₁.map v).prod = n,
 have : v = u := by {ext p,dsimp[u,v],rw[multiset.prod_repeat]},
 rw[this],
 let e : f.prod = n := by {rw[multiset.coe_prod],exact nat.prod_factors h},
 rw[← multiset.eq_repeat_count f] at e,
 rw[multiset.prod_bind] at e,
 exact e,
end

def square_free (n : ℕ) : Prop := ∀ k, (k * k) ∣ (n : ℕ) → k = 1

lemma square_free_iff (n : ℕ) : 
 square_free n ↔ ∀ p, nat.prime p → ¬ (p * p ∣ n) := 
begin
 split,
 {intros h p p_prime hp,
  exact nat.prime.ne_one p_prime (h p hp),
 },{
  intros h k hk, by_contradiction hk',
  let p := nat.min_fac k,
  let p_prime := nat.min_fac_prime hk',
  let pp_dvd : p * p ∣ n := 
    dvd_trans (mul_dvd_mul k.min_fac_dvd k.min_fac_dvd) hk,
  exact (h p p_prime pp_dvd).elim
 }
end

def square_free_radical (n : ℕ) : ℕ := 
 (n.factors : multiset ℕ).dedup.prod

lemma square_free_radical_dvd (n : ℕ) : 
 (square_free_radical n) ∣ n := begin
 by_cases hn : n = 0,
 {rw[hn],use 0,rw[mul_zero]},
 {
  let fl := n.factors,
  let fm : multiset ℕ := fl,
  let fs := fm.dedup,
  let ft := fm - fs,
  let hm : fm.prod = n :=
   (multiset.coe_prod fl).trans (nat.prod_factors hn),
  have hl : fs ≤ fm := multiset.dedup_le n.factors,
  have : fm = ft + fs := (tsub_add_cancel_of_le hl).symm,
  rw[this,multiset.prod_add,mul_comm] at hm,
  use ft.prod,exact hm.symm,
 }
end

lemma square_free_radical_primes {n : ℕ} (hn : n ≠ 0) 
 {p : ℕ} (p_prime : nat.prime p) : 
  p ∣ (square_free_radical n) ↔ p ∣ n := 
begin
 split,
 {intro h,exact dvd_trans h (square_free_radical_dvd n)},
 {intro p_dvd_n, 
  let fl := n.factors,
  let fm : multiset ℕ := fl,
  let fs := fm.dedup,
  change p ∣ fs.prod,
  have : p ∈ fm := (nat.mem_factors_iff_dvd hn p_prime).mpr p_dvd_n,
  have : p ∈ fs := multiset.mem_dedup.mpr this,
  rw[← multiset.cons_erase this,multiset.prod_cons], 
  apply dvd_mul_right,
 }
end

lemma square_free_radical_dvd_iff {n : ℕ} (hn : n ≠ 0) (m : ℕ) : 
 (square_free_radical n) ∣ m ↔ ∀ p, nat.prime p → p ∣ n → p ∣ m := begin
split,
{intros h p p_prime p_dvd_n,
 exact dvd_trans ((square_free_radical_primes hn p_prime).mpr p_dvd_n) h,
},{
 intro h,dsimp[square_free_radical],
 apply multiset.coprime_prod_dvd_of_dvd (unique_factors_coprime n),
 rw[multiset.all_prop_iff],intros p hp,
 replace hp := (mem_unique_factors hn p).mp hp,
 exact h p hp.left hp.right,
}
end

lemma dvd_square_free_radical {n : ℕ} (hn : n ≠ 0) :
 ∃ (k : ℕ), n ∣ n.square_free_radical ^ k := 
begin
 let f : multiset ℕ := n.factors,
 let f₁ := f.dedup,
 rcases multiset.le_smul_dedup f with ⟨k,hk⟩,
 use k,change n ∣ f₁.prod ^ k,
 let f₂ := add_monoid.nsmul k f₁, change f ≤ f₂ at hk,
 have : f₂.prod = f₁.prod ^ k := by {
   dsimp[f₂],rw[multiset.prod_nsmul]
 },
 rw[← this],
 have : f.prod = n := by {rw[multiset.coe_prod,nat.prod_factors hn],},
 rw[← this,← tsub_add_cancel_of_le hk,multiset.prod_add],
 apply dvd_mul_left, 
end

end nat