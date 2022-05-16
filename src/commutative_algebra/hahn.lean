import data.real.basic data.real.nnreal
import data.zmod.basic
import ring_theory.hahn_series

namespace infinite_root
noncomputable theory
local attribute [instance, priority 2000] classical.prop_decidable

lemma zmod_cases (a : zmod 2) : a = 0 ∨ a = 1 := 
begin
  fin_cases a, {left, refl}, {right, refl}
end

lemma zmod_nz {a : zmod 2} : a ≠ 0 ↔ a = 1 :=
begin
  split; intro h, 
  { cases (zmod_cases a) with h' h', exact (h h').elim,  exact h' },
  { intro h', rw[h] at h', cases h' }
end

lemma zmod_units {a b : zmod 2} (h : a * b = 1) : a = 1 ∧ b = 1 := 
begin 
  cases zmod_cases a with ha ha;
  cases zmod_cases b with hb hb;
  simp only[ha, hb, zero_mul, one_mul] at h ⊢; cases h; split; refl
end

localized "notation ` ℝ≥0 ` := nnreal" in infinite_root

instance : linear_ordered_cancel_add_comm_monoid ℝ≥0 := {
  add_left_cancel := λ a b c h, by {
    rw[← nnreal.eq_iff] at h ⊢, 
    rw[nnreal.coe_add, nnreal.coe_add] at h,
    exact (add_right_inj _).mp h
  },
  le_of_add_le_add_left := λ a b c h, begin 
    rw[← nnreal.coe_le_coe] at h ⊢,
    rw[nnreal.coe_add, nnreal.coe_add] at h,
    exact le_of_add_le_add_left h
  end,
  .. (by apply_instance : linear_ordered_add_comm_monoid ℝ≥0)
}

lemma midpoint_ineq₀ {a b : ℝ} (h : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b :=
begin
  split; linarith,
end

lemma midpoint_ineq {a b : ℝ≥0} (h : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b :=
begin
  rw[← nnreal.coe_lt_coe] at h,
  have e2 : ((2 : ℝ≥0) : ℝ) = 2 := rfl,
  rw[← nnreal.coe_lt_coe, ← nnreal.coe_lt_coe, nnreal.coe_div, nnreal.coe_add, e2],  
  apply midpoint_ineq₀ h
end

def A := hahn_series ℝ≥0 (zmod 2)

def t_pow (q : ℝ≥0) : A := hahn_series.single q (1 : zmod 2)

lemma coeff_t_pow (q r : ℝ≥0) : (t_pow q).coeff r = if r = q then 1 else 0 := 
  by { dsimp[t_pow],
    exact @hahn_series.single_coeff ℝ≥0 (zmod 2) _ _ q r 1,
   }

lemma coeff_t_pow_self (q : ℝ≥0) : (t_pow q).coeff q = 1 := 
  by { rw[coeff_t_pow, if_pos rfl] }

lemma order_t_pow (q : ℝ≥0) : (t_pow q).order = q := 
  hahn_series.order_single (by { intro h, cases h})

instance : comm_ring A := by { dsimp[A], apply_instance }
instance : is_domain A := by { dsimp[A], apply_instance }

lemma nz_of_coeff_nz {a : A} {q : ℝ≥0} (h : a.coeff q ≠ 0) : a ≠ 0 := 
  λ h', by { rw[h', hahn_series.zero_coeff] at h, exact h rfl }

lemma nz_of_coeff_eq_one {a : A} {q : ℝ≥0} (h : a.coeff q = 1) : a ≠ 0 := 
  λ h', by { rw[h', hahn_series.zero_coeff] at h, cases h }

lemma nz_of_order_nz {a : A} (h : a.order ≠ 0) : a ≠ 0 := 
  λ h', by { rw[h', hahn_series.order_zero] at h, exact h rfl }

lemma nz_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := 
begin
  intro h',
  have := eq_zero_or_eq_zero_of_mul_eq_zero h',
  cases this, exact ha this, exact hb this
end

lemma t_pow_nz (q : ℝ≥0) : t_pow q ≠ 0 := 
  nz_of_coeff_eq_one (coeff_t_pow_self q)

def order' (a : A) : ℝ≥0 := begin
  by_cases h : a = 0, exact 1, exact a.order
end

lemma order'_pos {a : A} : a.coeff 0 = 0 ↔ order' a > 0 := 
begin
  dsimp[order'],
  split_ifs,
  { rw[h, hahn_series.zero_coeff], simp only [gt_iff_lt, zero_lt_one, eq_self_iff_true] },
  { split; intro h',
    { apply zero_lt_iff.mpr, intro h'', 
      have := hahn_series.coeff_order_ne_zero h,
      rw[h''] at this, exact this h'
    }, {
      exact hahn_series.coeff_eq_zero_of_lt_order h'
    }
  }
end

lemma mul_t_pow_coeff_add (a : A) (q r : ℝ≥0) : 
  (a * (t_pow q)).coeff (r + q) = a.coeff r := 
begin
    rw[← mul_one (a.coeff r)],
    change (a * (hahn_series.single _ _)).coeff _ = _,
    exact hahn_series.mul_single_coeff_add,
end

lemma mul_t_pow_coeff (a : A) {q r : ℝ≥0} (h : q ≤ r) :
  (a * (t_pow (r - q))).coeff r = a.coeff q := 
begin
  have := mul_t_pow_coeff_add a (r - q) q,
  rw[add_tsub_cancel_of_le h] at this,
  exact this
end

def res (s : set ℝ≥0) : A →+ A := {
  to_fun := λ (a : hahn_series ℝ≥0 (zmod 2)), 
    ⟨λ (q : ℝ≥0), ite (q ∈ s) (a.coeff q) 0,  
      set.is_pwo.mono a.is_pwo_support (by {
        intros q hq, simp[set.mem] at hq, exact hq.2
      })
    ⟩,
  map_zero' := by { ext q, simp only[], rw[hahn_series.zero_coeff], split_ifs; refl },
  map_add' := λ a b, begin
    ext q, by_cases hq : q ∈ s, 
    { simp only[if_pos hq, hahn_series.add_coeff], },
    { simp only[if_neg hq, hahn_series.add_coeff, zero_add] }
  end 
}

lemma support_res (s : set ℝ≥0) (a : A) : 
  hahn_series.support (res s a) = s ∩ (hahn_series.support a) := 
begin
  ext q,
  change ite (q ∈ s) (a.coeff q) 0 ≠ 0 ↔ q ∈ s ∧ a.coeff q ≠ 0,
  split_ifs with h; simp[h]
end

lemma res_split (s : set ℝ≥0) (a : A) : (res s a) + (res sᶜ a) = a := 
begin
  ext1, ext1 q,
  change (ite (q ∈ s) (a.coeff q) 0) + (ite (¬ (q ∈ s)) (a.coeff q) 0 ) = a.coeff q,
  by_cases hq : q ∈ s,
  { rw[if_pos hq, if_neg (not_not.mpr hq), add_zero] },
  { rw[if_neg hq, if_pos hq, zero_add] }
end

lemma res_eq_self {s : set ℝ≥0} {a : A} : res s a = a ↔ hahn_series.support a ⊆ s := 
begin
  split; intro h,
  { rw[← h, support_res], apply set.inter_subset_left },
  { ext1, ext1 q, dsimp[res], split_ifs with hq, refl, 
    by_contra hq', change 0 ≠ a.coeff q at hq', exact hq (h hq'.symm) }
end

lemma res_eq_zero {s : set ℝ≥0} {a : A} : res s a = 0 ↔ hahn_series.support a ⊆ sᶜ := 
begin
  rw[← hahn_series.support_eq_empty_iff, support_res],
  rw[set.inter_comm, ← set.subset_compl_iff_disjoint]
end

lemma res_res_self (s : set ℝ≥0) (a : A) : res s (res s a) = res s a := 
begin
  rw[res_eq_self, support_res], apply set.inter_subset_left
end

lemma res_res_compl (s : set ℝ≥0) (a : A) : res s (res sᶜ a) = 0 := 
begin
   rw[res_eq_zero, support_res], 
   exact set.inter_subset_left sᶜ (hahn_series.support a)
end

@[irreducible]
def is_lb (q : ℝ≥0) (a : A) := ∀ {r : ℝ≥0}, r < q → a.coeff r = 0

@[irreducible]
def is_slb (q : ℝ≥0) (a : A) := ∀ {r : ℝ≥0}, r ≤ q → a.coeff r = 0

lemma is_lb_def {q : ℝ≥0} {a : A} : is_lb q a ↔ ∀ {r : ℝ≥0}, r < q → a.coeff r = 0 := 
 by { dsimp[is_lb], refl }

lemma is_slb_def {q : ℝ≥0} {a : A} : is_slb q a ↔ ∀ {r : ℝ≥0}, r ≤ q → a.coeff r = 0 := 
 by { dsimp[is_slb], refl }

lemma is_lb_zero (q : ℝ≥0) : is_lb q 0 := 
  by { dsimp[is_lb], intros r hr, refl }

lemma is_lb_alt {q : ℝ≥0} {a : A} : is_lb q a ↔ a = 0 ∨ a.order ≥ q := 
begin
  by_cases hz : a = 0, { rw[hz], simp[is_lb_zero q] },
  rw[is_lb_def],
  split; intro h,
  { right,
    apply le_of_not_gt, intro ho,
    exact (hahn_series.coeff_order_ne_zero hz) (h ho),
  },{
    cases h,
    { rw[h], exact false.elim (hz h) },
    { intros r hr,
      exact hahn_series.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hr h),
    }
  }
end

lemma is_lb_order (a : A) : is_lb a.order a := by {
  apply is_lb_alt.mpr, right, exact le_refl _,
}

lemma is_lb_order' (a : A) : is_lb (order' a) a := begin
  dsimp[order'],
  split_ifs,
  { rw[h], exact is_lb_zero _ },
  { exact is_lb_order a  }
end

lemma is_lb_bot (a : A) : is_lb 0 a := 
  by { dsimp[is_lb], intros r hr, exact (not_le_of_gt hr (zero_le r)).elim }

lemma is_lb_single {q p : ℝ≥0} (hqp : q ≤ p) (u : (zmod 2)): 
  is_lb q (hahn_series.single p u) := 
begin
  dsimp[is_lb],
  intros r hr,
  exact hahn_series.single_coeff_of_ne (ne_of_lt (lt_of_lt_of_le hr hqp))
end

lemma is_lb_t_pow {q p : ℝ≥0} : is_lb q (t_pow p) ↔ q ≤ p := 
begin
  split,
  { intro h, cases is_lb_alt.mp h with h' h', 
     { exfalso, exact t_pow_nz p h' },
     { rw[order_t_pow] at h', exact h' }
  },
  { intro h, exact is_lb_single h 1} 
end

lemma is_lb_neg {q : ℝ≥0} {a : A} (ha : is_lb q a) : is_lb q (- a) := 
begin
  dsimp[is_lb] at ha ⊢,
  intros r hr,
  rw[ha hr, neg_zero]
end

lemma is_lb_add {q : ℝ≥0} {a b : A} (ha : is_lb q a) (hb : is_lb q b) : 
  is_lb q (a + b) := 
begin
  dsimp[is_lb] at ha hb ⊢,
  intros r hr,
  change (a.coeff r) + (b.coeff r) = 0,
  rw[ha hr, hb hr, add_zero]
end

lemma is_lb_mul {p q : ℝ≥0} {a b : A} (ha : is_lb p a) (hb : is_lb q b) :
  is_lb (p + q) (a * b) :=
begin
  dsimp[is_lb] at ha hb ⊢,
  intros r hr,
  by_contra h,
  change r ∈ (a * b).support at h,
  replace h := hahn_series.support_mul_subset_add_support h,
  rcases (set.mem_add.mp h) with ⟨m,n,hm,hn,hmn⟩,
  by_cases hm' : m < p, { exact hm (ha hm') },
  by_cases hn' : n < q, { exact hn (hb hn') },
  replace hm' := le_of_not_gt hm',
  replace hn' := le_of_not_gt hn',
  have := add_le_add hm' hn',
  rw[hmn] at this,
  exact not_le_of_gt hr this
end

lemma is_slb_zero (q : ℝ≥0) : is_slb q 0 := 
  by { dsimp[is_slb], intros r hr, refl }

lemma is_slb_single {q p : ℝ≥0} (hqp : q < p) (u : (zmod 2)): 
  is_slb q (hahn_series.single p u) := 
begin
  dsimp[is_slb],
  intros r hr,
  exact hahn_series.single_coeff_of_ne (ne_of_lt (lt_of_le_of_lt hr hqp))
end

lemma is_slb_alt {q : ℝ≥0} {a : A} : is_slb q a ↔ a = 0 ∨ a.order > q := 
begin
  by_cases hz : a = 0, { rw[hz], simp[is_slb_zero q] },
  rw[is_slb_def],
  split; intro h,
  { right,
    apply lt_of_not_ge, intro ho,
    exact (hahn_series.coeff_order_ne_zero hz) (h ho),
  },{
    cases h,
    { rw[h], exact false.elim (hz h) },
    { intros r hr,
      exact hahn_series.coeff_eq_zero_of_lt_order (lt_of_le_of_lt hr h)
    }
  }
end

lemma is_slb_t_pow {q p : ℝ≥0} : is_slb q (t_pow p) ↔ q < p := 
begin
  split,
  { intro h, cases is_slb_alt.mp h with h' h', 
     { exfalso, exact t_pow_nz p h' },
     { rw[order_t_pow] at h', exact h' }
  },
  { intro h, exact is_slb_single h 1} 
end

lemma is_slb_neg {q : ℝ≥0} {a : A} (ha : is_slb q a) : is_slb q (- a) := 
begin
  dsimp[is_slb] at ha ⊢,
  intros r hr,
  rw[ha hr, neg_zero]
end

lemma is_slb_add {q : ℝ≥0} {a b : A} (ha : is_slb q a) (hb : is_slb q b) : 
  is_slb q (a + b) := 
begin
  dsimp[is_slb] at ha hb ⊢,
  intros r hr,
  change (a.coeff r) + (b.coeff r) = 0,
  rw[ha hr, hb hr, add_zero]
end

lemma is_slb_mul {p q : ℝ≥0} {a b : A} (ha : is_lb p a) (hb : is_slb q b) :
  is_slb (p + q) (a * b) :=
begin
  dsimp[is_lb] at ha,
  dsimp[is_slb] at hb ⊢,
  intros r hr,
  by_contra h,
  change r ∈ (a * b).support at h,
  replace h := hahn_series.support_mul_subset_add_support h,
  rcases (set.mem_add.mp h) with ⟨m,n,hm,hn,hmn⟩,
  by_cases hm' : m < p, { exact hm (ha hm') },
  by_cases hn' : n ≤ q, { exact hn (hb hn') },
  replace hm' := le_of_not_gt hm',
  replace hn' := lt_of_not_ge hn',
  have := add_lt_add_of_le_of_lt hm' hn',
  rw[hmn] at this,
  exact not_lt_of_ge hr this
end

lemma antidiagonal_zero {s t : set ℝ≥0} {hs : s.is_pwo} {ht : t.is_pwo}
 {p : ℝ≥0 × ℝ≥0} 
 (hp : p ∈ finset.add_antidiagonal hs ht 0) : p = ⟨0,0⟩ := 
begin
  rcases p with ⟨p₀,p₁⟩,
  rw[finset.mem_add_antidiagonal] at hp,
  rcases hp with ⟨h,_,_⟩,
  rcases (add_eq_zero_iff.mp h) with ⟨h₀ : p₀ = 0,h₁ : p₁ = 0⟩,
  rw[h₀, h₁]
end

lemma mul_with_lb {a b : A} {p q : ℝ≥0} (ha : is_lb p a) (hb : is_lb q b) :
  (a * b).coeff (p + q) = (a.coeff p) * (b.coeff q) := 
begin 
  have h_ad : ∀ {u : ℝ≥0 × ℝ≥0}, 
    u ∈ finset.add_antidiagonal a.is_pwo_support b.is_pwo_support (p + q)
     → u = ⟨p,q⟩ := λ u hu,
  begin
    rcases u with ⟨p',q'⟩,
    rw[finset.mem_add_antidiagonal] at hu,
    rcases hu with ⟨hpq : p' + q' = p + q, hp_nz : a.coeff p' ≠ 0, hq_nz : b.coeff q' ≠ 0⟩,
    rw[is_lb_def] at ha hb,
    have hp_ge : p' ≥ p := le_of_not_gt (λ h, hp_nz (ha h)),
    have hq_ge : q' ≥ q := le_of_not_gt (λ h, hq_nz (hb h)),
    have hp_le : ¬ (p' > p) := λ h, 
    begin
      have := add_lt_add_of_lt_of_le h hq_ge,
      rw[hpq] at this, exact lt_irrefl (p + q) this
    end,
    have hq_le : ¬ (q' > q) := λ h, 
    begin
      have := add_lt_add_of_le_of_lt hp_ge h,
      rw[hpq] at this, exact lt_irrefl (p + q) this
    end,
    rw[le_antisymm hp_ge (le_of_not_gt hp_le)],
    rw[le_antisymm hq_ge (le_of_not_gt hq_le)]
  end,
  rw[hahn_series.mul_coeff],
  apply finset.sum_eq_single (⟨p,q⟩ : ℝ≥0 × ℝ≥0),
  { intros pq' hpq' hne, exfalso, exact hne (h_ad hpq') },
  { contrapose, 
    rintro (hab : (a.coeff p) * (b.coeff q) ≠ 0) hpq,
    by_cases ha' : a.coeff p = 0, { rw[ha', zero_mul] at hab, exact hab rfl},
    by_cases hb' : b.coeff q = 0, { rw[hb', mul_zero] at hab, exact hab rfl},
    change p ∈ a.support at ha',
    change q ∈ b.support at hb',
    apply hpq, apply finset.mem_add_antidiagonal.mpr,
    exact ⟨rfl, ha', hb'⟩
  }
end

def ev₀ : A →+* (zmod 2) := {
  to_fun := λ a, a.coeff 0,
  map_zero' := rfl,
  map_one' := by {
   change (hahn_series.single _ _).coeff _ = _, 
   rw[hahn_series.single_coeff_same]
  },
  map_add' := λ a b, by { refl },
  map_mul' := λ a b, by {
    have := mul_with_lb (is_lb_bot a) (is_lb_bot b),
    rw[zero_add] at this, exact this
  }
}

lemma powers_support
  (x : A) : (⋃ n : ℕ, (x ^ n).support).is_pwo :=
begin
  apply (x.is_wf_support.is_pwo.add_submonoid_closure (λ g hg, _)).mono _,
  { exact zero_le g  },
  refine set.Union_subset (λ n, _),
  induction n with n ih;
  intros g hn,
  { simp only [exists_prop, and_true, set.mem_singleton_iff, set.set_of_eq_eq_singleton,
      hahn_series.mem_support, ite_eq_right_iff, ne.def, not_false_iff, one_ne_zero,
      pow_zero, not_forall, hahn_series.one_coeff] at hn,
    rw [hn, set_like.mem_coe],
    exact add_submonoid.zero_mem _ },
  { obtain ⟨i, j, hi, hj, rfl⟩ := hahn_series.support_mul_subset_add_support hn,
    exact set_like.mem_coe.2 (add_submonoid.add_mem _ (add_submonoid.subset_closure hi) (ih hj)) }
end

noncomputable def powers_family {x : A} (hx : x.coeff 0 = 0) :
  hahn_series.summable_family ℝ≥0 (zmod 2) ℕ :=
{ to_fun := λ n, x ^ n,
  is_pwo_Union_support' := powers_support x,
  finite_co_support' := λ g, begin
    have hx' := order'_pos.mp hx,
    have hpwo := (powers_support x),
    by_cases hg : g ∈ ⋃ n : ℕ, {g | (x ^ n).coeff g ≠ 0 },
    swap, { exact set.finite_empty.subset (λ n hn, hg (set.mem_Union.2 ⟨n, hn⟩)) },
    apply hpwo.is_wf.induction hg,
    intros y ys hy,
    refine ((((finset.add_antidiagonal x.is_pwo_support hpwo y).finite_to_set.bUnion (λ ij hij,
      hy ij.snd _ _)).image nat.succ).union (set.finite_singleton 0)).subset _,
    { exact (finset.mem_add_antidiagonal.1 (finset.mem_coe.1 hij)).2.2 },
    { obtain ⟨rfl, hi, hj⟩ := finset.mem_add_antidiagonal.1 (finset.mem_coe.1 hij),
      rw [← zero_add ij.snd, ← add_assoc, add_zero],
      apply add_lt_add_right,
      change x.coeff ij.1 ≠ 0 at hi,
      apply lt_of_not_ge, intro hi',
      exact hi (is_lb_def.mp (is_lb_order' x) (lt_of_le_of_lt hi' hx'))
    },
    { intros n hn,
      cases n,
      { exact set.mem_union_right _ (set.mem_singleton 0) },
      { obtain ⟨i, j, hi, hj, rfl⟩ := hahn_series.support_mul_subset_add_support hn,
        refine set.mem_union_left _ ⟨n, set.mem_Union.2 ⟨⟨i, j⟩, set.mem_Union.2 ⟨_, hj⟩⟩, rfl⟩,
        simp only [true_and, set.mem_Union, finset.mem_add_antidiagonal, finset.mem_coe, eq_self_iff_true,
          ne.def, hahn_series.mem_support, set.mem_set_of_eq],
        exact ⟨hi, ⟨n, hj⟩⟩ } }
  end }

lemma powers_succ {x : hahn_series ℝ≥0 (zmod 2)} (hx : x.coeff 0 = 0) :
  (x • (powers_family hx)).emb_domain ⟨nat.succ, nat.succ_injective⟩ =
    (powers_family hx) - hahn_series.summable_family.of_finsupp (finsupp.single 0 1) :=
begin
  apply hahn_series.summable_family.ext (λ n, _),
  cases n,
  { have : (powers_family hx) 0 = 1 := pow_zero x,
    rw [hahn_series.summable_family.emb_domain_notin_range, 
        hahn_series.summable_family.sub_apply, this, 
        hahn_series.summable_family.coe_of_finsupp,
        finsupp.single_eq_same, sub_self],
    rw [set.mem_range, not_exists],
    exact nat.succ_ne_zero },
  { refine eq.trans (hahn_series.summable_family.emb_domain_image _ ⟨nat.succ, nat.succ_injective⟩) _,
    have : ∀ (n : ℕ), powers_family hx n = x ^ n := λ n, rfl,
    simp only [pow_succ, this, hahn_series.summable_family.coe_sub, 
               hahn_series.summable_family.smul_apply, hahn_series.summable_family.coe_of_finsupp, pi.sub_apply],
    rw [finsupp.single_eq_of_ne (n.succ_ne_zero).symm, sub_zero] }
end

lemma unit_aux {x : hahn_series ℝ≥0 (zmod 2)} (hx : x.coeff 0 = 0) :
 (1 - x) * (powers_family hx).hsum = 1 := 
begin
  rw[← hahn_series.summable_family.hsum_smul,
    sub_smul, one_smul, hahn_series.summable_family.hsum_sub],
  rw[← hahn_series.summable_family.hsum_emb_domain 
        (x • (powers_family hx)) ⟨nat.succ, nat.succ_injective⟩],
  rw[powers_succ hx, hahn_series.summable_family.hsum_sub,
     hahn_series.summable_family.hsum_of_finsupp,
     finsupp.sum_single_index, sub_sub_cancel];
  rw[id.def],
end

lemma unit_aux' {a : A} (ha : a.coeff 0 ≠ 0) : (1 - a).coeff 0 = 0 := by {
 rw[sub_eq_add_neg, hahn_series.add_coeff, hahn_series.neg_coeff, ← sub_eq_add_neg,
    hahn_series.one_coeff, if_pos rfl, zmod_nz.mp ha, sub_self]
}

def to_unit {a : A} (ha : a.coeff 0 ≠ 0) : units A := 
 units.mk_of_mul_eq_one a (powers_family (unit_aux' ha)).hsum
  (by {
    have eq := unit_aux (unit_aux' ha),
    rw[sub_sub_cancel] at eq,
    exact eq
  })

lemma coe_to_unit {a : A} (ha : a.coeff 0 ≠ 0) : ((to_unit ha) : A) = a := rfl

def hinv {a : A} (ha : a.coeff 0 ≠ 0) : A := ((to_unit ha)⁻¹ : units A)

lemma mul_hinv {a : A} (ha : a.coeff 0 ≠ 0) : a * (hinv ha) = 1 := 
begin
  have := units.mul_inv (to_unit ha),
  rw[coe_to_unit] at this,
  exact this
end

lemma hinv_mul {a : A} (ha : a.coeff 0 ≠ 0) : (hinv ha) * a = 1 := 
  by { rw[mul_comm, mul_hinv] }

def left_shift (a : A) (q : ℝ≥0) : A := {
  coeff := λ r, a.coeff (q + r),
  is_pwo_support' := λ (f : ℕ → ℝ≥0) hf, begin
    let g : ℕ → ℝ≥0 := λ n, q + f n,
    have hg : set.range g ⊆ a.support := λ r hr, by { 
      rcases set.mem_range.mp hr with ⟨k, hk : q + f k = r⟩,
      rw[← hk],
      exact hf (set.mem_range_self k)
    },
    rcases a.is_pwo_support g hg with ⟨m,n,hmn,hgmn : q + f m ≤ q + f n⟩,
    exact ⟨m, n, hmn, le_of_add_le_add_left hgmn⟩
  end
}

lemma coeff_left_shift (a : A) (q r : ℝ≥0) : 
  (left_shift a q).coeff r = a.coeff (q + r) := rfl

lemma left_shift_zero (a : A) : left_shift a 0 = a := 
  by { ext q, rw[coeff_left_shift, zero_add]  }

lemma left_shift_add (a : A) (q r : ℝ≥0): left_shift a (q + r) = left_shift (left_shift a q) r := 
  by { ext s, repeat {rw[coeff_left_shift]}, rw[add_assoc] }

lemma mul_left_shift {a : A} {q : ℝ≥0} (ha : is_lb q a) : (left_shift a q) * (t_pow q) = a :=
begin
  ext1, ext1 r,
  by_cases hr : r < q,
  { have ha' := is_lb_mul (is_lb_bot (left_shift a q)) (is_lb_t_pow.mpr (le_refl q)) ,
    rw[is_lb_def, zero_add] at ha',
    rw[is_lb_def] at ha, rw[ha hr, ha' hr]
  } , {
    replace hr := add_tsub_cancel_of_le (le_of_not_gt hr),
    rw[← hr, add_comm q, mul_t_pow_coeff_add, ← add_comm q, coeff_left_shift]
  }
end

lemma left_shift_mul (a : A) (q : ℝ≥0) : left_shift (a * (t_pow q)) q = a := 
begin
  ext1, ext1 r,
  rw[coeff_left_shift, add_comm, mul_t_pow_coeff_add]
end

lemma t_pow_factor {a : A} (ha : a ≠ 0) : (left_shift a a.order) * (t_pow a.order) = a := 
 mul_left_shift (is_lb_order a)

lemma left_shift_unit_aux {a : A} (ha : a ≠ 0) : (left_shift a a.order).coeff 0 ≠ 0 :=
 by {
    rw[coeff_left_shift, add_zero],    
    exact hahn_series.coeff_order_ne_zero ha
  }

def hdiv {a b : A} (ha : a ≠ 0) (hb : is_lb a.order b) : A :=
  (left_shift b a.order) * (hinv (left_shift_unit_aux ha))

def hdiv' {a b : A} (ha : a ≠ 0) (hb : a.order ≤ b.order) : A := 
  hdiv ha (is_lb_alt.mpr (or.inr hb))

lemma mul_hdiv_cancel {a b : A} (ha : a ≠ 0) (hb : is_lb a.order b) : 
  (hdiv ha hb) * a = b := 
begin
  let q := a.order,
  let a' := left_shift a q,
  let b' := left_shift b q,
  have ha' : a' * (t_pow q) = a := mul_left_shift (is_lb_order a),
  have hb' : b' * (t_pow q) = b := mul_left_shift hb,
  let a'' := hinv (left_shift_unit_aux ha),
  have hu : a'' * a' = 1 := hinv_mul (left_shift_unit_aux ha),
  change b' * a'' * a = b,
  rw[← ha', mul_assoc, ← mul_assoc a'', hu, one_mul, hb']
end

lemma mul_hdiv_cancel' {a b : A} (ha : a ≠ 0) (hb : a.order ≤ b.order) :
  (hdiv' ha hb) * a = b := mul_hdiv_cancel ha (is_lb_alt.mpr (or.inr hb))

def Ic (q : ℝ≥0) : ideal A := {
 carrier := { a : A | is_lb q a },
 zero_mem' := is_lb_zero q,
 add_mem' := λ a b ha hb, is_lb_add ha hb,
 smul_mem' := λ a b hb, begin 
   have := is_lb_mul (is_lb_bot a) hb,
   rw[zero_add] at this,
   exact this
 end
}

def Io (q : ℝ≥0) : ideal A := {
 carrier := { a : A | is_slb q a },
 zero_mem' := is_slb_zero q,
 add_mem' := λ a b ha hb, is_slb_add ha hb,
 smul_mem' := λ a b hb, begin 
   have := is_slb_mul (is_lb_bot a) hb,
   rw[zero_add] at this,
   exact this
 end
}

lemma Ic_t_pow_mem {q r : ℝ≥0} : t_pow q ∈ Ic r ↔ q ≥ r := is_lb_t_pow

lemma Io_t_pow_mem {q r : ℝ≥0} : t_pow q ∈ Io r ↔ q > r := is_slb_t_pow

lemma Ic_nz (q : ℝ≥0) : Ic q ≠ 0 := 
begin 
  intro h,
  have h' : t_pow q ∈ Ic q := is_lb_t_pow.mpr (le_refl q),
  rw[h] at h',
  exact t_pow_nz q h'
end

lemma Io_nz (q : ℝ≥0) : Io q ≠ 0 := 
begin 
  intro h,
  have h' : t_pow (q + 1) ∈ Io q := is_slb_t_pow.mpr (lt_add_one q),
  rw[h] at h',
  exact t_pow_nz (q + 1) h'
end

lemma le_Ic_Ic (q r : ℝ≥0) : Ic q ≤ Ic r ↔ r ≤ q := 
begin
  split; intro h,
  { apply le_of_not_gt, intro h',
    have := is_lb_def.mp (h (is_lb_t_pow.mpr (le_refl q))) h',
    rw[coeff_t_pow_self] at this,
    cases this
  }, {
    intros a ha,
    change is_lb r a,
    change is_lb q a at ha,
    rw[is_lb_def] at ha ⊢,
    intros t ht,
    exact ha (lt_of_lt_of_le ht h)
  }
end

lemma le_Ic_Io (q r : ℝ≥0) : Ic q ≤ Io r ↔ r < q := 
begin
  split; intro h,
  { apply lt_of_not_ge, intro h',
    have := is_slb_def.mp (h (is_lb_t_pow.mpr (le_refl q))) h',
    rw[coeff_t_pow_self] at this,
    cases this
  }, {
    intros a ha,
    change is_slb r a,
    change is_lb q a at ha,
    rw[is_lb_def] at ha,
    rw[is_slb_def],
    intros t ht,
    exact ha (lt_of_le_of_lt ht h)
  }
end

lemma le_Io_Ic (q r : ℝ≥0) : Io q ≤ Ic r ↔ r ≤ q := 
begin
  split; intro h,
  { apply le_of_not_gt, intro h',
    let s := (q + r) / 2,
    have h'' : q < s ∧ s < r := midpoint_ineq h',
    have := is_lb_def.mp (h (is_slb_t_pow.mpr h''.1)) h''.2,
    rw[coeff_t_pow_self] at this,
    cases this
  }, {
    intros a ha,
    change is_lb r a,
    change is_slb q a at ha,
    rw[is_slb_def] at ha,
    rw[is_lb_def],
    intros t ht,
    exact ha (le_of_lt (lt_of_lt_of_le ht h))
  }
end

lemma le_Io_Io (q r : ℝ≥0) : Io q ≤ Io r ↔ r ≤ q := 
begin
  split; intro h,
  { apply le_of_not_gt, intro h',
    let s := (q + r) / 2,
    have h'' : q < s ∧ s < r := midpoint_ineq h',
    have := is_slb_def.mp (h (is_slb_t_pow.mpr h''.1)) (le_of_lt h''.2),
    rw[coeff_t_pow_self] at this,
    cases this
  }, {
    intros a ha,
    change is_slb r a,
    change is_slb q a at ha,
    rw[is_slb_def] at ha ⊢,
    intros t ht,
    exact ha (le_trans ht h)
  }
end

def ideal_support (I : ideal A) : set ℝ≥0 := 
  { q | ∃ (a : A), (a ∈ I) ∧ (a.coeff q ≠ 0) }

lemma ideal_support_alt (I : ideal A) : 
  ideal_support I = { q | ∃ (a : A), a ∈ I ∧ a ≠ 0 ∧ a.order = q } := 
begin
  ext q, dsimp[ideal_support, set.mem],
  split; rintro ⟨a,a_in_I,ha⟩,
  { let r := a.order,
    have r_def : r = a.order := rfl,
    have hr : r ≤ q := le_of_not_gt (λ h, ha (hahn_series.coeff_eq_zero_of_lt_order h)),
    let b := a * (t_pow (q - r)),
    have a_nz : a ≠ 0 := nz_of_coeff_nz ha,
    have t_nz : t_pow (q - r) ≠ 0 := t_pow_nz (q - r),
    have b_nz : b ≠ 0 := nz_mul a_nz t_nz,
    have b_in_I : b ∈ I := ideal.mul_mem_right (t_pow (q - r)) I a_in_I, 
    have hbo : b.order = q := 
    begin 
      dsimp[b],
      rw[hahn_series.order_mul a_nz t_nz],
      rw[order_t_pow, ← r_def, add_tsub_cancel_iff_le.mpr hr]
    end,
    exact ⟨b,b_in_I,b_nz,hbo⟩ 
  },
  { use a, rw[← ha.2], exact ⟨a_in_I, hahn_series.coeff_order_ne_zero ha.1⟩ }
end

lemma ideal_support_zero : ideal_support 0 = ∅ :=
begin
  rw[set.eq_empty_iff_forall_not_mem],
  rintros q ⟨a,az,anz⟩,
  exact nz_of_coeff_nz anz az
end

lemma ideal_support_empty {I : ideal A} : ideal_support I = ∅ ↔ I = 0 := 
begin
  rw[set.eq_empty_iff_forall_not_mem],
  split,
  { intro h, ext a, split,
    { intro a_in_I, change a = 0, ext1, ext1 q, rw[hahn_series.zero_coeff],
      by_contra h',
      exact h q ⟨a, a_in_I, h'⟩
    }, {
      rintro h' : a = 0, rw[h'], exact I.zero_mem
    }
  },{
    rintro h q ⟨a, a_in_I, h'⟩, rw[h] at a_in_I, 
    exact nz_of_coeff_nz h' a_in_I
  }
end

lemma ideal_support_nonempty {I : ideal A} : (ideal_support I).nonempty ↔ I ≠ 0 := 
begin
  change _ ↔ ¬ (I = 0),
  rw[← ideal_support_empty, ← set.ne_empty_iff_nonempty]
end

lemma ideal_support_Ic (q : ℝ≥0) : ideal_support (Ic q) = set.Ici q :=
begin
  ext r, rw[set.mem_Ici],
  split,
  { rintro ⟨a,ha : is_lb q a, anz⟩, 
    apply le_of_not_gt, intro hqr, 
    exact anz (is_lb_def.mp ha hqr) },
  { intro hqr, use t_pow r, split,
    { exact is_lb_t_pow.mpr hqr },
    { rw[coeff_t_pow_self], rintro ⟨_⟩ }
  }
end

lemma ideal_support_Io (q : ℝ≥0) : ideal_support (Io q) = set.Ioi q :=
begin
  ext r, rw[set.mem_Ioi],
  split,
  { rintro ⟨a,ha : is_slb q a, anz⟩, 
    apply lt_of_not_ge, intro hqr, 
    exact anz (is_slb_def.mp ha hqr) },
  { intro hqr, use t_pow r, split,
    { exact is_slb_t_pow.mpr hqr },
    { rw[coeff_t_pow_self], rintro ⟨_⟩ }
  }
end

lemma ideal_support_bdd_below (I : ideal A) : bdd_below (ideal_support I) := 
  ⟨0, λ q hq, zero_le q⟩

lemma ideal_support_upwards {I : ideal A} {q r : ℝ≥0} 
  (hq : q ∈ ideal_support I) (hqr : q ≤ r) : r ∈ ideal_support I :=
begin 
  rcases hq with ⟨a,a_in_I,a_nz⟩,
  let b := (t_pow (r - q)) * a,
  have b_in_I : b ∈ I := I.mul_mem_left _ a_in_I,
  have b_nz : b.coeff r ≠ 0 := by {
    change ((t_pow (r - q)) * a).coeff r ≠ 0,
    rw[mul_comm, mul_t_pow_coeff a hqr],
    exact a_nz
  },
  exact ⟨b,b_in_I,b_nz⟩
end

lemma ideal_contains_Ic {I : ideal A} {a : A} (a_nz : a ≠ 0) (a_in_I : a ∈ I) :
  Ic a.order ≤ I :=
begin
  rintro b (hb : is_lb a.order b),
  rw [← mul_hdiv_cancel a_nz hb],
  exact I.mul_mem_left _ a_in_I
end

lemma ideal_contained_in_Io {I : ideal A} {a : A} (h : a ∉ I) : 
  I ≤ Io a.order :=
begin
  intros b b_in_I,
  change is_slb a.order b,
  rw[is_slb_def],
  intros q hq,
  by_contra hb',
  have b_nz : b ≠ 0 := λ bz, by { rw[bz, hahn_series.zero_coeff] at hb', exact hb' rfl },
  have hbq : b.order ≤ q := by {
    apply le_of_not_gt, intro hb'', 
    exact hb' (hahn_series.coeff_eq_zero_of_lt_order hb'')
  },
  have hba : is_lb b.order a := by { rw[is_lb_def], intros r hr, 
     exact hahn_series.coeff_eq_zero_of_lt_order (lt_of_lt_of_le (lt_of_lt_of_le hr hbq) hq),
  },
  have := I.mul_mem_left (hdiv b_nz hba) b_in_I,
  rw[mul_hdiv_cancel b_nz hba] at this,
  exact h this
end

def ideal_order (I : ideal A) := Inf (ideal_support I)

def I : set ℝ → ℝ := Inf

example : I ∅ = 0 := begin
  dsimp[I, Inf, Sup],
  split_ifs with h,
  rcases h with ⟨⟨x,⟨h⟩⟩,_⟩,
  exact neg_zero
end

lemma ideal_order_zero : ideal_order 0 = 0 := 
  by { change Inf (ideal_support 0) = 0, rw[ideal_support_zero], 
    simp only [set.image_empty, real.Inf_empty, subset_Inf_def],
    split_ifs; refl
  }

lemma ideal_order_Ic (q : ℝ≥0) : ideal_order (Ic q) = q := 
begin
  change Inf (ideal_support (Ic q)) = q,
  rw[ideal_support_Ic], apply cInf_Ici
end

lemma ideal_order_Io (q : ℝ≥0) : ideal_order (Io q) = q := 
begin
  change Inf (ideal_support (Io q)) = q,
  rw[ideal_support_Io], apply cInf_Ioi
end

lemma ideal_le_Ic_order (I : ideal A) : I ≤ Ic (ideal_order I) := 
begin
  intros a a_in_I,
  apply is_lb_def.mpr, intros r hr,
  by_contra ha, apply not_le_of_gt hr,
  have hr' : r ∈ ideal_support I := ⟨a, a_in_I, ha⟩,
  exact cInf_le ⟨(0 : ℝ≥0),(λ s hs, zero_le s)⟩ hr'
end

lemma ideal_nonzero {I : ideal A} : I ≠ 0 ↔ ∃ (a : A), a ≠ 0 ∧ a ∈ I :=
begin
  rw[← not_iff_not, not_not, not_exists],
  split,
  { rintro hI a ⟨a_nz, a_in_I⟩, rw[hI] at a_in_I, exact a_nz a_in_I },
  { intro h, ext a, have ha := h a, rw[and_comm, not_and, not_not] at ha,
    split, 
    { exact ha },
    { rintro hz : a = 0, rw[hz], exact I.zero_mem }
  }
end

lemma ideal_ge_Io_order {I : ideal A} (h : I ≠ 0) : Io (ideal_order I) ≤ I := 
begin
  let q := ideal_order I,
  rintro b (hb : is_slb q b),
  rw[is_slb_alt] at hb,
  by_cases hb' : b = 0, { rw[hb'], exact I.zero_mem },
  cases hb, { exact false.elim (hb' hb) },
  let r := b.order, change q < r at hb,
  have q_is_glb : is_glb (ideal_support I) q :=
   is_glb_cInf (ideal_support_nonempty.mpr h) (ideal_support_bdd_below I),
  have : ∃ (s : ℝ≥0), s < r ∧ s ∈ (ideal_support I) := 
  begin
    by_contra hr', 
    have hr' : r ∈ lower_bounds (ideal_support I) := begin
      intros s hs, apply le_of_not_gt, intro hs', exact hr' ⟨s, hs', hs⟩
    end,
    exact not_lt_of_ge (q_is_glb.2 hr') hb
  end,
  rw[ideal_support_alt] at this,
  rcases this with ⟨s,⟨hsr,a,a_in_I,a_nz,a_ord⟩⟩,
  rw[← a_ord] at hsr,
  rw[← mul_hdiv_cancel' a_nz (le_of_lt hsr)],
  exact ideal.mul_mem_left I _ a_in_I
end

inductive ideal_spec 
| zero : ideal_spec
| Ic : ℝ≥0 → ideal_spec
| Io : ℝ≥0 → ideal_spec

def ideal_spec.to_ideal : ideal_spec → (ideal A) 
| ideal_spec.zero := 0
| (ideal_spec.Ic q) := Ic q
| (ideal_spec.Io q) := Io q

def ideal_spec.of_ideal (I : ideal A) : ideal_spec := 
begin
  by_cases h : I = 0,
  exact ideal_spec.zero,
  by_cases h' : t_pow (ideal_order I) ∈ I,
  exact ideal_spec.Ic (ideal_order I),
  exact ideal_spec.Io (ideal_order I)
end

def ideal_spec.support : ideal_spec → set ℝ≥0 
| ideal_spec.zero := ∅
| (ideal_spec.Ic q) := set.Ici q
| (ideal_spec.Io q) := set.Ioi q

def ideal_spec.equiv : ideal_spec ≃ ideal A := {
  to_fun := ideal_spec.to_ideal,
  inv_fun := ideal_spec.of_ideal,
  left_inv := λ x, begin 
    cases x with q q; dsimp[ideal_spec.to_ideal, ideal_spec.of_ideal],
    { rw[if_pos rfl] },
    { have : Ic q ≠ ⊥ := Ic_nz q, rw[if_neg this, ideal_order_Ic],
      rw[Ic_t_pow_mem,  if_pos (le_refl q)] },
    { have : Io q ≠ ⊥ := Io_nz q, rw[if_neg this, ideal_order_Io],
      rw[Io_t_pow_mem, if_neg (lt_irrefl q)] }
  end,
  right_inv := λ I, begin
    dsimp[ideal_spec.of_ideal],
    split_ifs with hz hb,
    { rw[hz], refl },
    { dsimp[ideal_spec.to_ideal],
      let q := ideal_order I, change t_pow q ∈ I at hb, change Ic q = I,
      have h_ge : Ic q ≥ I := ideal_le_Ic_order I,
      have h_le : Ic q ≤ I := λ a ha, 
      begin
        rw[← order_t_pow q] at ha,
        rw[← mul_hdiv_cancel (t_pow_nz q) ha],
        exact ideal.mul_mem_left I _ hb
      end,
      exact le_antisymm h_le h_ge
    },{
      dsimp[ideal_spec.to_ideal],
      let q := ideal_order I, change t_pow q ∉ I at hb, change Io q = I,
      have h_le : Io q ≤ I := ideal_ge_Io_order hz,
      have h_ge : Io q ≥ I := λ a ha, 
      begin
        change is_slb q a, rw[is_slb_alt],
        by_cases az : a = 0, { left, exact az },
        right, apply lt_of_not_ge, intro ha', apply hb,
        rw[← order_t_pow q] at ha',
        rw[← mul_hdiv_cancel' az ha'],
        exact ideal.mul_mem_left I _ ha
      end,
      exact le_antisymm h_le h_ge
    }
  end
}

lemma ideal_spec.to_ideal_support (J : ideal_spec) : ideal_support J.to_ideal = J.support :=
begin
  cases J with q q,
  { exact ideal_support_zero },
  { exact ideal_support_Ic q },
  { exact ideal_support_Io q }
end

lemma ideal_spec.mem_iff_support {J : ideal_spec} {a : A} : 
  a ∈ J.to_ideal ↔ hahn_series.support a ⊆ J.support := 
begin
  split,
  { intro ha, rw[← J.to_ideal_support], rintros q (hq : a.coeff q ≠ 0),
    exact ⟨a, ha, hq⟩ },
  { cases J with q q; 
    dsimp[ideal_spec.support, ideal_spec.to_ideal]; 
    intro ha,
    { rw[set.subset_empty_iff, hahn_series.support_eq_empty_iff] at ha,
      rw[ha], apply ideal.zero_mem },
    { change is_lb q a, rw[is_lb_def], intros r hrq, 
      by_contra har, exact not_lt_of_ge (ha har) hrq },
    { change is_slb q a, rw[is_slb_def], intros r hrq, 
      by_contra har, exact not_le_of_gt (ha har) hrq }
  }
end

def ideal_spec.section (J : ideal_spec) : add_subgroup A := {
  carrier := { a : A | hahn_series.support a ⊆ (J.support)ᶜ },
  zero_mem' := by {
    dsimp[set.mem], rw[hahn_series.support_zero], exact set.empty_subset _
  },
  add_mem' := λ a b ha hb, by {
    dsimp[set.mem] at ha hb ⊢,
    exact set.subset.trans hahn_series.support_add_subset (set.union_subset ha hb)
  },
  neg_mem' := λ a ha, by {
    dsimp[set.mem] at ha ⊢,
    rw[hahn_series.support_neg], exact ha
  }
}

lemma ideal_spec.mem_section {J : ideal_spec} {a : A} : 
  a ∈ J.section ↔ hahn_series.support a ⊆ J.supportᶜ := by { refl }

lemma ideal_section_prop (J : ideal_spec) : J.to_ideal × J.section ≃ A := {
  to_fun := λ a, a.1 + a.2,
  inv_fun := λ a, ⟨⟨res J.support a,
                    by { apply ideal_spec.mem_iff_support.mpr, 
                         rw[support_res], apply set.inter_subset_left}⟩,
                   ⟨res J.supportᶜ a,
                    by { rw[ideal_spec.mem_section, support_res], 
                         exact set.inter_subset_left J.supportᶜ (hahn_series.support a) }⟩⟩,
  left_inv := begin 
    rintro ⟨⟨b,hb⟩,⟨c,hc⟩⟩,
    have hb₀ : res J.support b = b := res_eq_self.mpr (ideal_spec.mem_iff_support.mp hb),
    have hb₁ : res J.supportᶜ b = 0 := by {
      rw[res_eq_zero, compl_compl, ← ideal_spec.mem_iff_support], exact hb,
    },
    have hc₀ : res J.support c = 0 := res_eq_zero.mpr hc,
    have hc₁ : res J.supportᶜ c = c := by {
      rw[res_eq_self], exact hc,
    },
    ext1; simp only[(res _).map_add]; ext1, 
    { change (res J.support b) + (res J.support c) = b, 
      rw[hb₀, hc₀, add_zero]  },
    { change (res J.supportᶜ b) + (res J.supportᶜ c) = c,
      rw[hb₁, hc₁, zero_add] } 
  end,
  right_inv := λ a, res_split J.support a
}

def F (n : ℕ) := (fin n) → A
instance (n : ℕ) : add_comm_group (F n) := by { dsimp[F], apply_instance }
instance (n : ℕ) : module A (F n) := by { dsimp[F], apply_instance }

def submodule_classify_step (n : ℕ) (J : fin n.succ → ideal_spec) 
 (hJ : ∀ (i : fin n), (J i.cast_succ).to_ideal ≤ (J i.succ).to_ideal)
 (M : submodule A (F n.succ))
 (hM₀ : ∀ (u : F n.succ) (i : fin n.succ), u ∈ M → u i ∈ (J i).to_ideal)
 (hM₁ : ∀ (u : F n.succ), (∀ (i : fin n), u i ∈ (J i).to_ideal) → u ⟨n,n.lt_succ_self⟩ = 0 → u ∈ M)
 (hM₂ : ∀ (a : A), a ∈ (J ⟨n,n.lt_succ_self⟩).to_ideal → ∃ (u : F n.succ), u ∈ M ∧ u ⟨n,n.lt_succ_self⟩ = a) :
 ∃ u : F n.succ, u ⟨n,n.lt_succ_self⟩ = 1 ∧ (∀ a : A, a • u ∈ M ↔ a ∈ (J ⟨n,n.lt_succ_self⟩).to_ideal) :=
begin
  let n' : fin n.succ := ⟨n, n.lt_succ_self⟩,
  have hJ' : ∀ (i j : ℕ) (hij : i ≤ j) (hj : j < n.succ), 
    (J ⟨i, lt_of_le_of_lt hij hj⟩).to_ideal ≤ (J ⟨j, hj⟩).to_ideal := 
  begin
    intros i j,
    induction j with j ih; intros hij hj,
    { rcases nat.eq_zero_of_le_zero hij with rfl, 
      exact le_refl (J ⟨0,_⟩).to_ideal },
    { by_cases hij' : i = j.succ, 
      { have : (⟨i, lt_of_le_of_lt hij hj⟩ : fin n.succ) = ⟨j.succ,hj⟩ := 
          by { ext, exact hij' },
        rw[this], exact le_refl _,
      },{
        have hij'' : i ≤ j := nat.lt_succ_iff.mp (lt_of_le_of_ne hij hij'),
        have hj' : j < n.succ := lt_trans j.lt_succ_self hj,
        have hj'' : j < n := nat.succ_lt_succ_iff.mp hj,
        exact le_trans (ih hij'' hj') (hJ ⟨j,hj''⟩)
      }
    }
  end,
  have hM₃ : ∀ (u : F n.succ), u ∈ M → u n' ∈ (J n').to_ideal := λ u h, hM₀ u n' h,
  have hJ'' : ∀ (i : fin n.succ), (J i).to_ideal ≤ (J n').to_ideal := 
    by { rintro ⟨i, hi⟩, exact hJ' i n (nat.lt_succ_iff.mp hi) n.lt_succ_self, },
  cases (J n') with q q,
  { /- Case J n = 0 -/ 
    let u : (fin n.succ) → A := λ i, ite (i = n') 1 0,
    have hu : u n' = 1 := by { dsimp[u], rw[if_pos rfl] },
    use u,
    split, exact hu,
    intro a,
    change a • u ∈ M ↔ a = 0,
    split; intro ha,
    { have ha' : a • (u n') = 0 := hM₃ (a • u) ha, 
      rw[hu, smul_eq_mul, mul_one] at ha', 
      exact ha'
    },
    { rw[ha, zero_smul], exact M.zero_mem }
  },
  { /- Case J n = Ic q -/
    have : t_pow q ∈ (ideal_spec.Ic q).to_ideal := Ic_t_pow_mem.mpr (le_refl q),
    rcases hM₂ (t_pow q) this with ⟨m,m_in_M,hm⟩,
    let u : F n.succ := λ i, left_shift (m i) q,
    have hu : (t_pow q) • u = m := by {
      ext1 i,
      change (t_pow q) * (left_shift (m i) q) = m i,
      rw[mul_comm], apply mul_left_shift,
      have := hJ'' i (hM₀ m i m_in_M),
      exact this
    },
    use u,
    sorry
  },
  sorry
end

end infinite_root