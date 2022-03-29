import data.rat data.pnat.basic data.pnat.factors
import data.rat_extra

def prat := {q : ℚ // q > 0}

notation ℚ+ := prat

namespace prat

instance to_rat : has_coe ℚ+ ℚ := ⟨subtype.val⟩

theorem pos (p : ℚ+) : (p : ℚ) > 0 := p.property

theorem eq {p q : ℚ+} : (p : ℚ) = (q : ℚ) → p = q := subtype.eq

instance : comm_group ℚ+ := 
{ one := ⟨(1 : ℚ), zero_lt_one ⟩,
  mul := λ p q,⟨(p * q : ℚ), mul_pos p.pos q.pos⟩,
  inv := λ q, ⟨(q ⁻¹ : ℚ), inv_pos.mpr q.pos⟩,
  one_mul      := λ q,     eq (one_mul q),
  mul_one      := λ q,     eq (mul_one q),
  mul_comm     := λ p q,   eq (mul_comm p q),
  mul_assoc    := λ p q r, eq (mul_assoc p q r),
  mul_left_inv := λ q,     eq (inv_mul_cancel (ne_of_gt q.pos)) }

instance : add_comm_semigroup ℚ+ := 
{ add := λ p q, ⟨(p + q : ℚ), add_pos p.pos q.pos⟩ ,
  add_comm  := λ p q,   eq (add_comm p q),
  add_assoc := λ p q r, eq (add_assoc p q r) }

instance : distrib ℚ+ :=
{ left_distrib  := λ a b c, eq (mul_add a b c),
  right_distrib := λ a b c, eq (add_mul a b c),
  .. (prat.add_comm_semigroup), .. (prat.comm_group) }

instance : decidable_eq ℚ+ := λ (a b : ℚ+), by apply_instance

instance : linear_order ℚ+ := subtype.linear_order _

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b. -/

def of_rat (q : ℚ) : ℚ+ := dite (q > 0) (λ h, ⟨q,h⟩) (λ h, 1) 

theorem of_rat_coe (q : ℚ) : ((of_rat q) : ℚ) = ite (q > 0) q 1 := 
by { dsimp [of_rat], split_ifs with h; refl}

theorem of_rat_pos_coe {q : ℚ} (h : q > 0) : ((of_rat q) : ℚ) = q := 
by rw [of_rat_coe, if_pos h]

instance : has_sub ℚ+ :=  ⟨λ a b, of_rat (a - b : ℚ)⟩

theorem one_coe            : ((1 : ℚ+) : ℚ) = 1            := rfl
theorem inv_coe (q : ℚ+)   : ((q⁻¹ : ℚ+) : ℚ) = (q : ℚ)⁻¹ := rfl 
theorem mul_coe (p q : ℚ+) : ((p * q : ℚ+) : ℚ) = p * q   := rfl
theorem add_coe (p q : ℚ+) : ((p + q : ℚ+) : ℚ) = p + q   := rfl
theorem lt_coe  (p q : ℚ+) : p < q ↔ (p : ℚ) < (q : ℚ)    := iff.refl _
theorem gt_coe  (p q : ℚ+) : p > q ↔ (p : ℚ) > (q : ℚ)    := iff.refl _

theorem sub_coe (a b : ℚ+) : ((a - b : ℚ+) : ℚ) = ite (a > b) ((a : ℚ) - (b : ℚ)) 1 :=
begin
  change ((of_rat (a - b : ℚ)) : ℚ) = ite ((a : ℚ) > (b : ℚ)) (a - b : ℚ) 1,
  rw[of_rat_coe],
  by_cases h : (a : ℚ) > (b : ℚ),
  { rw[if_pos h, if_pos (sub_pos_of_lt h)] },
  { rw[if_neg h, if_neg (mt lt_of_sub_pos h)] }
end

theorem add_sub_of_lt {a b : ℚ+} : a < b → a + (b - a) = b :=
 λ h, eq $ by { rw[add_coe, sub_coe, if_pos h, add_sub_cancel'_right] }

def mk (n d : ℕ+) : ℚ+ := 
⟨ rat.mk ((n : ℕ) : ℤ) d,
  begin
    let nz_pos : ((n : ℕ) : ℤ) > 0 := int.coe_nat_pos.mpr n.pos,
    let dz_pos : ((d : ℕ) : ℤ) > 0 := int.coe_nat_pos.mpr d.pos,
    by_cases h₀ : rat.mk (n : ℕ) (d : ℕ) = 0,
    { exfalso,
      exact ((ne_of_gt nz_pos) ((rat.mk_eq_zero (ne_of_gt dz_pos)).mp h₀)) },
    have : rat.mk (n : ℕ) (d : ℕ) ≠ 0 := h₀, 
    apply lt_of_le_of_ne _ this.symm,
    apply rat.nonneg_iff_zero_le.mp,
    exact ((rat.mk_nonneg (n : ℕ) dz_pos).mpr (le_of_lt nz_pos)) 
  end ⟩

theorem mk_coe (n d : ℕ+) : ((mk n d) : ℚ) = rat.mk (n : ℕ) (d : ℕ) := rfl

theorem mk_coe' (n d : ℕ+) : ((mk n d) : ℚ) = rat.mk_pnat (n : ℕ) d := 
begin
  dsimp [mk], unfold_coes,
  dsimp [rat.mk], rw[rat.mk_nat], rw[dif_neg (ne_of_gt d.pos)], 
  congr, apply subtype.eq, refl,
end

instance of_pnat : has_coe ℕ+ ℚ+ := ⟨λ n, mk n 1⟩

theorem coe_pnat_prat_rat (n : ℕ+) : ((n : ℚ+) : ℚ) = n := rfl

theorem coe_pnat_nat_rat : ∀ (n : ℕ+), ((n : ℕ) : ℚ) = n 
| ⟨n,hn⟩ := by { change (n : ℚ) = rat.mk_nat (n : ℤ) 1, 
                rw[rat.mk_nat_with_one_eq_cast n], refl }

theorem of_pnat_one : ((1 : ℕ+) : ℚ+) = 1 := prat.eq
begin 
  unfold_coes, dsimp[prat.mk], rw[zero_add, rat.mk_one_one], refl
end

theorem of_pnat_inj {n m : ℕ+} : (n : ℚ+) = (m : ℚ+) → n = m := 
begin
  intro h, 
  have : ((n : ℚ+) : ℚ) = ((m : ℚ+) : ℚ) := by { rw [h] },
  rw [coe_pnat_prat_rat, coe_pnat_prat_rat] at this,
  rw [← coe_pnat_nat_rat, ← coe_pnat_nat_rat] at this,
  exact pnat.eq (nat.cast_inj.mp this),
end

theorem of_pnat_mul (n m : ℕ+) : ((n * m : ℕ+) : ℚ+) = n * m := 
by { apply eq, 
     rw[mul_coe], 
     repeat { rw[coe_pnat_prat_rat] },
     repeat { rw[← coe_pnat_nat_rat] },
     rw [pnat.mul_coe, nat.cast_mul] }

theorem of_pnat_add (n m : ℕ+) : ((n + m : ℕ+) : ℚ+) = n + m := 
by { apply eq, 
     rw[add_coe], 
     repeat { rw[coe_pnat_prat_rat] },
     repeat { rw[← coe_pnat_nat_rat] },
     rw [pnat.add_coe, nat.cast_add] }

def num (q : ℚ+) : ℕ+ :=
 ⟨(q : ℚ).num.nat_abs, 
  int.nat_abs_pos_of_ne_zero (ne_of_gt (rat.num_pos_iff_pos.mpr q.pos))⟩ 

def denom (q : ℚ+) : ℕ+ := ⟨(q : ℚ).denom, (q : ℚ).pos⟩

theorem num_coe (q : ℚ+) : (q.num : ℕ) = (q : ℚ).num.nat_abs := rfl

theorem num_coe' (q : ℚ+) : ((q.num : ℕ) : ℤ) = (q : ℚ).num := 
 by { rw[num_coe q],
      exact (int.eq_nat_abs_of_zero_le (le_of_lt (rat.num_pos_iff_pos.mpr q.pos))).symm }

theorem denom_coe (q : ℚ+) : (denom q : ℕ) = (q : ℚ).denom := rfl

theorem num_denom_coprime (q : ℚ+) : nat.coprime q.num q.denom := (q : ℚ).cop

theorem mk_eq_div (n d : ℕ+) : mk n d = (n : ℚ+) * (d : ℚ+)⁻¹ := 
 by {apply eq,
     rw[mk_coe,mul_coe,inv_coe,← div_eq_mul_inv,rat.mk_eq_div,
        int.cast_coe_nat,int.cast_coe_nat,coe_pnat_nat_rat,coe_pnat_nat_rat,
        coe_pnat_prat_rat,coe_pnat_prat_rat]}

theorem num_denom (q : ℚ+) : q = mk q.num q.denom := 
 by {apply eq, rw[mk_coe, num_coe' q,denom_coe q], symmetry,
     exact rat.num_denom }

theorem num_denom' (q : ℚ+) : q = (q.num : ℚ+) * (q.denom : ℚ+)⁻¹ := 
 q.num_denom.trans (mk_eq_div _ _)

theorem mk_spec (n d : ℕ+) :
  n = (pnat.gcd n d) * (mk n d).num ∧ 
  d = (pnat.gcd n d) * (mk n d).denom := 
begin
  let g := pnat.gcd n d,
  rcases pnat.dvd_iff.mp (pnat.gcd_dvd_left  n d) with ⟨n',hn₀⟩,
  rcases pnat.dvd_iff.mp (pnat.gcd_dvd_right n d) with ⟨d',hd₀⟩,
  change (n : ℕ) = g * n' at hn₀,
  change (d : ℕ) = g * d' at hd₀,
  split; apply pnat.eq; rw[pnat.mul_coe],
  have hn₁ : (n' : ℕ) = (n : ℕ) / (g : ℕ) :=
    by { rw [hn₀, nat.mul_div_cancel_left _ g.pos] },
  have hd₁ : (d' : ℕ) = (d : ℕ) / (g : ℕ) :=
    by { rw [hd₀, nat.mul_div_cancel_left _ g.pos] },
  have hn₂ : (int.nat_abs ((n : ℕ) : ℤ)) = n := rfl,
  have hd₂ : ((mk n d).denom : ℕ) = d' := 
  begin
    dsimp[denom], 
    rw [mk_coe', rat.mk_pnat_denom, hn₂,← pnat.gcd_coe, hd₁]
  end, 
  have hn₃ : ((mk n d).num : ℕ) = n' := 
  begin
    dsimp[num],
    rw [mk_coe',rat.mk_pnat_num,hn₂,← pnat.gcd_coe,← int.coe_nat_div],
    norm_cast, exact hn₁.symm
  end,
  rw [hd₂, hn₂],
  exact ⟨hn₀.symm,hd₀.symm⟩,
end

theorem mk_spec' (n d : ℕ+) :
  n = (pnat.gcd n d) * ((n : ℚ+) * (d : ℚ+)⁻¹).num   ∧ 
  d = (pnat.gcd n d) * ((n : ℚ+) * (d : ℚ+)⁻¹).denom := 
(mk_eq_div n d) ▸ (mk_spec n d)

theorem eq_iff (n₁ d₁ n₂ d₂ : ℕ+) : 
 ((n₁ : ℚ+) * (d₁ : ℚ+)⁻¹) = ((n₂ : ℚ+) * (d₂ : ℚ+)⁻¹) ↔ n₁ * d₂ = n₂ * d₁ := 
begin
 rw[eq_mul_inv_iff_mul_eq, mul_comm, ← mul_assoc],
 have : ∀ (x y : ℚ+), x = y ↔ y = x := λ x y, ⟨λ h, h.symm, λ h, h.symm⟩,
 rw [this, eq_mul_inv_iff_mul_eq, ← of_pnat_mul, ← of_pnat_mul, mul_comm d₂, this],
 split,
 { intro h, exact of_pnat_inj h },
 { intro h, rw [h] }
end

theorem eq_iff' (q₁ q₂ : ℚ+) : q₁ = q₂ ↔ q₁.num * q₂.denom = q₂.num * q₁.denom := 
begin
 let n₁ := q₁.num, let d₁ := q₁.denom,
 let n₂ := q₂.num, let d₂ := q₂.denom,
 change q₁ = q₂ ↔ n₁ * d₂ = n₂ * d₁, 
 have : q₁ = n₁ * d₁ ⁻¹ := num_denom' q₁, rw [this],
 have : q₂ = n₂ * d₂ ⁻¹ := num_denom' q₂, rw [this],
 apply eq_iff
end

theorem mk_eq_mk_iff (n₁ d₁ n₂ d₂ : ℕ+) : mk n₁ d₁ = mk n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := 
by { rw[mk_eq_div, mk_eq_div], apply eq_iff }

theorem eq_mk_iff (q : ℚ+) (n d : ℕ+) : q = mk n d ↔ q.num * d = n * q.denom := 
begin
  rw [mk_eq_div],
  let n' := q.num, let d' := q.denom, 
  change _ ↔ n' * d = n * d',
  have : q = (n' : ℚ+) * (d' : ℚ+)⁻¹ := num_denom' q, 
  rw [this],
  apply eq_iff
end

def size (q : ℚ+) : ℕ := q.num + q.denom

instance : has_sizeof ℚ+ := ⟨size⟩

theorem sizeof_val (q : ℚ+) : sizeof q = q.num + q.denom := rfl

theorem sizeof_le (a b : ℕ+) : 
  sizeof ((a : ℚ+) * (b : ℚ+)⁻¹) ≤ a + b := 
begin
  let g := pnat.gcd a b,
  let a' := (mk a b).num,
  let b' := (mk a b).denom,
  rw[← mk_eq_div, sizeof_val],
  change (a' + b' : ℕ) ≤ a + b,
  let h := mk_spec a b,
  have ha : a = g * a' := h.1,
  have hb : b = g * b' := h.2,
  rw [ha, hb, pnat.mul_coe, pnat.mul_coe, ← mul_add],
  exact nat.le_mul_of_pos_left g.pos
end

theorem inv_num_denom (q : ℚ+) : q⁻¹.num = q.denom ∧ q⁻¹.denom = q.num := 
begin
  let n := q.num,
  let d := q.denom,
  have h : pnat.gcd d n = 1 := 
    pnat.eq (by { rw[pnat.gcd_coe, pnat.one_coe, nat.gcd_comm], 
                  exact q.num_denom_coprime }),
  have := calc
    q⁻¹ = ((n : ℚ+) * (d : ℚ+)⁻¹)⁻¹ : by rw [num_denom' q]
    ... = (d : ℚ+) * (n : ℚ+)⁻¹ : by rw[mul_inv_rev, inv_inv]
    ... = mk d n : (mk_eq_div d n).symm,
  rw [this],
  have h' := mk_spec d n,
  rw [h, one_mul, one_mul] at h',
  exact ⟨h'.1.symm, h'.2.symm⟩ 
end

@[simp] theorem inv_num   (q : ℚ+) : q⁻¹.num = q.denom := q.inv_num_denom.1
@[simp] theorem inv_denom (q : ℚ+) : q⁻¹.denom = q.num := q.inv_num_denom.2

theorem inv_sizeof (q : ℚ+) : sizeof q⁻¹ = sizeof q :=
by { rw[q.sizeof_val, q⁻¹.sizeof_val, q.inv_num, q.inv_denom, add_comm] }

theorem inv_gt_one_iff {q : ℚ+} : q⁻¹ > 1 ↔ q < 1 := 
begin
  let h := inv_lt_inv (1 : ℚ+).pos q.pos,
  rw [← inv_coe, ← inv_coe, one_coe, one_inv, one_coe] at h,
  exact h
end

theorem inv_lt_one_iff {q : ℚ+} : q⁻¹ < 1 ↔ q > 1 := 
by { let h := iff.symm (@inv_gt_one_iff q⁻¹),
     rw [inv_inv q] at h, exact h }

def succ   (q : ℚ+) : ℚ+ := q + 1
def pred   (q : ℚ+) : ℚ+ := q - 1
def cosucc (q : ℚ+) : ℚ+ := (q⁻¹.succ)⁻¹ 
def copred (q : ℚ+) : ℚ+ := (q⁻¹.pred)⁻¹

theorem succ_coe   (q : ℚ+) : (q.succ : ℚ) = q + 1 := rfl 
theorem cosucc_coe (q : ℚ+) : (q.cosucc : ℚ) = (q⁻¹ + 1)⁻¹ := rfl 

theorem pred_coe   {q : ℚ+} (h : q > 1) : (q.pred : ℚ) = q - 1 :=
by { rw[pred, sub_coe, if_pos h, one_coe] }

theorem copred_coe {q : ℚ+} (h : q < 1) : (q.copred : ℚ) = (q⁻¹ - 1)⁻¹ :=
by { rw[copred, inv_coe, pred_coe (inv_gt_one_iff.mpr h), inv_coe] }

theorem succ_gt_one (q : ℚ+) : q.succ > 1 := 
by { change (q : ℚ) + 1 > 1, exact lt_add_of_pos_left _ q.pos }

theorem cosucc_lt_one (q : ℚ+) : q.cosucc < 1 := 
inv_lt_one_iff.mpr q⁻¹.succ_gt_one

theorem pred_succ (q : ℚ+) : q.succ.pred = q := 
eq $ (by rw[pred_coe (succ_gt_one q), succ, add_coe, one_coe, add_sub_cancel])

theorem copred_cosucc (q : ℚ+) : q.cosucc.copred = q := 
by { rw [cosucc, copred, inv_inv, pred_succ, inv_inv] }

theorem succ_pred {q : ℚ+} (h : q > 1) : succ (pred q) = q :=
eq $ (by { rw[succ_coe, pred_coe h, sub_add_cancel] })

theorem cosucc_copred {q : ℚ+} (h : q < 1): q.copred.cosucc = q := 
by { rw [copred, cosucc, inv_inv, succ_pred (inv_gt_one_iff.mpr h), inv_inv] }

theorem succ_num_denom (q : ℚ+) : 
  q.succ.num = q.num + q.denom ∧ q.succ.denom = q.denom := 
begin
  let n := q.num, let d := q.denom,
  change q.succ.num = n + d ∧ q.succ.denom = d,
  have h₀ := calc
    q.succ = q + 1 : rfl
    ... = n * d⁻¹ + (d * d⁻¹) : by { rw[mul_inv_self, num_denom' q] }
    ... = (n + d : ℕ+) * d⁻¹ : by { rw [of_pnat_add, add_mul] },
  have h₁ : pnat.gcd (n + d) d = 1 := 
  begin
    apply pnat.eq, 
    rw[pnat.gcd_coe, pnat.one_coe,pnat.add_coe],
    let d' := nat.gcd (n + d) d, change d' = 1,
    have hd : d' ∣ d := nat.gcd_dvd_right (n + d) d,
    have hn := (nat.dvd_add_iff_left hd).mpr (nat.gcd_dvd_left (n + d) d), 
    exact nat.eq_one_of_dvd_one (q.num_denom_coprime ▸ (nat.dvd_gcd hn hd))
  end,
  have h₂ := mk_spec' (n + d) d,
  rw [h₁, one_mul, one_mul, ← h₀] at h₂,
  exact ⟨h₂.1.symm, h₂.2.symm⟩
end

theorem pred_num_denom {q : ℚ+} (h : q > 1) : 
  q.pred.num + q.denom = q.num ∧ q.pred.denom = q.denom := 
begin
  let r := q.pred,
  change r.num + q.denom = q.num ∧ r.denom = q.denom,
  have : q = r.succ := (succ_pred h).symm,
  let h := succ_num_denom r,
  rw [← this] at h,
  exact ⟨h.2.symm ▸ h.1.symm, h.2.symm⟩
end

theorem cosucc_num_denom (q : ℚ+) : 
  q.cosucc.num = q.num ∧ q.cosucc.denom = q.denom + q.num := 
begin
  let h := succ_num_denom q⁻¹,
  rw [cosucc, inv_num, inv_denom, h.1, h.2, inv_denom, inv_num],
  split; refl
end

theorem copred_num_denom {q : ℚ+} (h : q < 1) :
  q.copred.num = q.num ∧ q.copred.denom + q.num = q.denom := 
begin
  let h' := pred_num_denom (inv_gt_one_iff.mpr h),
  rw [inv_num, inv_denom] at h',
  rw [copred, inv_num, inv_denom, h'.2, h'.1],
  split; refl  
end

theorem pred_sizeof {q : ℚ+} (h : q > 1) : sizeof (pred q) < sizeof q := 
by { let h := pred_num_denom h,
     rw [sizeof_val, sizeof_val, ← h.1, ← h.2, pnat.add_coe], 
     apply nat.lt_add_of_pos_right q.pred.denom.pos }

theorem copred_sizeof {q : ℚ+} (h : q < 1) : sizeof (copred q) < sizeof q := 
by { dsimp [copred], rw[inv_sizeof (pred q⁻¹), ← inv_sizeof q],
     exact pred_sizeof (inv_gt_one_iff.mpr h) }

def of_word : list bool → ℚ+ 
| list.nil := 1
| (list.cons tt l) := succ (of_word l)
| (list.cons ff l) := cosucc (of_word l)

def to_word : ℚ+ → list bool
| q := dite (q = 1) 
        (λ h_eq, list.nil)
        (λ h_ne, dite (q > 1)
                 (λ h_gt, 
                    have h' : _ := pred_sizeof h_gt,
                    list.cons tt (to_word (pred q)) )
                 (λ h_le, 
                    have h_lt : q < 1 := lt_of_le_of_ne (le_of_not_gt h_le) h_ne,
                    have h' : _ := copred_sizeof h_lt,
                    list.cons ff (to_word (copred q)))) 

theorem to_word_one : to_word (1 : ℚ+) = list.nil := begin
  have h : (1 : ℚ+) = (1 : ℚ+) := rfl,
  rw[to_word, dif_pos h]
end

theorem to_word_of_gt_one {q : ℚ+} (h : q > 1) : 
  q.to_word = list.cons tt q.pred.to_word := 
by rw [to_word, dif_neg (ne_of_gt h), dif_pos h]

theorem to_word_of_lt_one {q : ℚ+} (h : q < 1) : 
  q.to_word = list.cons ff q.copred.to_word := 
by rw [to_word, dif_neg (ne_of_lt h), dif_neg (not_lt_of_ge (le_of_lt h)) ]

theorem to_of_word : ∀ l : list bool, to_word (of_word l) = l 
| list.nil := to_word_one
| (list.cons tt l) :=
    by rw [of_word, to_word_of_gt_one (succ_gt_one _), pred_succ, to_of_word l]
| (list.cons ff l) :=
    by rw [of_word, to_word_of_lt_one (cosucc_lt_one _), copred_cosucc, to_of_word l]

theorem of_to_word : ∀ (q : ℚ+), of_word (to_word q) = q
| q := dite (q = 1)
         (λ h_eq, by { rw[h_eq,to_word_one], refl })
         (λ h_ne, dite (q > 1)
                  (λ h_gt,
                     have h' : _ := pred_sizeof h_gt, 
                     by { rw [to_word_of_gt_one h_gt, of_word, 
                              of_to_word q.pred, succ_pred h_gt] }
                  )
                  (λ h_le, 
                     have h_lt : q < 1 := lt_of_le_of_ne (le_of_not_gt h_le) h_ne,
                     have h' : _ := copred_sizeof h_lt,
                     by { rw [to_word_of_lt_one h_lt, of_word, 
                              of_to_word q.copred, cosucc_copred h_lt] } ) )


end prat