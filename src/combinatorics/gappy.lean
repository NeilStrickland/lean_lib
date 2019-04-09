import data.fintype 

namespace combinatorics

/-
 This question is about "gappy sets", ie subsets s in 
 fin n = {0,...,n-1} such that s contains no adjacent pairs
 {i,i+1}.  
-/

/- We find it convenient to introduce a new notation for
   the zero element in fin m.  Notice that this only exists
   when m > 0, or equivalently, when m has the form 
   n.succ = n + 1 for some n.
-/
def fin.z {n : ℕ} : fin (n.succ) := 0

lemma fin.z_val {n : ℕ} : (@fin.z n).val = 0 := rfl

lemma fin.succ_ne_z {n : ℕ} (a : fin n) : a.succ ≠ fin.z := 
begin
 intro e,
 replace e := fin.veq_of_eq e,
 rw[fin.succ_val,fin.z_val] at e,
 injection e,
end

lemma fin.succ_inj {n : ℕ} {a b : fin n} (e : a.succ = b.succ) : 
 a = b := 
begin 
 apply fin.eq_of_veq,
 replace e := congr_arg fin.val e,
 rw[fin.succ_val,fin.succ_val] at e,
 exact nat.succ_inj e,
end

def is_gappy : ∀ {n : ℕ} (s : finset (fin n)), Prop 
| 0 _ := true
| (nat.succ n) s := ∀ a : fin n, ¬ (a.cast_succ ∈ s ∧ a.succ ∈ s)

instance is_gappy_decidable :
 forall {n : ℕ} (s : finset (fin n)), decidable (is_gappy s)
| 0 _ := by {dsimp[is_gappy],apply_instance}
| (nat.succ n) s := by {dsimp[is_gappy],apply_instance}

def gappy' (n : ℕ) : finset (finset (fin n)) := 
 finset.univ.filter is_gappy

def gappy (n : ℕ) : Type := 
 { s : finset (fin n) // is_gappy s }

instance {n : ℕ} : fintype (gappy n) := 
 by { dsimp[gappy], apply_instance }

instance {n : ℕ} : decidable_eq (gappy n) := 
 by { dsimp[gappy], apply_instance }

instance {n : ℕ} : has_repr (gappy n) := 
 ⟨λ (s : gappy n), repr s.val⟩

def shift {n : ℕ} (s : finset (fin n)) : finset (fin n.succ) := 
 s.image fin.succ

def unshift {n : ℕ} (s : finset (fin n.succ)) : finset (fin n) := 
 finset.univ.filter (λ a, a.succ ∈ s)

lemma mem_shift {n : ℕ} (s : finset (fin n)) (a : fin n.succ) :
 a ∈ shift s ↔ ∃ b : fin n, b ∈ s ∧ b.succ = a := 
begin
 rw[shift],split,
 {intro a_in_shift,
  rcases finset.mem_image.mp a_in_shift with ⟨b,⟨b_in_s,e⟩⟩,
  use b,
  exact ⟨b_in_s,e⟩, 
 },{
  rintro ⟨b,⟨b_in_s,e⟩⟩,
  exact finset.mem_image.mpr ⟨b,⟨b_in_s,e⟩⟩, 
 }
end

lemma zero_not_in_shift {n : ℕ} (s : finset (fin n)) : 
 fin.z ∉ shift s := 
begin
 intro h0,
 rcases ((mem_shift s) 0).mp h0 with ⟨b,⟨b_in_s,e⟩⟩,
 let h1 := congr_arg fin.val e,
 rw[fin.succ_val] at h1,
 injection h1,
end

lemma succ_mem_shift_iff {n : ℕ} (s : finset (fin n)) (a : fin n) : 
 a.succ ∈ shift s ↔ a ∈ s := 
begin
 rw[mem_shift s a.succ],
 split,{
   rintro ⟨b,⟨b_in_s,u⟩⟩,
   rw[(fin.succ_inj u).symm],
   exact b_in_s,
 },{
   intro a_in_s,use a,exact ⟨a_in_s,rfl⟩,
 }
end

lemma mem_unshift {n : ℕ} (s : finset (fin n.succ)) (a : fin n) :
 a ∈ unshift s ↔ a.succ ∈ s := 
begin
 rw[unshift,finset.mem_filter],
 split,
 {intro h,exact h.right},
 {intro h,exact ⟨finset.mem_univ a,h⟩ }
end

lemma unshift_shift {n : ℕ} (s : finset (fin n)) : 
 unshift (shift s) = s := 
begin
 ext,rw[mem_unshift (shift s) a],rw[succ_mem_shift_iff],
end

lemma unshift_insert {n : ℕ} (s : finset (fin n.succ)) : 
 unshift (insert fin.z s) = unshift s := 
begin
 ext,rw[mem_unshift,mem_unshift,finset.mem_insert],
 split,
 {intro h,rcases h with h0 | h1,
  {exfalso,exact fin.succ_ne_z a h0},
  {exact h1}
 },
 {exact λ h,or.inr h}
end

lemma shift_unshift0 {n : ℕ} (s : finset (fin n.succ)) (h : fin.z ∉ s) :
 shift (unshift s) = s := 
begin
 ext, 
 rcases a with ⟨_ | b_val,a_is_lt⟩,
 {have e : @fin.z n = ⟨0,a_is_lt⟩ := fin.eq_of_veq rfl,
  rw[← e],simp only[zero_not_in_shift,h],
 },{
  let b : fin n := ⟨b_val,nat.lt_of_succ_lt_succ a_is_lt⟩,
  have e : b.succ = ⟨b_val.succ,a_is_lt⟩ := 
    by { apply fin.eq_of_veq,rw[fin.succ_val], },
  rw[← e,succ_mem_shift_iff (unshift s) b,mem_unshift s b],
 }
end

lemma shift_unshift1 {n : ℕ} (s : finset (fin n.succ)) (h : fin.z ∈ s) :
 insert fin.z (shift (unshift s)) = s :=
begin
 ext, 
 rw[finset.mem_insert],
 rcases a with ⟨_ | b_val,a_is_lt⟩,
 {have e : @fin.z n = ⟨0,a_is_lt⟩ := fin.eq_of_veq rfl,
  rw[← e],simp only[h,eq_self_iff_true,true_or],
 },{
  let b : fin n := ⟨b_val,nat.lt_of_succ_lt_succ a_is_lt⟩,
  have e : b.succ = ⟨b_val.succ,a_is_lt⟩ := 
    by { apply fin.eq_of_veq,rw[fin.succ_val], },
  rw[← e,succ_mem_shift_iff (unshift s) b,mem_unshift s b],
  split,
  {rintro (u0 | u1),
   {exfalso,exact fin.succ_ne_z b u0,},
   {exact u1}
  },
  {intro h,right,exact h,}
 }
end

lemma shift_gappy : ∀ {n : ℕ} {s : finset (fin n)},
 is_gappy s → is_gappy (shift s)
| 0 _ _ := λ a, fin.elim0 a
| (nat.succ n) s s_gappy := begin
 rintros a ⟨a_in_shift,a_succ_in_shift⟩,
 let a_in_s : a ∈ s := (succ_mem_shift_iff s a).mp a_succ_in_shift,
 rcases (mem_shift s a.cast_succ).mp a_in_shift with ⟨b,⟨b_in_s,eb⟩⟩,
 replace eb := congr_arg fin.val eb,
 rw[fin.succ_val,fin.cast_succ_val] at eb,
 let c_is_lt : b.val < n :=
  nat.lt_of_succ_lt_succ (eb.symm ▸ a.is_lt), 
 let c : fin n := ⟨b.val,c_is_lt⟩,
 have ebc : b = fin.cast_succ c := fin.eq_of_veq (by rw[fin.cast_succ_val]),
 have eac : a = fin.succ c := fin.eq_of_veq (nat.succ_inj (by rw[← eb,fin.succ_val])),
 rw[ebc] at b_in_s,
 rw[eac] at a_in_s,
 exact s_gappy c ⟨b_in_s,a_in_s⟩, 
end

lemma unshift_gappy : ∀ {n : ℕ} {s : finset (fin n.succ)},
 is_gappy s → is_gappy (unshift s)
| 0 _ _ := trivial
| (nat.succ n) s s_gappy := begin
 rintros a ⟨a_in_unshift,a_succ_in_unshift⟩,
 let a_succ_in_s := (mem_unshift s a.cast_succ).mp a_in_unshift,
 let a_succ_succ_in_s := (mem_unshift s a.succ).mp a_succ_in_unshift,
 have e : a.cast_succ.succ = a.succ.cast_succ := 
  fin.eq_of_veq
   (by {rw[fin.succ_val,fin.cast_succ_val,fin.cast_succ_val,fin.succ_val]}),
 rw[e] at a_succ_in_s,
 exact s_gappy a.succ ⟨a_succ_in_s,a_succ_succ_in_s⟩,
end

lemma insert_gappy : ∀ {n : ℕ} {s : finset (fin n.succ.succ)}, 
 is_gappy s → (∀ (a : fin n.succ.succ), a ∈ s → a.val ≥ 2) → 
  is_gappy (insert fin.z s) := 
begin
 rintros n s s_gappy s_big a ⟨a_in_t,a_succ_in_t⟩,
 rcases finset.mem_insert.mp a_succ_in_t with a_succ_zero | a_succ_in_s,
 {exact fin.succ_ne_z a a_succ_zero},
 let a_pos : 0 < a.val :=
  nat.lt_of_succ_lt_succ ((fin.succ_val a) ▸ (s_big a.succ a_succ_in_s)),
 rcases finset.mem_insert.mp a_in_t with a_zero | a_in_s,
 {replace a_zero : a.val = 0 :=
  (fin.cast_succ_val a).symm.trans (congr_arg fin.val a_zero),
  rw[a_zero] at a_pos,
  exact lt_irrefl 0 a_pos,
 },{
  exact s_gappy a ⟨a_in_s,a_succ_in_s⟩, 
 }
end

def i {n : ℕ} (s : gappy n) : gappy n.succ := 
 ⟨shift s.val,shift_gappy s.property⟩ 

lemma i_val {n : ℕ} (s : gappy n) : (i s).val = shift s.val := rfl

lemma zero_not_in_i {n : ℕ} (s : gappy n) : fin.z ∉ (i s).val := 
 zero_not_in_shift s.val

lemma shift_big {n : ℕ} (s : finset (fin n)) : 
 ∀ (a : fin n.succ.succ), a ∈ shift (shift s) → a.val ≥ 2 := 
begin
 intros a ma,
 rcases (mem_shift (shift s) a).mp ma with ⟨b,⟨mb,eb⟩⟩,
 rcases (mem_shift s b).mp mb with ⟨c,⟨mc,ec⟩⟩,
 rw[← eb,← ec,fin.succ_val,fin.succ_val],
 apply nat.succ_le_succ,
 apply nat.succ_le_succ,
 exact nat.zero_le c.val,
end

def j {n : ℕ} (s : gappy n) : gappy n.succ.succ := 
 ⟨insert fin.z (shift (shift s.val)),
  begin 
   let h := insert_gappy (shift_gappy (shift_gappy s.property)) (shift_big s.val),
   exact h,
  end⟩

lemma j_val {n : ℕ} (s : gappy n) :
 (j s).val = insert fin.z (shift (shift s.val)) := rfl

lemma zero_in_j {n : ℕ} (s : gappy n) : fin.z ∈ (j s).val := 
 finset.mem_insert_self _ _

def p {n : ℕ} : (gappy n) ⊕ (gappy n.succ) → gappy n.succ.succ 
| (sum.inl s) := j s
| (sum.inr s) := i s

def q {n : ℕ} (s : gappy n.succ.succ) : (gappy n) ⊕ (gappy n.succ) := 
if fin.z ∈ s.val then
 sum.inl ⟨unshift (unshift s.val),unshift_gappy (unshift_gappy s.property)⟩
else
 sum.inr ⟨unshift s.val,unshift_gappy s.property⟩ 

lemma qp {n : ℕ} (s : (gappy n) ⊕ (gappy n.succ)) : q (p s) = s := 
begin
 rcases s with s | s; dsimp[p,q],
 {rw[if_pos (zero_in_j s)],congr,apply subtype.eq,
  change unshift (unshift (j s).val) = s.val,
  rw[j_val,unshift_insert,unshift_shift,unshift_shift],
 },
 {rw[if_neg (zero_not_in_i s)],congr,apply subtype.eq,
  change unshift (i s).val = s.val,
  rw[i_val,unshift_shift],
 }
end

lemma pq {n : ℕ} (s : gappy n.succ.succ) : p (q s) = s := 
begin
 dsimp[q],split_ifs; dsimp[p]; apply subtype.eq,
 {rw[j_val],
  change insert fin.z (shift (shift (unshift (unshift s.val )))) = s.val,
  have z_not_in_us : fin.z ∉ unshift s.val := begin
   intro z_in_us,
   let z_succ_in_s := (mem_unshift s.val fin.z).mp z_in_us,
   exact s.property fin.z ⟨h,z_succ_in_s⟩,
  end,
  rw[shift_unshift0 (unshift s.val) z_not_in_us],
  rw[shift_unshift1 s.val h],
 },{
  rw[i_val],
  change shift (unshift s.val) = s.val,
  exact shift_unshift0 s.val h,  
 }
end

def gappy_equiv {n : ℕ} :
 ((gappy n) ⊕ (gappy n.succ)) ≃ (gappy n.succ.succ) := {
 to_fun := p,
 inv_fun := q,
 left_inv := qp,
 right_inv := pq
}

lemma gappy_card_step (n : ℕ) :
 fintype.card (gappy n.succ.succ) =
  fintype.card (gappy n) + fintype.card (gappy n.succ) := 
begin
 let e0 := fintype.card_congr (@gappy_equiv n),
 let e1 := fintype.card_sum (gappy n) (gappy n.succ),
 exact e0.symm.trans e1,
end

def fibonacci : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (nat.succ (nat.succ n)) := (fibonacci n) + (fibonacci n.succ)

lemma gappy_card : ∀ (n : ℕ), fintype.card (gappy n) = fibonacci n.succ.succ
| 0 := rfl
| 1 := rfl
| (nat.succ (nat.succ n)) := begin
 rw[gappy_card_step n,gappy_card n,gappy_card n.succ],
 dsimp[fibonacci],refl,
end

end combinatorics