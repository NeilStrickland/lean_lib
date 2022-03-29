/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This is about "gappy sets", ie subsets s in fin n = {0,...,n-1} 
such that s contains no adjacent pairs {i,i+1}.  We define 
`(gappy n)` to be the set of such subsets.

A key point is that there is a bijection 
`(gappy n) ⊕ (gappy n + 1) ≃ (gappy n + 2)`, which we define as
`(gappy_equiv n)`.  From this it follows inductively that the 
cardinality of `(gappy n)` is the (n + 2)nd Fibonacci number.

-/

import data.fintype.basic 
import combinatorics.fibonacci combinatorics.shift

namespace combinatorics

/- We find it convenient to introduce a new notation for
   the zero element in fin m.  Notice that this only exists
   when m > 0, or equivalently, when m has the form 
   n.succ = n + 1 for some n.
-/
def fin.z {n : ℕ} : fin (n.succ) := 0

lemma fin.z_val {n : ℕ} : (@fin.z n).val = 0 := rfl

lemma fin.succ_ne_z {n : ℕ} (i : fin n) : i.succ ≠ fin.z := 
begin
 cases i with i i_is_lt,
 intro e,
 cases e
end

/- Definition of gappiness -/
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

instance {n : ℕ} : has_coe (gappy n) (finset (fin n)) :=
 by { dsimp[gappy], apply_instance }

lemma gappy_spec {n : ℕ} (s : gappy n) : is_gappy (s : finset (fin n)) := s.property 

/- How to generate a string describing a gappy set -/
instance {n : ℕ} : has_repr (gappy n) := 
 ⟨λ (s : gappy n), repr s.val⟩

/- Some lemmas about (un)shifting and gappiness -/

lemma shift_gappy : ∀ {n : ℕ} {s : finset (fin n)},
 is_gappy s → is_gappy (shift s)
| 0 _ _ := λ a, fin.elim0 a
| (nat.succ n) s s_gappy := begin
 rintros a ⟨a_in_shift,a_succ_in_shift⟩,
 let a_in_s : a ∈ s := (succ_mem_shift_iff s a).mp a_succ_in_shift,
 rcases (mem_shift s a.cast_succ).mp a_in_shift with ⟨b,⟨b_in_s,eb⟩⟩,
 replace eb := congr_arg (coe : (fin _) → ℕ) eb,
 rw[fin.coe_succ,fin.coe_cast_succ] at eb,
 have a_is_lt : (a : ℕ) < n.succ := a.property,
 rw[← eb] at a_is_lt,
 let c_is_lt : (b : ℕ) < n := nat.lt_of_succ_lt_succ a_is_lt, 
 let c : fin n := ⟨b,c_is_lt⟩,
 have ebc : b = fin.cast_succ c := fin.ext (by { rw[fin.coe_cast_succ], refl } ),
 have eac : a = fin.succ c := fin.ext (nat.succ_inj'.mp (by { rw[← eb,fin.coe_succ], refl })),
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
  fin.ext
   (by { rw[fin.coe_succ,fin.coe_cast_succ,fin.coe_cast_succ,fin.coe_succ]}),
 rw[e] at a_succ_in_s,
 exact s_gappy a.succ ⟨a_succ_in_s,a_succ_succ_in_s⟩,
end

lemma insert_gappy : ∀ {n : ℕ} {s : finset (fin n.succ.succ)}, 
 is_gappy s → (∀ (a : fin n.succ.succ), a ∈ s → a.val ≥ 2) → 
  is_gappy (insert (0 : fin _) s) := 
begin
 rintros n s s_gappy s_big a ⟨a_in_t,a_succ_in_t⟩,
 rcases finset.mem_insert.mp a_succ_in_t with a_succ_zero | a_succ_in_s,
 {exact fin.succ_ne_z a a_succ_zero},
 have a_pos₀ : (a.succ : ℕ) ≥ 2 := (s_big a.succ a_succ_in_s),
 rw[fin.coe_succ] at a_pos₀,
 let a_pos : 0 < (a : ℕ) := nat.lt_of_succ_lt_succ a_pos₀,
 rcases finset.mem_insert.mp a_in_t with a_zero | a_in_s,
 {replace a_zero : (a : ℕ) = 0 :=
  (fin.coe_cast_succ a).symm.trans (congr_arg coe a_zero),
  rw[a_zero] at a_pos,
  exact lt_irrefl 0 a_pos,
 },{
  exact s_gappy a ⟨a_in_s,a_succ_in_s⟩, 
 }
end

def i {n : ℕ} (s : gappy n) : gappy n.succ := 
 ⟨shift s.val,shift_gappy s.property⟩ 

lemma i_val {n : ℕ} (s : gappy n) : (i s).val = shift s.val := rfl

lemma zero_not_in_i {n : ℕ} (s : gappy n) : (0 : fin _) ∉ ((i s) : finset (fin n.succ)) := 
 zero_not_mem_shift s.val

lemma shift_big {n : ℕ} (s : finset (fin n)) : 
 ∀ (a : fin n.succ.succ), a ∈ shift (shift s) → (a : ℕ) ≥ 2 := 
begin
 intros a ma,
 rcases (mem_shift (shift s) a).mp ma with ⟨b,⟨mb,eb⟩⟩,
 rcases (mem_shift s b).mp mb with ⟨c,⟨mc,ec⟩⟩,
 rw[← eb,← ec,fin.coe_succ,fin.coe_succ],
 apply nat.succ_le_succ,
 apply nat.succ_le_succ,
 exact nat.zero_le c.val,
end

def j {n : ℕ} (s : gappy n) : gappy n.succ.succ := 
 ⟨insert (0 : fin _) (shift (shift s.val)),
  begin 
   let h := insert_gappy (shift_gappy (shift_gappy s.property)) (shift_big s.val),
   exact h,
  end⟩

lemma j_val {n : ℕ} (s : gappy n) :
 (j s).val = insert (0 : fin _) (shift (shift s.val)) := rfl

lemma zero_in_j {n : ℕ} (s : gappy n) : (0 : fin _) ∈ (j s : finset (fin n.succ.succ)) := 
 finset.mem_insert_self _ _

def p {n : ℕ} : (gappy n) ⊕ (gappy n.succ) → gappy n.succ.succ 
| (sum.inl s) := j s
| (sum.inr s) := i s

def q {n : ℕ} (s : gappy n.succ.succ) : (gappy n) ⊕ (gappy n.succ) := 
if (0 : fin _) ∈ s.val then
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
  change insert (0 : fin _) (shift (shift (unshift (unshift s.val )))) = s.val,
  have z_not_in_us : (0 : fin _) ∉ unshift s.val := begin
   intro z_in_us,
   let z_succ_in_s := (mem_unshift s.val (0 : fin _)).mp z_in_us,
   exact s.property (0 : fin _) ⟨h,z_succ_in_s⟩,
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
 rw[fintype.card_sum] at e0,
 exact e0.symm
end

lemma gappy_card : ∀ (n : ℕ), fintype.card (gappy n) = fibonacci n.succ.succ
| 0 := rfl
| 1 := rfl
| (nat.succ (nat.succ n)) := begin
 rw[gappy_card_step n,gappy_card n,gappy_card n.succ],
 dsimp[fibonacci],refl,
end

end combinatorics