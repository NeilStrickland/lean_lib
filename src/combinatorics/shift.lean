/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.fintype.basic 
import combinatorics.fibonacci

def nat.succ_emb : ℕ ↪ ℕ :=
  ⟨nat.succ, λ i j e, nat.succ.inj e⟩

def fin.succ_emb (n : ℕ) : (fin n) ↪ (fin n.succ) := 
  ⟨fin.succ, λ i j e, fin.succ_inj.mp e⟩ 

def fin.val_emb (n : ℕ) : (fin n) ↪ ℕ := 
  ⟨coe, λ i j e, fin.eq_of_veq e⟩

namespace combinatorics

def shift {n : ℕ} (s : finset (fin n)) : finset (fin n.succ) := 
 s.map (fin.succ_emb n)

/- Given a set s ⊆ {0,..,n}, we can shift it to the left 
   to get a set (unshift s) = {i : i + 1 ∈ s} ⊆ {0,..,n-1}
-/
def unshift {n : ℕ} (s : finset (fin n.succ)) : finset (fin n) := 
 finset.univ.filter (λ a, a.succ ∈ s)

lemma mem_shift {n : ℕ} (s : finset (fin n)) (a : fin n.succ) :
 a ∈ shift s ↔ ∃ b : fin n, b ∈ s ∧ b.succ = a := 
begin
 rw[shift],split,
 {intro a_in_shift,
  rcases finset.mem_map.mp a_in_shift with ⟨b,⟨b_in_s,e⟩⟩,
  use b,
  exact ⟨b_in_s,e⟩, 
 },{
  rintro ⟨b,⟨b_in_s,e⟩⟩,
  exact finset.mem_map.mpr ⟨b,⟨b_in_s,e⟩⟩, 
 }
end

lemma zero_not_mem_shift {n : ℕ} (s : finset (fin n)) : 
 (0 : (fin n.succ)) ∉ shift s := 
begin
 intro h0,
 rcases ((mem_shift s) 0).mp h0 with ⟨⟨b,hb⟩,⟨b_in_s,e⟩⟩,
 cases e
end

lemma succ_mem_shift_iff {n : ℕ} (s : finset (fin n)) (a : fin n) : 
 a.succ ∈ shift s ↔ a ∈ s := 
begin
 rw[mem_shift s a.succ],
 split,{
   rintro ⟨b,⟨b_in_s,u⟩⟩,
   rw[(fin.succ_inj.mp u).symm],
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
 unshift (insert (0 : (fin n.succ)) s) = unshift s := 
begin
 ext ⟨i,hi⟩,rw[mem_unshift,mem_unshift,finset.mem_insert],
 split,
 {intro h,rcases h with h0 | h1,
  {cases h0},
  {exact h1} },
 {exact λ h,or.inr h}
end

lemma shift_unshift0 {n : ℕ} (s : finset (fin n.succ)) 
  (h : (0 : (fin n.succ)) ∉ s) : shift (unshift s) = s := 
begin
 ext ⟨_ | a,a_is_lt⟩, 
 { have e : (0 : fin n.succ) = ⟨0,a_is_lt⟩ := fin.eq_of_veq rfl,
   rw[← e],simp only[zero_not_mem_shift,h] },
 { let b : fin n := ⟨a,nat.lt_of_succ_lt_succ a_is_lt⟩,
   have e : b.succ = ⟨a.succ,a_is_lt⟩ := 
    by { apply fin.eq_of_veq, refl, },
   rw[← e,succ_mem_shift_iff (unshift s) b,mem_unshift s b] }
end

lemma shift_unshift1 {n : ℕ} (s : finset (fin n.succ))
 (h : (0 : fin n.succ) ∈ s) : insert (0 : fin n.succ) (shift (unshift s)) = s :=
begin
  ext ⟨_ | a,a_is_lt⟩;
  rw[finset.mem_insert],
  { have e : (0 : fin n.succ) = ⟨0,a_is_lt⟩ := fin.eq_of_veq rfl,
    rw [← e], simp only[h,eq_self_iff_true,true_or] },
  { let b : fin n := ⟨a,nat.lt_of_succ_lt_succ a_is_lt⟩,
    have e : b.succ = ⟨a.succ,a_is_lt⟩ := 
      by { apply fin.eq_of_veq,refl, },
    rw [← e, succ_mem_shift_iff (unshift s) b, mem_unshift s b],
    split,
    { rintro (u0 | u1),
      { cases fin.veq_of_eq u0 },
      { exact u1 } } ,
    { intro h, right, exact h } }
end

lemma shift_card {n : ℕ} (s : finset (fin n)) : (shift s).card = s.card := 
 by { apply finset.card_map, }

lemma finset_fin_zero_empty (s : finset (fin 0)) : s = ∅ :=
  finset.eq_empty_of_forall_not_mem (λ i, fin.elim0 i)

lemma finset_fin_zero_card (s : finset (fin 0)) : s.card = 0 :=
  by { rw [finset_fin_zero_empty s, finset.card_empty] }

lemma unshift_card0 {n : ℕ} {s : finset (fin n.succ)} 
  (h : (0 : fin n.succ) ∉ s) : s.card = (unshift s).card := 
begin
  let t := unshift s,
  change s.card = t.card, 
  have : s = (shift t) := (shift_unshift0 s h).symm,
  rw [this, shift_card]
end

lemma unshift_card1 {n : ℕ} {s : finset (fin n.succ)} 
  (h : (0 : fin n.succ) ∈ s) : s.card = (unshift s).card.succ := 
begin
  let t := unshift s,
  change s.card = t.card.succ, 
  have : s = insert 0 (shift t) := (shift_unshift1 s h).symm,
  rw [this],
  rw [finset.card_insert_of_not_mem (zero_not_mem_shift t), shift_card]
end

lemma unshift_card {n : ℕ} (s : finset (fin n.succ)) : 
  s.card = 
   (if (0 : fin n.succ) ∈ s then (unshift s).card.succ else (unshift s).card) :=
begin
  split_ifs, apply unshift_card1 h, apply unshift_card0 h
end

def emb_nat_finset {n : ℕ} : (finset (fin n)) ↪ finset ℕ  :=
  ⟨λ s, s.map ⟨coe, λ i j e, fin.eq_of_veq e⟩,
   λ s t e, finset.map_inj.mp e⟩ 

lemma emb_nat_finset_shift {n : ℕ} (s : finset (fin n)) :
  emb_nat_finset.to_fun (shift s) = 
   (emb_nat_finset.to_fun s).map nat.succ_emb :=
begin
  ext i, rw[emb_nat_finset, finset.mem_map, finset.mem_map],
  split,
  { rintro ⟨⟨j,j_is_lt⟩,⟨hm,he⟩⟩, change j = i at he, 
    rcases (mem_shift s ⟨j,_⟩).mp hm with ⟨⟨k,k_is_lt⟩,⟨hk,hsk⟩⟩,
    use k,
    have : k ∈ emb_nat_finset.to_fun s := 
      by { rw [emb_nat_finset, finset.mem_map], use ⟨k,k_is_lt⟩, use hk, refl },
    use this,
    exact (fin.veq_of_eq hsk).trans he},
  { rintro ⟨j,⟨hj,he⟩⟩, change j.succ = i at he,
    rcases finset.mem_map.mp hj with ⟨⟨k,k_is_lt⟩,⟨hk,hv⟩⟩,
    change k = j at hv,
    use fin.succ ⟨k,k_is_lt⟩,
    use (succ_mem_shift_iff s ⟨k,k_is_lt⟩).mpr hk,
    change k.succ = i,
    rw [hv, he] }
end

lemma emb_nat_finset_unshift {n : ℕ} (s : finset (fin n.succ)) :
  emb_nat_finset.to_fun (unshift s) = 
   (finset.range n).filter (λ i, i.succ ∈ emb_nat_finset.to_fun s) :=
begin
  ext i,
  rw [finset.mem_filter, finset.mem_range,
      emb_nat_finset, emb_nat_finset, 
      finset.mem_map, finset.mem_map],
  split,
  { rintro ⟨⟨j,j_is_lt⟩,⟨hm,he⟩⟩, change j = i at he, rw[mem_unshift] at hm,
    split,
    { rw[← he], exact j_is_lt },
    { use fin.succ ⟨j,j_is_lt⟩, use hm, change j.succ = i.succ, rw[he]} },
  { rintro ⟨hi,⟨⟨j,j_is_lt⟩,⟨hm,he⟩⟩⟩, change j = i.succ at he,
    let i0 : fin n := ⟨i,hi⟩,
    have hj : (⟨j,j_is_lt⟩ : (fin n.succ)) = i0.succ := fin.eq_of_veq he,
    rw [hj] at hm,
    use i0, use (mem_unshift s i0).mpr hm, refl }
end

end combinatorics