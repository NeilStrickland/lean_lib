/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.list.basic data.vector data.finset data.nat.choose
import data.fintype
import combinatorics.shift

import tactic.squeeze
namespace combinatorics

/- @latex: defn-binseq -/
def binseq := list bool

namespace binseq

instance : has_append binseq := 
  by { dsimp[binseq], apply_instance }

def repr' : binseq → string
| [] := ""
| (ff :: u) := "0" ++ (repr' u)
| (tt :: u) := "1" ++ (repr' u)

instance : has_repr binseq := 
 ⟨λ u, if u = [] then "∅" else repr' u⟩ 

def of_string (s : string) : binseq := 
 s.fold [] (λ l c, if c = '0' then (l ++ [ff])
                    else (if c = '1' then (l ++ [tt]) else l))

def rank : ∀ (u : binseq), ℕ 
| [] := 0
| (ff :: v) := (rank v)
| (tt :: v) := (rank v).succ

def enum_by_length : ∀ (n : ℕ), list binseq 
| 0 := [[]]
| (n + 1) := ((enum_by_length n).map (list.cons ff)) ++ 
             ((enum_by_length n).map (list.cons tt))

def enum_by_length_and_rank : ∀ (n k : ℕ), list binseq 
| 0 0 := [[]]
| 0 (k + 1) := []
| (n + 1) 0 := 
   (enum_by_length_and_rank n 0).map (list.cons ff)
| (n + 1) (k + 1) :=
   (enum_by_length_and_rank n (k + 1)).map (list.cons ff) ++
   (enum_by_length_and_rank n k).map (list.cons tt)

namespace eg

/- @latex: eg-binseq -/
def a := binseq.of_string "010110"
#eval a
#eval a.length
#eval a.rank

#eval enum_by_length 3
#eval enum_by_length_and_rank 5 3

end eg

namespace enum_by_length

lemma length (n : ℕ) : (enum_by_length n).length = 2 ^ n := 
begin
  induction n with n ih; rw[enum_by_length],
  { simp },
  { rw[list.length_append, list.length_map, list.length_map,
       ih, nat.pow_succ, mul_two] }
end

lemma nodup (n : ℕ) : (enum_by_length n).nodup := 
begin
  induction n with n ih; rw[enum_by_length],
  { exact list.nodup_singleton _ },
  { rw[list.nodup_append], split,
    { exact list.nodup_map (@list.cons_inj _ ff) ih },
    split,
    {  exact list.nodup_map (@list.cons_inj _ tt) ih },
    { intros u hff htt,
      rcases list.mem_map.mp hff with ⟨v,⟨mv,ev⟩⟩,
      rcases list.mem_map.mp htt with ⟨w,⟨mw,ew⟩⟩,
      injection (ev.trans ew.symm) with hb ht,
      cases hb }
  }
end

lemma mem_iff {n : ℕ} {u : binseq} : u ∈ (enum_by_length n) ↔ u.length = n := 
begin
  induction n with n ih generalizing u; rw[enum_by_length],
  { rw[list.mem_singleton], symmetry, exact list.length_eq_zero },
  { rw[list.mem_append],
    split,
    rintro (hff|htt),
    { rcases list.mem_map.mp hff with ⟨v,⟨mv,ev⟩⟩,
      rw[← ev, list.length, ih.mp mv] },
    { rcases list.mem_map.mp htt with ⟨v,⟨mv,ev⟩⟩,
      rw[← ev, list.length, ih.mp mv] },
    { intro mu,
      cases u with b v,
      {cases mu},
      {cases b; rw[list.length] at mu; replace mu := nat.succ_inj mu;
       let hu := ih.mpr mu,
       { left , apply list.mem_map.mpr, use v, exact ⟨hu,rfl⟩ },
       { right, apply list.mem_map.mpr, use v, exact ⟨hu,rfl⟩ } } } }
end

end enum_by_length

def elems_by_length (n : ℕ) : finset binseq := 
 ⟨enum_by_length n,enum_by_length.nodup n⟩ 

namespace elems_by_length

/- @latex: prop-binseq -/
lemma card (n : ℕ) : (elems_by_length n).card = 2 ^ n := 
  enum_by_length.length n

lemma mem_iff {n : ℕ} {u : binseq} : u ∈ (elems_by_length n) ↔ u.length = n := 
  enum_by_length.mem_iff

instance (n : ℕ) : fintype { u : binseq // u.length = n } := 
fintype.of_finset (elems_by_length n) (@elems_by_length.mem_iff n)

end elems_by_length

/- @latex: prop-binseq -/
lemma card_by_length (n : ℕ) : 
  fintype.card { u : binseq // u.length = n } = 2 ^ n := 
(fintype.card_of_finset (elems_by_length n) (@elems_by_length.mem_iff n)).trans
 (elems_by_length.card n)

namespace enum_by_length_and_rank

lemma length : ∀ (n k : ℕ),
 (enum_by_length_and_rank n k).length = n.choose k :=
begin
  intro n,
  induction n with n ih_n,
  { rintro ⟨_|k⟩; simp[enum_by_length_and_rank] },
  { rintro ⟨_|k⟩; simp[enum_by_length_and_rank, nat.choose], 
    { rw[ih_n, nat.choose_zero_right] },
    { rw[ih_n, ih_n] } }
end

lemma nodup : forall (n k : ℕ) , (enum_by_length_and_rank n k).nodup := 
begin
  intro n,
  induction n with n ih; rintro ⟨_|k⟩; rw[enum_by_length_and_rank],
  { exact list.nodup_singleton _ },
  { exact list.nodup_nil},
  { exact list.nodup_map (@list.cons_inj _ ff) (ih 0) },
  { rw[list.nodup_append], split,
    { exact list.nodup_map (@list.cons_inj _ ff) (ih (k + 1)) },
    split,
    { exact list.nodup_map (@list.cons_inj _ tt) (ih k) },
    { intros u hff htt,
      rcases list.mem_map.mp hff with ⟨v,⟨mv,ev⟩⟩,
      rcases list.mem_map.mp htt with ⟨w,⟨mw,ew⟩⟩,
      injection (ev.trans ew.symm) with hb ht,
      cases hb }
  }
end

lemma mem_iff {n k : ℕ} {u : binseq} :
 u ∈ (enum_by_length_and_rank n k) ↔ u.length = n ∧ u.rank = k := 
begin
  have L : ∀ (u : binseq) (x y : bool) (l : list binseq), 
    x :: u ∈ l.map (list.cons y) ↔ x = y ∧ u ∈ l := 
  begin
    intros u x y l,
    rw[list.mem_map],
    split; intro h,
    { rcases h with ⟨v,⟨h_mem,h_eq⟩⟩,
      injection h_eq with hxy hvu, 
      rw[← hvu],
      exact ⟨hxy.symm,h_mem⟩ },
    { use u, rw[h.left], exact ⟨h.right,rfl⟩ }
  end,
  revert n k,
  induction u with b u ih,
  { rintro ⟨_|n⟩ ⟨_|k⟩; simp [enum_by_length_and_rank, rank]; 
    intros; exact (nat.succ_ne_zero _).symm },
  { rintro ⟨_|n⟩ ⟨_|k⟩; cases b; 
    simp only
     [enum_by_length_and_rank, list.length, rank, L,
      list.not_mem_nil, list.mem_singleton, list.mem_append,
      nat.succ_ne_zero,
      ih, nat.succ_inj', eq_self_iff_true,
      true_and, false_and, and_false, false_or, or_false, iff_self]
   }
end

end enum_by_length_and_rank

def elems_by_length_and_rank (n k : ℕ) : finset binseq := 
 ⟨enum_by_length_and_rank n k,enum_by_length_and_rank.nodup n k⟩ 

namespace elems_by_length_and_rank

/- @latex: prop-binseq -/
lemma card (n k : ℕ) : (elems_by_length_and_rank n k).card = n.choose k := 
  enum_by_length_and_rank.length n k

lemma mem_iff {n k : ℕ} {u : binseq} : 
  u ∈ (elems_by_length_and_rank n k) ↔ u.length = n ∧ u.rank = k := 
  enum_by_length_and_rank.mem_iff

instance (n k : ℕ) : fintype { u : binseq // u.length = n ∧ u.rank = k } := 
fintype.of_finset (elems_by_length_and_rank n k)
 (@elems_by_length_and_rank.mem_iff n k)

end elems_by_length_and_rank

lemma card_by_length_and_rank (n k : ℕ) : 
  fintype.card { u : binseq // u.length = n ∧ u.rank = k } = n.choose k := 
(fintype.card_of_finset (elems_by_length_and_rank n k) 
  (@elems_by_length_and_rank.mem_iff n k)).trans
 (elems_by_length_and_rank.card n k)

def to_nat_list : ∀ (u : binseq), list ℕ 
| [] := [] 
| (ff :: u) := (to_nat_list u).map nat.succ
| (tt :: u) := 0 :: ((to_nat_list u).map nat.succ)

namespace to_nat_list

lemma length (u : binseq) : u.to_nat_list.length = u.rank := 
begin
  induction u with b u ih,
  simp [to_nat_list, rank],
  cases b; simp[to_nat_list, rank, ih]
end

lemma mem_iff {u : binseq} {i : ℕ} :
 i ∈ u.to_nat_list ↔ tt ∈ u.nth i := 
begin
  revert i,
  induction u with b u ih,
  { simp [to_nat_list], },
  cases b; rintro ⟨_|i⟩ ; 
  rw [to_nat_list, list.nth],
  { rw [option.mem_def, option.some_inj, list.mem_map],
    { split, { rintro ⟨k,⟨h,⟨_⟩⟩⟩ }, { rintro ⟨_⟩ } } },
  { rw [list.mem_map],
    { split,
     { rintro ⟨j,⟨hm,he⟩⟩, rw [nat.succ_inj he] at hm, exact ih.mp hm },
     { intro h, use i, exact ⟨ih.mpr h,rfl⟩ } } },
  { rw [option.mem_def, eq_self_iff_true, iff_true],
    exact list.mem_cons_self _ _ },
  { split, 
    { intro h, rw [list.mem_cons_iff] at h, rcases h with ⟨⟨_⟩|h⟩,
      rcases list.mem_map.mp h with ⟨j,⟨hm,he⟩⟩,
      rw [nat.succ_inj he] at hm, exact ih.mp hm },
    { intro h, apply list.mem_cons_of_mem, apply list.mem_map_of_mem,
      exact ih.mpr h } } 
end

lemma bound (u : binseq) (i : ℕ) : i ∈ u.to_nat_list → i < u.length := 
begin
  revert i,
  induction u with b u ih,
  { simp [to_nat_list] },
  { cases b; rintro ⟨_|i⟩; 
    simp only [to_nat_list, list.length, nat.zero_lt_succ, imp_true_iff],
    { intro h, rcases list.mem_map.mp h with ⟨j,⟨hm,he⟩⟩,
      rw [← he],
      exact nat.succ_lt_succ (ih j hm) },
    { intro h, rw[list.mem_cons_iff] at h,
      rcases h with ⟨⟨_⟩|h⟩,
      rcases list.mem_map.mp h with ⟨j,⟨hm,he⟩⟩,
      rw [← he],
      exact nat.succ_lt_succ (ih j hm) } }  
end

lemma sorted (u : binseq) : list.sorted has_lt.lt u.to_nat_list := 
begin
  induction u with b u ih,
  { exact list.sorted_nil },
  { have h : ((to_nat_list u).map nat.succ).sorted has_lt.lt := 
      list.pairwise_map_of_pairwise nat.succ @nat.succ_lt_succ ih,
    cases b; rw[to_nat_list],
    { exact h },
    { rw [list.sorted_cons], split,
      { intros i hi, rcases list.mem_map.mp hi with ⟨j,⟨hm,he⟩⟩,
        rw[← he], exact nat.zero_lt_succ _ },
      { exact h } } }
end

lemma nodup (u : binseq) : u.to_nat_list.nodup := 
begin
  have h : ∀ i j : ℕ, i < j → i ≠ j := λ _ _ p, ne_of_lt p,
  exact list.pairwise.imp h (sorted u)
end

end to_nat_list

def to_nat_finset (u : binseq) : finset ℕ := 
  ⟨to_nat_list u, to_nat_list.nodup u⟩

namespace to_nat_finset

lemma card (u : binseq) : u.to_nat_finset.card = u.rank := 
  to_nat_list.length u

lemma mem_iff {u : binseq} {i : ℕ} : i ∈ u.to_nat_finset ↔ tt ∈ (u.nth i) := 
  to_nat_list.mem_iff 

lemma bound (u : binseq) (i : ℕ) : i ∈ u.to_nat_finset → i < u.length := 
  to_nat_list.bound u i

lemma nil : to_nat_finset list.nil = ∅ := 
begin
  apply finset.eq_empty_of_forall_not_mem, intro i,
  rw [mem_iff, list.nth], exact option.not_mem_none tt
end

lemma ff_cons (u : binseq) :
 to_nat_finset (ff :: u) = (to_nat_finset u).map nat.succ_emb :=
by { rw[to_nat_finset, to_nat_finset, finset.map], congr } 

lemma tt_cons (u : binseq) :
 to_nat_finset (tt :: u) = insert 0 ((to_nat_finset u).map nat.succ_emb) :=
by { rw[to_nat_finset, to_nat_finset, finset.map],
     congr, rw [to_nat_list], symmetry,
     apply list.insert_neg, intro h,
     rcases (list.mem_map.mp h) with ⟨i,⟨_,⟨_⟩⟩⟩ } 

lemma cons (b : bool) (u : binseq) : 
  to_nat_finset (b :: u) = 
    cond b (insert 0 ((to_nat_finset u).map nat.succ_emb)) 
           ((to_nat_finset u).map nat.succ_emb) := 
begin
  cases b; rw[cond], apply ff_cons, apply tt_cons
end

end to_nat_finset

def to_fin_list {n : ℕ} (u : binseq) (h : u.length = n) : list (fin n) := 
begin
  have hb : ∀ i : ℕ, i ∈ u.to_nat_list → i < n := 
    λ i hi, h ▸ (to_nat_list.bound u i hi),
  exact list.pmap fin.mk u.to_nat_list hb
end

namespace to_fin_list

variables {n : ℕ} (u : binseq) (h : u.length = n)

lemma val : (u.to_fin_list h).map fin.val = u.to_nat_list := 
begin
  rw[to_fin_list, list.map_pmap],
  have : (λ (i : ℕ) (h : i < n), (fin.mk i h).val) = 
         (λ (i : ℕ) (h : i < n), id i) := 
    by { funext i h, refl },
  rw [this, list.pmap_eq_map, list.map_id]
end

lemma length : (u.to_fin_list h).length = u.rank := 
by { rw[to_fin_list, list.length_pmap, to_nat_list.length u] }

variables {u h}

lemma mem_iff {i : fin n} : 
  i ∈ u.to_fin_list h ↔ u.nth_le i.val (h.symm ▸ i.is_lt) = tt := 
begin
  have hi : i.val < u.length := h.symm ▸ i.is_lt,
  have hn : u.nth i.val = some (u.nth_le i.val hi) := list.nth_le_nth _,
  rw [to_fin_list, list.mem_pmap],
  split,
  { rintro ⟨j,⟨hj,he⟩⟩,
    let ho := option.mem_def.mp (to_nat_list.mem_iff.mp hj),
    have hv : i.val = j := by { rw[← he] },
    rw [← hv] at ho,
    rw [ho] at hn,
    exact (option.some_inj.mp hn).symm },
  { intro hv, rw[hv] at hn, use i.val,
    use to_nat_list.mem_iff.mpr hn, apply fin.eq_of_veq, refl }
end

variables (u h)

lemma sorted : (u.to_fin_list h).sorted has_lt.lt := 
begin
  have hs : ((u.to_fin_list h).map fin.val).pairwise has_lt.lt := 
  by { rw [val], exact to_nat_list.sorted u },
  have hp : ∀ i j : fin n, i.val < j.val → i < j := 
    λ i j hij, hij,
  exact list.pairwise_of_pairwise_map fin.val hp hs
end

lemma nodup : (u.to_fin_list h).nodup := 
begin
  have hp : ∀ i j : (fin n), i < j → i ≠ j := λ _ _ p, ne_of_lt p,
  exact list.pairwise.imp hp (sorted u h)
end

end to_fin_list

def to_fin_finset {n : ℕ} (u : binseq) (h : u.length = n): finset (fin n) := 
  ⟨to_fin_list u h, to_fin_list.nodup u h⟩

namespace to_fin_finset

variables {n : ℕ} (u : binseq) (h : u.length = n)

lemma val :
  (to_fin_finset u h).map (fin.val_emb n) = to_nat_finset u := 
begin
  rw [to_fin_finset, finset.map, to_nat_finset, ← finset.val_inj],
  simp only [multiset.coe_map, multiset.coe_eq_coe, list.map],
  rw [← to_fin_list.val u h], refl
end

lemma card : (to_fin_finset u h).card = u.rank := 
  to_fin_list.length u h

lemma mem_iff {i : fin n} : i ∈ (to_fin_finset u h) ↔ u.nth_le i.val (h.symm ▸ i.is_lt) = tt := 
  to_fin_list.mem_iff

lemma nil (h : list.nil.length = 0) : to_fin_finset list.nil h = ∅ := rfl

lemma ff_cons : 
  to_fin_finset (ff :: u) (by { rw[list.length, h] }) = 
   shift (to_fin_finset u h) :=
begin
  have hi : ∀ (p : ℕ) (l m : list (fin p)), 
    l.map fin.val = m.map fin.val → l = m :=
  begin
    intros p l m e,
    exact list.injective_map_iff.mpr
      (λ (i j : fin p) (e₀ : i.val = j.val), fin.eq_of_veq e₀) e,
  end,
  rw [to_fin_finset, to_fin_finset], congr,
  apply hi,
  rw [to_fin_list.val, to_nat_list, list.map_map],
  have : fin.val ∘ (fin.succ_emb n) = 
         nat.succ ∘ fin.val := 
  begin
    ext ⟨i,hi⟩, unfold_coes, simp [fin.succ_emb]
  end,
  rw [this, ← list.map_map nat.succ fin.val, to_fin_list.val]
end

lemma tt_cons : 
  to_fin_finset (tt :: u) (by { rw[list.length, h] }) = 
   insert (0 : fin n.succ) (shift (to_fin_finset u h)) :=
begin
  have hi : ∀ (p : ℕ) (l m : list (fin p)), 
    l.map fin.val = m.map fin.val → l = m :=
  begin
    intros p l m e,
    exact list.injective_map_iff.mpr
      (λ (i j : fin p) (e₀ : i.val = j.val), fin.eq_of_veq e₀) e,
  end,
  rw [to_fin_finset, to_fin_finset], congr,
  have hn : (0 : fin n.succ) ∉ (to_fin_list u h).map (fin.succ_emb n) := 
  begin
    intro hm,
    rcases list.mem_map.mp hm with ⟨i,⟨_,he⟩⟩,
    exact fin.succ_ne_zero _ he,
  end,
  apply hi,
  let hh := congr_arg (list.map fin.val) (list.insert_of_not_mem hn),
  rw [to_fin_list.val, to_nat_list], 
  have : (list.insert 0 (list.map ⇑(fin.succ_emb n) (to_fin_list u h))) = 
         (insert 0 (list.map ⇑(fin.succ_emb n) (to_fin_list u h))) := rfl,
  rw [this, hh, list.map, list.map_map],
  have : fin.val ∘ (fin.succ_emb n) = 
         nat.succ ∘ fin.val := 
  begin
    ext ⟨i,hi⟩, unfold_coes, simp [fin.succ_emb]
  end,
  rw [this, ← list.map_map nat.succ fin.val, to_fin_list.val],
  have : (0 : fin n.succ).val = 0 := rfl,
  rw [this],
end

lemma cons (b : bool) : 
  to_fin_finset (b :: u) (by { rw[list.length, h] }) =
   let s := (shift (to_fin_finset u h)) in (cond b (insert 0 s) s) := 
begin
  cases b, apply ff_cons, apply tt_cons
end

end to_fin_finset

def of_fin_finset : ∀ {n : ℕ} (s : finset (fin n)), binseq 
| 0 _ := []
| (n + 1) s :=
  (if (0 : (fin n.succ)) ∈ s then tt else ff) :: 
          (of_fin_finset (unshift s))

namespace of_fin_finset

lemma ff_step {n : ℕ} {s : finset (fin n.succ)} (h : (0 : fin n.succ) ∉ s) :
  of_fin_finset s = ff :: (of_fin_finset (unshift s)) := 
by rw [of_fin_finset, if_neg h]

lemma tt_step {n : ℕ} {s : finset (fin n.succ)} (h : (0 : fin n.succ) ∈ s) :
  of_fin_finset s = tt :: (of_fin_finset (unshift s)) := 
by rw [of_fin_finset, if_pos h]

lemma length {n : ℕ} (s : (finset (fin n))) : (of_fin_finset s).length = n :=
begin
  induction n with n ih,
  { rw [of_fin_finset, list.length ] },
  { rw [of_fin_finset, list.length, ih] }
end

lemma rank {n : ℕ} (s : (finset (fin n))) : (of_fin_finset s).rank = s.card :=
begin
  induction n with n ih,
  { have : s = ∅ := finset.eq_empty_of_forall_not_mem (λ i, fin.elim0 i),
    rw [of_fin_finset, rank, this, finset.card_empty] },
  { rw [of_fin_finset], split_ifs; rw [rank],
    { rw [ih (unshift s)], exact (unshift_card1 h).symm },
    { rw [ih (unshift s)], exact (unshift_card0 h).symm } }
end

lemma shift {n : ℕ} (s : (finset (fin n))) :
  of_fin_finset (combinatorics.shift s) = ff :: of_fin_finset s :=
begin
  induction n with n ih,
  { have : s = ∅ := finset.eq_empty_of_forall_not_mem (λ i, fin.elim0 i),
    rw [this], refl },
  { rw [of_fin_finset],
    split_ifs,
    { exfalso, exact zero_not_mem_shift s h },
    { rw[unshift_shift] } }
end

lemma insert {n : ℕ} (s : (finset (fin n))) :
  of_fin_finset (insert (0 : fin n.succ) (combinatorics.shift s)) = tt :: of_fin_finset s :=
begin
  induction n with n ih,
  { have : s = ∅ := finset.eq_empty_of_forall_not_mem (λ i, fin.elim0 i),
    rw [this], refl },
  { rw [of_fin_finset],
    split_ifs,
    { rw[unshift_insert, unshift_shift], },
    { exfalso, exact h (finset.mem_insert_self _ _) } }
end

end of_fin_finset

lemma of_to_fin_finset {n : ℕ} (u : binseq) (h : u.length = n) : 
  of_fin_finset (to_fin_finset u h) = u := 
begin
  revert u,
  induction n with n ih,
  { intro u, cases u with b u, 
    { intro h, refl },
    { intro h, exfalso, exact nat.succ_ne_zero u.length h } },
  { intro u, cases u with b u,
    { intro h, exfalso, exact nat.succ_ne_zero n h.symm },
    { intro h, have hl := nat.succ_inj h, 
      cases b,
      { rw [to_fin_finset.ff_cons u hl, of_fin_finset.shift, ih u hl] },
      { rw [to_fin_finset.tt_cons u hl, of_fin_finset.insert, ih u hl] } } }
end

lemma to_of_fin_finset {n : ℕ} (s : finset (fin n)) :
  to_fin_finset (of_fin_finset s) (of_fin_finset.length s) = s := 
begin
  induction n with n ih,
  { have : s = ∅ := finset.eq_empty_of_forall_not_mem (λ i, fin.elim0 i),
    rw [this], refl },
  { have he : ∀ (u₀ u₁ : binseq) (h₀ : u₀.length = n.succ) (e : u₀ = u₁),  
      to_fin_finset u₀ h₀ = 
      to_fin_finset u₁ ((congr_arg list.length e).symm.trans h₀) := 
    by { intros, cases e, refl },
    let t := unshift s,
    by_cases h : (0 : fin n.succ) ∈ s,
    { have : s = insert (0 : fin n.succ) (shift t) := (shift_unshift1 s h).symm,
      rw [this] at *,
      have ht := of_fin_finset.insert t,  
      have hf := he (of_fin_finset (insert (0 : fin n.succ) (shift t)))
        (tt :: of_fin_finset t) _ ht,
      let hc := to_fin_finset.tt_cons (of_fin_finset t) (of_fin_finset.length t),
      rw [hf, hc, ih t] },
    { have : s = shift t := (shift_unshift0 s h).symm, 
      rw [this] at *,
      have ht := of_fin_finset.shift t,
      have hf := he (of_fin_finset (shift t))
        (ff :: of_fin_finset t) _ ht,
      let hc := to_fin_finset.ff_cons (of_fin_finset t) (of_fin_finset.length t),
      rw [hf, hc, ih t] } }
end

def finset_equiv (n k : ℕ) : 
 { u : binseq // u.length = n ∧ u.rank = k } ≃ 
 { s : finset (fin n) // s.card = k } := 
 { to_fun    := λ u, ⟨to_fin_finset u.val u.property.left,
                     (to_fin_finset.card u.val u.property.left).trans
                      u.property.right⟩,
   inv_fun   := λ s, ⟨
    of_fin_finset s.val,
    ⟨of_fin_finset.length s.val,(of_fin_finset.rank s.val).trans s.property⟩⟩,
  left_inv  := λ u, subtype.eq (of_to_fin_finset u.val u.property.left),
  right_inv := λ s, subtype.eq (to_of_fin_finset s.val) }


end binseq

end combinatorics