/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This is about matching problems.  We have two sets `A` and `B`,
and a relation between them (formalised as `E : finset (A × B)`).
Everything is assumed to be finite and decidable.  Standard 
motivating examples:

- `A` is a set of jobs, `B` is a set of people, `(a,b)` lies 
  in `E` iff person `b` is qualified for job `a`.  We seek 
  to assign jobs to qualified people in such a way that 
  no one has more than one job.

- `A` and `B` are sets of people such that people in `A` are
  only interested in marrying people in `B` and vice-versa.
  A pair `(a,b)` lies in `E` iff `a` and `b` would be content
  to marry each other.  We seek to assign marriage partners 
  in such a way that everyone is content.

Formally, a (partial) matching is a subset `M ⊆ E` such that
the projections `M → A` and `M → B` are both injective.  The
theory contains various results about the existence or number
of partial matchings with various additional properties.  The
key result is Hall's Marriage Theorem; we have not yet written
either the statement or the proof.

The main result that we have written is the inclusion-exclusion
principle.  To explain this, note that each `b ∈ B` gives us 
a "column set" `col E b = {a : (a,b) ∈ E}`.  (There are also
"row sets", defined in a similar way, and we have lots of fairly
trivial lemmas translating information about `E` into information
about row sets or column sets and vice versa.)  The 
inclusion-exclusion principle is usually formulated as an 
equation for the order of the union of a finite family of
finite sets.  Such a family can be encoded as the column sets
of a matching problem as above; then the union of the columns
corresponds to the set of nonempty rows.  It is tidier to 
count the number of empty rows, which is the complement of the
union of the columns.  The inclusion-exclusion principle says
that the number of empty rows is the sum over `U ⊆ B` of 
`(-1)^|U| * |X_U|`, where `X_U` is the intersection of the sets
`col E b` for `b ∈ U`.  In Lean notation, the number 
`(-1)^|U|` is `card_sign U`, and the set `X_U` is 
`col_inter E U`.  The IEP is formalised as 
`combinatorics.matching.inclusion_exclusion`.

-/

import data.fintype
import combinatorics.card_sign

open finset 

lemma finset.mem_univ_filter {α : Type*} [fintype α]
 {p : α → Prop} [decidable_pred p] {a : α} :
  a ∈ univ.filter p ↔ p a := 
by {rw[mem_filter],simp only [mem_univ a,true_and],}

lemma finset.mem_bind_univ
 {α : Type*} [fintype α]  {β : Type*} [decidable_eq β]
  {f : α → finset β} {b : β} :
    b ∈ univ.bind f ↔ ∃ a : α, b ∈ (f a) := 
by {split,
    {intro h,rcases mem_bind.mp h with ⟨a,_,ha⟩,exact ⟨a,ha⟩},
    {rintro ⟨a,ha⟩,exact mem_bind.mpr ⟨a,⟨mem_univ a,ha⟩⟩}}

namespace combinatorics
namespace matching

universes u v

variables {A : Type u} [fintype A] [decidable_eq A] 
variables {B : Type u} [fintype B] [decidable_eq B] 

def swap : A × B → B × A := λ ab, ⟨ab.2,ab.1⟩

lemma swap_swap : ∀ ab : (A × B), swap (swap ab) = ab
| ⟨a,b⟩ := rfl

lemma fst_swap : prod.fst ∘ (swap : A × B → B × A) = prod.snd := 
 by { ext ⟨a,b⟩, refl }

lemma snd_swap : prod.snd ∘ (swap : A × B → B × A) = prod.fst := 
 by { ext ⟨a,b⟩, refl }

def swap_equiv : (A × B) ≃ (B × A) := {
 to_fun := swap, inv_fun := swap,
 left_inv := swap_swap, right_inv := swap_swap
}

def sswap : finset (A × B) → finset (B × A) := 
 λ M, M.map swap_equiv.to_embedding

lemma mem_sswap (M : finset (A × B)) (ba : B × A) :
 ba ∈ sswap M ↔ swap ba ∈ M := 
begin
 split,
 {intro h,rcases mem_map.mp h with ⟨ab,⟨hab,e⟩⟩,
  change swap ab = ba at e,rw[← e,swap_swap],exact hab,
 },{
  intro hba,apply mem_map.mpr,use swap ba,use hba,
  exact swap_swap ba,
 }
end

lemma mem_sswap' (M : finset (A × B)) (a : A) (b : B) : 
 prod.mk b a ∈ sswap M ↔ prod.mk a b ∈ M := 
  by {rw[mem_sswap,swap],}

lemma sswap_sswap (M : finset (A × B)) : sswap (sswap M) = M := 
 by {ext ⟨a,b⟩,rw[mem_sswap',mem_sswap']}

def incl (a : A) : B ↪ (A × B) := 
 ⟨λ b,prod.mk a b,λ b₀ b₁ e, congr_arg prod.snd e⟩

def incr (b : B) : A ↪ (A × B) := 
 ⟨λ a,prod.mk a b,λ a₀ a₁ e,congr_arg prod.fst e⟩ 

lemma mem_incl {U : finset B} {a : A} : ∀ {xy : A × B},
 xy ∈ U.map (incl a) ↔ xy.1 = a ∧ xy.2 ∈ U
| ⟨x,y⟩ := begin
 split,
 {rintro hxy,rcases mem_map.mp hxy with ⟨b,⟨hb,e⟩⟩,
  have ea : a = x := congr_arg prod.fst e,
  have eb : b = y := congr_arg prod.snd e,
  rw[← ea,← eb],exact ⟨rfl,hb⟩,
 },{
  rintro ⟨ex,hy⟩,change x = a at ex,change y ∈ U at hy,
  rw[ex],exact mem_map.mpr ⟨y,hy,rfl⟩,
 }
end

lemma mem_incr {T : finset A} {b : B} : ∀ {xy : A × B},
 xy ∈ T.map (incr b) ↔ xy.1 ∈ T ∧ xy.2 = b
| ⟨x,y⟩ := begin
 split,
 {rintro hxy,rcases mem_map.mp hxy with ⟨a,⟨ha,e⟩⟩,
  have ea : a = x := congr_arg prod.fst e,
  have eb : b = y := congr_arg prod.snd e,
  rw[← ea,← eb],exact ⟨ha,rfl⟩,
 },{
  rintro ⟨hx,ey⟩,change x ∈ T at hx,change y = b at ey,
  rw[ey],exact mem_map.mpr ⟨x,hx,rfl⟩,
 }
end

variable E : finset (A × B) 

def row (a : A) : finset B := univ.filter (λ b, (prod.mk a b) ∈ E)

def row' (a : A) := E.filter (λ ab, ab.1 = a)

def col (b : B) : finset A := univ.filter (λ a, (prod.mk a b) ∈ E)

def col' (b : B) := E.filter (λ ab, ab.2 = b)

def row_union (T : finset A) := T.bind (row E)

def col_union (U : finset B) := U.bind (col E)

def row_inter (T : finset A) : finset B := univ.filter (λ b, T ⊆ col E b)

def col_inter (U : finset B) : finset A := univ.filter (λ a, U ⊆ row E a)

def clear_rows : finset A := univ.filter (λ a, row E a = ∅)

def clear_cols : finset B := univ.filter (λ b, col E b = ∅)

lemma mem_row (a : A) {b : B} : b ∈ row E a ↔ (prod.mk a b  ∈ E) := 
 by {apply finset.mem_univ_filter,}

lemma mem_col (b : B) {a : A} : a ∈ col E b ↔ (prod.mk a b  ∈ E) := 
 by {apply finset.mem_univ_filter,}

lemma mem_row_col {a : A} {b : B} : b ∈ row E a ↔ a ∈ col E b := 
 by {rw[mem_row,mem_col]}

lemma mem_row_union (T : finset A) (b : B) :
 b ∈ row_union E T ↔ ∃ a ∈ T, b ∈ row E a := 
  by {rw[row_union,mem_bind]}

lemma mem_col_union (U : finset B) (a : A) :
 a ∈ col_union E U ↔ ∃ b ∈ U, a ∈ col E b := 
  by {rw[col_union,mem_bind]}

lemma mem_row_inter (T : finset A) (b : B) :
 b ∈ row_inter E T ↔ ∀ a ∈ T, b ∈ row E a := 
  by {
   rw[row_inter,finset.mem_univ_filter],
   split; intros h a haT,
   {exact (mem_row E a).mpr ((mem_col E b).mp (h haT)),},
   {exact (mem_col E b).mpr ((mem_row E a).mp (h a haT)),}
  }

lemma mem_col_inter (U : finset B) (a : A) :
 a ∈ col_inter E U ↔ ∀ b ∈ U, a ∈ col E b := 
  by {
   rw[col_inter,finset.mem_univ_filter],
   split; intros h b hbU,
   {exact (mem_col E b).mpr ((mem_row E a).mp (h hbU)),},
   {exact (mem_row E a).mpr ((mem_col E b).mp (h b hbU)),}
  }

lemma mem_clear_rows (a : A) : a ∈ clear_rows E ↔ row E a = ∅ := 
 by {rw[clear_rows,finset.mem_univ_filter],}

lemma mem_clear_cols (b : B) : b ∈ clear_cols E ↔ col E b = ∅ := 
 by {rw[clear_cols,finset.mem_univ_filter],}

lemma row_sswap (b : B) : row (sswap E) b = col E b := 
 by {ext a,rw[mem_row,mem_col,mem_sswap'],}

lemma col_sswap (a : A) : col (sswap E) a = row E a := 
 by {ext b,rw[mem_row,mem_col,mem_sswap'],}

lemma row'_sswap (b : B) : row' (sswap E) b = sswap (col' E b) := 
 by {ext  ⟨x,y⟩,
     rw[mem_sswap',row',col',mem_filter,mem_filter,mem_sswap'],}

lemma col'_sswap (a : A) : col' (sswap E) a = sswap (row' E a) := 
 by {ext  ⟨x,y⟩,
     rw[mem_sswap',row',col',mem_filter,mem_filter,mem_sswap'],}

lemma row_union_sswap (U : finset B) : row_union (sswap E) U = col_union E U := 
 by {ext a,rw[mem_row_union,mem_col_union],
  split; rintro ⟨b,⟨hb,h⟩⟩; use b; use hb,
  {rw[row_sswap] at h,exact h},
  {rw[row_sswap] at ⊢,exact h}
 }

lemma col_union_sswap (T : finset A) : col_union (sswap E) T = row_union E T := 
 by {ext b,rw[mem_row_union,mem_col_union],
  split; rintro ⟨a,⟨ha,h⟩⟩; use a; use ha,
  {rw[col_sswap] at h,exact h},
  {rw[col_sswap] at ⊢,exact h}
 }

lemma row_inter_sswap (U : finset B) : row_inter (sswap E) U = col_inter E U := 
 by {ext a,rw[mem_row_inter,mem_col_inter],
  split; intros h b b_in_U; let h' := h b b_in_U,
  {rw[row_sswap] at h',exact h'},
  {rw[row_sswap] at ⊢ ,exact h'}
 }

lemma clear_rows_sswap : clear_rows (sswap E) = clear_cols E := 
 by {ext b,rw[mem_clear_rows,mem_clear_cols,row_sswap],}

lemma clear_cols_sswap : clear_cols (sswap E) = clear_rows E := 
 by {ext a,rw[mem_clear_rows,mem_clear_cols,col_sswap],}

lemma row_of_row' (a : A) : row E a = (row' E a).image prod.snd := 
 begin
  ext b,rw[mem_row,mem_image],split,
  {intro h,use ⟨a,b⟩,
   have : (prod.mk a b) ∈ row' E a :=
    by {rw[row',mem_filter],simp only [h,true_and],},
   use this,
  },{
   rintro ⟨⟨a',b'⟩,hab',hb⟩,
   rcases mem_filter.mp hab' with ⟨hab'',ha⟩,
   change a' = a at ha, change b' = b at hb,rw[← ha,← hb],exact hab''
  }
 end

lemma row'_of_row (a : A) : row' E a = (row E a).map (incl a) := 
 begin
  ext ⟨a',b⟩,
  rw[row',mem_filter,mem_incl,mem_row],
  split,
  {rintro ⟨h,e⟩,change a' = a at e,rw[e] at h ⊢,exact ⟨rfl,h⟩,},
  {rintro ⟨e,h⟩,change a' = a at e,rw[e] at h ⊢,exact ⟨h,rfl⟩,}
 end

lemma col_of_col' (b : B) : col E b = (col' E b).image prod.fst := 
begin
 let f : (A × B) ≃ (B × A) := swap_equiv,
 let fe := f.to_embedding,
 let C := col' E b,
 rw[← row_sswap,row_of_row',row'_sswap,sswap],
 change (C.map fe).image prod.snd = C.image prod.fst,
 rw[finset.map_eq_image,finset.image_image],
 change C.image (prod.snd ∘ swap) = C.image prod.fst,
 rw[snd_swap],
end

lemma col'_of_col (b : B) : col' E b = (col E b).map (incr b) := 
begin
 let f : (B × A) ≃ (A × B) := swap_equiv,
 let fe := f.to_embedding,
 let C := col E b,
 let e := (congr_arg sswap (row'_sswap E b)).trans (sswap_sswap _),
 rw[← e,row'_of_row,row_sswap,sswap],
 change (C.map (incl b)).map fe = C.map (incr b),
 rw[finset.map_map],congr,
end

def is_matching (M : finset (A × B)) := 
 M ⊆ E ∧
 (∀ x y : (A × B), x ∈ M → y ∈ M → x.1 = y.1 → x = y) ∧ 
 (∀ x y : (A × B), x ∈ M → y ∈ M → x.2 = y.2 → x = y) 

lemma inclusion_exclusion : 
 ((clear_rows E).card : ℤ) = 
  (@univ B _).powerset.sum (λ U, (card_sign U) * (card (col_inter E U))) := 
begin 
 let i : A → ((finset B) ↪ (A × (finset B))) := incl, 
 let j : (finset B) → (A ↪ (A × (finset B))) := incr, 
 let p : A → finset (A × (finset B)) := (λ a, (row E a).powerset.map (i a)),
 let q : finset B → finset (A × (finset B)) := (λ U, (col_inter E U).map (j U)),
 let Y := (@univ A _).bind p,
 let Z := (@univ (finset B) _).bind q,
 let c : A × (finset B) → ℤ := λ aU, aU.2.card_sign,
 have p_disjoint : ∀ a₀ a₁, a₀ ≠ a₁ → (p a₀) ∩ (p a₁) = ∅ := 
  λ a₀ a₁ h, by {
      apply eq_empty_of_forall_not_mem,rintros ⟨a,U⟩ h',
      rw[mem_inter,mem_incl,mem_incl] at h',
      exact h (h'.1.1.symm.trans h'.2.1),},
 have q_disjoint : ∀ U₀ U₁, U₀ ≠ U₁ → (q U₀) ∩ (q U₁) = ∅ := 
  λ U₀ U₁ h, by {
      apply eq_empty_of_forall_not_mem,rintros ⟨a,U⟩ h',
      rw[mem_inter,mem_incr,mem_incr] at h',
      exact h (h'.1.2.symm.trans h'.2.2),
  },
 have e : Y = Z := begin
  ext ⟨a,U⟩,
  split,
  {intro hY,rcases finset.mem_bind_univ.mp hY with ⟨a',hY'⟩,
   have ea : a = a'  := (mem_incl.mp hY').left,
   let hU : U ⊆ row E a' := mem_powerset.mp (mem_incl.mp hY').right,
   rw[← ea] at hU,
   apply finset.mem_bind_univ.mpr,use U,
   let haU : a ∈ col_inter E U := (mem_col_inter E U a).mpr
     (λ b hb, (mem_col E b).mpr ((mem_row E a).mp (hU hb))),
   apply mem_map.mpr,use a,use haU,refl,
  },
  {intro hZ,rcases finset.mem_bind_univ.mp hZ with ⟨U',hU'⟩,
   have eU : U = U' := (mem_incr.mp hU').right,
   let ha : a ∈ col_inter E U' := (mem_incr.mp hU').left,
   rw[← eU] at ha,
   let ha' := (mem_col_inter E U a).mp ha,
   have hU'' : U ∈ (row E a).powerset := begin 
    rw[mem_powerset],intros b b_in_U,exact (mem_row_col E).mpr (ha' b b_in_U),
   end, 
   apply finset.mem_bind_univ.mpr,use a,
   apply mem_incl.mpr,
   exact ⟨rfl,hU''⟩,
   }
 end,
 let Y_sum : Y.sum c = (@univ A _).sum (λ a, (p a).sum c) := 
  sum_bind (λ a₀ _ a₁ _ h, p_disjoint a₀ a₁ h),
 let Z_sum : Z.sum c = (@univ (finset B) _).sum (λ U, (q U).sum c) := 
  sum_bind (λ U₀ _ U₁ _ h, q_disjoint U₀ U₁ h),
 have p_sum : ∀ a, (p a).sum c = if (row E a) = ∅ then 1 else 0 := 
 λ a, begin 
  let h := card_sign_sum_eq (row E a),
  dsimp[card_sign_sum] at h,
  dsimp[p],rw[sum_map,← h],congr,
 end,
 let A₀ := clear_rows E,
 let A₁ := univ \ A₀,
 have p_sum₀ : ∀ a, a ∈ A₀ → (p a).sum c = 1 := λ a ha, 
  begin 
   let h := p_sum a,
   rw[if_pos (finset.mem_univ_filter.mp ha)] at h,
   exact h,
  end,
 have p_sum₁ : ∀ a, a ∈ A₁ → (p a).sum c = 0 := λ a ha, 
  begin 
   let h := p_sum a,
   let ha' :=
    (mem_sdiff.mp ha).right ∘ finset.mem_univ_filter.mpr,
   rw[if_neg ha'] at h,
   exact h,
  end,
 let Y_sum' := calc
  Y.sum c = univ.sum (λ a, (p a).sum c) : Y_sum 
  ... = (A₀ ∪ A₁).sum (λ a, (p a).sum c) : 
        by rw[union_sdiff_of_subset (subset_univ A₀)]
  ... = A₀.sum (λ a, (p a).sum c) + A₁.sum (λ a, (p a).sum c) :
         by rw[sum_union (inter_sdiff_self _ _)] 
  ... = A₀.sum (λ a, 1) + A₁.sum (λ a, 0) : 
         by rw[sum_congr rfl p_sum₀, sum_congr rfl p_sum₁]
  ... = A₀.sum (λ a, 1) : by rw[sum_const_zero,add_zero]
  ... = add_monoid.smul A₀.card 1 : by rw[sum_const]
  ... = A₀.card : by simp only[add_monoid.smul_one,int.nat_cast_eq_coe_nat]
   ,
 have q_sum : ∀ U, (q U).sum c = (card_sign U) * (card (col_inter E U)) := 
  λ U,begin 
   dsimp[q],
   have : (λ a, c ((j U) a)) = (λ a, card_sign U) := by {ext,refl},
   rw[sum_map,this,sum_const,add_monoid.smul_eq_mul',int.nat_cast_eq_coe_nat],
  end,
 exact calc
  ((clear_rows E).card : ℤ) = Y.sum c : Y_sum'.symm
  ... = Z.sum c : by rw[e]
  ... = univ.sum (λ U, (q U).sum c) : Z_sum
  ... = univ.sum (λ U, (card_sign U) * (card (col_inter E U))) : 
         by {congr, ext, rw[q_sum]}
end

end matching
end combinatorics