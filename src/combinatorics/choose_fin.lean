/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

In this file we give an equivalence from lists in ℕ with no 
duplicates to arbitrary lists in ℕ.  

-/

import combinatorics.choose combinatorics.simplicial

open combinatorics
open simplicial.infinite

namespace natlist

/- The map `spread` converts arbitrary lists to nonduplicating 
   lists, by moving the later entries upwards so that they 
   cannot conflict with the earlier ones.  It uses the map 
   `δ` from the `simplicial.infinite` namespace. 
-/
def spread : list ℕ → list ℕ 
| [] := []
| (i :: l) := i :: ((spread l).map (δ i))

/- The map `squash` converts nonduplicating lists to arbitrary
   lists by moving later entries downwards to eliminate the 
   gaps forced by the nonduplicating property.  It uses the 
   map `σ` from the `simplicial.infinite` namespace. Although
   `squash` is designed to be used on nonduplicating lists, it
   is convenient to give the definition in a form that does not
   rely on that property.
-/
def squash : ∀ (l : list ℕ ), list ℕ 
| [] := []
| (i :: l) := i :: squash (l.map (simplicial.infinite.σ i.pred))
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩],
  dec_tac := well_founded_tactics.default_dec_tac }

@[simp] lemma squash.nil : squash [] = [] := by simp[squash]

@[simp] lemma squash.cons (i : ℕ) (l : list ℕ) : 
  squash (i :: l)  = i :: (squash (l.map (σ i.pred))) := by simp[squash]

lemma spread.nodup (l : list ℕ) : (spread l).nodup := 
begin
  induction l with i l ih,
  { exact list.nodup_nil },
  { rw [spread, list.nodup_cons], split,
    { intro h, rcases list.mem_map.mp h with ⟨j,⟨hm,he⟩⟩, exact δ_ne i j he },
    { exact list.nodup_map (δ_inj i) ih } }
end

@[simp] lemma spread.length (l : list ℕ) : (spread l).length = l.length :=
begin
  induction l with i l ih,
  { refl },
  { rw [spread, list.length_cons, list.length_cons, list.length_map, ih] }
end

@[simp] lemma squash.length : ∀ (l : list ℕ), (squash l).length = l.length
| [] := by simp[squash]
| (i :: l) := 
begin
  rw [squash.cons, list.length_cons, squash.length, list.length_map, list.length_cons]
end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩],
  dec_tac := well_founded_tactics.default_dec_tac }

lemma squash_spread : ∀ (l : list ℕ), squash (spread l) = l
| [] := by simp[squash,spread]
| (i :: l) :=
  by { rw [spread, squash.cons, list.map_map, σδ_pred, list.map_id, squash_spread] }

lemma spread_squash : ∀ {l : list ℕ} (hl : l.nodup), spread (squash l) = l
| [] _ := by simp[squash,spread]
| (i :: l) hl := begin
  rw [list.nodup_cons] at hl,
  let m := l.map (σ i.pred),
  have hm : m.nodup := σ_pred_nodup hl.right hl.left,
  rw [squash.cons, spread, spread_squash hm],
  congr' 1, dsimp[m], rw [list.map_map],
  let p : ℕ → ℕ := (δ i) ∘ (σ i.pred), change l.map p = l,
  have hp : ∀ (k : ℕ) (hk : k ≠ i), p k = k := 
    λ k hk, simplicial.infinite.δσ_pred hk,
  have : l.map p = l.map id := 
  begin
    apply list.map_congr, intros k hk, 
    have : k ≠ i := λ h, hl.left (h ▸ hk),
    exact δσ_pred this
  end,
  rw [this, list.map_id],
end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, list.length x.1)⟩],
  dec_tac := well_founded_tactics.default_dec_tac }

def spread_equiv : list ℕ ≃ { l : list ℕ // l.nodup } := {
  to_fun := λ l, ⟨spread l, spread.nodup l⟩,
  inv_fun := λ l, squash l.val,
  left_inv := λ l, squash_spread l,
  right_inv := λ l, subtype.eq (spread_squash l.property) }

/- We now prove upper bounds for the entries in the lists 
   `spread l` and `squash l`.  This will enable us to define
   functions related to `spread` and `squash` using `fin n`
   instead of `ℕ`.   Everything is formulated in terms of the
   predicates `below_line n l` and `below_triangle n l` for
   `l : list ℕ`.  The first of these says that all entries 
   of `l` are less than `n`, and the second says that the `i`th
   entry is less than `n - i`. 
-/

def below_line : ∀ (n : ℕ) (l : list ℕ), Prop 
| n [] := true
| n (i :: l) := i < n ∧ below_line n l

def below_triangle : ∀ (n : ℕ) (l : list ℕ), Prop
| 0 [] := true
| 0 (i :: l) := false
| (n + 1) [] := true
| (n + 1) (i :: l) := i < n + 1 ∧ below_triangle n l

lemma below_line.iff {n : ℕ} {l : list ℕ} : 
  below_line n l ↔ ∀ j, j ∈ l → j < n := 
begin
  split; induction l with i l ih,
  { intros h j hj, exfalso, exact list.not_mem_nil j hj },
  { intros h j hj, rw [below_line] at h, 
    rcases ((list.mem_cons_iff _ _ _).mp hj) with ⟨⟨_⟩|hj'⟩,
    { exact h.1 },
    { exact ih h.2 j (by assumption) } },
  { intro h, exact true.intro },
  { intro h, dsimp [below_line], split,
    { exact h i (l.mem_cons_self i) },
    { apply ih, intros j hj, exact h j (list.mem_cons_of_mem i hj) } }
end

lemma below_line.δ (i : ℕ) {n : ℕ} {l : list ℕ} (h : below_line n l ) : 
  below_line (n + 1) (l.map (simplicial.infinite.δ i)) := 
begin
  rw [below_line.iff] at h ⊢, 
  intros k hk,
  rcases list.mem_map.mp hk with ⟨j,⟨hm,he⟩⟩,
  rw [← he], 
  exact lt_of_le_of_lt (simplicial.infinite.δ_bound' i j).2
                       (nat.succ_lt_succ (h j hm))
end

lemma below_line.σ {i n : ℕ} {l : list ℕ} 
  (hi : i < n) (hl : below_line (n + 1) l) : 
    (below_line n (l.map (simplicial.infinite.σ i))) := 
begin
  rw [below_line.iff] at hl ⊢,
  intros k hk,
  rcases list.mem_map.mp hk with ⟨j,⟨hm,he⟩⟩,
  rw [← he],
  exact simplicial.infinite.σ_bound hi (hl j hm)
end

lemma below_line.of_fin {n : ℕ} (l : list (fin n)) : below_line n (l.map coe) := 
below_line.iff.mpr $ (λ j hj, begin 
 rcases list.mem_map.mp hj with ⟨i,⟨hm,he⟩⟩, rw [← he], exact i.is_lt
end)

lemma below_triangle.nil (n : ℕ) : below_triangle n [] := 
by { cases n; trivial }

lemma spread.below : ∀ {n : ℕ} {l : list ℕ} (hb : below_triangle n l),
  below_line n (spread l)
| n [] h := by {  simp only [spread, below_line] }
| 0 (i :: l) hb := false.elim hb
| (n + 1) (i :: l) hb := 
begin
  dsimp[below_triangle] at hb,
  split,
  { exact hb.1 },
  { exact below_line.δ i (spread.below hb.2) }
end

lemma squash.below : ∀ {n : ℕ} {l : list ℕ}
  (hb : below_line n l) (hn : l.nodup), 
  below_triangle n (squash l)
| 0 [] hb hn := by { simp only [squash, below_triangle] }
| (n + 1) [] hb hn := by { simp only [squash, below_triangle] }
| 0 (i :: l) hb hn := false.elim (nat.not_lt_zero i hb.1)
| (n + 1) (i :: l) hb hn := 
begin
  dsimp [below_line] at hb,
  rw [squash.cons, below_triangle],
  split, { exact hb.1 },
  rw [list.nodup_cons] at hn,
  apply squash.below _ (σ_pred_nodup hn.right hn.left),
  by_cases hb' : i < n,
  { rw [below_line.iff] at hb ⊢, 
      intros j hj,
      rcases list.mem_map.mp hj with ⟨j',hj'⟩,
      have hj'' := hb.right j' hj'.left,
      exact hj'.right ▸ (σ_bound (lt_of_le_of_lt i.pred_le hb') hj'') },
  { have : i = n := le_antisymm (nat.le_of_lt_succ hb.left) (le_of_not_gt hb'),
    cases this,
    rw [below_line.iff] at hb ⊢, 
    intros j hj,
    rcases list.mem_map.mp hj with ⟨j',⟨hm',he'⟩⟩,
    have hj' : j' ≤ n := nat.le_of_lt_succ (hb.right j' hm'),
    by_cases hjn : j' = n,
    { exfalso, exact hn.left (hjn ▸ hm') },
    { rw [← he'],
      exact lt_of_le_of_lt (σ_le n.pred j') (lt_of_le_of_ne hj' hjn) } }
end

end natlist

/- `fin_falling` is an inductive type defined in the most obvious 
   way to ensure that `fin_falling n k` has size `falling n k` 
   (where `falling n k` is n (n - 1) (n - 2) ... (n - k + 1) ) 
-/
@[derive decidable_eq]
inductive fin_falling : ∀ (n : ℕ), Type 
| nil (n : ℕ) : fin_falling n
| cons {n : ℕ} (i : fin (n + 1)) (l : fin_falling n) : fin_falling (n + 1)

namespace fin_falling

def length : ∀ {n : ℕ} (l : fin_falling n), ℕ := 
 @fin_falling.rec (λ n l, ℕ) (λ n, 0) (λ n i l k, k + 1)

@[simp] lemma length.nil (n : ℕ) : (fin_falling.nil n).length = 0 := rfl

@[simp] lemma length.cons {n : ℕ} (i : fin (n + 1)) (l : fin_falling n) : 
  (fin_falling.cons i l).length = l.length + 1 := rfl

/- We will define three different functions that convert an element 
   `l : fin_falling n k` to a list.  
   * `to_list l` will be a nonduplicating list in `fin n`
   * `to_spread_list l` will be a nonduplicating list in `ℕ`, and will
     be the same as `(to_list l).map fin.val`
   * `to_squash_list l` will be a list in `ℕ`, and will be the same as
     `natlist.squash (to_spread_list l)`.
-/

def to_squash_list : ∀ { n : ℕ } (l : fin_falling n), list ℕ := 
 @fin_falling.rec (λ n l, list ℕ) (λ n, list.nil)
   (λ n i l ih, i :: ih)

lemma to_squash_list.nil (n : ℕ) : to_squash_list (fin_falling.nil n) = [] := rfl

lemma to_squash_list.cons {n : ℕ} (i : fin (n + 1)) (l : fin_falling n) : 
  to_squash_list (fin_falling.cons i l) = i :: (to_squash_list l) := rfl

lemma to_squash_list.length : ∀ {n : ℕ} (l : fin_falling n), l.to_squash_list.length = l.length 
| _ (fin_falling.nil n) := 
  by { rw[to_squash_list.nil, list.length, length.nil] }
| n (fin_falling.cons i l) := 
  by { rw[to_squash_list.cons, list.length, to_squash_list.length l, length.cons] }

lemma to_squash_list.below : ∀ {n : ℕ} (l : fin_falling n),
  natlist.below_triangle n l.to_squash_list
| _ (fin_falling.nil n) := natlist.below_triangle.nil n
| n (fin_falling.cons i l) := and.intro i.is_lt (to_squash_list.below l)

def to_spread_list : ∀ { n : ℕ } (l : fin_falling n), list ℕ := 
 @fin_falling.rec (λ n l, list ℕ) (λ n, list.nil)
   (λ n i l ih, i :: (ih.map (simplicial.infinite.δ i)))

lemma to_spread_list.nil (n : ℕ) : to_spread_list (fin_falling.nil n) = [] := rfl

lemma to_spread_list.cons {n : ℕ} (i : fin (n + 1)) (l : fin_falling n) : 
  to_spread_list (fin_falling.cons i l) = 
    i :: ((to_spread_list l).map (simplicial.infinite.δ i)) := rfl

lemma to_spread_list.length : ∀ {n : ℕ} (l : fin_falling n),
  (to_spread_list l).length = l.length 
| _ (fin_falling.nil n) := 
  by { rw[to_spread_list.nil, list.length, length.nil] }
| n (fin_falling.cons i l) := 
  by { rw[to_spread_list.cons, list.length, list.length_map, 
          to_spread_list.length l, length.cons] }

lemma to_spread_list.below : ∀ {n : ℕ} (l : fin_falling n),
  natlist.below_line n l.to_spread_list
| _ (fin_falling.nil n) := true.intro
| n (fin_falling.cons i l) := 
begin
  rw [to_spread_list.cons, natlist.below_line],
  split, exact i.is_lt,
  have h := to_spread_list.below l,
  rw [natlist.below_line.iff] at h ⊢, 
  intros j hj,
  rcases list.mem_map.mp hj with ⟨j₀,⟨hm,he⟩⟩,
  exact he ▸ (lt_of_le_of_lt (δ_bound' i j₀).right (nat.succ_lt_succ (h j₀ hm))), 
end

lemma spread_squash : ∀ {n : ℕ } (l : fin_falling n),
  natlist.spread l.to_squash_list = l.to_spread_list 
| _ (fin_falling.nil n) := rfl
| n (fin_falling.cons i l) := 
by { rw [to_squash_list.cons, to_spread_list.cons, natlist.spread, spread_squash] }

lemma to_spread_list.nodup {n : ℕ } (l : fin_falling n) :
  l.to_spread_list.nodup := 
by { rw[← l.spread_squash], exact natlist.spread.nodup _ }

lemma squash_spread {n : ℕ} (l : fin_falling n) :
  natlist.squash l.to_spread_list = l.to_squash_list := 
by { rw [← spread_squash l, natlist.squash_spread] }

def to_list : ∀ { n : ℕ } (l : fin_falling n), list (fin n) :=
 @fin_falling.rec (λ n l, list (fin n)) (λ n, list.nil)
  (λ n i l ih, i :: (ih.map (simplicial.δ i)))

lemma to_list.nil (n : ℕ) : to_list (fin_falling.nil n) = [] := rfl

lemma to_list.cons {n : ℕ} (i : fin (n + 1)) (l : fin_falling n) : 
  to_list (fin_falling.cons i l) = i :: (to_list l).map (simplicial.δ i) := rfl

lemma to_list.length : ∀ {n : ℕ} (l : fin_falling n), (to_list l).length = l.length
| _ (fin_falling.nil n) := 
  by { rw[to_list.nil, list.length, length.nil] }
| n (fin_falling.cons i l) := 
  by { rw[to_list.cons, list.length, list.length_map, to_list.length l, length.cons] }

lemma to_list.nodup : ∀ {n : ℕ} (l : fin_falling n), (to_list l).nodup
| _ (fin_falling.nil n) := list.nodup_nil
| n (fin_falling.cons i l) := 
begin
  rw [to_list.cons, list.nodup_cons], split,
  { rw [list.mem_map],
    rintro ⟨k,⟨hm,he⟩⟩, exact simplicial.δ_ne _ _ he, },
  { exact list.nodup_map (simplicial.δ_inj i) (to_list.nodup l) }
end

lemma to_list.val : ∀ {n : ℕ} (l : fin_falling n), 
  (to_list l).map (coe : fin n → ℕ) = to_spread_list l 
| _ (fin_falling.nil n) := rfl
| n (fin_falling.cons i l) := 
begin
  rw [to_list.cons, to_spread_list.cons, list.map_cons, list.map_map],
  have : (coe : (fin _) → ℕ) ∘ (simplicial.δ i) = (δ i) ∘ coe := 
  begin ext j, simp only [function.comp_app, simplicial.δ_infinite] end,
  rw [this, ← list.map_map, to_list.val]
end

def of_squash_list : ∀ {n : ℕ} (l : list ℕ)
  (hb : natlist.below_triangle n l), fin_falling n
| n [] hb := fin_falling.nil n
| 0 (i :: l) hb := false.elim hb
| (n + 1) (i :: l) hb := 
    fin_falling.cons ⟨i,hb.left⟩ (of_squash_list l hb.right)

lemma of_squash_list.nil (n : ℕ) (hb : natlist.below_triangle n []) : 
  of_squash_list [] hb = fin_falling.nil n := by { cases n; refl }

lemma of_squash_list.length : ∀ {n : ℕ} (l : list ℕ)
  (hb : natlist.below_triangle n l), (of_squash_list l hb).length = l.length
| n [] hb := by { cases n; refl }
| 0 (i :: l) hb := false.elim hb
| (n + 1) (i :: l) hb :=
  by { rw [of_squash_list, length.cons, list.length_cons, of_squash_list.length] }

def of_spread_list {n : ℕ} (l : list ℕ) (hn : l.nodup) (hb : natlist.below_line n l) :
 fin_falling n := of_squash_list (natlist.squash l) (natlist.squash.below hb hn)

lemma of_spread_list.length {n : ℕ} (l : list ℕ)
  (hn : l.nodup) (hb : natlist.below_line n l) : 
  (of_spread_list l hn hb).length = l.length := 
by { rw [of_spread_list, of_squash_list.length, natlist.squash.length] }

def of_list {n : ℕ} (l : list (fin n)) (hn : l.nodup) : fin_falling n :=
 of_spread_list (l.map coe) 
  (list.nodup_map (λ _ _ e, subtype.val_injective e) hn) (natlist.below_line.of_fin l)

lemma of_list.length {n : ℕ} (l : list (fin n)) (hn : l.nodup) :
  (of_list l hn).length = l.length := 
by { rw [of_list, of_spread_list.length, list.length_map] }

lemma to_of_squash_list : ∀ {n : ℕ} {l : list ℕ} (hb : natlist.below_triangle n l),
 to_squash_list (of_squash_list l hb) = l 
| n [] hb := by { cases n; refl }
| 0 (i :: l) hb := false.elim hb
| (n + 1) (i :: l) hb := 
  by { rw [of_squash_list, to_squash_list.cons, to_of_squash_list], refl }

lemma of_to_squash_list_aux : ∀ {n : ℕ} (l : fin_falling n) (h),
 of_squash_list (to_squash_list l) h = l := 
begin
  intros n l,
  induction l with n₀ n₁ i l ih, 
  { rw [to_squash_list.nil], intro h, rw [of_squash_list.nil] },
  { rw [to_squash_list.cons], intro h, rw [of_squash_list, ih], congr' 1,
    exact fin.coe_inj rfl }
end

lemma of_to_squash_list {n : ℕ} (l : fin_falling n) :
 of_squash_list (to_squash_list l) (to_squash_list.below l) = l := 
of_to_squash_list_aux l _

lemma to_of_spread_list {n : ℕ} {l : list ℕ} (hn : l.nodup) (hb : natlist.below_line n l) :
 to_spread_list (of_spread_list l hn hb) = l := 
by { rw [of_spread_list, ← spread_squash, to_of_squash_list, natlist.spread_squash hn] }

lemma of_to_spread_list_aux {n : ℕ} (l : fin_falling n) (hn) (hb):
 of_spread_list (to_spread_list l) hn hb = l := 
begin
  dsimp [of_spread_list], 
  have : ∀ {l₀ l₁ : list ℕ} (e : l₀ = l₁) (h₁ : natlist.below_triangle n l₁), 
           (of_squash_list l₀ (by { rw[e], exact h₁})) = (of_squash_list l₁ h₁) := 
  by { intros, cases e, refl },
  rw [this (squash_spread l) (to_squash_list.below l), of_to_squash_list_aux]
end

lemma to_of_list {n : ℕ} (l : list (fin n)) (hn : l.nodup): 
  to_list (of_list l hn) = l := 
begin
  apply list.map_injective_iff.mpr (@fin.coe_inj n),
  rw [to_list.val, of_list, to_of_spread_list]
end

lemma of_to_list {n : ℕ} (l : fin_falling n) : 
  of_list (to_list l) (to_list.nodup l) = l := 
begin
  rw [of_list],
  have : ∀ {l₀ l₁ : list ℕ} (e : l₀ = l₁) 
           (hn : l₁.nodup) (hb : natlist.below_line n l₁), 
           (of_spread_list l₀ (by { rw[e], exact hn}) (by { rw[e], exact hb})) =
             (of_spread_list l₁ hn hb) := 
  by { intros, cases e, refl },
  rw [this (to_list.val l) (to_spread_list.nodup l) (to_spread_list.below l)],
  apply of_to_spread_list_aux
end

def ordered_subset_equiv (n k : ℕ) : 
  { l : fin_falling n // l.length = k } ≃ ordered_subset (fin n) k := 
{ to_fun := λ l, ⟨fin_falling.to_list l,
                  ⟨(to_list.length l.val).trans l.property, to_list.nodup l.val⟩⟩,
  inv_fun := λ l, ⟨fin_falling.of_list l.val l.property.2, 
                   (of_list.length l.val l.property.2).trans l.property.1⟩,
  left_inv := λ l, subtype.eq (of_to_list l),
  right_inv := λ l, subtype.eq (to_of_list l.val _) }

end fin_falling

