/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

-/

import data.vector data.list.sort data.fintype.basic algebra.big_operators
import data.fin_extra order.sort_rank data.heq_extra data.enumeration 
import combinatorics.partition.basic combinatorics.stirling

/-
 Elsewhere, we have defined a type (partition α) for any finite 
 type α, representing the set of partitions of α.  In particular,
 for any natural number n we have a finite type (fin n) of numbers
 less than n, and thus a type (partition (fin n)) of partitions.  
 From this, we can extract a subtype of partitions of rank r 
 (where the rank is defined to be the number of blocks).
 However, this is defined in a way that is not well-designed for
 efficient computation. The aim of this file is to define an equivalent
 type (fin_map n r) that has better computational properties.
 
 Specifically, an element of (fin_map n r) is essentially 
 a structure consisting of maps b : (fin n) → (fin r) and 
 t : (fin r) → (fin n) and proofs of three properties: that b ∘ t is 
 the identity, that t ∘ b is everywhere greater than or equal to 
 the identity, and that t is strictly increasing.  Given any such 
 pair, we can partition (fin n) using the fibres of the map b.  It 
 is not hard to see that each partition of rank r arises from a
 unique pair (b,t) in this way.  

 The word "essentially" in the above paragraph covers the following 
 technicality.  For any type α, maps (fin k) → α biject in an obvious
 way with lists in α of length k.  Such lists can be considered as
 elements of the subtype (vector α k).  Lists and vectors are standard
 data structures that can be represented efficiently in the Lean 
 virtual machine, especially when the entries are just natural numbers.  
 For this reason, in the definition of (fin_map n r), we
 encode b and t as vectors rather than functions.
-/

namespace combinatorics.partition
open fin fintype combinatorics combinatorics.partition

section block_max

variables {n : ℕ} {p : partition (fin n)} 

/-
 As a basic ingredient of all the constructions in this file, we need
 to order the blocks of a given partition by declaring that b < c
 iff (largest element of b) < (largest element of c), and we need to
 sort the set of blocks according to this order.
-/

/-
 We start with a function that extracts the largest element of each 
 block.  For this to make sense we need to know that each block is
 nonempty; this is proved by the lemma block_not_empty from 
 partition.lean.

 I am not sure why Lean thinks this is noncomputable
-/
noncomputable def block_max (b : p.block_type) : fin n := 
 (finset_largest_element b.val (block_not_empty b.property)).val

/-
 This defines a lemma showing that (block_max b) has the expected
 defining properties (it lies in b and is maximal subject to that).
-/
def block_max_spec (b : p.block_type) :=
 (finset_largest_element b.val (block_not_empty b.property)).property

/-
 The block containing (block_max b) is just b.
-/
lemma block_max_block (b : p.block_type) :
 b = p.block_alt (block_max b) := 
  block_eq_of_mem (block_max_spec b).left

variable (p)

/-
 We now define our order on the set of blocks, packaging it as an 
 instance of the linear_order typeclass.
-/
noncomputable instance block_order : linear_order p.block_type := {
 le := λ b c ,(block_max b) ≤ (block_max c),
 lt := λ b c ,(block_max b) < (block_max c),
 lt_iff_le_not_le := λ b c, @lt_iff_le_not_le (fin n) _ (block_max b) (block_max c),
 le_refl := λ b,le_refl (block_max b),
 le_trans := λ (a b c : p.block_type) 
   (a_le_b : block_max a ≤ block_max b) 
   (b_le_c : block_max b ≤ block_max c),
    le_trans a_le_b b_le_c,
 le_antisymm := λ (a b : p.block_type)
   (a_le_b : block_max a ≤ block_max b) 
   (b_le_a : block_max b ≤ block_max a),
   begin
    have s_eq_s : block_max a = block_max b :=
     le_antisymm a_le_b b_le_a,
    exact
     ((block_max_block a).trans
      (congr_arg p.block_alt s_eq_s)).trans
     (block_max_block b).symm,
   end,
 le_total := λ (a b : p.block_type),
   le_total (block_max a) (block_max b),
 decidable_le := λ b c, fin.decidable_le (block_max b) (block_max c) 
}

/-
 If the number of blocks is r, then the following function returns the
 unique order-equivalence from the set of blocks to (fin r).
-/
noncomputable def block_rank_equiv {r : ℕ} (p_rank : p.rank = r) := 
 fintype.rank_equiv ((block_type_card p).trans p_rank)

end block_max

/-
 We now define the type (fin_map n r).  The elements are 
 structures with data fields block and top, together with three 
 propositional fields (which will be ignored in compiled code for
 the Lean virtual machine).  The block field is a vector of length
 n with entries in (fin r).  This gives rise to a map
 (fin n) → (fin r), which is called block.nth in Lean notation.
 Similarly, the top field is a vector of length r with entries in 
 (fin n), corresponding to a map top.nth : (fin r) → (fin n).
-/
structure fin_map (n r : ℕ) :=
(block : vector (fin r) n)
(top : vector (fin n) r)
(block_top : ∀ j, block.nth (top.nth j) = j)
(top_block : ∀ i, top.nth (block.nth i) ≥ i)
(top_mono : ∀ j1 j2, j1 < j2 → top.nth j1 < top.nth j2)

/- -------------------------------------------------------------- -/
/- -------------------------------------------------------------- -/
/- -------------------------------------------------------------- -/
/- -------------------------------------------------------------- -/

namespace fin_map 
open fin_map

def tot (n : ℕ) := Σ (r : ℕ), fin_map n r

def to_tot {n r : ℕ} (p : fin_map n r) : tot n := ⟨r,p⟩ 

variables {n r : ℕ}

/-
 The next definition tells Lean how to convert a term of type 
 `(fin_map n r)` to a string, for display to the user.
 Lean already knows how to display terms of type `(fin r)`, and
 also knows a rule for how to display lists if it already knows
 how to display each entry.  If `p` is of type 
 `(fin_map n r)` then `p.block` is a vector and so 
 `p.block.val` is a list.  We tell Lean to use the string
 representation of `p.block.val` as a representation for `p`
 itself.  (Lemma `eq_of_block_eq` below will verify that 
 `p.block.val` determines all of `p`.)
-/
instance (n r : ℕ) : has_repr (fin_map n r) := 
 ⟨λ p, repr p.block.val⟩ 

/-
 One of our axioms is that the map top : (fin r) → (fin n) should 
 preserve strict inequalities.  We now prove the obvious consequence
 that it also preserves weak inequalities.
-/
lemma top_mono_weak (p : fin_map n r) (j1 j2 : fin r) :
 j1 ≤ j2 → p.top.nth j1 ≤ p.top.nth j2 := 
begin
 by_cases e : j1 = j2,
 {rw[e],intro,exact le_refl _,},
 {intro j1_le_j2,
  exact le_of_lt (p.top_mono j1 j2 (lt_of_le_of_ne j1_le_j2 e)),
 }
end

lemma top_mono_iff (p : fin_map n r) (j1 j2 : fin r) :
 j1 < j2 ↔ p.top.nth j1 < p.top.nth j2 := 
begin
 split,
 {exact top_mono p j1 j2},
 {intro top_lt,
  by_cases h : j1 < j2,
  {exact h},
  {exfalso,
   let top_ge := top_mono_weak p j2 j1 (le_of_not_lt h),
   exact not_lt_of_ge top_ge top_lt,
  }
 }
end

@[ext]
lemma eq_of_block_eq (p1 p2 : fin_map n r)
 (e_block : ∀ i, p1.block.nth i = p2.block.nth i) : p1 = p2 := 
begin
 rcases p1,
 rcases p2,
 simp at e_block,
 have e_block1 : p1_block = p2_block := vector.ext e_block,
 have e_top : ∀ j, p1_top.nth j = p2_top.nth j := 
 begin
  intro j,
  let h0 := (congr_arg p1_top.nth ((e_block (p2_top.nth j)).trans
             (p2_block_top j))).subst (p1_top_block (p2_top.nth j)),
  let h1 := (congr_arg p2_top.nth ((e_block (p1_top.nth j)).symm.trans 
             (p1_block_top j))).subst (p2_top_block (p1_top.nth j)),
  exact le_antisymm h1 h0,
 end,
 have e_top1 : p1_top = p2_top := vector.ext e_top,
 simp[e_block1,e_top1],
end

/-
 This function converts an element of (fin_map n r) to
 the corresponding partition of the set (fin n).
-/
def to_partition (p : fin_map n r) : 
 partition (fin n) := partition.fiber_partition p.block.nth

lemma to_partition_top (p : fin_map n r) (i : fin n) :
 block_max ((to_partition p).block_alt i) =
  p.top.nth (p.block.nth i) := 
begin
 let q := to_partition p,
 let b := q.block_alt i,
 have i_in_b : i ∈ b.val := partition.mem_block _ i,
 let j := p.block.nth i,
 let i1 := p.top.nth j,
 have i_blocks0 : p.block.nth i1 = j := p.block_top j,
 have i_blocks1 : q.block_alt i1 = b :=
  (partition.fiber_partition_blocks_alt p.block.nth i1 i).mpr i_blocks0,
 have i_blocks2 : q.block i1 = b.val := partition.block_veq_of_eq i_blocks1,
 have i1_in_b : i1 ∈ b.val := i_blocks2.subst (partition.mem_block q i1),
 let m := block_max b,
 let m_in_b : m ∈ b.val := (block_max_spec b).left,
 let i1_le_m : i1 ≤ m := (block_max_spec b).right i1 i1_in_b,
 have m_block : b = q.block_alt m := partition.block_eq_of_mem m_in_b,
 let h0 := (congr_arg p.top.nth 
           ((partition.fiber_partition_blocks_alt p.block.nth i1 m).mp
            (i_blocks1.trans m_block))),
 let h1 := p.top_block m,
 let h2 := h0.symm.trans (congr_arg p.top.nth i_blocks0),
 let m_le_i1 : m ≤ i1 := h2.subst h1,
 exact le_antisymm m_le_i1 i1_le_m,
end

/-
 Given an element of (fin_map n r), the above definition
 gives us a partition of (fin n), and thus a set of blocks.  The
 next definition gives a bijection from that block set to (fin r).
 This bijection is packaged using the framework set up in the 
 standard library file data.equiv.lean, so we have a structure 
 involving maps to_fun and inv_fun together with proofs (named 
 left_inv and right_inv) that their composites are equal 
 (pointwise) to identity functions.
-/
noncomputable def to_partition_blocks (p : fin_map n r) : 
 (to_partition p).block_type ≃ fin r := 
begin
 let q := (to_partition p),
 let to_fun : q.block_type → fin r :=
  λ b, p.block.nth (block_max b),
 let inv_fun : fin r → q.block_type := 
  λ j, q.block_alt (p.top.nth j),
 have left_inv : ∀ b, inv_fun (to_fun b) = b := 
 begin
  intro b,
  let i1 := block_max b,
  let j1 := p.block.nth i1,
  let i2 := p.top.nth j1,
  let e : p.block.nth i2 = p.block.nth i1 := p.block_top j1,
  let h0 : q.block_alt i1 = q.block_alt i2 :=
   subtype.eq ((partition.fiber_partition_blocks p.block.nth i1 i2).mpr e.symm),
  let h1 : b = q.block_alt i1 := block_max_block b,
  exact (h1.trans h0).symm
 end,
 have right_inv : ∀ j, to_fun (inv_fun j) = j := 
 begin
  intro j,
  let i1 := p.top.nth j,
  let b := q.block_alt i1,
  have i1_in_b : i1 ∈ b.val := q.mem_block i1,
  let i2 := block_max b,
  let h0 := block_max_spec b,
  have i2_in_b : i2 ∈ b.val := h0.left,
  have i1_le_i2 : i1 ≤ i2 := h0.right i1 i1_in_b,
  have i2_block : q.block i1 = q.block i2 :=
   partition.block_alt_eq.mpr (block_max_block b),
  let h1 : p.block.nth i1 = p.block.nth i2 :=
    (partition.fiber_partition_blocks p.block.nth i1 i2).mp i2_block,
  let h2 : p.block.nth i1 = j := p.block_top j,
  let h3 : j = p.block.nth i2 := h2.symm.trans h1,
  let h4 : p.top.nth (p.block.nth i2) = i1 := (congr_arg p.top.nth h3).symm,
  let h5 : p.top.nth (p.block.nth i2) ≥ i2 := (p.top_block i2),
  let i1_ge_i2 : i1 ≥ i2 := h4.subst h5,
  let i1_eq_i2 := le_antisymm i1_le_i2 i1_ge_i2,
  have h6 : to_fun (inv_fun j) = p.block.nth i2 := rfl,
  exact (h6.trans (congr_arg p.block.nth i1_eq_i2.symm)).trans h2,
 end,
 exact ⟨to_fun,inv_fun,left_inv,right_inv⟩ 
end

/-
 From the above bijection it is clear that the relevant partition
 of (fin n) has rank r.
-/
lemma to_partition_rank (p : fin_map n r) : 
 (to_partition p).rank = r := 
begin
 let q := to_partition p,
 let e0 := (partition.block_type_card q).symm,
 let e1 := fintype.card_congr (to_partition_blocks p),
 let e2 := fintype.card_fin r,
 have e3 := subsingleton.elim (fin.fintype r) (@enumeration_fintype (fin r) (fin.enumeration r)), 
 rw[e3] at e2,
 simp[e0,e1,e2],
end

lemma to_partition_block_type_card (p : fin_map n r) : 
 fintype.card (to_partition p).block_type = r := 
  (partition.block_type_card (to_partition p)).trans (to_partition_rank p)

lemma to_partition_blocks_ordered (p : fin_map n r) (j1 j2 : fin r) :
 j1 < j2 ↔ (to_partition_blocks p).inv_fun j1 < (to_partition_blocks p).inv_fun j2 := 
begin
 let q := to_partition p,
 let i1 := p.top.nth j1,
 let i2 := p.top.nth j2,
 let b1 := q.block_alt i1,
 let b2 := q.block_alt i2,
 let max1 : block_max b1 = i1 :=
  (to_partition_top p i1).trans (congr_arg p.top.nth (p.block_top j1)),
 let max2 : block_max b2 = i2 :=
  (to_partition_top p i2).trans (congr_arg p.top.nth (p.block_top j2)),
 let h : j1 < j2 ↔ i1 < i2 := top_mono_iff p j1 j2,
 rw[max1.symm,max2.symm] at h,
 exact h,
end

lemma to_partition_blocks_ordered_alt (p : fin_map n r)
 (b1 b2 : (to_partition p).block_type) :
  b1 < b2 ↔ (to_partition_blocks p).to_fun b1 < (to_partition_blocks p).to_fun b2 :=
begin
 let j1 := (to_partition_blocks p).to_fun b1,
 let j2 := (to_partition_blocks p).to_fun b2,
 let h := (to_partition_blocks_ordered p j1 j2).symm,
 rw[(to_partition_blocks p).left_inv] at h,
 rw[(to_partition_blocks p).left_inv] at h,
 exact h,
end

lemma block_rank_equiv_eq (p : fin_map n r) :
 (block_rank_equiv (to_partition p) (to_partition_rank p)) = 
  (to_partition_blocks p) := 
begin
 let q := to_partition p,
 let f := block_rank_equiv q (to_partition_rank p),
 let g := to_partition_blocks p,
 let h : fin r → fin r := λ j, f.to_fun (g.inv_fun j),
 have h_mono : ∀ j1 j2, j1 < j2 → (h j1) < (h j2) := 
 begin
  intros j1 j2 j1_lt_j2,
  let r0 : g.inv_fun j1 < g.inv_fun j2 :=
   (to_partition_blocks_ordered p j1 j2).mp j1_lt_j2, 
  exact (@fintype.rank_lt q.block_type _ _ _ r
         (to_partition_block_type_card p) (g.inv_fun j1) (g.inv_fun j2)).mp r0,
 end,
 have h_id : ∀ j, h j = j := fin.rigid h_mono,
 ext b, congr' 1, 
 exact (congr_arg f.to_fun (g.left_inv b)).symm.trans (h_id (g.to_fun b)),
end

/-
 This function accepts a partition of (fin n) of rank r and 
 produces the corresponding element of (fin_map n r).
-/
noncomputable def of_partition (q : partition (fin n)) (e : q.rank = r) : 
 fin_map n r := 
begin
 let r0 := fintype.card q.block_type,
 have e0 : r0 = r := q.block_type_card.trans e,
 let f := block_rank_equiv q e,
 let block_map : fin n → fin r := λ i, f.to_fun (q.block_alt i),
 let top_map : fin r → fin n := λ j, block_max (f.inv_fun j), 
 let block_vec := vector.of_fn block_map,
 let top_vec := vector.of_fn top_map,
 have block_top : ∀ j, block_vec.nth (top_vec.nth j) = j := 
 begin
  intro j,dsimp[block_vec,top_vec],
  simp only [vector.nth_of_fn top_map,vector.nth_of_fn block_map],
  dsimp[top_map,block_map],
  let h0 := (block_max_block (f.symm j)).symm,
  rw[h0],
  exact f.right_inv j,
 end,
 have top_block : ∀ i, top_vec.nth (block_vec.nth i) ≥ i := 
 begin
  intro i,dsimp[top_vec,block_vec],
  simp only [vector.nth_of_fn top_map,vector.nth_of_fn block_map],
  dsimp[top_map,block_map],
  let h0 : f.symm (f _) = _ := f.left_inv (q.block_alt i),
  rw[h0],
  let h1 := (block_max_spec (q.block_alt i)).right i
             (partition.mem_block q i),
  exact h1,
 end,
 have top_mono : ∀ j1 j2, j1 < j2 → top_vec.nth j1 < top_vec.nth j2 := 
 begin
  intros j1 j2 j1_lt_j2,
  simp only[top_vec,vector.nth_of_fn,top_map],
  exact (@fintype.seq_lt q.block_type 
   (combinatorics.partition.block_order q) _ _ r e0 j1 j2).mp j1_lt_j2,
 end,
 exact {
   block := block_vec,
   top := top_vec,
   block_top := block_top,
   top_block := top_block,
   top_mono := top_mono
 },
end

lemma of_partition_block (q : partition (fin n)) (e : q.rank = r) (i : fin n) :
 ((of_partition q e).block.nth i) =
  ((block_rank_equiv q e).to_fun (q.block_alt i)) :=
begin
 cases e,
 simp[of_partition],
end

lemma of_partition_to_partition (p : fin_map n r) :
 of_partition (to_partition p) (to_partition_rank p) = p := 
begin
 ext i,
 simp[of_partition],
 rw[block_rank_equiv_eq p],
 dsimp[to_partition_blocks],
 rw[to_partition_top p i,p.block_top (p.block.nth i)]
end

lemma to_partition_of_partition (q : partition (fin n)) (e : q.rank = r) :
 to_partition (of_partition q e) = q := 
begin
 let p := of_partition q e,
 let r := to_partition p,
 ext i1 i2,
 let b1 := q.block_alt i1,
 let b2 := q.block_alt i2,
 let j1 := p.block.nth i1,
 let j2 := p.block.nth i2,
 have h0 : i2 ∈ r.block i1 ↔ j2 = j1 := 
 begin
  let h1 := partition.fiber_partition_blocks p.block.nth i2 i1,
  split; intro h2,
  {
    have h3 : i2 ∈ (r.block_alt i1).val := h2,
    exact h1.mp (partition.block_val_eq_of_mem h3).symm,
  },{
    exact (h1.mpr h2).subst (partition.mem_block r i2),
  }
 end,
 rw[h0],
 have h1 : i2 ∈ q.block i1 ↔ b2 = b1 := 
 begin
  split,
  {intro i2_in_b1,
   let i2_in_b1_alt : i2 ∈ b1.val := i2_in_b1,
   exact (partition.block_eq_of_mem i2_in_b1_alt).symm,
  },{
   intro b2_eq_b1,
   exact (partition.block_veq_of_eq b2_eq_b1).subst (partition.mem_block q i2),
  }
 end,
 rw[h1],
 let f := block_rank_equiv q e,
 have e1a : j1 = f.to_fun b1 := of_partition_block q e i1, 
 have e2a : j2 = f.to_fun b2 := of_partition_block q e i2,
 have e1b : b1 = f.inv_fun j1 := ((congr_arg f.inv_fun e1a).trans (f.left_inv b1)).symm, 
 have e2b : b2 = f.inv_fun j2 := ((congr_arg f.inv_fun e2a).trans (f.left_inv b2)).symm,
 split,
 {intro j1_eq_j2,rw[e1b,e2b,j1_eq_j2],},
 {intro b1_eq_b2,rw[e1a,e2a,b1_eq_b2],},
end

noncomputable def partition_equiv : (fin_map n r) ≃ { q : partition (fin n) // q.rank = r} := 
{
 to_fun := λ p, ⟨to_partition p,to_partition_rank p⟩,
 inv_fun := λ q, of_partition q.val q.property, 
 left_inv := λ p, of_partition_to_partition p,
 right_inv := begin 
  intro q,
  cases q,
  exact subtype.eq (to_partition_of_partition q_val q_property),
 end
}

noncomputable def partition_equiv_tot : tot n ≃ partition (fin n) := 
{
 to_fun := λ rp, to_partition rp.2, 
 inv_fun := λ q, ⟨q.rank,@of_partition n q.rank q rfl⟩,
 right_inv := λ q, @to_partition_of_partition n q.rank q rfl,
 left_inv := 
 begin
  intro rp,cases rp with r p,
  let q := @to_partition n r p,
  let r_eq := to_partition_rank p,
  let p_eq := of_partition_to_partition p,
  let C : ∀ (r1 : ℕ) (u1 : q.rank = r1), Prop := 
   λ r1 u1, @of_partition n q.rank q rfl == @of_partition n r1 q u1,
  let c : C q.rank rfl := by simp[C],
  simp[r_eq,p_eq],
  exact (@eq.dcases_on ℕ q.rank C r r_eq c).trans (heq_of_eq p_eq),
 end 
}

/- A convenience function for manipulating vectors. -/
def bump {p q : ℕ} (v : vector (fin p) q) : vector (fin p.succ) q.succ := 
 vector.cons (0 : fin p.succ) (vector.map fin.succ v)

/- Three obvious lemmas about vectors and the corresponding functions. -/
lemma vector.zth {α : Type*} {n : ℕ} (a : α) (v : vector α n) (h : 0 < n.succ) :
 (vector.cons a v).nth ⟨0,h⟩ = a := 
  vector.nth_cons_zero a v

lemma vector.sth {α : Type*} {n : ℕ} (a : α) (v : vector α n)
 (i0 : ℕ) (h0 : i0 < n) (h1 : i0.succ < n.succ):
 (vector.cons a v).nth ⟨i0.succ,h1⟩ = v.nth ⟨i0,h0⟩ := 
  vector.nth_cons_succ a v ⟨i0,h0⟩

lemma vector.nth_map {α β : Type*} (f : α → β) {n : ℕ} (v : vector α n) (i : fin n) :
 (vector.map f v).nth i = f (v.nth i) :=
begin
 cases v,cases i,
 dsimp[vector.map,vector.nth],
 apply list.nth_le_map
end

lemma bump.zth {p q : ℕ} (v : vector (fin p) q) : (bump v).nth 0 = 0 := 
 by { apply vector.zth }

/- 
 Suppose that p is a partition of (fin n), of rank r.  We can then 
 produce a partition of (fin (n + 1)) of rank r + 1, as follows: 
 we take 0 as a block on its own, and then shift all the blocks of p 
 up by one.  The resulting partition is called (add p).
-/
def add (p : fin_map n r) : fin_map n.succ r.succ :=
begin
 let block := bump p.block,
 let top := bump p.top,
 have block_top : ∀ j, block.nth (top.nth j) = j := 
 begin
  intro j,cases j with j_val j_is_lt,cases j_val with j0_val; dsimp[block,top,bump],
  {simp[vector.zth]},
  {
   have j0_is_lt : j0_val < r := nat.lt_of_succ_lt_succ j_is_lt,
   let j0 : fin r := ⟨j0_val,j0_is_lt⟩,
   simp [vector.sth _ _ j0_val j0_is_lt,vector.nth_map,p.block_top j0,fin.succ],
  }
 end,
 have top_block : ∀ i, top.nth (block.nth i) ≥ i := 
 begin
  intro i,cases i with i_val i_is_lt,cases i_val with i0_val; dsimp[block,top,bump],
  {simp[vector.zth]},
  {
   have i0_is_lt : i0_val < n := nat.lt_of_succ_lt_succ i_is_lt,
   let i0 : fin n := ⟨i0_val,i0_is_lt⟩,
   simp[vector.sth _ _ i0_val i0_is_lt,vector.nth_map],
   exact fin.succ_le_succ (p.top_block i0),
  }
 end,
 have top_mono : ∀ j1 j2, j1 < j2 → top.nth j1 < top.nth j2 := 
 begin
  intros j1 j2 j1_lt_j2,
  cases j2 with j2_val j2_is_lt,cases j2_val with j20_val,
  {exact false.elim (nat.not_lt_zero j1.val j1_lt_j2),},
  {have j20_is_lt : j20_val < r := nat.lt_of_succ_lt_succ j2_is_lt,
   cases j1 with j1_val j1_is_lt,cases j1_val with j10_val,
   {simp[top,bump,vector.zth,vector.sth _ _ j20_val j20_is_lt,vector.nth_map,fin.zero_lt_succ],},
   {have j10_is_lt : j10_val < r := nat.lt_of_succ_lt_succ j1_is_lt,
     simp[top,bump,
          vector.sth _ _ j10_val j10_is_lt,
          vector.sth _ _ j20_val j20_is_lt,
          vector.nth_map],
    apply p.top_mono,
    exact fin.lt_of_succ_lt_succ j1_lt_j2,
   }
  }
 end,
 exact ⟨block,top,block_top,top_block,top_mono⟩ 
end

/- 
 Suppose that p is a partition of (fin n), of rank r, and that u is
 in (fin r).  We can then produce a partition of (fin (n + 1)) of rank r, 
 as follows: we shift all the blocks of p up by one, and then add 0 as
 an extra element in the u'th block.  The resulting partition is called
 (join p u).
-/
def join (p : fin_map n r) (u : fin r) : fin_map n.succ r := 
begin
 let block := vector.cons u p.block,
 let top := vector.map fin.succ p.top,
 have block_top : ∀ j, block.nth (top.nth j) = j := 
 begin 
  intro j,dsimp[top,block],
  simp[vector.nth_map,p.block_top j],
 end,
 have top_block : ∀ i, top.nth (block.nth i) ≥ i := 
 begin
  intro i, cases i with i_val i_is_lt, cases i_val with i0_val,
  {simp[vector.zth],exact fin.zero_le _,},
  {have i0_is_lt : i0_val < n := nat.lt_of_succ_lt_succ i_is_lt,
   let h0 := fin.succ_le_succ (p.top_block ⟨i0_val,i0_is_lt⟩),
   dsimp[block,top],
   simp[vector.sth _ _ i0_val i0_is_lt,vector.nth_map],
   exact h0,
   }
 end,
 have top_mono : ∀ j1 j2, j1 < j2 → top.nth j1 < top.nth j2 := 
 begin
  intros j1 j2 j1_lt_j2,
  simp[top,vector.nth_map],
  exact p.top_mono j1 j2 j1_lt_j2
 end,
 exact ⟨block,top,block_top,top_block,top_mono⟩ 
end

def add_cond (q : fin_map n.succ r.succ) := (q.top.nth 0 = 0)

def join_cond (q : fin_map n.succ r.succ) := (q.top.nth 0 ≠ 0)

lemma add_add_cond (p : fin_map n r) :
 add_cond (add p) := 
begin
 dsimp[add_cond,add,bump],
 exact vector.zth 0 _ _,
end

lemma join_join_cond (p : fin_map n r.succ) (u : fin r.succ) :
 join_cond (join p u) := 
begin
 intro e,
 exact fin.zero_ne_succ (e.symm.trans (vector.nth_map fin.succ p.top 0)),
end

/-
 Let q be a partition of (fin (n + 1)), with rank r + 1.  Suppose also 
 that the map q.top.nth : (fin (r + 1)) → (fin (n + 1)) sends 0 to 0.
 It is then not hard to see that there is a unique p in
 (fin_map n r) with (add p) = q.  The present function produces 
 this p.
-/
def add_res (q : fin_map n.succ r.succ) (e : add_cond q) :
 {p : fin_map n r // q = add p} := 
begin
 let block_map_aux : ∀ (i0 : fin n), { j0 : fin r // j0.succ = q.block.nth i0.succ } := 
 begin
  dsimp[add_cond] at e,
  intro i0,
  let j := q.block.nth i0.succ,
  by_cases e1 : j = 0,
  {exfalso,
   let h0 : i0.succ ≤ q.top.nth j := q.top_block i0.succ,
   let h1 : 0 < q.top.nth j :=
    @lt_of_lt_of_le (fin n.succ) _ 0 i0.succ _ fin.zero_lt_succ h0,
    rw[e1,e] at h1,exact fin.not_lt_zero (0 : fin n.succ) h1,
  },{
   exact ⟨ fin.pred j e1, fin.succ_pred j e1⟩,
  }
 end,
 let block_map := λ i0, (block_map_aux i0).val,
 let block_map_spec : ∀ i0, (block_map i0).succ = q.block.nth i0.succ := 
  λ i0,(block_map_aux i0).property,
 let top_map_aux : ∀ (j0 : fin r), { i0 : fin n // i0.succ = q.top.nth j0.succ }:= 
 begin
  dsimp[add_cond] at e,
  intro j0,
  let i := q.top.nth j0.succ,
  let e1 := (ne_of_lt (q.top_mono 0 j0.succ fin.zero_lt_succ)).symm,
  rw[e] at e1,
  exact ⟨fin.pred i e1, fin.succ_pred i e1⟩
 end,
 let top_map := λ j0, (top_map_aux j0).val,
 let top_map_spec : ∀ j0, (top_map j0).succ = q.top.nth j0.succ := 
  λ j0,(top_map_aux j0).property,
 let block_vec := vector.of_fn block_map,
 let top_vec := vector.of_fn top_map,
 have block_top : ∀ j0, block_vec.nth (top_vec.nth j0) = j0 := 
 begin
  intro j0,
  dsimp[block_vec,top_vec],
  simp[vector.nth_of_fn],
  apply fin.succ_inj.mp,
  let h0 := block_map_spec (top_map j0),
  let h1 := congr_arg q.block.nth (top_map_spec j0),
  let h2 := q.block_top j0.succ,
  let h3 := h0.trans (h1.trans h2),
  exact h3,
 end,
 have top_block : ∀ i0, top_vec.nth (block_vec.nth i0) ≥ i0 := 
 begin
  intro i0,
  dsimp[block_vec,top_vec],
  simp[vector.nth_of_fn],
  apply fin.le_of_succ_le_succ,
  let h0 := top_map_spec (block_map i0),
  let h1 := congr_arg q.top.nth (block_map_spec i0),
  let h2 : i0.succ ≤ q.top.nth (q.block.nth i0.succ) := (q.top_block i0.succ),
  let h3 := (h0.trans h1).symm.subst h2,
  exact h3,
 end,
 have top_mono : ∀ j10 j20, j10 < j20 → top_vec.nth j10 < top_vec.nth j20 := 
 begin
  intros j10 j20 j10_lt_j20,
  dsimp[block_vec,top_vec],
  simp[vector.nth_of_fn],
  apply fin.lt_of_succ_lt_succ,rw[top_map_spec,top_map_spec],
  exact q.top_mono j10.succ j20.succ (fin.succ_lt_succ j10_lt_j20),
 end,
 let p : fin_map n r := ⟨block_vec,top_vec,block_top,top_block,top_mono⟩,
 have eq : q = add p := 
 begin
  ext i,cases i with i_val i_is_lt, cases i_val with i0_val,
  { have : (0 : fin n.succ) = ⟨0,i_is_lt⟩ := rfl, rw[← this],
    have h₀ := (congr_arg q.block.nth e).symm,
    have h₁ := q.block_top 0,
    have h₂ := h₀.trans h₁,
    rw[h₂,fin_map.add],simp only[bump.zth]
  },{
   dsimp[add,p,bump],
   let i0_is_lt := nat.lt_of_succ_lt_succ i_is_lt,
   have h₀ := vector.sth (0 : fin r.succ) (vector.map fin.succ block_vec) i0_val i0_is_lt i_is_lt,
   rw[h₀,vector.nth_map],dsimp[block_vec],rw[vector.nth_of_fn,block_map_spec],
   refl
  }
 end,
 exact ⟨p,eq⟩, 
end

lemma res_add (p : fin_map n r) (e : add_cond (add p)) :
 (add_res (add p) e) = ⟨p,rfl⟩ := 
begin
 apply subtype.eq,
 ext ⟨i,i_is_lt⟩,
 cases (p.add.add_res e) with p₀ hp₀,simp only [],
 unfold_coes,
 simp[add_res],
 have h0 : (add p).block.nth ⟨i.succ,nat.succ_lt_succ i_is_lt⟩ = 
   (p.block.nth ⟨i,i_is_lt⟩).succ := 
   begin 
    dsimp[add,bump],
    have h1 := vector.sth (0 : fin r.succ) (vector.map fin.succ p.block) i i_is_lt
      (nat.succ_lt_succ i_is_lt),
      rw[vector.nth_map] at h1,
      rw[← h1],
    end,
 have h1 : (add p).block.nth (fin.succ ⟨i,i_is_lt⟩) ≠ 0 := 
     λ h2, fin.zero_ne_succ (h2.symm.trans h0),
 simp[add,add_res,e,h1,bump,vector.nth_map],
end

/-
 Let q be a partition of (fin (n + 1)), with rank r + 1.  Suppose also 
 that the map q.top.nth : (fin (r + 1)) → (fin (n + 1)) does not send 0
 to 0.  It is then not hard to see that there is a unique p in
 (fin_map n (r + 1)) and u in (fin (r + 1)) with (join p u) = q. 
 The present function produces this p and u.
-/
def join_res  (q : fin_map n.succ r.succ) (e : q.top.nth 0 ≠ 0) :
 { pu : (fin_map n r.succ) × (fin r.succ) // q = (join pu.1 pu.2) } := 
begin
 have e0 : 0 < q.top.nth 0 := 
  lt_of_le_of_ne (fin.zero_le (q.top.nth 0)) e.symm,
 let block_map : fin n → fin r.succ := λ i0, q.block.nth i0.succ,
 let top_map_aux : ∀ (j : fin r.succ), { i0 : fin n // i0.succ = q.top.nth j }:= 
 begin
  intro j,
  let i := q.top.nth j,
  let e1 : 0 < q.top.nth j := lt_of_lt_of_le e0 (top_mono_weak q 0 j (fin.zero_le j)),
  let e2 := (ne_of_lt e1).symm,
  exact ⟨fin.pred i e2, fin.succ_pred i e2⟩
 end,
 let top_map := λ j, (top_map_aux j).val,
 let top_map_spec : ∀ j, (top_map j).succ = q.top.nth j := 
  λ j,(top_map_aux j).property,
 let block_vec := vector.of_fn block_map,
 let top_vec := vector.of_fn top_map,
 have block_top : ∀ j, block_vec.nth (top_vec.nth j) = j := 
 begin
  intro j,
  dsimp[block_vec,top_vec],
  simp[vector.nth_of_fn,block_map],
  exact q.block_top j,
 end,
 have top_block : ∀ i0, top_vec.nth (block_vec.nth i0) ≥ i0 := 
 begin
  intro i0,
  dsimp[block_vec,top_vec],
  simp[vector.nth_of_fn,block_map],
  apply fin.le_of_succ_le_succ,
  rw[top_map_spec],
  exact q.top_block i0.succ,
 end,
 have top_mono : ∀ j1 j2, j1 < j2 → top_vec.nth j1 < top_vec.nth j2 := 
 begin
  intros j1 j2 j1_lt_j2,
  dsimp[block_vec,top_vec],
  simp[vector.nth_of_fn],
  apply fin.lt_of_succ_lt_succ,rw[top_map_spec,top_map_spec],
  exact q.top_mono j1 j2 j1_lt_j2,
 end,
 let p : fin_map n r.succ :=
  ⟨block_vec,top_vec,block_top,top_block,top_mono⟩,
 let u : fin r.succ := q.block.nth 0,
 have eq : q = join p u := 
 begin
  ext i,cases i, cases i_val with i0_val,
  {exact (vector.zth u block_vec i_is_lt).symm,},
  {
   let i0_is_lt := nat.lt_of_succ_lt_succ i_is_lt,
   exact (vector.nth_of_fn block_map ⟨i0_val,i0_is_lt⟩).symm.trans
          (vector.sth u block_vec i0_val i0_is_lt i_is_lt).symm,
  }
 end,
 exact ⟨⟨p,u⟩,eq⟩, 
end

lemma res_join (p : fin_map n r.succ) (u : fin r.succ) (e : join_cond (join p u)) :
 (join_res (join p u) e) = ⟨⟨p,u⟩,rfl⟩ := 
begin
 apply subtype.eq,
 ext i; simp[join_res,join],
end

variables (n r)

def empty : (fin_map 0 0) := {
  block := vector.nil,
  top := vector.nil,
  block_top := begin intro i, exact fin.elim0 i, end,
  top_block := begin intro j, exact fin.elim0 j, end,
  top_mono := begin intros j1 j2, exact fin.elim0 j1, end,
}

end fin_map

/- -------------------------------------------------------------- -/
/- -------------------------------------------------------------- -/
/- -------------------------------------------------------------- -/
/- -------------------------------------------------------------- -/

@[derive decidable_eq]
inductive fin_ind_partition : ℕ → ℕ → Type
| empty : (fin_ind_partition 0 0)
| add : ∀ {n r : ℕ}, (fin_ind_partition n r) → (fin_ind_partition n.succ r.succ)
| join : ∀ {n r : ℕ}, (fin_ind_partition n r) → (fin r) → (fin_ind_partition n.succ r)

namespace fin_ind_partition

def tot (n : ℕ) := Σ (r : ℕ), fin_ind_partition n r

def to_tot {n r : ℕ} (p : fin_ind_partition n r) : tot n := ⟨r,p⟩ 

private def repr_aux : ∀{n r : ℕ}, (fin_ind_partition n r) → string 
| 0 0 empty := "O"
| _ _ (add p) := "A" ++ (repr_aux p)
| _ _ (join p u) := "J" ++ (repr u) ++ (repr_aux p)

instance (n r : ℕ) : has_repr (fin_ind_partition n r) := 
 ⟨@repr_aux n r⟩ 

lemma rank_bound : ∀ {n r : ℕ} (p : fin_ind_partition n r), r ≤ n 
| 0 0 empty := le_refl 0
| _ _ (@add n r p) := nat.succ_le_succ (rank_bound p)
| _ _ (@join n r p u) := le_trans (rank_bound p) (nat.le_succ n)

def to_map_partition : ∀ {n r : ℕ} (p : fin_ind_partition n r), fin_map n r
| 0 0 empty := fin_map.empty
| _ _ (add p) := fin_map.add (to_map_partition p)
| _ _ (join p u) := fin_map.join (to_map_partition p) u

def of_map_partition : ∀ {n r : ℕ} (q : fin_map n r), fin_ind_partition n r :=
begin
 intro n,
 induction n with n0 ih_n; intros r q; cases r with r0,
 {exact empty,},
 {exact fin.elim0 (q.top.nth 0),},
 {exact fin.elim0 (q.block.nth 0),},
 {
   by_cases h : q.top.nth 0 = 0,
   {exact add (ih_n (fin_map.add_res q h).val),},
   {
     let pr := (fin_map.join_res q h).val,
     exact join (ih_n pr.1) pr.2,
   }
 }
end

lemma of_add {n r : ℕ} (q : fin_map n r) :
 of_map_partition q.add = (of_map_partition q).add := 
begin
 have h0 : q.add.top.nth 0 = 0 := fin_map.add_add_cond q,
 let h1 := q.res_add h0,
 simp[of_map_partition,h0,h1]
end

lemma of_join {n r : ℕ} (q : fin_map n r) (u : fin r) :
 of_map_partition (q.join u) = (of_map_partition q).join u := 
begin
 cases r with r0,
 {exact fin.elim0 u,},
 {
   have h0 : (q.join u).top.nth 0 ≠ 0 := fin_map.join_join_cond q u,
   let h1 := q.res_join u h0,
   simp[of_map_partition,h0,h1],
 }
end

lemma of_to_map_partition : ∀ {n r : ℕ} (p : fin_ind_partition n r),
 of_map_partition (to_map_partition p) = p
| 0 0 empty := rfl
| _ _ (@add n r p) := 
  (of_add (to_map_partition p)).trans
   (congr_arg add (of_to_map_partition p))
| _ _ (@join n r p u) := 
  (of_join (to_map_partition p) u).trans 
   (congr_fun (congr_arg join (of_to_map_partition p)) u)

lemma to_of_map_partition : ∀ {n r : ℕ} (q : fin_map n r),
 to_map_partition (of_map_partition q) = q 
| 0 0 q := by {ext i, exact fin.elim0 i,}
| 0 (nat.succ r) q := fin.elim0 (q.top.nth fin.has_zero.zero)
| (nat.succ n) 0 q := fin.elim0 (q.block.nth fin.has_zero.zero)
| (nat.succ n) (nat.succ r) q := 
  begin
   by_cases h : q.top.nth 0 = 0,
   {
     let q0e0 := fin_map.add_res q h,
     let q0 := q0e0.val,
     let e0 : q = q0.add := q0e0.property,
     exact calc
      to_map_partition (of_map_partition q)
          = to_map_partition (of_map_partition q0.add) : by rw[← e0]
      ... = to_map_partition (of_map_partition q0).add : by rw[of_add q0]
      ... = (to_map_partition (of_map_partition q0)).add : rfl
      ... = q0.add : by rw[to_of_map_partition q0]
      ... = q : by rw[e0],
   },{
     let q0ue0 := fin_map.join_res q h,
     let q0 := q0ue0.val.1,
     let u := q0ue0.val.2,
     let e0 : q = q0.join u := q0ue0.property,
     exact calc 
      to_map_partition (of_map_partition q)
          = to_map_partition (of_map_partition (q0.join u)) : by rw[← e0]
      ... = to_map_partition ((of_map_partition q0).join u) : by rw[of_join q0 u]
      ... = (to_map_partition (of_map_partition q0)).join u : rfl
      ... = q0.join u : by rw[to_of_map_partition q0]
      ... = q : by rw[e0],
   }
  end

def map_equiv (n r : ℕ) : fin_ind_partition n r ≃ fin_map n r := 
{
  to_fun := @to_map_partition n r,
  inv_fun := @of_map_partition n r,
  left_inv := @of_to_map_partition n r,
  right_inv := @to_of_map_partition n r
}

private def tot_to_fun {n : ℕ} : fin_ind_partition.tot n → fin_map.tot n
| ⟨r,p⟩ := ⟨r,(map_equiv n r).to_fun p⟩

private def tot_inv_fun {n : ℕ} : fin_map.tot n → fin_ind_partition.tot n
| ⟨r,q⟩ := ⟨r,(map_equiv n r).inv_fun q⟩

private def tot_left_inv {n : ℕ} : ∀ rp : fin_ind_partition.tot n,
  tot_inv_fun (tot_to_fun rp) = rp 
| ⟨r,p⟩ := by { simp[tot_inv_fun,tot_to_fun,(map_equiv n r).left_inv p] }

private def tot_right_inv {n : ℕ} : ∀ rq : fin_map.tot n,
  tot_to_fun (tot_inv_fun rq) = rq 
| ⟨r,q⟩ := by { simp[tot_inv_fun,tot_to_fun,(map_equiv n r).right_inv q] }

def map_equiv_tot (n : ℕ) : fin_ind_partition.tot n ≃ fin_map.tot n := 
{
  to_fun := @tot_to_fun n,
  inv_fun := @tot_inv_fun n,
  left_inv := @tot_left_inv n,
  right_inv := @tot_right_inv n,
}

instance enum : ∀ (n r : ℕ), enumeration (fin_ind_partition n r)
| 0 0 := {
   elems := [empty],
   nodup := list.nodup_singleton empty,
   complete := begin 
    intro p,cases p,exact list.mem_cons_self empty list.nil
   end
  }
| 0 (r + 1) := {
   elems := list.nil,
   nodup := list.nodup_nil,
   complete := by {intro p, cases p}
  }
| (n + 1) 0 :=  {
   elems := list.nil,
   nodup := list.nodup_nil,
   complete := by {intro p, exfalso, cases p,apply fin.elim0,assumption}
  }
| (n + 1) (r + 1) := begin
   let e0 := enum n r,
   let e1 := enum n (r + 1),
   let L_add := e0.elems.map add,
   let R := fin.elems_list (r + 1),
   let f : fin (r + 1) → list (fin_ind_partition (n + 1) (r + 1)) :=
    λ u, e1.elems.map (λ p, join p u),
   let LL_join := R.map f,
   let L_join := list.join LL_join,
   let elems := list.append L_add L_join,
   let complete : ∀ p : fin_ind_partition (n + 1) (r + 1), p ∈ elems :=
   begin
    intro p,
    cases p with _ _ p0 _ _ p0 u,
    {
     have p0_mem : p0 ∈ e0.elems := (@enumeration.complete _ e0 p0),
     exact list.mem_append_left _ (list.mem_map_of_mem add p0_mem),
    },{
     have p0_mem : p0 ∈ e1.elems := (@enumeration.complete _ e1 p0),
     let h0 := fin.elems_list_complete u,
     let h1 : f u ∈ LL_join := list.mem_map_of_mem f h0,
     let h2 : join p0 u ∈ f u := list.mem_map_of_mem (λ q,join q u) p0_mem,
     let h3 : join p0 u ∈ L_join := list.mem_join_of_mem h1 h2,
     exact list.mem_append_right _ h3,
    }
   end,
   let nodup : list.nodup elems :=
   begin
    have add_inj : function.injective (@add n r) := by simp[function.injective],
    have L_add_nodup : L_add.nodup := list.nodup_map add_inj e0.nodup,
    have LL_nodup : ∀ u, (f u).nodup := 
     λ u, list.nodup_map (by simp[function.injective]) e1.nodup,
    have LL_disjoint_aux : ∀ u v : fin (r + 1), u ≠ v → list.disjoint (f u) (f v) :=
    begin
     intros u v u_ne_v p p_in_f_u p_in_f_v,
     rcases (list.mem_map.mp p_in_f_u) with ⟨pu,⟨pu_in_elems,pu_eq⟩⟩,
     rcases (list.mem_map.mp p_in_f_v) with ⟨pv,⟨pv_in_elems,pv_eq⟩⟩,
     injection (pu_eq.trans pv_eq.symm) with _ u_eq_v,
     exact u_ne_v u_eq_v,
    end,
    have LL_disjoint : list.pairwise list.disjoint LL_join := 
    begin
     apply (@list.pairwise_map _ (fin (r + 1)) list.disjoint f R).mpr,
     exact list.pairwise.imp LL_disjoint_aux (fin.elems_list_nodup (r + 1)),
    end,
    have L_join_nodup : L_join.nodup := 
    begin
     apply list.nodup_join.mpr,
     split,
     {intros l l_in_LL,
      rcases (list.mem_map.mp l_in_LL) with ⟨u,⟨u_in_R,f_u_eq_l⟩⟩,
      rw[← f_u_eq_l],
      exact (LL_nodup u),
     },{
      exact LL_disjoint, 
     }
    end,
    have L_disjoint : list.disjoint L_add L_join := 
    begin
     intros p p_in_L_add p_in_L_join,
     rcases (list.mem_map.mp p_in_L_add) with ⟨p0,⟨p0_in_elems,p0_eq⟩⟩,
     rcases list.mem_join.mp p_in_L_join with ⟨l,⟨l_in_LL_join,p_in_l⟩⟩,
     rcases (list.mem_map.mp l_in_LL_join) with ⟨u,⟨u_in_R,f_u_eq_l⟩⟩,
     rw[← f_u_eq_l] at p_in_l,
     rcases (list.mem_map.mp p_in_l) with ⟨p1,⟨p1_in_elems,p1_eq⟩⟩,
     injection (p0_eq.trans p1_eq.symm),
    end,
    exact list.nodup_append.mpr ⟨L_add_nodup,L_join_nodup,L_disjoint⟩,
   end,
   exact {
     elems := elems, nodup := nodup, complete := complete
   },
  end

lemma card_step (n r : ℕ) : 
 (fin_ind_partition.enum n.succ r.succ).elems.length = 
   (fin_ind_partition.enum n r).elems.length +
   (fin_ind_partition.enum n r.succ).elems.length * r.succ := 
begin
 let e0 := fin_ind_partition.enum n r,
 let e1 := fin_ind_partition.enum n (r + 1),
 let e2 := fin_ind_partition.enum (n + 1) (r + 1),
 let n0 := e0.elems.length,
 let n1 := e1.elems.length,
 let n2 := e2.elems.length,
 let L_add := e0.elems.map add,
 let R := fin.elems_list (r + 1),
 let f : fin (r + 1) → list (fin_ind_partition (n + 1) (r + 1)) :=
    λ u, e1.elems.map (λ p, join p u),
 let LL_join := R.map f,
 let L_join := list.join LL_join,
 have h0 : n2 = L_add.length + L_join.length := list.length_append L_add L_join,
 have h1 : L_add.length = n0 := list.length_map add _,
 let h2 : LL_join.length = r.succ :=
  (list.length_map f R).trans (fin.elems_list_length r.succ),
 have h3 : ∀ u, (f u).length = n1 := 
  λ u,list.length_map (λ p, join p u) _,
 let h4 : LL_join.map list.length = list.repeat n1 r.succ := 
 begin
  apply list.eq_repeat.mpr,
  split,
  {exact ((list.length_map list.length LL_join).trans h2),},
  {intros k k_in_ks,
   rcases (list.mem_map.mp k_in_ks) with ⟨l,⟨l_in_LL_join,l_len⟩⟩,
   rcases (list.mem_map.mp l_in_LL_join) with ⟨u,⟨u_in_R,f_u_eq_l⟩⟩,
   rw[← l_len,← f_u_eq_l],
   exact h3 u,
  }
 end,
 have h5 : L_join.length = n1 * r.succ := (list.length_join LL_join).trans
   ((congr_arg list.sum h4).trans (list.sum_const_nat n1 r.succ)),
 exact calc
  n2 = L_add.length + L_join.length : h0 
  ... = n0 + n1 * r.succ : by rw[h1,h5]
end

lemma card_stirling : ∀ (n r : ℕ),
 (fintype.card (fin_ind_partition n r)) = partition.number.stirling2 n r
| 0 0 := rfl
| 0 (r + 1) := rfl
| (n + 1) 0 := rfl
| (n + 1) (r + 1) := 
  begin
   rw[partition.number.stirling2,enumeration.enum_card,card_step n r],
   rw[← enumeration.enum_card,← enumeration.enum_card],
   rw[card_stirling n r,card_stirling n (r + 1)],
  end

instance tot_enum (n : ℕ) : enumeration (tot n) := 
begin
 let e0 := fin_ind_partition.enum n,
 let elems0 : ℕ → list (tot n) := λ r, (e0 r).elems.map to_tot,
 let elems1 := ((list.range n.succ).map elems0),
 let elems := elems1.join,
 let nodup0 : ∀ r, (elems0 r).nodup := 
 begin
  intro r,
  have tot_inj : function.injective (@to_tot n r) := 
  begin
   intros p1 p2 tot_eq,
   injection tot_eq with r_eq p_heq,
   cases r_eq,
   exact eq_of_heq p_heq,
  end,
  exact list.nodup_map tot_inj (e0 r).nodup,
 end,
 let nodup1 : ∀ l, l ∈ elems1 → (list.nodup l) := 
 begin
  intros l l_in_elems1,
  rcases (list.mem_map.mp l_in_elems1) with ⟨r,⟨r_mem,l_eq⟩⟩,
  rw[← l_eq],
  exact nodup0 r,
 end,
 let disjoint0 : ∀ r1 r2, r1 ≠ r2 → list.disjoint (elems0 r1) (elems0 r2) := 
 begin
  intros r1 r2 r_ne q q_in_l1 q_in_l2,
  rcases (list.mem_map.mp q_in_l1) with ⟨p1,⟨p1_in_elems,p1_eq⟩⟩,
  rcases (list.mem_map.mp q_in_l2) with ⟨p2,⟨p2_in_elems,p2_eq⟩⟩,
  let r_eq : r1 = r2 := (congr_arg sigma.fst p1_eq).trans 
                        (congr_arg sigma.fst p2_eq).symm,
  exact r_ne r_eq,
 end,
 let disjoint1 := @list.pairwise.imp ℕ ne
  (λ r1 r2, list.disjoint (elems0 r1) (elems0 r2))
   disjoint0 _ (list.nodup_range n.succ), 
 let disjoint2 := (list.pairwise_map elems0).mpr disjoint1,
 let nodup := list.nodup_join.mpr ⟨nodup1,disjoint2⟩,
 let complete : ∀ rp : tot n, rp ∈ elems := 
 begin
  intro rp,
  rcases rp with ⟨r,p⟩,
  have rp_eq : to_tot p = ⟨r,p⟩ := rfl,
  rw[← rp_eq],
  have mem0 : p ∈ (e0 r).elems := @enumeration.complete _ (e0 r) p,
  have mem1 : to_tot p ∈ elems0 r := 
   list.mem_map_of_mem to_tot mem0,
  have mem2 : elems0 r ∈ elems1 := list.mem_map_of_mem elems0 
   (list.mem_range.mpr (nat.lt_succ_of_le (rank_bound p))),
  exact list.mem_join.mpr ⟨elems0 r,⟨mem2,mem1⟩⟩,
 end,
 exact {elems := elems, nodup := nodup, complete := complete},
end

lemma card_bell (n : ℕ) :
 fintype.card (tot n) = partition.number.bell n :=
begin
 let f := λ (r : ℕ), list.map to_tot (enumeration.elems (fin_ind_partition n r)),
 have h : list.length ∘ f = partition.number.stirling2 n := 
 begin
  ext r,simp,rw[← enumeration.enum_card],exact card_stirling n r,
 end,
 rw[enumeration.enum_card,partition.number.bell],
 dsimp[enumeration.elems],
 rw[list.length_join,list.map_map,h],
end

end fin_ind_partition

namespace fin_map 

instance enum (n r : ℕ) : enumeration (fin_map n r) :=
 enumeration.of_equiv (fin_ind_partition n r)
  (fin_ind_partition.map_equiv n r)

lemma card_stirling (n r : ℕ) :
 (fintype.card (fin_map n r)) = partition.number.stirling2 n r :=
  (fintype.card_congr (fin_ind_partition.map_equiv n r)).symm.trans
           (fin_ind_partition.card_stirling n r)

instance enum_tot (n : ℕ) : enumeration (fin_map.tot n) :=
 enumeration.of_equiv (fin_ind_partition.tot n)
  (fin_ind_partition.map_equiv_tot n)

lemma card_bell (n : ℕ) :
 (fintype.card (fin_map.tot n)) = partition.number.bell n :=
  (fintype.card_congr (fin_ind_partition.map_equiv_tot n)).symm.trans
           (fin_ind_partition.card_bell n)

end fin_map

lemma card_stirling (n r : ℕ) :
 fintype.card { p : partition (fin n) // p.rank = r } = partition.number.stirling2 n r :=
  (fintype.card_congr (@fin_map.partition_equiv n r)).symm.trans
           (fin_map.card_stirling n r)

lemma card_bell (n : ℕ) :
 fintype.card (partition (fin n)) = partition.number.bell n :=
  (fintype.card_congr (@fin_map.partition_equiv_tot n)).symm.trans
           (fin_map.card_bell n)

lemma card_bell' (α : Type*) [fintype α] [decidable_eq α] :
 fintype.card (partition α) = partition.number.bell (fintype.card α) :=
begin
 refine trunc.induction_on (fintype.equiv_fin α) _,
 intro equiv_fin,
 exact (fintype.card_congr (isofunctor equiv_fin)).trans 
            (card_bell (fintype.card α)),
end

end combinatorics.partition
