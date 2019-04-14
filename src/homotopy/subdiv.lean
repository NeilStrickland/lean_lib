/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Given a poset `P`, we define `subdiv P` to be the poset of 
finite nonempty chains `s ⊆ P`.  Any such `s` has a largest 
element, and the map `max : (subdiv P) → P` is a morphism 
of posets.  There is an approach to the homotopy theory of
finite complexes based on finite posets, and the above map
`max` plays a key role in this. 
-/

import data.list.sort
import homotopy.poset order.sort_rank

universes uP uQ uR uS

variables (P : Type uP) [partial_order P] [decidable_eq P]
variables (Q : Type uQ) [partial_order Q] [decidable_eq Q]
variables (R : Type uR) [partial_order R] [decidable_eq R]
variables (S : Type uS) [partial_order S] [decidable_eq S]

variable [decidable_rel (has_le.le : P → P → Prop)]
variable [decidable_rel (has_le.le : Q → Q → Prop)]
variable [decidable_rel (has_le.le : R → R → Prop)]
variable [decidable_rel (has_le.le : S → S → Prop)]

namespace poset 
open poset

variable {P}
def is_chain (s : finset P) : Prop := 
 ∀ (p ∈ s) (q ∈ s), (p ≤ q ∨ q ≤ p)

instance decidable_is_chain (s : finset P) : decidable (is_chain s) := 
 by { unfold is_chain, apply_instance }

def is_simplex (s : finset P) : Prop := 
 s ≠ ∅ ∧ (is_chain s)

instance decidable_is_simplex (s : finset P) : decidable (is_simplex s) := 
 by { unfold is_simplex, apply_instance }

variable (P)

def subdiv := {s : finset P // is_simplex s}

namespace subdiv

instance : decidable_eq (subdiv P) := 
 by { unfold subdiv, apply_instance }

instance : partial_order (subdiv P) := {
 le := λ s t, s.val ⊆ t.val,
 le_refl := λ s, (le_refl s.val),
 le_antisymm := λ s t hst hts, subtype.eq (le_antisymm hst hts),
 le_trans := λ s t u (hst : s.val ⊆ t.val) (htu : t.val ⊆ u.val) p hs, 
               (htu (hst hs))  
}

instance decidable_le : decidable_rel
 (has_le.le : (subdiv P) → (subdiv P) → Prop) := 
  λ s t, by { apply_instance }

variable {P}
def dim (s : subdiv P) : ℕ := s.val.card.pred

lemma card_eq (s : subdiv P) : s.val.card = s.dim.succ := 
begin 
 by_cases h : s.val.card = 0,
 {exact (s.property.left (finset.card_eq_zero.mp h)).elim},
 {replace h := nat.pos_of_ne_zero h,
  exact (nat.succ_pred_eq_of_pos h).symm
 }
end

lemma dim_mono : monotone (dim : (subdiv P) → ℕ) := 
begin
 intros s t hst,
 let h := finset.card_le_of_subset hst,
 rw[card_eq,card_eq] at h,
 exact nat.le_of_succ_le_succ h
end

lemma eq_of_le_of_dim_ge (s t : subdiv P)
 (hst : s ≤ t) (hd : s.dim ≥ t.dim) : s = t := 
begin
 let hc := nat.succ_le_succ hd,
 rw[← card_eq,← card_eq] at hc,
 exact subtype.eq (finset.eq_of_subset_of_card_le hst hc),
end

instance : has_coe_to_sort (subdiv P) := 
 ⟨_,λ s, {p : P // p ∈ s.val}⟩

section els

variable (s : subdiv P)

instance els_decidable_eq : decidable_eq s := by {apply_instance}
instance els_fintype : fintype s := by {apply_instance}

lemma card_eq' : fintype.card s = s.dim.succ := 
 (fintype.card_coe s.val).trans s.card_eq

instance els_order : decidable_linear_order s := {
 le := λ p q,p.val ≤ q.val,
 le_refl := λ p, ((le_refl (p.val : P)) : p.val ≤ p.val),
 le_antisymm := λ p q (hpq : p.val ≤ q.val) (hqp : q.val ≤ p.val),
                 subtype.eq (le_antisymm hpq hqp),
 le_trans := λ p q r (hpq : p.val ≤ q.val) (hqr : q.val ≤ r.val), 
                 le_trans hpq hqr,
 le_total := λ p q,s.property.right p.val p.property q.val q.property,
 lt := λ p q,p.val < q.val,
 lt_iff_le_not_le := λ p q, 
 begin 
  change p.val < q.val ↔ p.val ≤ q.val ∧ ¬ q.val ≤ p.val,
  apply lt_iff_le_not_le, 
 end,
 decidable_le := λ p q,by {apply_instance}
}

variable {s}
def inc : s → P := λ p, p.val

lemma inc_inj (p₀ p₁ : s) : (inc p₀) = (inc p₁) → p₀ = p₁ := subtype.eq

lemma inc_mono : monotone (inc : s → P) := λ p₀ p₁ hp, hp

variable (s)
variables {d : ℕ} (e : s.dim = d)

def rank_equiv : s ≃ fin d.succ := 
 fintype.rank_equiv (s.card_eq'.trans (congr_arg nat.succ e))

def seq : (fin d.succ) → P := λ i, inc ((rank_equiv s e).inv_fun i)

def rank (p : P) (hp : p ∈ s.val) : fin d.succ := 
 (rank_equiv s e).to_fun ⟨p,hp⟩

lemma seq_mem (i : fin d.succ) : seq s e i ∈ s.val := 
  ((rank_equiv s e).inv_fun i).property

lemma seq_rank (p : P) (hp : p ∈ s.val) : 
 seq s e (rank s e p hp) = p := 
  congr_arg inc ((rank_equiv s e).left_inv ⟨p,hp⟩)

lemma seq_eq (i : fin d.succ) :
 ((rank_equiv s e).inv_fun i) = ⟨seq s e i,seq_mem s e i⟩ := 
  by { apply subtype.eq, refl }

lemma rank_seq (i : fin d.succ) : 
 rank s e (seq s e i) (seq_mem s e i) = i := 
by {dsimp[rank],rw[← seq_eq,(rank_equiv s e).right_inv],}

lemma seq_le (i₀ i₁ : fin d.succ) :
 i₀ ≤ i₁ ↔ seq s e i₀ ≤ seq s e i₁ := 
  fintype.seq_le (s.card_eq'.trans (congr_arg nat.succ e)) i₀ i₁

lemma seq_lt (i₀ i₁ : fin d.succ) :
 i₀ < i₁ ↔ seq s e i₀ < seq s e i₁ := 
  fintype.seq_lt (s.card_eq'.trans (congr_arg nat.succ e)) i₀ i₁

def max : P := seq s rfl (fin.last s.dim)

lemma max_mem : s.max ∈ s.val := seq_mem s rfl (fin.last s.dim)

lemma le_max  (p : P) (hp : p ∈ s.val) : p ≤ s.max := 
begin
 rw[← seq_rank s rfl p hp],
 apply (seq_le s rfl (rank s rfl p hp) (fin.last s.dim)).mp,
 apply fin.le_last, 
end

end els

lemma max_mono : monotone (max : subdiv P → P) := 
  λ s t hst, t.le_max s.max (hst s.max_mem)

def max' : hom (subdiv P) P := ⟨max,max_mono⟩

end subdiv

end poset