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

import data.list.sort data.fintype.basic
import poset.basic order.sort_rank

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

variables {P} [fintype P]

/-- Definition of chains 
  LaTeX: defn-subdiv
-/
def is_chain (s : finset P) : Prop := 
 ∀ (p ∈ s) (q ∈ s), (p ≤ q ∨ q ≤ p)

instance decidable_is_chain (s : finset P) : decidable (is_chain s) := 
by { unfold is_chain, apply_instance }

/-- Definition of simplices as nonempty chains 
  LaTeX: defn-subdiv
-/
def is_simplex (s : finset P) : Prop := s.nonempty ∧ (is_chain s)

instance decidable_is_simplex (s : finset P) : decidable (is_simplex s) := 
by { unfold is_simplex, unfold finset.nonempty, apply_instance }

variable (P)

/-- Definition of subdiv P as a type 
  LaTeX: defn-subdiv
-/
def subdiv := {s : finset P // is_simplex s}

instance : has_coe (subdiv P) (finset P) := ⟨subtype.val⟩

/-- Vertices as 0-simplices -/
variable {P}
def vertex (p : P) : subdiv P := ⟨ 
{p},
begin
  split,
  {exact ⟨p,finset.mem_singleton_self p⟩},
  {intros x hx y hy,
   rw [finset.mem_singleton.mp hx, finset.mem_singleton.mp hy],
   left, exact le_refl p }
end⟩ 
variable (P)

namespace subdiv

instance : decidable_eq (subdiv P) := 
  by { unfold subdiv, apply_instance }

/-- Definition of the partial order on subdiv P 
  LaTeX: defn-subdiv
-/
instance : partial_order (subdiv P) := 
{ le := λ s t, s.val ⊆ t.val,
  le_refl := λ s, (le_refl s.val),
  le_antisymm := λ s t hst hts, subtype.eq (le_antisymm hst hts),
  le_trans := λ s t u (hst : s.val ⊆ t.val) (htu : t.val ⊆ u.val) p hs, 
                (htu (hst hs)) }

instance decidable_le : decidable_rel
 (has_le.le : (subdiv P) → (subdiv P) → Prop) := 
  λ s t, by { apply_instance }

variable {P}

/-- Definition of the dimension of a simplex, as one less than 
  the cardinality.  We use the predecessor operation on 
  natural numbers, which sends zero to zero.  Because of this,
  we need a small argument to show that the cardinality is 
  strictly positive and thus equal to one more than the dimension.

  LaTeX: defn-subdiv
-/
def dim (s : subdiv P) : ℕ := (s : finset P).card.pred

lemma card_eq (s : subdiv P) : (s : finset P).card = s.dim.succ := 
begin 
  by_cases h : s.val.card = 0,
  { exfalso,
    have h₀ := s.property.left, rw[finset.card_eq_zero.mp h] at h₀,
    exact finset.not_nonempty_empty h₀},
  { replace h := nat.pos_of_ne_zero h,
    exact (nat.succ_pred_eq_of_pos h).symm }
end

/-- The dimension function dim : subdiv P → ℕ is monotone. -/
lemma dim_mono : monotone (dim : (subdiv P) → ℕ) := 
begin
  intros s t hst,
  let h : (s : finset P).card ≤ (t : finset P).card := finset.card_le_of_subset hst,
  rw[card_eq,card_eq] at h,
  exact nat.le_of_succ_le_succ h
end

/-- If we have simplices s ≤ t with dim s ≥ dim t then s = t. -/
lemma eq_of_le_of_dim_ge (s t : subdiv P)
 (hst : s ≤ t) (hd : s.dim ≥ t.dim) : s = t := 
begin
  let hc := nat.succ_le_succ hd,
  rw [← card_eq, ← card_eq] at hc,
  exact subtype.eq (finset.eq_of_subset_of_card_le hst hc)
end

/-- This allows us to treat a simplex as a type in its own right. -/
instance : has_coe_to_sort (subdiv P) (Type uP) := ⟨λ s, {p : P // p ∈ s.val}⟩

section els

variable (s : subdiv P)

instance els_decidable_eq : decidable_eq s := by { apply_instance }
instance els_fintype : fintype s           := by { apply_instance }

lemma card_eq' : fintype.card s = s.dim.succ := begin
 rw[← s.card_eq], rw[← fintype.card_coe],congr
end

/-- If s is a simplex, we can treat it as a linearly ordered set. -/
instance els_order : linear_order s := 
{ le := λ p q,p.val ≤ q.val,
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
  decidable_le := λ p q, by { apply_instance } }

variable {s}

/-- The inclusion of a simplex in the full poset P. -/
def inc : s → P := λ p, p.val

/-- The inclusion map is injective. -/
lemma inc_inj (p₀ p₁ : s) : (inc p₀) = (inc p₁) → p₀ = p₁ := subtype.eq

/-- The inclusion map is monotone. -/
lemma inc_mono : monotone (inc : s → P) := λ p₀ p₁ hp, hp

variable (s)
variables {d : ℕ} (e : s.dim = d)

/-- If dim s = d, then we have a canonical bijection from s 
  to the set  fin d.succ = { 0,1,...,d }.  We define 
  rank_equiv s to be a package consisting of this bijection
  and its inverse.  We define seq s and rank s to be 
  auxiliary functions defined in terms of rank_equiv s,
  and we prove some lemmas about the behaviour of these.
-/

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
 ((rank_equiv s e).symm i) = ⟨seq s e i,seq_mem s e i⟩ := 
  by { apply subtype.eq, refl }

lemma rank_seq (i : fin d.succ) : 
 rank s e (seq s e i) (seq_mem s e i) = i := 
begin
  dsimp [rank],
  rw [← (seq_eq s e i)], 
  exact (rank_equiv s e).right_inv i,
end

lemma seq_le (i₀ i₁ : fin d.succ) :
 i₀ ≤ i₁ ↔ seq s e i₀ ≤ seq s e i₁ := 
  fintype.seq_le (s.card_eq'.trans (congr_arg nat.succ e)) i₀ i₁

lemma seq_lt (i₀ i₁ : fin d.succ) :
 i₀ < i₁ ↔ seq s e i₀ < seq s e i₁ := 
  fintype.seq_lt (s.card_eq'.trans (congr_arg nat.succ e)) i₀ i₁


variables {P Q} [fintype Q]

def map (f : poset.hom P Q) : (poset.hom (subdiv P) (subdiv Q)) := 
begin
  let sf : subdiv P → subdiv Q := λ s, 
  begin
    let t0 : finset Q := s.val.image f.val,
    have : is_simplex t0 := 
    begin 
      split,
      { rcases s.property.1 with ⟨p,p_in_s⟩, 
        exact ⟨_,(finset.mem_image_of_mem f.val p_in_s)⟩ },
      { intros q₀ hq₀ q₁ hq₁, 
        rcases finset.mem_image.mp hq₀ with ⟨p₀,hp₀,hfp₀⟩,
        rcases finset.mem_image.mp hq₁ with ⟨p₁,hp₁,hfp₁⟩,
        rw [← hfp₀, ← hfp₁],
        rcases s.property.2 p₀ hp₀ p₁ hp₁ with h₀₁ | h₁₀,
        { left,  exact f.property h₀₁ },
        { right, exact f.property h₁₀ } }
    end,
    exact ⟨t0,this⟩
  end,
  have : monotone sf := λ s₀ s₁ hs, 
  begin
    change s₀.val.image f.val ⊆ s₁.val.image f.val, 
    intros q hq, 
    rcases finset.mem_image.mp hq with ⟨p,hp,hfp⟩,
    exact finset.mem_image.mpr ⟨p,hs hp,hfp⟩
  end,
  exact ⟨sf, this⟩
end

lemma map_val (f : poset.hom P Q) (s : subdiv P) : 
 ((subdiv.map f).val s).val = s.val.image f.val := rfl

section interleave 

variables [fintype P] {f g : poset.hom P Q} (hfg : f ≤ g)
include hfg

def interleave :
 ∀ (r : fin_ranking P) (m : ℕ), hom (subdiv P) (subdiv Q) 
| ⟨n,r,r_mono⟩ m := 
  ⟨ λ (σ : subdiv P), 
    ⟨ ((σ.val.filter (λ p, 2 * (r p).val < m)).image f) ∪  
      ((σ.val.filter (λ p, 2 * (r p).val + 1 ≥ m)).image g),  
      begin 
        split,
        { rcases σ.property.1 with ⟨p, p_in_σ⟩,
          by_cases h : 2 * (r p).val < m,
          { use f p,
            apply finset.mem_union_left,
            apply finset.mem_image_of_mem,
            rw [finset.mem_filter],
            exact ⟨p_in_σ, h⟩ },
          { replace h := le_trans (le_of_not_gt h) (nat.le_succ _), 
            use (g p),
            apply finset.mem_union_right,
            apply finset.mem_image_of_mem,
            rw [finset.mem_filter],
            exact ⟨p_in_σ, h⟩ } },
        { intros q₀ h₀ q₁ h₁,
          rcases finset.mem_union.mp h₀ with h₀ | h₀;
          rcases finset.mem_union.mp h₁ with h₁ | h₁;
          rcases finset.mem_image.mp h₀ with ⟨p₀,hf₀,he₀⟩;
          rcases finset.mem_image.mp h₁ with ⟨p₁,hf₁,he₁⟩;
          rw [finset.mem_filter] at hf₀ hf₁; 
          rw [← he₀, ← he₁];
          let r₀ := (r p₀).val ; let r₁ := (r p₁).val ; 
          rcases σ.property.right p₀ hf₀.1 p₁ hf₁.1 with hpp | hpp;
          let hfpp := f.property hpp;
          let hgpp := g.property hpp,
          { left , exact hfpp },
          { right, exact hfpp },
          { left , exact le_trans hfpp (hfg p₁) },
          { by_cases hrr : r₀ = r₁, 
            { rw [r.injective (fin.eq_of_veq hrr)],
              left, exact hfg p₁ },
            { exfalso, 
              change r₀ ≠ r₁ at hrr,
              replace hrr : r₁ < r₀ := lt_of_le_of_ne (r_mono hpp) hrr.symm, 
              change r₁ + 1 ≤ r₀ at hrr,
              have := calc
                2 * r₁ + 2 = 2 * (r₁ + 1) : by rw [mul_add, mul_one]
                ... ≤ 2 * r₀ : nat.mul_le_mul_left 2 hrr
                ... < m : hf₀.2
                ... ≤ 2 * r₁ + 1 : hf₁.2 
                ... < 2 * r₁ + 2 : nat.lt_succ_self _, 
              exact lt_irrefl _ this } }, 
          { by_cases hrr : r₀ = r₁, 
            { rw [r.injective (fin.eq_of_veq hrr)],
              right, exact hfg p₁ },
            { exfalso, 
              change r₀ ≠ r₁ at hrr,
              replace hrr : r₀ < r₁ := lt_of_le_of_ne (r_mono hpp) hrr, 
              change r₀ + 1 ≤ r₁ at hrr,
              have := calc
                2 * r₁ < m : hf₁.2 
                ... ≤ 2 * r₀ + 1 : hf₀.2 
                ... < 2 * r₀ + 2 : nat.lt_succ_self _
                ... = 2 * (r₀ + 1) : by rw [mul_add, mul_one]
                ... ≤ 2 * r₁ : nat.mul_le_mul_left 2 hrr,
              exact lt_irrefl _ this } }, 
          { right, exact le_trans hfpp (hfg p₀) },
          { left , exact hgpp },
          { right, exact hgpp } }
      end ⟩,
      begin 
        intros σ₀ σ₁ h_le q hq,
        rw [finset.mem_union] at hq ⊢, 
        rcases hq with hq | hq;
        rcases finset.mem_image.mp hq with ⟨p,hm,he⟩;
        rw [← he];
        rw [finset.mem_filter] at hm;
        replace hm := and.intro (h_le hm.1) hm.2,
        { left , apply finset.mem_image_of_mem, 
          rw [finset.mem_filter], exact hm },
        { right, apply finset.mem_image_of_mem, 
          rw [finset.mem_filter], exact hm }
      end ⟩ 

lemma interleave_start :
 ∀ (r : fin_ranking P), interleave hfg r 0 = subdiv.map g 
| ⟨n,r,r_mono⟩ := 
begin
  ext1 σ, 
  apply subtype.eq,
  change _ ∪ _ = σ.val.image g.val,
  ext q,
  have : σ.val.filter (λ (p : P), 2 * (r p).val < 0) = ∅ := 
  begin
    ext p, rw [finset.mem_filter],
    simp [nat.not_lt_zero, finset.not_mem_empty] 
  end,
  rw [this, finset.image_empty],
  have : σ.val.filter (λ (p : P), 2 * (r p).val + 1 ≥ 0) = σ.val := 
  begin
    ext p, rw [finset.mem_filter], 
    have : _ ≥ 0 := nat.zero_le (2 * (r p).val + 1),
    simp only [this, and_true]
  end,
  rw [this, finset.mem_union],
  have : (g : P → Q) = g.val := rfl, rw [this], 
  simp [finset.not_mem_empty],
end

lemma interleave_end :
 ∀ (r : fin_ranking P) (m : ℕ) (hm : m ≥ 2 * r.card), 
  interleave hfg r m = subdiv.map f 
| ⟨n,r,r_mono⟩ m hm := 
begin
  change m ≥ 2 * n at hm,
  ext1 σ,
  apply subtype.eq,
  change _ ∪ _ = σ.val.image f.val,
  ext q,
  have : σ.val.filter (λ (p : P), 2 * (r p).val < m) = σ.val := 
  begin
    ext p, rw [finset.mem_filter], 
    have := calc
      2 * (r p).val < 2 * n :
        nat.mul_lt_mul_of_pos_left (r p).is_lt (dec_trivial : 2 > 0)
      ... ≤ m : hm,
    simp only [this,and_true],
  end,
  rw [this],
  have : σ.val.filter (λ (p : P), 2 * (r p).val + 1 ≥ m) = ∅ := 
  begin
    ext p, rw [finset.mem_filter],
    have := calc 
      2 * (r p).val + 1 < 2 * (r p).val + 2 : nat.lt_succ_self _
      ... = 2 * ((r p).val + 1) : by rw [mul_add, mul_one]
      ... ≤ 2 * n : nat.mul_le_mul_left 2 (r p).is_lt
      ... ≤ m : hm,
    have : ¬ (_ ≥ m) := not_le_of_gt this,
    simp only [this, finset.not_mem_empty, and_false]
  end,
  rw [this, finset.image_empty, finset.union_empty],
  have : (f : P → Q) = f.val := rfl, rw [this]
end

lemma interleave_even_step : 
 ∀ (r : fin_ranking P) (k : ℕ), 
  interleave hfg r (2 * k) ≤ interleave hfg r (2 * k + 1)
| ⟨n,r,r_mono⟩ k := 
begin
  intros σ q h,
  change q ∈ _ ∪ _ at h,
  change q ∈ _ ∪ _, 
  rw [finset.mem_union] at h ⊢,  
  rcases h with h | h;
  rcases finset.mem_image.mp h with ⟨p,hf,he⟩; 
  rw [finset.mem_filter] at hf;
  rw [← he],
  { left, 
    apply finset.mem_image_of_mem, 
    rw [finset.mem_filter],
    exact ⟨hf.1, lt_trans hf.2 (nat.lt_succ_self _)⟩ },
  { right,
    apply finset.mem_image_of_mem,
    rw [finset.mem_filter],
    rcases le_or_gt k (r p).val with hk | hk,
    { exact ⟨hf.1, nat.succ_le_succ (nat.mul_le_mul_left 2 hk)⟩ },
    { exfalso, 
      have := calc
        2 * (r p).val + 2 = 2 * ((r p).val + 1) : by rw [mul_add, mul_one]
        ... ≤ 2 * k : nat.mul_le_mul_left 2 hk
        ... ≤ 2 * (r p).val + 1 : hf.2
        ... < 2 * (r p).val + 2 : nat.lt_succ_self _,
      exact lt_irrefl _ this } }
end

lemma interleave_odd_step : 
 ∀ (r : fin_ranking P) (k : ℕ), 
  interleave hfg r (2 * k + 2) ≤ interleave hfg r (2 * k + 1)
| ⟨n,r,r_mono⟩ k := 
begin
  intros σ q h,
  change q ∈ _ ∪ _ at h,
  change q ∈ _ ∪ _, 
  rw [finset.mem_union] at h ⊢,  
  rcases h with h | h;
  rcases finset.mem_image.mp h with ⟨p,hf,he⟩; 
  rw [finset.mem_filter] at hf;
  rw [← he],
  { left, 
    apply finset.mem_image_of_mem, 
    rw [finset.mem_filter],
    rcases le_or_gt (r p).val k with hk | hk,
    { have := calc
       2 * (r p).val ≤ 2 * k : nat.mul_le_mul_left 2 hk
       ... < 2 * k + 1 : nat.lt_succ_self _,
      exact ⟨hf.1, this⟩ },
    { exfalso, 
      have := calc
        2 * k + 2 = 2 * (k + 1) : by rw [mul_add, mul_one]
        ... ≤ 2 * (r p).val : nat.mul_le_mul_left 2 hk
        ... < 2 * k + 2 : hf.2,
      exact lt_irrefl _ this } },
  { right,
    apply finset.mem_image_of_mem,
    rw [finset.mem_filter],
    exact ⟨hf.1, le_trans (le_of_lt (nat.lt_succ_self (2 * k + 1))) hf.2⟩ }
end

lemma interleave_component (r : fin_ranking P) (m : ℕ) : 
  component (interleave hfg r m) = component (interleave hfg r 0) := 
zigzag (interleave hfg r) 
  (interleave_even_step hfg r)
  (interleave_odd_step hfg r) m

end interleave 

def subdiv.mapₕ [fintype P] :
  π₀ (hom P Q) → π₀ (hom (subdiv P) (subdiv Q)) := 
π₀.lift (λ f, component (subdiv.map f))
begin
  intros f g hfg,
  rcases exists_fin_ranking P with ⟨r⟩,
  let n := r.card,
  let c := interleave hfg r,
  have : c 0 = subdiv.map g := interleave_start hfg r,
  rw [← this],
  have : c (2 * n) = subdiv.map f := interleave_end hfg r (2 * n) (le_refl _),
  rw [← this],
  apply interleave_component
end

/-- For a simplex s, we define max s to be the largest element. -/

def max₀ : P := seq s rfl (fin.last s.dim)

lemma max₀_mem : s.max₀ ∈ s.val := seq_mem s rfl (fin.last s.dim)

lemma le_max₀ (p : P) (hp : p ∈ s.val) : p ≤ s.max₀ := 
begin
  rw [← seq_rank s rfl p hp],
  apply (seq_le s rfl (rank s rfl p hp) (fin.last s.dim)).mp,
  apply fin.le_last
end

end els

/-- The function max : subdiv P → P is monotone. -/
lemma max₀_mono : monotone (max₀ : subdiv P → P) := 
  λ s t hst, t.le_max₀ s.max₀ (hst s.max₀_mem)

variable (P)

def max : hom (subdiv P) P := ⟨max₀,max₀_mono⟩

lemma max_mem (s : subdiv P) : max P s ∈ s.val := max₀_mem s

lemma le_max (s : subdiv P) (p : P) (hp : p ∈ s.val) : p ≤ max P s := 
le_max₀ s p hp

lemma max_vertex (p : P) : max P (vertex p) = p := 
 finset.mem_singleton.mp (max₀_mem (vertex p))

lemma max_cofinal : cofinalₕ (max P) := 
begin
  intro p,
  let C := comma (max P) p,
  let c : C := ⟨vertex p,by {rw[max_vertex]}⟩, 
  let T := punit.{uP + 1},
  let f : hom C T := const C punit.star, 
  let g : hom T C := const T c,
  have hfg : comp f g = id T := 
  by { ext t, rcases t, refl },
  let m₀ : C → C := λ x, 
  begin
    let τ₀ := x.val.val ∪ {p},
    have h₀ : τ₀.nonempty := ⟨_,(finset.mem_union_right _ (finset.mem_singleton_self p))⟩,
    have h₁ : is_chain τ₀ := λ a ha b hb, 
    begin
      rcases finset.mem_union.mp ha with hax | hap;
      rcases finset.mem_union.mp hb with hbx | hbp,
      { exact x.val.property.2 a hax b hbx },
      { left, 
        rw [finset.mem_singleton.mp hbp],
        exact le_trans (le_max P x.val a hax) x.property },
      { right,
        rw [finset.mem_singleton.mp hap],
        exact le_trans (le_max P x.val b hbx) x.property },
      { left, 
        rw [finset.mem_singleton.mp hbp],
        rw [finset.mem_singleton.mp hap] }
    end,
    let τ : subdiv P := ⟨τ₀,⟨h₀,h₁⟩⟩,
    have h₂ : max P τ ≤ p := 
    begin
      rcases finset.mem_union.mp (max_mem P τ) with h | h,
      { exact le_trans (le_max P x.val _ h) x.property },
      { rw [finset.mem_singleton.mp h] } 
    end,
    exact ⟨τ,h₂⟩
  end,
  have m₀_mono : monotone m₀ := λ x₀ x₁ h,
  begin
    change x₀.val.val ⊆ x₁.val.val at h,
    change x₀.val.val ∪ {p} ⊆ x₁.val.val ∪ {p},
    intros a ha,
    rcases finset.mem_union.mp ha with hax | hap,
    { exact finset.mem_union_left _ (h hax) },
    { exact finset.mem_union_right _ hap }
  end,
  let m : hom C C := ⟨m₀,m₀_mono⟩,
  have hm₀ : comp g f ≤ m := λ x a ha, 
  begin
    change a ∈ {p} at ha,
    change a ∈ x.val.val ∪ {p},
    exact finset.mem_union_right _ ha
  end,
  have hm₁ : id C ≤ m := λ x a ha,
  begin
    change a ∈ x.val.val at ha,
    change a ∈ x.val.val ∪ {p},
    exact finset.mem_union_left _ ha
  end,
  let hgf := (π₀.sound hm₀).trans (π₀.sound hm₁).symm,
  have e : equivₕ C T := 
  { to_fun := component f,
    inv_fun := component g,
    left_inv := hgf,
    right_inv := congr_arg component hfg },
  exact ⟨e⟩ 
end

end subdiv

end poset