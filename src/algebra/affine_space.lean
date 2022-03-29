/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file sets up the theory of affine spaces.  One approach
would be to say that an affine space consists of a commutative
additive group A together with a type V and a free transitive 
action of A on V.  From this point of view, we could define a 
parallelogram to be a list of the form 
[v, v + a, v + b, v + a + b] for some v in V and a,b in A.

Here, however, we proceed in a slightly different way: we assume
that we are given an inhabited type V and a set of parallelograms 
subject to some axioms.  From these we construct A as a quotient
of V × V, and then construct a free transitive action of A on V.
-/

import algebra.group

class affine_space (V : Type*) := 
(is_parallelogram : V → V → V → V → Prop)
(flip  : ∀ {a b c d}, is_parallelogram a b c d → is_parallelogram c d a b)
(flip' : ∀ {a b c d}, is_parallelogram a b c d → is_parallelogram a c b d)
(glue : ∀ {a b c d e f}, is_parallelogram a b c d → 
 is_parallelogram c d e f → is_parallelogram a b e f)
(thin : ∀ a b, is_parallelogram a b a b)
(fill : V → V → V → V)
(fill_iff : ∀ {a b c d}, is_parallelogram a b c d ↔ d = fill a b c)

namespace affine_space 

variables (V : Type*) [affine_space V] [inhabited V]
variables a b c d e f a' b' c' d' : V

instance translation_setoid : setoid (V × V) := 
{ r := λ st uv , is_parallelogram st.1 st.2 uv.1 uv.2,
  iseqv := by {
    split,
    {intro st, exact thin st.1 st.2},
    split,
    {intros st uv h, exact flip h},
    {intros st uv xy h k, exact glue h k} } }

variable {V}

lemma flip_iff : is_parallelogram a b c d ↔ is_parallelogram c d a b := 
 ⟨flip, flip⟩ 

lemma flip'_iff : is_parallelogram a b c d ↔ is_parallelogram a c b d := 
 ⟨flip', flip'⟩ 

lemma fill_prop : is_parallelogram a b c (fill a b c) := 
 (@fill_iff V _ _ _ _ _).mpr (rfl : fill a b c = fill a b c)

lemma fill_symm : fill a b c = fill a c b := 
 (@fill_iff V _ _ _ _ _).mp (flip' (fill_prop a b c))

variables {a b c d a' b' c' d'}

lemma inj_d : is_parallelogram a b c d  → 
              is_parallelogram a b c d' → d = d' := 
by { rw [fill_iff, fill_iff], intros h h', exact h.trans h'.symm }

lemma inj_c : is_parallelogram a b c  d → 
              is_parallelogram a b c' d → c = c' := 
by { intros h h', rw [flip'_iff, flip_iff] at h h', exact inj_d h h' }

lemma inj_b : is_parallelogram a b  c d → 
              is_parallelogram a b' c d → b = b' := 
by { intros h h', rw [flip'_iff] at h h', exact inj_c h h' }

lemma inj_a : is_parallelogram a  b c d → 
              is_parallelogram a' b c d → a = a' := 
by { intros h h', rw [flip_iff] at h h', exact inj_c h h' }

lemma fill_zero (a b : V) : fill a a b = b := 
 by { symmetry, rw [← fill_iff], apply flip', apply thin}

variable (V)
def translations : Type* := quotient (by apply_instance : setoid (V × V))

namespace translations

variable {V}

variables (t u : translations V)

def gap (a b : V) : translations V := quotient.mk ⟨a,b⟩

lemma gap_eq_iff : gap a b = gap c d ↔ is_parallelogram a b c d := 
⟨ @quotient.exact (V × V) _ ⟨a,b⟩ ⟨c,d⟩, @quotient.sound (V × V) _ ⟨a,b⟩ ⟨c,d⟩⟩ 

def add' : translations V → V → V := 
 quotient.lift (λ (ab : V × V) (x : V), fill ab.1 ab.2 x) 
  (λ ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ h, by {funext x,
  simp only [],rw[← fill_iff],
  change is_parallelogram a₁ b₁ a₂ b₂ at h,
  exact glue (flip h) (fill_prop a₁ b₁ x) })

theorem is_parallelogram_add' (a b : V) (t : translations V) :
 is_parallelogram a b (add' t a) (add' t b) := 
begin
  rcases t with ⟨⟨x,y⟩⟩,
  change is_parallelogram a b (fill x y a) (fill x y b),
  have ha : is_parallelogram x y a (fill x y a) := fill_prop x y a,
  have hb : is_parallelogram x y b (fill x y b) := fill_prop x y b,
  exact flip' (glue (flip ha) hb),
end

theorem gap_add' : add' (gap a b) c = fill a b c := rfl

theorem gap_add'' : add' (gap a b) a = b := 
by { change fill a b a = b, symmetry, rw[← fill_iff], exact thin a b }

theorem add'_gap (a : V) (t : translations V) : gap a (add' t a) = t := 
by { rcases t with ⟨⟨x,y⟩⟩, change gap a (fill x y a) = gap x y,
     rw [gap_eq_iff, flip_iff], apply fill_prop }

def zero : translations V := gap default default

lemma gap_eq_zero_iff (a b : V) : gap a b = zero ↔ a = b :=
begin
  dsimp [zero], rw [gap_eq_iff, flip_iff, fill_iff, fill_zero],
  split; intro h; exact h.symm
end

def neg : translations V → translations V := 
  quotient.lift (λ (ab : V × V), gap ab.2 ab.1)
    (λ ⟨a,b⟩ ⟨c,d⟩ h, gap_eq_iff.mpr (flip' (flip (flip' h))))

theorem neg_gap : neg (gap a b) = gap b a := rfl

def add : translations V → translations V → translations V := 
 λ t, quotient.lift (λ cd : V × V, gap cd.1 (add' t cd.2))
 (λ ⟨c₁,d₁⟩ ⟨c₂,d₂⟩ h, by {
  change is_parallelogram c₁ d₁ c₂ d₂ at h,
  change gap c₁ (add' t d₁) = gap c₂ (add' t d₂),
  rw [gap_eq_iff, flip'_iff], 
  exact glue (flip' h) (is_parallelogram_add' d₁ d₂ t) })

theorem add_gap : add (gap a b) (gap c d) = gap c (fill a b d) := rfl

theorem add_gap' : add (gap a b) (gap b c) = gap a c := 
 by { rw [add_gap, gap_eq_iff, flip_iff, flip'_iff],
      exact fill_prop a b c }

theorem zero_add (t : translations V) : add zero t = t := 
begin
  rcases t with ⟨a,b⟩, 
  change _ = gap a b,
  change gap a (fill default default b) = gap a b,
  rw [gap_eq_iff, fill_zero],
  apply thin
end

theorem zero_neg (t : translations V) : add t (neg t) = zero := 
begin
 rcases t with ⟨a,b⟩, 
 change add (gap a b) (gap b a) = zero,
 rw [add_gap, gap_eq_zero_iff, ← fill_iff], 
 apply thin,
end

theorem add_comm (t u : translations V) : add t u = add u t := 
begin
 rcases t with ⟨a,b⟩, 
 change add (gap a b) u = add u (gap a b),
 let c := add' u b, 
 have : u = gap b c := (add'_gap b u).symm, 
 rw [this, add_gap', add_gap, gap_eq_iff, flip'_iff, fill_symm, 
     fill_zero, flip'_iff],
 apply thin
end

theorem add_assoc (t u v : translations V) : 
 add (add t u) v = add t (add u v) := 
begin
 rcases t with ⟨a,b⟩, 
 let c := add' u b, 
 have : u = gap b c := (add'_gap b u).symm, rw [this],
 let d := add' v c, 
 have : v = gap c d := (add'_gap c v).symm, rw [this], 
 change add (add (gap a b) (gap b c)) (gap c d) = 
        add (gap a b) (add (gap b c) (gap c d)),
 simp only [add_gap'],
end

end translations

end affine_space