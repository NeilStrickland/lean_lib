/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Suppose we have a finite type `α`, and we consider the type 
`α₊ = (option α)`, which is essentially `α` with an extra 
element adjoined.  The power set `P(α₊)` then has an evident 
bijection with `P(α) ∐ P(α)`, or equivalently with 
`P(α) × bool`.  Here we set up this bijection.  There is 
another take on essentially the same thing in 
combinatorics/card_sign.lean.  In both cases the amount of
work involved seems unreasonably large, but we have not 
succeeded in reducing it.

-/

import data.fintype.basic algebra.big_operators.basic
import algebra.prod_equiv
import tactic.squeeze

namespace finset
open finset

variables {α : Type*} [decidable_eq α] [fintype α]

def finset_option_equiv : finset (option α) ≃ ((finset α) × bool) := {
 to_fun := λ s, ⟨univ.filter (λ a, some a ∈ s),if none ∈ s then tt else ff⟩,
 inv_fun := λ sb, cond sb.2 (insert none (sb.1.image some)) (sb.1.image some),
 left_inv := λ s, begin 
  simp only [],split_ifs; rw[cond];ext x;rcases x with _ | a,
  {simp[h],},
  {split,
   {intro ha,rcases mem_insert.mp ha with ha | ha,
    {cases ha},
    {rcases mem_image.mp ha with ⟨a',⟨ha,ea⟩⟩,
     have ea : a' = a := by {injection ea},
     exact ea ▸ (mem_filter.mp ha).right,
    }
   },{
    intro ha,apply mem_insert_of_mem,apply mem_image.mpr,
    use a,use mem_filter.mpr ⟨mem_univ a,ha⟩,   
   }
  },{
   split,
   {intro h',rcases mem_image.mp h' with ⟨a,⟨_,⟨_⟩⟩⟩,},
   {intro h',exact (h h').elim}
  },{
   split,
   {intro h',rcases mem_image.mp h' with ⟨a',⟨h',ea⟩⟩,
    exact ea ▸ (mem_filter.mp h').right,
   },
   {intro ha,apply mem_image.mpr,
    use a,use mem_filter.mpr ⟨mem_univ a,ha⟩,}
  }
 end,
 right_inv := λ ⟨s,b⟩, begin
  have ne_none : ∀ a : α, some a ≠ none := λ a e, by {rcases e,},
  have mem_some : ∀ a, a ∈ s ↔ some a ∈ s.image some := 
   λ a, ⟨mem_image_of_mem some,
        λ h, begin rcases mem_image.mp h with ⟨a',⟨h',e⟩⟩, 
                   have e : a' = a := by { injection e }, exact e ▸ h', 
            end⟩,
  have not_mem_some : none ∉ s.image some :=
   λ e, by {rcases mem_image.mp e with ⟨_,⟨_,⟨_⟩⟩⟩,},
  cases b;simp only[cond],
  {rw[if_neg not_mem_some],congr,ext a,rw[mem_filter,← mem_some],
   simp only[mem_univ a,true_and],
  },
  {rw[if_pos (mem_insert_self none (s.image some))],congr,
   ext a,rw[mem_filter,mem_insert,← mem_some],
   simp only[mem_univ a,ne_none a,true_and,false_or],
  }
 end
}

end finset
