/-
 Let p be a partition of a finite type α with decidable equality.  
 Then the type α₀ of blocks can be regarded as a quotient of α 
 in an obvious way, so we can construct a map s₀ : α₀ → β by
 defining a map s : α → β and checking that it respects 
 the relevant equivalence relation.  We can also do slightly 
 more subtle versions where s₀ x has a type (β x) depending on x.

 In this file we define two constructions in the above spirit.  
 We have avoided using the standard apparatus of equivalence 
 relations from mathlib, due to concerns about computational
 purity.  Those concerns may well be misguided, I have not yet
 understood the relevant issues properly.  It is possible to avoid
 that apparatus because we have strong assumptions about finiteness
 and decidability.  In order to take advantage of these, we use
 the theory developed in the file unique_element.lean
-/

import data.fintype tactic.squeeze tactic.fin_cases
import data.finset_transfer data.unique_element data.heq_extra 
import combinatorics.partition.basic

universes u v

open combinatorics.partition finset fintype
namespace combinatorics
namespace partition

variables (α : Type u) [fintype α] [decidable_eq α]

/-
 Here we assume given a partition p, a map s : α → β, a proof that
 s respects the relevant equivalence relation, and a block b of
 p.  As discussed previously, there is an induced map s₀ from the
 set of blocks to β, and thus a value y = (s₀ b) in β.  The 
 function below will return y packaged together with a proof of
 its defining property, namely that s x = y for any x in b.
-/
def rec0 {p : partition α} {β : Type v} [decidable_eq β]
 (s : α → β)
 (e : ∀ {a0 a1 : α}, p.block a0 = p.block a1 → s a0 = s a1) 
 (b : p.block_type) :
  { y : β // ∀ {x : α}, x ∈ b.val → s x = y } := 
begin
 let c := b.val.image s,
 have eu : ∃! y0 : β, y0 ∈ c := 
 begin
  cases mem_image.mp b.property with x0 x0_prop,
  replace x0_prop := (exists_prop.mp x0_prop).right,
  let y0 := s x0,
  existsi y0,split,
  {apply mem_image.mpr,existsi x0,simp[y0,x0_prop.subst(p.ispart.left x0)],},
  {intros y y_in_c,
   rcases mem_image.mp y_in_c with ⟨x,⟨x_in_b,s_x_y⟩⟩,
   let h0 : b.val = p.block x := (block_val_eq_of_mem x_in_b),
   let h1 := e (x0_prop.trans h0),
   exact (h1.trans s_x_y).symm,
  },
 end,
 let ue := finset.unique_element c (finset.card_one_of_prop c eu),
 let y := ue.val,
 have y_prop : ∀ x : α, x ∈ b.val → s x = y := 
 begin
  intros x x_in_b,
  have s_x_in_c : s x ∈ c := mem_image_of_mem s x_in_b,
  exact (@mem_singleton _ y (s x)).mp (ue.property.subst s_x_in_c),
 end,
 exact ⟨y,y_prop⟩ 
end

/-
 This function is similar to the previous one, except that we have a family
 of types (β b) indexed by the blocks b, instead of a single type β.  
 In this context, the defining property of y needs to be expressed in 
 terms of heterogenous equality.
-/
def rec1 {p : partition α} {β : p.block_type → Type v} 
 [∀ b, decidable_eq (β b)]
 (s : ∀ a : α, β (p.block_alt a))
 (e : ∀ a0 a1 : α, p.block a0 = p.block a1 → s a0 == s a1) 
 (b : p.block_type) :
  { y : β b // ∀ {x : α}, x ∈ b.val → s x == y } := 
begin
 let B := Σ b : p.block_type, β b,
 let m : ∀ (b : p.block_type) (y : β b), B := sigma.mk,
 let S : α → B := λ a, ⟨p.block_alt a,s a⟩,
 have E : ∀ (a0 a1 : α), p.block a0 = p.block a1 → S a0 = S a1 :=
 begin
  rintros a0 a1 same_block,
  have same_block_alt : p.block_alt a0 = p.block_alt a1 := subtype.eq same_block,
  have s_heq : s a0 == s a1 := e a0 a1 same_block,
  exact heq_sigma m same_block_alt s_heq,
 end,
 let Y := @rec0 α _ _ p B _ S E b,
 let V := Y.val,
 have h0 : V.1 = b := begin
  cases mem_image.mp b.property with x0 x0_prop,
  replace x0_prop := (exists_prop.mp x0_prop).right,
  have x0_in_b := x0_prop.subst (p.ispart.left x0),
  have h1 : V.1 = p.block_alt x0 :=
     congr_arg sigma.fst (Y.property x0_in_b).symm,
  have h2 : p.block_alt x0 = b := 
   subtype.eq x0_prop,
  exact h1.trans h2
 end,
 have h1 : β V.1 = β b := congr_arg β h0,
 let y0 : β V.1 := V.2,
 let y : β b := eq.rec_on h0 y0,
 have y_prop : ∀ x, x ∈ b.val → s x == y := 
 begin
  intros x x_in_b,
  let h3 : s x == y0 := heq_snd (Y.property x_in_b),
  let h4 : y0 == y := @heq_rec p.block_type β V.1 b h0 y0,
  exact h3.trans h4,
 end,
 exact ⟨y,y_prop⟩ 
end

end partition
end combinatorics
