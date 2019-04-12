import data.fintype 
import MAS114.fiber

namespace MAS114
namespace exercises_1
namespace Q03

/-
 Here we ask various questions about functions between the
 sets A = {1,2,..,10} and B = {1,2,...,100}.

 Everything would be a bit easier if we modified the question
 and used the sets {0,...,9} and {0,...,99} instead, because 
 Lean starts things at zero by default.  However, we have 
 decided to bite the bullet and deal with the extra complexity.
-/

def A0 : finset ℕ := (finset.range 11).erase 0
def B0 : finset ℕ := (finset.range 101).erase 0

def A := {n // n ∈ A0}
def B := {n // n ∈ B0}

instance A_fintype : fintype A := by {dsimp[A],apply_instance}
instance B_fintype : fintype B := by {dsimp[B],apply_instance}

lemma A_card : fintype.card A = 10 := 
 fintype.subtype_card A0 (by {intro H,refl})

lemma B_card : fintype.card B = 100 := 
 fintype.subtype_card B0 (by {intro H,refl})

lemma A_in_B {i : ℕ} (i_in_A : i ∈ A0) : i ∈ B0 := 
begin
 rcases (finset.mem_erase.mp i_in_A) with ⟨i_ne_0,i_in_range_11⟩,
 have i_lt_11 := finset.mem_range.mp i_in_range_11,
 have : 11 < 101 := dec_trivial,
 have i_lt_101 : i < 101 := lt_trans i_lt_11 this,
 have i_in_range_101 := finset.mem_range.mpr i_lt_101,
 exact finset.mem_erase.mpr ⟨i_ne_0,i_in_range_101⟩
end

/-
 We want to define f : A → B to be the inclusion.  
 In Lean, the proof that A is contained in B has to be 
 wrapped in to the definition of f.
-/

def f : A → B := λ ⟨i,i_in_A⟩, ⟨i,A_in_B i_in_A⟩

/- f is injective -/
lemma f_inj : function.injective f := 
begin
 rintros ⟨i,i_in_A⟩ ⟨j,j_in_A⟩ e,
 dsimp[f] at e,
 have e1 : i = j := congr_arg subtype.val e,
 exact subtype.eq e1
end

/-
 We now want to define g : B → A by g n = n for n ≤ 10, 
 and g n = 10 for n > 10.  We first define this as a 
 map g0 : B → ℕ, then give the proof that g0 B ⊆ A, 
 then use this to construct g as a map B → A.
-/
def g0 : B → ℕ := λ ⟨j,j_in_B⟩, if j < 11 then j else 10

lemma g0_in_A : ∀ b : B, (g0 b ∈ A0) 
| ⟨j,j_in_B⟩ := begin
 rcases (finset.mem_erase.mp j_in_B) with ⟨j_ne_0,j_in_range_101⟩,
 have j_lt_101 := finset.mem_range.mp j_in_range_101,
 by_cases h : j < 11,
 {have : g0 ⟨j,j_in_B⟩ = j := by {dsimp[g0],rw[if_pos h]},
  rw[this],
  let j_in_range_11 := finset.mem_range.mpr h,
  exact finset.mem_erase.mpr ⟨j_ne_0,j_in_range_11⟩, 
 },{
  have : g0 ⟨j,j_in_B⟩ = 10 := by {dsimp[g0],rw[if_neg h]},
  rw[this],
  exact finset.mem_erase.mpr ⟨dec_trivial,finset.mem_range.mpr dec_trivial⟩, 
 } 
end

def g (b : B) : A := ⟨g0 b,g0_in_A b⟩

/- We have g f a = a for all a ∈ A, so g is a left inverse for f -/

lemma gf : function.left_inverse g f 
| ⟨i,i_in_A⟩ := begin
 rcases (finset.mem_erase.mp i_in_A) with ⟨i_ne_0,i_in_range_11⟩,
 have i_lt_11 := finset.mem_range.mp i_in_range_11,
 apply subtype.eq,
 dsimp[f,g,g0],
 rw[if_pos i_lt_11],
end

/- g is surjective (because it has a right inverse) -/
lemma g_surj : function.surjective g := 
 function.surjective_of_has_right_inverse ⟨f,gf⟩

/- There is no injective map j : B → A, because |B| > |A|.
   We use the library theorem fintype.card_le_of_injective
   for this.
-/
lemma no_injection : ¬ ∃ j : B → A, function.injective j := 
begin
 rintro ⟨j,j_inj⟩,
 let h := fintype.card_le_of_injective j j_inj,
 rw[A_card,B_card] at h,
 exact not_lt_of_ge h dec_trivial,
end

/- There is no surjective map p : A → B, because |B| > |A|.
   We use the theorem card_le_of_projective for this.
   Surprisingly, this does not seem to be in the standard
   library.  It is proved in the separate file fiber.lean
   distributed alongside this one.
-/
lemma no_surjection : ¬ ∃ p : A → B, function.surjective p := 
begin 
 rintro ⟨p,p_surj⟩,
 let h := card_le_of_surjective p_surj,
 rw[A_card,B_card] at h,
 exact not_lt_of_ge h dec_trivial,
end

end Q03
end exercises_1
end MAS114