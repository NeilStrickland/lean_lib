import data.real.basic data.real.sqrt data.fintype.basic 
         algebra.big_operators data.nat.modeq data.int.modeq data.fin.basic
         data.zmod.basic
import tactic.find tactic.squeeze 
import combinatorics.fiber

namespace MAS114
namespace exercises_1
namespace Q2

/- part (i) 
 We are asked about the following definition:
  f : ℕ → ℝ is given by f n = sqrt n.

 There are two wrinkles when formalising this in Lean.

 Firstly, like most things with reals, we need to mark the 
 definition as noncomputable.  In Lean, "computation" means
 "exact computation", and we do not have algorithms for
 exact computation with real numbers.

 Secondly, the Lean library defines a function 
 real.sqrt : ℝ → ℝ, which is the ordinary square root for
 nonnegative arguments, but is zero for negative arguments,
 so it does not satisfy (real.sqrt x) ^ 2 = x in general.
 Because of this, we feel obliged to provide a proof that
 our function f has the expected property (f n) ^ 2 = n.
 Note here that the right hand side of this equation involves
 an implicit cast from ℕ to ℝ.  We will have to do quite a
 lot of messing around with casts like this.
-/

noncomputable def f : ℕ → ℝ := λ n, real.sqrt n

lemma f_spec : ∀ n : ℕ, (f n) ^ 2 = n := 
begin
 intro n,
 have h0 : (0 : ℝ) ≤ (n : ℝ) := nat.cast_le.mpr (nat.zero_le n),
 exact real.sq_sqrt h0,
end

/- f is injective -/
lemma f_inj : function.injective f := 
begin
 intros n₀ n₁ e,
 let n_R₀ := (n₀ : ℝ),
 let n_R₁ := (n₁ : ℝ),
 have e₁ : n_R₀ = n_R₁ := calc 
  n_R₀  = (f n₀) ^ 2 : (f_spec n₀).symm
    ... = (f n₁) ^ 2 : by rw[e]
    ... = n_R₁ : (f_spec n₁),
 exact nat.cast_inj.mp e₁,
end

/- f is not surjective -/
lemma f_not_surj : ¬ (function.surjective f) := 
begin
 intro f_surj,
 rcases (f_surj (1/2)) with ⟨n,e0⟩,
 let n_R := (n : ℝ),
 have e1 : 4 * n_R  = (((4 * n) : ℕ) : ℝ) := by
  { dsimp[n_R],rw[nat.cast_mul,nat.cast_bit0,nat.cast_bit0,nat.cast_one] },
 let e2 := calc 
  4 * n_R = 4 * ((f n) ^ 2) : by rw[f_spec n]
  ... = 4 * ((1 / 2) ^ 2) : by rw[e0]
  ... = 1 : by ring 
  ... = ((1 : ℕ) : ℝ) : by rw[nat.cast_one],
 let e3 : 4 * n = 1 := nat.cast_inj.mp (e1.symm.trans e2),
 let e4 := calc 
  0 = (4 * n) % 4 : (nat.mul_mod_right 4 n).symm
  ... = 1 % 4 : by rw[e3]
  ... = 1 : rfl,
 injection e4,
end

/- part (ii) -/

/-
 We are asked to pass judgement on the following "definition" : 

  g : ℤ → ℝ is given by g n = sqrt n.

 We do this by proving that there is no map g : ℤ → ℝ such that 
 (g n) ^ 2 = n for all n.
-/

lemma square_nonneg {α : Type*} [linear_ordered_ring α] (x : α) : 0 ≤ x * x := 
begin 
 rcases (le_or_gt 0 x) with x_nonneg | x_neg,
 {exact mul_nonneg x_nonneg x_nonneg,},
 {have x_nonpos : x ≤ 0 := le_of_lt x_neg,
  exact mul_nonneg_of_nonpos_of_nonpos x_nonpos x_nonpos
 }
end

/-
 I am surprised that this does not seem to be in the library.
 Perhaps I did not look in the right way.
-/
lemma neg_one_not_square {α : Type*} [linear_ordered_ring α] (x : α) :
 x * x ≠ -1 :=
begin
 intro e0,
 have e1 : (0 : α) ≤ -1 := e0.subst (square_nonneg x),
 have e2 : (-1 : α) < 0 := neg_neg_of_pos zero_lt_one,
 exact not_le_of_gt e2 e1,
end

lemma g_does_not_exist : ¬ ∃ (g : ℤ → ℝ), (∀ n : ℤ, (g n) ^ 2 = n) := 
begin
 rintro ⟨g,g_spec⟩,
 let x := g ( -1 ),
 have e0 : -1 = (( -1 : ℤ ) : ℝ) := by simp, 
 have e1 : x * x = -1 := 
  by { rw[← pow_two], dsimp[x], rw[e0], exact g_spec ( -1 )},
 exact neg_one_not_square x e1,
end

/- part (iii) -/

/-
 We are asked about the following definition:

  h : ℤ → ℕ is given by h(n) = |n|.

 There is no problem with formalising the definition.  Note,
 however, that the Lean library defines both 
 int.abs : ℤ → ℤ and int.nat_abs : ℤ → ℕ; we need the
 latter here.
-/

def h : ℤ → ℕ := int.nat_abs

/- h is not injective -/
lemma h_not_inj : ¬ (function.injective h) := 
begin
 intro h_inj,
 let e : (1 : ℤ) = (-1 : ℤ) := @h_inj (1 : ℤ) (-1 : ℤ) rfl,
 injection e,
end

/- h is surjective -/
lemma h_surj : function.surjective h := 
begin
 intro n,use n,refl,
end

/- part (iv) -/

/-
 We are asked to pass judgement on the following "definition" : 

  i : ℕ → ℕ is given by i n = 100 - n.

 We do this by proving that there is no map i : ℕ → ℕ such that 
 (i n) + n = 100 for all n.

  Note, however, that Lean would happily accept the definition
   def i (n : ℕ) : ℕ := 100 - n, but it would interpret the 
  minus sign as truncated subtraction, so that i n = 0 for n ≥ 100.
-/

lemma i_does_not_exist : ¬ ∃ (i : ℕ → ℕ), (∀ n : ℕ, (i n) + n = 100) := 
begin
 rintro ⟨i,i_spec⟩,
 have e0 : 101 ≤ 100 := (i_spec 101).subst (nat.le_add_left 101 (i 101)),
 let e1 : 100 < 101 := nat.lt_succ_self 100,
 exact not_le_of_gt e1 e0,
end

/- part (v) -/

/-
 We are asked about the following definition:

  j : ℤ → ℤ is given by j(n) = - n.

 There is no problem with formalising the definition.  We 
 then prove that j j = 1, so j is self-inverse.  We use 
 theorems from the library to deduce from this that j is
 injective, surjective and bijective, rather than working
 directly from the definitions. 
-/

def j : ℤ → ℤ := λ n, - n

lemma jj (n : ℤ) : j (j n) = n := by simp[j]

lemma j_inj : function.injective j := function.left_inverse.injective jj

lemma j_surj : function.surjective j := function.right_inverse.surjective jj

lemma j_bij : function.bijective j := ⟨j_inj,j_surj⟩

/- part (vi) -/

/-
 We are asked to pass judgement on the following "definition" : 

  k : ℝ → ℤ sends x ∈ ℝ to the closest integer.

 We define precisely what it means for n to be the closest
 integer to x : we should have | x - m | > | x - n | for any
 integer m ≠ n.  We then show that if m ∈ ℤ, there is no 
 closest integer to m + 1/2.  From this we deduce that there
 is no function k with the expected properties.

 This is much harder work than you might think.  A lot of the 
 problem is caused by the cast maps ℤ → ℚ → ℝ
-/

def is_closest_integer (n : ℤ) (x : ℝ) := 
 ∀ m : ℤ, m ≠ n → abs ( x - m ) > abs ( x - n )

/-
 Even basic identities like 1/2 - 1 = -1/2 cannot easily be 
 proved directly in ℝ, because there are no general algorithms
 for exact calculation in ℝ.  We need to work in ℚ and then 
 apply the cast map.
-/

def half_Q : ℚ := 1 / 2
def neg_half_Q : ℚ := - half_Q
noncomputable def half_R : ℝ := half_Q
noncomputable def neg_half_R : ℝ := neg_half_Q

/-
 Here is a small identity that could in principle be proved 
 by a long string of applications of the commutative ring axioms.
 The "ring" tactic automates the process of finding this string.

 For reasons that I do not fully understand, the ring tactic
 seems to work more reliably if we do it in a separate lemma 
 so that the terms are just free variables.  We can then 
 substitute values for this variables as an extra step.  In 
 particular, we will substitute h = 1/2, and then give a 
 separate argument that the final term 2 * h - 1 is zero.
-/
lemma misc_identity (m n h : ℝ) :
 (m + h) - (2 * m + 1 - n) = - ((m + h) - n) + (2 * h - 1) := 
  by ring 

/-
 We now prove that there is no closest integer to m + 1/2.
 The obvious approach would be to focus attention on the 
 candidates n = m and n = m + 1, but it turns out that that
 creates more work than necessary.  It is more efficient to 
 prove that for all n, the integer k = 2 m + 1 - n is different
 from n and lies at the same distance from m + 1/2, so 
 n does not have the required property.  
-/
lemma no_closest_integer (n m : ℤ) : 
 ¬ (is_closest_integer n ((m : ℝ) + half_R)) := 
begin
 intro h0,
 let x_Q : ℚ := (m : ℚ) + half_Q, 
 let x_R : ℝ := (m : ℝ) + half_R, 
 let k := 2 * m + 1 - n,
 by_cases e0 : k = n,
 {-- In this block we consider the possibility that k = n, and 
  -- show that it is impossible.
  exfalso,
  dsimp[k] at e0,
  let e1 := calc 
   (1 : ℤ) = (2 * m + 1 - n) + n - 2 * m : by ring
   ... = n + n - 2 * m : by rw[e0]
   ... = 2 * (n - m) : by ring,
  have e2 := calc 
   (1 : ℤ) = int.mod 1 2 : rfl
   ... = int.mod (2 * (n - m)) 2 : congr_arg (λ x, int.mod x 2) e1
   ... = 0 : int.mul_mod_right 2 (n - m),
  exact (dec_trivial : (1 : ℤ) ≠ 0) e2,
 },{
  let h1 := ne_of_gt (h0 k e0),
  let u_R := x_R - n,
  let v_R := x_R - k,
  have h2 : v_R = - u_R + (2 * half_R - 1) := begin
   dsimp[u_R,v_R,x_R,k],
   rw[int.cast_sub,int.cast_add,int.cast_mul,int.cast_bit0,int.cast_one],
   exact misc_identity (↑ m) (↑ n) half_R,
  end,
  have h3 : 2 * half_R - 1 = 0 := by { dsimp[half_R,half_Q], norm_num },
  rw[h3,add_zero] at h2,
  have h4 : abs v_R = abs u_R := by rw[h2,abs_neg],
  exact h1 h4,
 }
end

lemma k_does_not_exist : ¬ ∃ (k : ℝ → ℤ), (∀ x : ℝ, is_closest_integer (k x) x) := 
begin
 rintro ⟨k,k_spec⟩,
 let x : ℝ := (0 : ℤ) + half_R, 
 exact no_closest_integer (k x) 0 (k_spec x)
end

end Q2

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q3

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
lemma g_surj : function.surjective g := function.right_inverse.surjective gf

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
 let h := combinatorics.card_le_of_surjective p_surj,
 rw[A_card,B_card] at h,
 exact not_lt_of_ge h dec_trivial,
end

end Q3

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q4

/-
 This question is about "gappy sets", ie subsets s in 
 fin n = {0,...,n-1} such that s contains no adjacent pairs
 {i,i+1}.  
-/

/- We find it convenient to introduce a new notation for
   the zero element in fin m.  Notice that this only exists
   when m > 0, or equivalently, when m has the form 
   n.succ = n + 1 for some n.
-/
def fin.z {n : ℕ} : fin (n.succ) := 0

lemma fin.z_val {n : ℕ} : (@fin.z n).val = 0 := rfl

lemma fin.succ_ne_z {n : ℕ} (a : fin n) : a.succ ≠ fin.z := 
begin
 cases a with a_val a_is_lt,
 intro e,
 replace e := fin.veq_of_eq e, cases e
end

def is_gappy : ∀ {n : ℕ} (s : finset (fin n)), Prop 
| 0 _ := true
| (nat.succ n) s := ∀ a : fin n, ¬ (a.cast_succ ∈ s ∧ a.succ ∈ s)

instance is_gappy_decidable :
 forall {n : ℕ} (s : finset (fin n)), decidable (is_gappy s)
| 0 _ := by {dsimp[is_gappy],apply_instance}
| (nat.succ n) s := by {dsimp[is_gappy],apply_instance}

def gappy' (n : ℕ) : finset (finset (fin n)) := 
 finset.univ.filter is_gappy

def gappy (n : ℕ) : Type := 
 { s : finset (fin n) // is_gappy s }

instance {n : ℕ} : fintype (gappy n) := 
 by { dsimp[gappy], apply_instance }

instance {n : ℕ} : decidable_eq (gappy n) := 
 by { dsimp[gappy], apply_instance }

instance {n : ℕ} : has_repr (gappy n) := 
 ⟨λ (s : gappy n), repr s.val⟩

instance {n : ℕ} : has_mem (fin n) (gappy n) := ⟨λ i s, i ∈ s.val⟩

def shift {n : ℕ} (s : finset (fin n)) : finset (fin n.succ) := 
 s.image fin.succ

def unshift {n : ℕ} (s : finset (fin n.succ)) : finset (fin n) := 
 finset.univ.filter (λ a, a.succ ∈ s)

lemma mem_shift {n : ℕ} (s : finset (fin n)) (a : fin n.succ) :
 a ∈ shift s ↔ ∃ b : fin n, b ∈ s ∧ b.succ = a := 
begin
 rw[shift],split,
 {intro a_in_shift,
  rcases finset.mem_image.mp a_in_shift with ⟨b,⟨b_in_s,e⟩⟩,
  use b,
  exact ⟨b_in_s,e⟩, 
 },{
  rintro ⟨b,⟨b_in_s,e⟩⟩,
  exact finset.mem_image.mpr ⟨b,⟨b_in_s,e⟩⟩, 
 }
end

lemma zero_not_in_shift {n : ℕ} (s : finset (fin n)) : 
 fin.z ∉ shift s := 
begin
 intro h0,
 rcases ((mem_shift s) 0).mp h0 with ⟨⟨b,b_is_lt⟩,⟨b_in_s,e⟩⟩,
 cases congr_arg subtype.val e
end

lemma succ_mem_shift_iff {n : ℕ} (s : finset (fin n)) (a : fin n) : 
 a.succ ∈ shift s ↔ a ∈ s := 
begin
 rw[mem_shift s a.succ],
 split,{
   rintro ⟨b,⟨b_in_s,u⟩⟩,
   rw[(fin.succ_inj.mp u).symm],
   exact b_in_s,
 },{
   intro a_in_s,use a,exact ⟨a_in_s,rfl⟩,
 }
end

lemma mem_unshift {n : ℕ} (s : finset (fin n.succ)) (a : fin n) :
 a ∈ unshift s ↔ a.succ ∈ s := 
begin
 rw[unshift,finset.mem_filter],
 split,
 {intro h,exact h.right},
 {intro h,exact ⟨finset.mem_univ a,h⟩ }
end

lemma unshift_shift {n : ℕ} (s : finset (fin n)) : 
 unshift (shift s) = s := 
begin
 ext,rw[mem_unshift (shift s) a],rw[succ_mem_shift_iff],
end

lemma unshift_insert {n : ℕ} (s : finset (fin n.succ)) : 
 unshift (insert fin.z s) = unshift s := 
begin
 ext,rw[mem_unshift,mem_unshift,finset.mem_insert],
 split,
 {intro h,rcases h with h0 | h1,
  {exfalso,exact fin.succ_ne_z a h0},
  {exact h1}
 },
 {exact λ h,or.inr h}
end

lemma shift_unshift0 {n : ℕ} (s : finset (fin n.succ)) (h : fin.z ∉ s) :
 shift (unshift s) = s := 
begin
 ext, 
 rcases a with ⟨_ | b_val,a_is_lt⟩,
 {have e : @fin.z n = ⟨0,a_is_lt⟩ := fin.eq_of_veq rfl,
  rw[← e],simp only[zero_not_in_shift,h],
 },{
  let b : fin n := ⟨b_val,nat.lt_of_succ_lt_succ a_is_lt⟩,
  have e : b.succ = ⟨b_val.succ,a_is_lt⟩ := 
    by { apply fin.eq_of_veq, refl },
  rw[← e,succ_mem_shift_iff (unshift s) b,mem_unshift s b],
 }
end

lemma shift_unshift1 {n : ℕ} (s : finset (fin n.succ)) (h : fin.z ∈ s) :
 insert fin.z (shift (unshift s)) = s :=
begin
 ext, 
 rw[finset.mem_insert],
 rcases a with ⟨_ | b_val,a_is_lt⟩,
 {have e : @fin.z n = ⟨0,a_is_lt⟩ := fin.eq_of_veq rfl,
  rw[← e],simp only[h,eq_self_iff_true,true_or],
 },{
  let b : fin n := ⟨b_val,nat.lt_of_succ_lt_succ a_is_lt⟩,
  have e : b.succ = ⟨b_val.succ,a_is_lt⟩ := 
    by { apply fin.eq_of_veq, refl, },
  rw[← e,succ_mem_shift_iff (unshift s) b,mem_unshift s b],
  split,
  {rintro (u0 | u1),
   {exfalso,exact fin.succ_ne_z b u0,},
   {exact u1}
  },
  {intro h,right,exact h,}
 }
end

lemma shift_gappy : ∀ {n : ℕ} {s : finset (fin n)},
 is_gappy s → is_gappy (shift s)
| 0 _ _ := λ a, fin.elim0 a
| (nat.succ n) s s_gappy := begin
 rintros ⟨a,a_is_lt⟩ ⟨a_in_shift,a_succ_in_shift⟩,
 let a₀ : fin n.succ := ⟨a,a_is_lt⟩,
 let a_in_s : a₀ ∈ s := 
   (succ_mem_shift_iff s a₀).mp a_succ_in_shift,
 rcases (mem_shift s a₀.cast_succ).mp a_in_shift with ⟨⟨b,b_is_lt⟩,⟨b_in_s,eb⟩⟩,
 let b₀ : fin n.succ := ⟨b,b_is_lt⟩,
 replace eb := congr_arg subtype.val eb,
 change b.succ = a at eb,
 let c_is_lt : b < n :=
  nat.lt_of_succ_lt_succ (eb.symm ▸ a_is_lt), 
 let c₀ : fin n := ⟨b,c_is_lt⟩,
 have ebc : b₀ = fin.cast_succ c₀ := fin.eq_of_veq rfl,
 have eac : a₀ = fin.succ c₀ := 
   fin.eq_of_veq (nat.succ.inj (by { change a.succ = b.succ.succ, rw[← eb],})),
 change b₀ ∈ s at b_in_s, rw[ebc] at b_in_s,
 rw[eac] at a_in_s,
 exact s_gappy c₀ ⟨b_in_s,a_in_s⟩, 
end

lemma unshift_gappy : ∀ {n : ℕ} {s : finset (fin n.succ)},
 is_gappy s → is_gappy (unshift s)
| 0 _ _ := trivial
| (nat.succ n) s s_gappy := begin
 rintros ⟨a,a_is_lt⟩ ⟨a_in_unshift,a_succ_in_unshift⟩,
 let a₀ : fin n := ⟨a,a_is_lt⟩,
 let a_succ_in_s := (mem_unshift s a₀.cast_succ).mp a_in_unshift,
 let a_succ_succ_in_s := (mem_unshift s a₀.succ).mp a_succ_in_unshift,
 have e : a₀.cast_succ.succ = a₀.succ.cast_succ := fin.eq_of_veq rfl,
 rw[e] at a_succ_in_s,
 exact s_gappy a₀.succ ⟨a_succ_in_s,a_succ_succ_in_s⟩,
end

lemma insert_gappy : ∀ {n : ℕ} {s : finset (fin n.succ.succ)}, 
 is_gappy s → (∀ (a : fin n.succ.succ), a ∈ s → a.val ≥ 2) → 
  is_gappy (insert fin.z s) := 
begin
 rintros n s s_gappy s_big ⟨a,a_is_lt⟩ ⟨a_in_t,a_succ_in_t⟩,
 rcases finset.mem_insert.mp a_succ_in_t with a_succ_zero | a_succ_in_s;
 let a₀ : fin n.succ := ⟨a,a_is_lt⟩,
 {exact fin.succ_ne_z a₀ a_succ_zero},
 let a_pos : 0 < a := nat.lt_of_succ_lt_succ (s_big a₀.succ a_succ_in_s),
 rcases finset.mem_insert.mp a_in_t with a_zero | a_in_s,
 {replace a_zero : a = 0 := congr_arg subtype.val a_zero,
  rw[a_zero] at a_pos,
  exact lt_irrefl 0 a_pos,
 },{
  exact s_gappy a₀ ⟨a_in_s,a_succ_in_s⟩, 
 }
end

def i {n : ℕ} (s : gappy n) : gappy n.succ := 
 ⟨shift s.val,shift_gappy s.property⟩ 

lemma i_val {n : ℕ} (s : gappy n) : (i s).val = shift s.val := rfl

lemma zero_not_in_i {n : ℕ} (s : gappy n) : fin.z ∉ (i s) := 
 zero_not_in_shift s.val

lemma shift_big {n : ℕ} (s : finset (fin n)) : 
 ∀ (a : fin n.succ.succ), a ∈ shift (shift s) → a.val ≥ 2 := 
begin
 rintro ⟨a,a_is_lt⟩ ma,
 rcases (mem_shift (shift s) ⟨a,a_is_lt⟩).mp ma with ⟨⟨b,b_is_lt⟩,⟨mb,eb⟩⟩,
 rcases (mem_shift s ⟨b,b_is_lt⟩).mp mb with ⟨⟨c,c_is_lt⟩,⟨mc,ec⟩⟩,
 rw[← eb,← ec],
 apply nat.succ_le_succ,
 apply nat.succ_le_succ,
 exact nat.zero_le c
end

def j {n : ℕ} (s : gappy n) : gappy n.succ.succ := 
 ⟨insert fin.z (shift (shift s.val)),
  begin 
   let h := insert_gappy (shift_gappy (shift_gappy s.property)) (shift_big s.val),
   exact h,
  end⟩

lemma j_val {n : ℕ} (s : gappy n) :
 (j s).val = insert fin.z (shift (shift s.val)) := rfl

lemma zero_in_j {n : ℕ} (s : gappy n) : fin.z ∈ (j s) := 
 finset.mem_insert_self _ _

def p {n : ℕ} : (gappy n) ⊕ (gappy n.succ) → gappy n.succ.succ 
| (sum.inl s) := j s
| (sum.inr s) := i s

def q {n : ℕ} (s : gappy n.succ.succ) : (gappy n) ⊕ (gappy n.succ) := 
if fin.z ∈ s then
 sum.inl ⟨unshift (unshift s.val),unshift_gappy (unshift_gappy s.property)⟩
else
 sum.inr ⟨unshift s.val,unshift_gappy s.property⟩ 

lemma qp {n : ℕ} (s : (gappy n) ⊕ (gappy n.succ)) : q (p s) = s := 
begin
 rcases s with s | s; dsimp[p,q],
 {rw[if_pos (zero_in_j s)],
  congr,apply subtype.eq,
  change unshift (unshift (j s).val) = s.val,
  rw[j_val,unshift_insert,unshift_shift,unshift_shift],
 },
 {rw[if_neg (zero_not_in_i s)],congr,apply subtype.eq,
  change unshift (i s).val = s.val,
  rw[i_val,unshift_shift],
 }
end

lemma pq {n : ℕ} (s : gappy n.succ.succ) : p (q s) = s := 
begin
 dsimp[q],split_ifs; dsimp[p]; apply subtype.eq,
 {rw[j_val],
  change insert fin.z (shift (shift (unshift (unshift s.val )))) = s.val,
  have z_not_in_us : fin.z ∉ unshift s.val := begin
   intro z_in_us,
   let z_succ_in_s := (mem_unshift s.val fin.z).mp z_in_us,
   exact s.property fin.z ⟨h,z_succ_in_s⟩,
  end,
  rw[shift_unshift0 (unshift s.val) z_not_in_us],
  rw[shift_unshift1 s.val h],
 },{
  rw[i_val],
  change shift (unshift s.val) = s.val,
  exact shift_unshift0 s.val h,  
 }
end

def gappy_equiv {n : ℕ} :
 ((gappy n) ⊕ (gappy n.succ)) ≃ (gappy n.succ.succ) := {
 to_fun := p,
 inv_fun := q,
 left_inv := qp,
 right_inv := pq
}

lemma gappy_card_step (n : ℕ) :
 fintype.card (gappy n.succ.succ) =
  fintype.card (gappy n) + fintype.card (gappy n.succ) := 
by rw[← fintype.card_congr (@gappy_equiv n),fintype.card_sum]

def fibonacci : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (nat.succ (nat.succ n)) := (fibonacci n) + (fibonacci n.succ)

lemma gappy_card : ∀ (n : ℕ), fintype.card (gappy n) = fibonacci n.succ.succ
| 0 := rfl
| 1 := rfl
| (nat.succ (nat.succ n)) := begin
 rw[gappy_card_step n,gappy_card n,gappy_card n.succ],
 dsimp[fibonacci],refl,
end

end Q4

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q5

def A : finset ℕ := [0,1,2].to_finset
def B : finset ℕ := [0,1,2,3].to_finset
def C : finset ℤ := [-2,-1,0,1,2].to_finset
def D : finset ℤ := [-3,-2,-1,0,1,2,3].to_finset

lemma int.lt_succ_iff {n m : ℤ} : n < m + 1 ↔ n ≤ m := 
 ⟨int.le_of_lt_add_one,int.lt_add_one_of_le⟩ 

lemma nat.square_le {n m : ℕ} : m ^ 2 ≤ n ↔ m ≤ n.sqrt := 
 ⟨λ h0, le_of_not_gt (λ h1, not_le_of_gt ((pow_two m).symm.subst (nat.sqrt_lt.mp h1)) h0),
  λ h0, le_of_not_gt (λ h1,not_le_of_gt (nat.sqrt_lt.mpr ((pow_two m).subst h1)) h0)⟩ 

lemma nat.square_lt {n m : ℕ} : m ^ 2 < n.succ ↔ m ≤ n.sqrt :=
 (@nat.lt_succ_iff (m ^ 2) n).trans (@nat.square_le n m)

lemma int.abs_le {n m : ℤ} : abs m ≤ n ↔ (- n ≤ m ∧ m ≤ n) := 
begin
 by_cases hm : 0 ≤ m,
 { rw[abs_of_nonneg hm],
   exact ⟨ 
     λ hmn, ⟨le_trans (neg_nonpos_of_nonneg (le_trans hm hmn)) hm,hmn⟩,
     λ hmn, hmn.right
      ⟩ 
 },{
   let hma := le_of_lt (lt_of_not_ge hm),
   let hmb := neg_nonneg_of_nonpos hma,
   rw[abs_of_nonpos hma],
   exact ⟨ 
     λ hmn, ⟨(neg_neg m) ▸ (neg_le_neg hmn),le_trans (le_trans hma hmb) hmn⟩,
     λ hmn, (neg_neg n) ▸ (neg_le_neg hmn.left), 
    ⟩
 }
end

lemma int.abs_le' {n : ℕ} {m : ℤ} : m.nat_abs ≤ n ↔ (- (n : ℤ) ≤ m ∧ m ≤ n) := 
begin
 let h := @int.abs_le n m,
 rw[int.abs_eq_nat_abs,int.coe_nat_le] at h,
 exact h,
end

lemma int.abs_square (n : ℤ) : n ^ 2 = (abs n) ^ 2 := begin
 by_cases h0 : n ≥ 0,
 {rw[abs_of_nonneg h0]},
 {rw[abs_of_neg (lt_of_not_ge h0),pow_two,pow_two,neg_mul_neg],}
end

lemma int.abs_square' (n : ℤ) : n ^ 2 = ((int.nat_abs n) ^ 2 : ℕ) :=
 calc 
   n ^ 2 = n * n : pow_two n
   ... = ↑ (n.nat_abs * n.nat_abs) : int.nat_abs_mul_self.symm
   ... = ↑ (n.nat_abs ^ 2 : ℕ) : by rw[(pow_two n.nat_abs).symm]

lemma int.square_le {n : ℕ} {m : ℤ} : 
 m ^ 2 ≤ n ↔ - (n.sqrt : ℤ) ≤ m ∧ m ≤ n.sqrt := 
begin
 rw[int.abs_square',int.coe_nat_le,nat.square_le,int.abs_le'],
end

lemma int.square_lt {n : ℕ} {m : ℤ} : 
 m ^ 2 < n.succ ↔ - (n.sqrt : ℤ) ≤ m ∧ m ≤ n.sqrt := 
begin
 rw[int.abs_square',int.coe_nat_lt,nat.square_lt,int.abs_le'],
end

lemma A_spec (n : ℕ) : n ∈ A ↔ n ^ 2 < 9 := begin
 have sqrt_8 : 2 = nat.sqrt 8 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 exact calc
  n ∈ A ↔ n ∈ finset.range 3 : by rw[(dec_trivial : A = finset.range 3)]
  ... ↔ n < 3 : finset.mem_range
  ... ↔ n ≤ 2 : by rw[nat.lt_succ_iff]
  ... ↔ n ≤ nat.sqrt 8 : by rw[← sqrt_8]
  ... ↔ n ^ 2 < 9 : by rw[nat.square_lt]
end

lemma B_spec (n : ℕ) : n ∈ B ↔ n ^ 2 ≤ 9 := begin
 have sqrt_9 : 3 = nat.sqrt 9 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 exact calc
  n ∈ B ↔ n ∈ finset.range 4 : by rw[(dec_trivial : B = finset.range 4)]
  ... ↔ n < 4 : finset.mem_range
  ... ↔ n ≤ 3 : by rw[nat.lt_succ_iff]
  ... ↔ n ≤ nat.sqrt 9 : by rw[← sqrt_9]
  ... ↔ n ^ 2 ≤ 9 : by rw[nat.square_le]
end

lemma C_spec (n : ℤ) : n ∈ C ↔ n ^ 2 < 9 := begin
 have sqrt_8 : 2 = nat.sqrt 8 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 have e0 : (3 : ℤ) = ((2 : ℕ) : ℤ) + (1 : ℤ) := rfl,
 have e1 : (-2 : ℤ) = - ((2 : ℕ) : ℤ) := rfl, 
 have e2 : ((nat.succ 8) : ℤ)  = 9 := rfl,
 let e3 := @int.square_lt 8 n,
 let J := finset.Ico (-2 : ℤ) (3 : ℤ),
 exact calc
  n ∈ C ↔ n ∈ J :
   by rw[(dec_trivial : C = J)]
  ... ↔ -2 ≤ n ∧ n < 3 : finset.mem_Ico
  ... ↔ - ((2 : ℕ) : ℤ) ≤ n ∧ n < (2 : ℕ) + 1 : by rw[e0,e1]
  ... ↔ - ((2 : ℕ) : ℤ) ≤ n ∧ n ≤ (2 : ℕ) : by rw[int.lt_succ_iff]
  ... ↔ - (nat.sqrt 8 : ℤ) ≤ n ∧ n ≤ nat.sqrt 8 : by rw[← sqrt_8]
  ... ↔ n ^ 2 < nat.succ 8 : by rw[e3]
  ... ↔ n ^ 2 < 9 : by rw[e2],
end

lemma D_spec (n : ℤ) : n ∈ D ↔ n ^ 2 ≤ 9 := begin
 have sqrt_9 : 3 = nat.sqrt 9 := nat.eq_sqrt.mpr ⟨dec_trivial,dec_trivial⟩,
 have e0 : (4 : ℤ) = ((3 : ℕ) : ℤ) + (1 : ℤ) := rfl,
 have e1 : (-3 : ℤ) = - ((3 : ℕ) : ℤ) := rfl, 
 have e2 : ((9 : ℕ) : ℤ)  = 9 := rfl,
 let e3 := @int.square_le 9 n,
 let J := finset.Ico (-3 : ℤ) (4 : ℤ),
 exact calc
  n ∈ D ↔ n ∈ J :
   by rw[(dec_trivial : D = J)]
  ... ↔ -3 ≤ n ∧ n < 4 : finset.mem_Ico
  ... ↔ - ((3 : ℕ) : ℤ) ≤ n ∧ n < (3 : ℕ) + 1 : by rw[e0,e1]
  ... ↔ - ((3 : ℕ) : ℤ) ≤ n ∧ n ≤ (3 : ℕ) : by rw[int.lt_succ_iff]
  ... ↔ - (nat.sqrt 9 : ℤ) ≤ n ∧ n ≤ nat.sqrt 9 : by rw[← sqrt_9]
  ... ↔ n ^ 2 ≤ (9 : ℕ) : by rw[e3]
  ... ↔ n ^ 2 ≤ 9 : by rw[e2]
end

end Q5

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q6

def A : finset ℕ := [1,2,4].to_finset
def B : finset ℕ := [2,3,5].to_finset
def C : finset ℕ := [1,2,3,4,5].to_finset
def D : finset ℕ := [2].to_finset
def E : finset ℕ := [3,4].to_finset

lemma L1 : A ∪ B = C := dec_trivial
lemma L2 : A ∩ B = D := dec_trivial 
lemma L3 : D ∩ E = ∅ := dec_trivial 

end Q6

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q7

local attribute [instance] classical.prop_decidable

lemma L1 (U : Type) (A B : set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ :=
 by { simp }

lemma L2 (U : Type) (A B : set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := 
begin
 ext x,
 rw[set.mem_union,set.mem_compl_iff,set.mem_compl_iff,set.mem_compl_iff],
 by_cases hA : (x ∈ A); by_cases hB : (x ∈ B); simp[hA,hB], 
end

end Q7

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q8

end Q8

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q9

def even (n : ℤ) := ∃ k : ℤ, n = 2 * k

def odd (n : ℤ) := ∃ k : ℤ, n = 2 * k + 1

lemma L1 (n : ℤ) : even n → even (n ^ 2) := 
begin
 rintro ⟨k,e⟩,
 use n * k,
 rw[e,pow_two],ring,
end

lemma L2 (n m : ℤ) : even n → even m → even (n + m) := 
begin
 rintros ⟨k,ek⟩ ⟨l,el⟩,
 use k + l,
 rw[ek,el],
 ring,
end

lemma L3 (n m : ℤ) : odd n → odd m → odd (n * m) := 
begin
 rintros ⟨k,ek⟩ ⟨l,el⟩,
 use k + l + 2 * k * l,
 rw[ek,el],
 ring,
end

/- Do the converses -/

end Q9

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q10 

def f : ℝ → ℝ := λ x, x ^ 2 - 7 * x + 10 
def f_alt : ℝ → ℝ := λ x, (x - 2) * (x - 5)

lemma f_eq (x : ℝ) : f x = f_alt x := by {dsimp[f,f_alt],ring}
lemma f_two  : f 2 = 0 := by {dsimp[f],ring}
lemma f_five : f 5 = 0 := by {dsimp[f],ring}
lemma two_ne_five : (2 : ℝ) ≠ (5 : ℝ) := 
begin
 intro e,
 have h2 : (2 : ℝ) = ((2 : ℕ) : ℝ) := by {simp}, 
 have h5 : (5 : ℝ) = ((5 : ℕ) : ℝ) := by {simp}, 
 rw[h5,h2] at e,
 exact (dec_trivial : 2 ≠ 5) (nat.cast_inj.mp e),
end

def P1 (x : ℝ) : Prop := f x = 0 → x = 2 ∧ x = 5
def P2 (x : ℝ) : Prop := f x = 0 → x = 2 ∨ x = 5

lemma L1 : ¬ (∀ x : ℝ, P1 x) := 
begin
 intro h_P1,
 exact two_ne_five (h_P1 2 f_two).right,
end

lemma L2 : ∀ x : ℝ, P2 x := 
begin
 intros x fx,
 rw[f_eq x] at fx,
 dsimp[f_alt] at fx,
 rcases eq_zero_or_eq_zero_of_mul_eq_zero fx with x_eq_2 | x_eq_5,
 {exact or.inl (sub_eq_zero.mp x_eq_2)},
 {exact or.inr (sub_eq_zero.mp x_eq_5)}
end

end Q10 

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q11

end Q11

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q12

def f : ℚ → ℚ := λ x, x * (x + 1) * (2 * x + 1) / 6

lemma f_step (x : ℚ) : f (x + 1) = (f x) + (x + 1) ^ 2 := 
begin
 dsimp[f],
 apply sub_eq_zero.mp,
 rw[pow_two],
 ring,
end

lemma sum_of_squares : ∀ (n : ℕ), 
 (((finset.range n.succ).sum (λ i, i ^ 2)) : ℚ) = f n
| 0 := begin
   rw[finset.sum_range_succ,finset.sum_range_zero,f],simp, 
  end
| (n + 1) := begin
  rw[finset.sum_range_succ,sum_of_squares n],
  have : (((n + 1) : ℕ) : ℚ) = ((n + 1) : ℚ ) := by simp, 
  rw[this,f_step n],
 end

end Q12

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q13

end Q13

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q14

def f : ℚ → ℚ := λ x, (x + 1) / (2 * x)

lemma f_step (x : ℚ) : x > 1 → (1 - 1 / (x ^ 2)) * f (x - 1) = f x := 
begin
 intro x_big,
 let d := 2 * (x - 1) * (x ^ 2) ,
 let nz_2 : (2 : ℚ) ≠ 0 := by norm_num,
 /- Prove that all relevant denominators are nonzero -/
 let nz_x  : x ≠ 0     := (ne_of_lt (by linarith [x_big])).symm,
 let nz_2x : 2 * x ≠ 0 := mul_ne_zero nz_2 nz_x,
 let nz_x2 : x ^ 2 ≠ 0 := by {rw[pow_two], exact mul_ne_zero nz_x nz_x},
 let nz_y  : x - 1 ≠ 0 := (ne_of_lt (by linarith [x_big])).symm,
 let nz_2y : 2 * (x - 1) ≠ 0 := mul_ne_zero nz_2 nz_y,
 let nz_d : d ≠ 0 := mul_ne_zero nz_2y nz_x2,
 let e0 := calc
  (x ^ 2) * (1 - 1 / (x ^ 2)) = (x ^ 2) * 1 - (x ^ 2) * (1 / (x ^ 2)) : 
   by rw[mul_sub] 
  ... = x ^ 2 - 1 : by rw[mul_one,mul_div_cancel' 1 nz_x2],
 let e1 := calc 
  d * (1 - 1 / (x ^ 2)) = (2 * (x - 1)) * ((x ^ 2) * (1 - 1 / (x ^ 2))) :
   by rw[mul_assoc]
  ... = (2 * (x - 1)) * (x ^ 2 - 1) : by rw[e0]
  ... = (x ^ 2 - 1) * (2 * (x - 1)) : by rw[mul_comm],
 let e2 : (x - 1) + 1 = x := by ring,
 let e3 := calc 
  (2 * (x - 1)) * f (x - 1) = (2 * (x - 1)) * (((x - 1) + 1) / (2 * (x - 1))) : rfl
  ... = (2 * (x - 1)) * (x / (2 * (x - 1))) : by rw[e2]
  ... = x * (2 * (x - 1) / (2 * (x - 1))) : mul_div_left_comm (2 * (x - 1)) x (2 * (x - 1))
  ... = x : by rw[div_self nz_2y,mul_one],
 let e4 := calc
  d * ((1 - 1 / (x ^ 2)) * f (x - 1)) = (d * (1 - 1 / (x ^ 2))) * f (x - 1) :
   by rw[← mul_assoc]
  ... = (x ^ 2 - 1) * (2 * (x - 1)) * f (x - 1) : by rw[e1]
  ... = (x ^ 2 - 1) * x : by rw[mul_assoc,e3]
  ... = (x ^ 2) * x - 1 * x : by rw[sub_mul]
  ... = x ^ 3 - x : by rw[← pow_succ',one_mul],
 let e5 : d = (x * x - x) * (2 * x) := by {dsimp[d],ring},
 let e6 := calc 
  d * f x = d * ((x + 1) / (2 * x)) : rfl 
  ... = ((x * x - x) * (2 * x)) * ((x + 1) / (2 * x)) : by rw[e5]
  ... = (x * x - x) * ((2 * x) * ((x + 1) / (2 * x))) : by rw[mul_assoc]
  ... = (x * x - x) * (x + 1) : by rw[mul_div_left_comm,div_self nz_2x,mul_one]
  ... = x ^ 3 - x : by ring,
  exact (mul_right_inj' nz_d).mp (e4.trans e6.symm)
end

lemma product_formula : ∀ (n : ℕ), 
 (finset.range n).prod (λ k, ((1 - 1 / ((k + 2) ^ 2)) : ℚ)) = f (n + 1)
| 0 := by { rw[finset.prod_range_zero,f], norm_num }
| (n + 1) := begin
 have e0 : 1 < n + 2 := by linarith,
 have e1 : (1 : ℚ) < ((n + 2) : ℕ) := by {
  have : (1 : ℚ) = (1 : ℕ) := by norm_num, rw[this],
  exact nat.cast_lt.mpr e0,
 }, 
 rw[nat.cast_add,nat.cast_bit0,nat.cast_one] at e1,
 rw[finset.prod_range_succ,product_formula n],
 let e2 := f_step (n + 2) e1,
 have e3 : (n : ℚ) + 2 - 1 = n + 1 := by ring,
 have e4 : (((n + 1) : ℕ) : ℚ) + 1 = (n : ℚ) + 2 :=
  by { rw[nat.cast_add,nat.cast_one],ring},
 rw[e3] at e2,
 rw[mul_comm,e2,e4],
end

end Q14

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q15

end Q15 

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q16

lemma nat.bodd_even (n : ℕ) : (2 * n).bodd = ff := 
 by {rw[nat.bodd_mul,nat.bodd_two,band],} 

lemma nat.bodd_odd (n : ℕ) : (2 * n + 1).bodd = tt := 
 by {rw[nat.bodd_add,nat.bodd_even],refl} 

lemma nat.div2_even : ∀ (n : ℕ), (2 * n).div2 = n 
| 0 := rfl
| (n + 1) := begin 
 have : 2 * (n + 1) = (2 * n + 1).succ := by ring_nf,
 rw[this,nat.div2_succ,nat.bodd_odd,bool.cond_tt],
 rw[nat.div2_succ,nat.bodd_even,bool.cond_ff],
 rw[nat.div2_even n],
end

lemma nat.div2_odd (n : ℕ) : (2 * n + 1).div2 = n := 
by {rw[nat.div2_succ,nat.bodd_even,bool.cond_ff,nat.div2_even]}

lemma wf_lemma : ∀ (m : ℕ), m.succ.div2 < m.succ 
| 0 := dec_trivial
| (nat.succ m) := begin
 rw[nat.div2_succ],
 cases m.succ.bodd; simp only[bool.cond_tt,bool.cond_ff],
 exact lt_trans (wf_lemma m) m.succ.lt_succ_self,
 exact nat.succ_lt_succ (wf_lemma m)
end

lemma wf_lemma' (m : ℕ) :
 cond (nat.bodd m) (nat.succ (nat.div2 m)) (nat.div2 m) < nat.succ m :=
begin
 cases m,
 {exact dec_trivial,},
 let u := wf_lemma m,
 cases m.succ.bodd; simp only[bool.cond_tt,bool.cond_ff],
 exact lt_trans u m.succ.lt_succ_self,
 exact nat.succ_lt_succ u,
end

def f : bool → ℕ → ℕ 
| ff u := 4 * u + 1
| tt u := 9 * u + 2

def a : ℕ → ℕ 
| 0 := 0 
| (nat.succ m) := 
   have cond (nat.bodd m) (nat.succ (nat.div2 m)) (nat.div2 m) < nat.succ m := wf_lemma' m,
   f m.succ.bodd (a m.succ.div2)

lemma a_even (n : ℕ) : n > 0 → a (2 * n) = 4 * (a n) + 1 := 
begin
 intro n_pos,
 let k := n.pred,
 have e0 : n = k + 1 := (nat.succ_pred_eq_of_pos n_pos).symm,
 let m := 2 * k + 1,
 have e1 : 2 * n = m.succ := calc
  2 * n = 2 * (k + 1) : by rw[e0]
  ... = 2 * k + 2 : by rw[mul_add,mul_one]
  ... = m.succ : rfl,
 rw[e1,a,← e1,nat.bodd_even,nat.div2_even,f],
end

lemma a_odd (n : ℕ) : a (2 * n + 1) = 9 * (a n) + 2 := 
begin
 change a (2 * n).succ = 9 * (a n) + 2,
 rw[a,nat.bodd_odd,nat.div2_odd,f],
end

lemma a_even_step (n : ℕ) : n > 0 → n ^ 2 ≤ a n → (2 * n) ^ 2 ≤ a (2 * n) := 
begin
 intros n_pos ih,
 rw[a_even n n_pos],
 exact calc
  (2 * n) ^ 2 = 4 * n ^ 2 : by ring
  ... ≤ 4 * a n : nat.mul_le_mul_left 4 ih
  ... ≤ 4 * a n + 1 : nat.le_succ _ 
end

lemma a_odd_step (n : ℕ) : n ^ 2 ≤ a n → (2 * n + 1) ^ 2 ≤ a (2 * n + 1) := 
begin
 intro ih,
 rw[a_odd n],
 exact calc
  (2 * n + 1) ^ 2 = 4 * n + (4 * n ^ 2 + 1) : by ring
   ... ≤ 4 * n ^ 2 + (4 * n ^ 2 + 1) : 
      by {apply (nat.add_le_add_iff_le_right _ _ _).mpr,
          rw[pow_two],
          exact nat.mul_le_mul_left 4 (nat.le_mul_self n),} 
   ... = 8 * n ^ 2 + 1 : by ring
   ... ≤ (8 * n ^ 2 + 1) + (n ^ 2 + 1) : le_self_add 
   ... = 9 * n ^ 2 + 2 : by ring
   ... ≤ 9 * a n + 2 : 
      by {apply (nat.add_le_add_iff_le_right _ _ _).mpr,
          exact nat.mul_le_mul_left 9 ih,}  
end

lemma square_le : ∀ n, n ^ 2 ≤ a n 
| 0 := by { norm_num }
| (nat.succ m) := 
   have cond (nat.bodd m) (nat.succ (nat.div2 m)) (nat.div2 m) < nat.succ m := wf_lemma' m,
   begin
    let e := nat.bodd_add_div2 m.succ,
    rw[nat.bodd_succ] at e,
    rw[← e],
    rcases m.bodd;
    simp only[bnot,bool.cond_ff,bool.cond_tt,zero_add],
    {intros u0 u1,
     rw[nat.add_comm 1],
     exact a_odd_step m.succ.div2 (square_le m.succ.div2),
    },{
     intros u0 u1,
     by_cases h : m.succ.div2 = 0,
     {exfalso,rw[h,mul_zero] at u0,exact nat.succ_ne_zero m u0.symm},
     exact a_even_step m.succ.div2 (nat.pos_of_ne_zero h) (square_le m.succ.div2),
    }
   end

end Q16

/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/
/- --------------------------------------------------------- -/

namespace Q17

/- This is the basic definition of fibonacci numbers.  It 
   is not good for efficient evaluation.
-/

def fibonacci : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n + 2) := (fibonacci n) + (fibonacci (n + 1))

/- We now do a more efficient version, and prove that it is 
   consistent with the original one.
-/

def fibonacci_step : ℕ × ℕ → ℕ × ℕ := 
 λ ⟨a,b⟩, ⟨b, a + b⟩

def fibonacci_pair : ℕ → ℕ × ℕ 
| 0 := ⟨0,1⟩ 
| (n + 1) := fibonacci_step (fibonacci_pair n)

lemma fibonacci_pair_spec : ∀ n , 
 fibonacci_pair n = ⟨fibonacci n,fibonacci n.succ⟩ 
| 0 := rfl
| (nat.succ n) := begin
 rw[fibonacci_pair,fibonacci_pair_spec n,fibonacci_step,fibonacci],
 ext,refl,refl,
end

lemma fibonacci_from_pair (n : ℕ) : 
 fibonacci n = (fibonacci_pair n).fst := 
  by rw[fibonacci_pair_spec n].

/- We now prove a fact about the fibonacci numbers mod 2.
   Later we will generalise this for an arbitrary modulus.
-/

lemma fibonacci_bodd_step (n : ℕ) : 
 (fibonacci (n + 3)).bodd = (fibonacci n).bodd := 
begin
 rw[fibonacci,fibonacci,nat.bodd_add,nat.bodd_add],
 cases (fibonacci (n + 1)).bodd;
 cases (fibonacci n).bodd;
 refl,
end

lemma fibonacci_bodd : ∀ n, (fibonacci n).bodd = bnot (n % 3 = 0)
| 0 := rfl
| 1 := rfl
| 2 := rfl
| (n + 3) := begin
 rw[fibonacci_bodd_step n,fibonacci_bodd n,nat.add_mod_right]
end

lemma F2013_even : (fibonacci 2013).bodd = ff := calc
 (fibonacci 2013).bodd = bnot (2013 % 3 = 0) : fibonacci_bodd _
  ... = ff : by norm_num

/-
 We now do a more general theory of modular periodicity
 of fibonacci numbers.  For computational efficiency, we
 give an inductive definition of modular fibonacci numbers
 that does not require us to calculate the non-modular ones.
 We then prove that it is consistent with the original 
 definition.
-/

def pair_mod (p : ℕ) : ℕ × ℕ → ℕ × ℕ := 
 λ ⟨a,b⟩, ⟨a % p,b % p⟩ 

lemma pair_mod_mod (p : ℕ) : ∀ (c : ℕ × ℕ), 
 pair_mod p (pair_mod p c) = pair_mod p c := 
λ ⟨a,b⟩, by {simp[pair_mod,nat.mod_mod],}

def fibonacci_pair_mod (p : ℕ) : ℕ → ℕ × ℕ 
| 0 := pair_mod p ⟨0,1⟩ 
| (n + 1) := pair_mod p (fibonacci_step (fibonacci_pair_mod n))

lemma fibonacci_pair_mod_mod (p : ℕ) : ∀ n,
 pair_mod p (fibonacci_pair_mod p n) = fibonacci_pair_mod p n
| 0 := by {rw[fibonacci_pair_mod,pair_mod_mod],} 
| (n + 1) := by {rw[fibonacci_pair_mod,pair_mod_mod],} 

lemma mod_step_mod (p : ℕ) : ∀ (c : ℕ × ℕ), 
 pair_mod p (fibonacci_step c) = 
  pair_mod p (fibonacci_step (pair_mod p c)) :=
λ ⟨a,b⟩, begin
 change (⟨b % p,(a + b) % p⟩ : ℕ × ℕ) = 
  ⟨b % p % p,(a % p + b % p) % p⟩,
 have e0 : b % p % p = b % p := nat.mod_mod b p,
 have e1 : (a % p + b % p) % p = (a + b) % p :=
  nat.modeq.add (nat.mod_mod a p) (nat.mod_mod b p),
 rw[e0,e1]
end

lemma fibonacci_pair_mod_spec (p : ℕ) : ∀ n, 
 fibonacci_pair_mod p n = pair_mod p (fibonacci_pair n) 
| 0 := rfl
| (n + 1) := begin
 rw[fibonacci_pair_mod,fibonacci_pair,fibonacci_pair_mod_spec n],
 rw[← mod_step_mod],
end

lemma fibonacci_mod_spec (p : ℕ) (n : ℕ) :
 (fibonacci_pair_mod p n).fst = (fibonacci n) % p := 
begin
 rw[fibonacci_pair_mod_spec,fibonacci_pair_spec,pair_mod],
 refl,
end

lemma fibonacci_pair_period₀ {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) :
  ∀ n, fibonacci_pair_mod p (n + d) = fibonacci_pair_mod p n
| 0 := by {rw[zero_add,h,fibonacci_pair_mod],}
| (n + 1) := by {
  rw[add_assoc,add_comm 1 d,← add_assoc],
  rw[fibonacci_pair_mod,fibonacci_pair_mod],
  rw[fibonacci_pair_period₀ n],
}

lemma fibonacci_pair_period₁ {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) (m : ℕ) :
  ∀ n, fibonacci_pair_mod p (m + d * n) = fibonacci_pair_mod p m
| 0 := by {rw[mul_zero,add_zero]}
| (n + 1) := by {
  have : m + d * (n + 1) = (m + d * n) + d := by ring,
  rw[this,fibonacci_pair_period₀ h,fibonacci_pair_period₁],
}

lemma fibonacci_pair_period {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) (n : ℕ) : 
  fibonacci_pair_mod p n = fibonacci_pair_mod p (n % d) := 
calc 
 fibonacci_pair_mod p n = fibonacci_pair_mod p (n % d + d * (n / d)) :
  congr_arg (fibonacci_pair_mod p) (nat.mod_add_div n d).symm
  ... = fibonacci_pair_mod p (n % d) : fibonacci_pair_period₁ h (n % d) (n / d)

lemma fibonacci_period  {p : ℕ} {d : ℕ} 
 (h : fibonacci_pair_mod p d = pair_mod p ⟨0,1⟩) (n : ℕ) : 
  (fibonacci n) ≡ (fibonacci (n % d)) [MOD p] := 
begin
 rw[nat.modeq,← fibonacci_mod_spec,← fibonacci_mod_spec],
 rw[fibonacci_pair_period],
 exact h,
end

lemma prime_89 : nat.prime 89 := by { norm_num, }

lemma L89_dvd_F2013 : 89 ∣ (fibonacci 2013) := 
begin
 apply (nat.dvd_iff_mod_eq_zero _ _).mpr,
 have h0 : fibonacci_pair_mod 89 44 = ⟨0,1⟩ :=
  by {unfold fibonacci_pair_mod fibonacci_step pair_mod; norm_num},
 have h1 : fibonacci_pair_mod 89 33 = ⟨0,34⟩ :=
  by {unfold fibonacci_pair_mod fibonacci_step pair_mod; norm_num},
 have h2 : 2013 % 44 = 33 := by {norm_num},
 let h3 := (fibonacci_mod_spec 89 2013).symm,
 let h4 := congr_arg prod.fst (fibonacci_pair_period h0 2013),
 let h5 := congr_arg prod.fst (congr_arg (fibonacci_pair_mod 89) h2),
 let h6 := congr_arg prod.fst h1,
 exact ((h3.trans h4).trans h5).trans h6,
end


end Q17

namespace Q18

variables (a b c d : ℤ)

lemma L_i : a ∣ b → b ∣ c → a ∣ c := 
by { rintros ⟨uab,hab⟩ ⟨ubc,hbc⟩, use uab * ubc, rw[← mul_assoc,← hab,← hbc] }

lemma L_ii : a ∣ b → a ∣ c → a ∣ (b + c) := 
by { rintros ⟨uab,hab⟩ ⟨uac,hac⟩, use uab + uac, rw[mul_add,hab,hac] }

lemma L_iii_false : ¬ (∀ a b c : ℤ, (a ∣ (b + c)) → (a ∣ b) ∧ (a ∣ c)) := 
begin
 intro h₀,
 have h₁ :    (2 : ℤ) ∣ 1  := (h₀ 2 1 1 dec_trivial).left,
 have h₂ : ¬ ((2 : ℤ) ∣ 1) := dec_trivial,
 exact h₂ h₁
end

lemma L_iv : a ∣ b → a ∣ c → a ∣ (b * c) := 
by { rintros ⟨uab,hab⟩ ⟨uac,hac⟩, use uab * c, rw[← mul_assoc,hab] }

lemma L_v_false : ¬ (∀ a b c : ℤ, (a ∣ (b * c)) → (a ∣ b) ∧ (a ∣ c)) := 
begin
 intro h₀,
 have h₁ :    (4 : ℤ) ∣ 2  := (h₀ 4 2 2 dec_trivial).left,
 have h₂ : ¬ ((4 : ℤ) ∣ 2) := dec_trivial,
 exact h₂ h₁
end

lemma L_vi : a ∣ b → c ∣ d → (a * c) ∣ (b * d) := 
by { rintros ⟨uab,hab⟩ ⟨ucd,hcd⟩, use uab * ucd, rw[hab,hcd], ring }

end Q18

namespace Q19
def f (n : ℤ) : ℤ := n * (n + 1) * (n + 2) * (n + 3)

lemma f_mod (p n₀ n₁ : ℤ) (h0 : n₀ ≡ n₁ [ZMOD p]) : f n₀ ≡ f n₁ [ZMOD p] := 
begin
 have h1 : n₀ + 1 ≡ n₁ + 1 [ZMOD p] := int.modeq.add h0 rfl,
 have h2 : n₀ + 2 ≡ n₁ + 2 [ZMOD p] := int.modeq.add h0 rfl,
 have h3 : n₀ + 3 ≡ n₁ + 3 [ZMOD p] := int.modeq.add h0 rfl,
 have h01 : n₀ * (n₀ + 1) ≡ n₁ * (n₁ + 1) [ZMOD p] := 
  int.modeq.mul h0 h1,
 have h02 : n₀ * (n₀ + 1) * (n₀ + 2) ≡ n₁ * (n₁ + 1) * (n₁ + 2) [ZMOD p] := 
  int.modeq.mul h01 h2,
 exact int.modeq.mul h02 h3,
end

lemma f_mod_3 (n : ℕ) : f n ≡ 0 [ZMOD 3] := 
begin
 have three_pos : (3 : ℤ) > 0 := dec_trivial,
 rcases int.exists_unique_equiv_nat n three_pos with ⟨r,⟨r_is_lt,r_equiv⟩⟩,
 let e := (f_mod 3 r n r_equiv).symm,
 suffices : f r ≡ 0 [ZMOD 3],
 {exact e.trans this,},
 rcases r with _ | _ | _ | r0; rw[f]; try {refl},
 {exfalso,
  have : (3 : ℤ) = ((3 : ℕ) : ℤ) := rfl,
  rw[this] at r_is_lt,
  let h0 := int.coe_nat_lt.mp r_is_lt,
  replace h0 := nat.lt_of_succ_lt_succ h0,
  replace h0 := nat.lt_of_succ_lt_succ h0,
  replace h0 := nat.lt_of_succ_lt_succ h0,
  exact nat.not_lt_zero r0 h0,
 }
end

lemma f_mod_8 (n : ℕ) : f n ≡ 0 [ZMOD 8] := 
begin
 have eight_pos : (8 : ℤ) > 0 := dec_trivial,
 rcases int.exists_unique_equiv_nat n eight_pos with ⟨r,⟨r_is_lt,r_equiv⟩⟩,
 let e := (f_mod 8 r n r_equiv).symm,
 suffices : f r ≡ 0 [ZMOD 8],
 {exact e.trans this,},
 rcases r with _ | _ | _ | _ | _ | _ | _ | _ | r0;
  rw[int.modeq,f]; try {norm_num},
 {exfalso,
  have : (8 : ℤ) = ((8 : ℕ) : ℤ) := rfl,
  rw[this] at r_is_lt,
  let h0 := int.coe_nat_lt.mp r_is_lt,
  repeat { replace h0 := nat.lt_of_succ_lt_succ h0 },
  exact nat.not_lt_zero r0 h0,
 }
end

lemma f_mod_24 (n : ℕ) : f n ≡ 0 [ZMOD 24] := 
begin
 let i3 : ℤ := 3,
 let i8 : ℤ := 8,
 have : (24 : ℤ) = i3 * i8 := rfl,
 rw[this],
 have cp : nat.coprime i3.nat_abs i8.nat_abs := by {dsimp[i3,i8], norm_num},
 exact (int.modeq_and_modeq_iff_modeq_mul cp).mp ⟨f_mod_3 n,f_mod_8 n⟩,
end

/- ----------- Part (ii) ------------- -/

def h {R : Type} [comm_ring R] (a b c d : R) : R := 
 (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) 

lemma h_shift {R : Type} [comm_ring R] (a b c d : R) : 
 h a b c d = h (a - d) (b - d) (c - d) 0 := 
begin
 have e : ∀ x y z : R, (x - z) - (y - z) = x - y := 
  by {intros, ring},
 dsimp[h],
 rw[sub_zero,sub_zero,sub_zero,e,e,e]
end

lemma h_zero_shift {R : Type} [comm_ring R] : 
 (∀ a b c : R, h a b c 0 = 0) → (∀ a b c d : R, h a b c d = 0) := 
  λ p a b c d, (h_shift a b c d).trans (p (a - d) (b - d) (c - d))

lemma h_zero_3 : ∀ a b c d : zmod 3, h a b c d = 0 := 
 h_zero_shift dec_trivial

lemma h_zero_4 : ∀ a b c d : zmod 4, h a b c d = 0 :=
 h_zero_shift dec_trivial

lemma h_map {R S : Type} [comm_ring R] [comm_ring S] 
 (φ : R →+* S) (a b c d : R) :
  φ (h a b c d) = h (φ a) (φ b) (φ c) (φ d) := 
begin
 dsimp[h],
 let em := φ.map_mul,
 let es := φ.map_sub,
 rw[em,em,em,em,em,es,es,es,es,es,es]
end

lemma h_zero_mod (p : ℕ+) :
 (∀ a b c d : zmod p, h a b c d = 0) → 
  (∀ a b c d : ℤ, h a b c d ≡ 0 [ZMOD p]) := 
begin
 intros e a b c d,
 have h₀ := eq_iff_modeq_int (zmod p) (p : ℕ),
 have : (p : ℤ) = ((p : ℕ) : ℤ) := by norm_cast,
 rw [← this] at h₀, rw[← h₀],
 let π : ℤ →+* (zmod p) := int.cast_ring_hom _,
 exact calc 
  π (h a b c d) = h (π a) (π b) (π c) (π d) : by rw[h_map π]
  ... = 0 : e (π a) (π b) (π c) (π d),
end

lemma h_zero_12 : ∀ (a b c d : ℤ), h a b c d ≡ 0 [ZMOD 12] := 
begin
 intros,
 let i3 : ℤ := 3,
 let i4 : ℤ := 4,
 let h3 := h_zero_mod 3 h_zero_3 a b c d,
 let h4 := h_zero_mod 4 h_zero_4 a b c d,
 have : (12 : ℤ) = i3 * i4 := rfl,
 rw[this],
 have cp : nat.coprime i3.nat_abs i4.nat_abs := by {dsimp[i3,i4], norm_num},
 exact (int.modeq_and_modeq_iff_modeq_mul cp).mp ⟨h3,h4⟩
end

/-
 Here are partial results for a more general case
-/

def π (m : ℕ+) : ℤ →+* (zmod m) := int.cast_ring_hom _

def F (n : ℕ) := { ij : (fin n) × (fin n) // ij.1.val < ij.2.val }

instance (n : ℕ) : fintype (F n) := by { dsimp[F], apply_instance,}

def g (n : ℕ) (u : (fin n) → ℤ) : ℤ := 
 (@finset.univ (F n) _).prod (λ ij, (u ij.val.2) - (u ij.val.1))

def g_mod (n : ℕ) (m : ℕ+) (u : (fin n) → ℤ) : zmod m := 
 (@finset.univ (F n) _).prod (λ ij, (π m (u ij.val.2)) - (π m (u ij.val.1)))

lemma g_mod_spec (n : ℕ) (m : ℕ+) (u : (fin n) → ℤ) : 
 π m (g n u) = g_mod n m u := 
begin
 dsimp[g,g_mod],
 let ms := (π m).map_sub,
 let ma := (π m).map_add,
 conv
 begin
  to_rhs, congr, skip, funext, rw[← ms],
 end,
 rw[ ← (π m).map_prod ],
end

lemma must_repeat (n : ℕ) (m : ℕ+) (m_lt_n : m.val < n)
 (u : fin n → ℤ) : ∃ i j : fin n, (i.val < j.val ∧ (π m (u i)) = (π m (u j))) := 
begin
 let P := { ij : (fin n) × (fin n) // ij.1 ≠ ij.2 },
 let p : P → Prop := λ ij, π m (u ij.val.1) = π m (u ij.val.2),
 let q := exists ij, p ij,
 by_cases h : q,
 { rcases h with ⟨⟨⟨i,j⟩,i_ne_j⟩,eq_mod⟩,
   change i ≠ j at i_ne_j,
   let i_ne_j_val : i.val ≠ j.val := λ e,i_ne_j (fin.eq_of_veq e),
   change (π m (u i)) = (π m (u j)) at eq_mod,
   by_cases hij : i.val < j.val,
   {use i,use j,exact ⟨hij,eq_mod⟩},
   { let hij' := lt_of_le_of_ne (le_of_not_gt hij) i_ne_j_val.symm,
    use j,use i,exact ⟨hij',eq_mod.symm⟩ } },
 { exfalso,
   let v : fin n → zmod m := λ i, π m (u i),
   have v_inj : function.injective v := 
   begin 
     intros i j ev,
     by_cases hij : i = j,
     { exact hij },
     { exfalso, exact h ⟨⟨⟨i,j⟩,hij⟩,ev⟩ }
   end,  
   haveI : fact (0 < (m : ℕ)) := ⟨m.property⟩,
   let e := calc
     n = fintype.card (fin n) : (fintype.card_fin n).symm
     ... ≤ fintype.card (zmod m) : fintype.card_le_of_injective v v_inj
     ... = m : zmod.card m
     ... < n : m_lt_n,
   exact lt_irrefl _ e }
end

lemma g_mod_zero (n : ℕ) (m : ℕ+) (m_lt_n : m.val < n)
 (u : fin n → ℤ) : g_mod n m u = 0 := 
begin
  rcases must_repeat n m m_lt_n u with ⟨i,j,i_lt_j,e⟩,
  dsimp[π] at e,
  let ij : F n := ⟨⟨i,j⟩,i_lt_j⟩,
  dsimp[g_mod],
  apply finset.prod_eq_zero (finset.mem_univ ij),
  dsimp[ij],
  change π m (u i) = π m (u j) at e,
  rw[e,sub_self],
end

end Q19

namespace Q20
lemma L1 : nat.gcd 896 1200 = 16 := 
begin
 have e0 : 1200 % 896 = 304 := by norm_num,
 have e1 :  896 % 304 = 288 := by norm_num,
 have e2 :  304 % 288 =  16 := by norm_num,
 have e3 :  288 %  16 =   0 := by norm_num,
 exact calc
  nat.gcd 896 1200 = nat.gcd 304 896 : by rw[nat.gcd_rec,e0]
               ... = nat.gcd 288 304 : by rw[nat.gcd_rec,e1] 
               ... = nat.gcd  16 288 : by rw[nat.gcd_rec,e2] 
               ... = nat.gcd   0  16 : by rw[nat.gcd_rec,e3] 
               ... = 16 : nat.gcd_zero_left 16
end

lemma L2 : nat.gcd 123456789 987654321 = 9 := 
begin
 have e0 : 987654321 % 123456789 = 9 := by norm_num,
 have e1 : 123456789 % 9 = 0 := by norm_num,
 exact calc
  nat.gcd 123456789 987654321 
       = nat.gcd 9 123456789  : by rw[nat.gcd_rec,e0]
   ... = nat.gcd 0 9          : by rw[nat.gcd_rec,e1]
   ... = 9 : nat.gcd_zero_left 9
end

end Q20

namespace Q21

def u (n : ℕ) : ℕ := 2 ^ n
def a (n : ℕ) : ℕ := 2 ^ (u n) + 1

lemma u_ge_1 (n : ℕ) : u n ≥ 1 := 
 by {
  let e := @nat.pow_le_pow_of_le_right 2 dec_trivial 0 n (nat.zero_le n),
  rw[pow_zero] at e,
  exact e,
 }

lemma u_step (n : ℕ) : u (n + 1) = 2 * (u n) := 
 by {dsimp[u],rw[pow_succ],}

def a_pos (n : ℕ) : ℕ+ := ⟨a n,nat.zero_lt_succ _⟩

lemma a_step (n : ℕ) : a (n + 1) + 2 * (a n) = 2 + (a n) * (a n) := 
begin
 have h : ∀ (x : ℕ), x ^ 2 + 1 + 2 * (x + 1) 
   = 2 + (x + 1) * (x + 1) := by {intro, ring,},
 rw[a,a,u_step,mul_comm 2 (u n),pow_mul,h (2 ^ (u n))]
end

lemma a_ge_3 (n : ℕ) : a n ≥ 3 := 
begin
 let e := @nat.pow_le_pow_of_le_right 2 dec_trivial _ _ (u_ge_1 n),
 rw[pow_one] at e,
 exact nat.succ_le_succ e,
end

lemma a_ne_1 (n : ℕ) : a n ≠ 1 := ne_of_gt (lt_trans dec_trivial (a_ge_3 n))

lemma a_odd (n : ℕ) : (a n) % 2 = 1 := 
begin
 dsimp[a],
 rw[← nat.add_sub_of_le (u_ge_1 n),pow_add,pow_one],
 rw[add_comm _ 1,nat.add_mul_mod_self_left],
 refl,
end

lemma a_mod_a : ∀ (n m : ℕ), a (n + m + 1) ≡ 2 [MOD (a n)] 
| n 0 := begin 
   rw[add_zero n],
   let e : (a (n + 1) + 2 * (a n)) % (a n) = 
           (2 + (a n) * (a n)) % (a n) :=
            congr_arg (λ i, i % (a n)) (a_step n),
   rw[nat.add_mul_mod_self_right] at e,
   rw[nat.add_mul_mod_self_right] at e,
   exact e,
  end
| n (m + 1) := begin
   rw[← (add_assoc n m 1)],
   let e := a_step (n + m + 1),
   replace e : (a (n + m + 1 + 1) + 2 * a (n + m + 1)) % (a n) = 
             (2 + a (n + m + 1) * a (n + m + 1)) % (a n) := by {rw[e]},
   let ih := a_mod_a n m,
   let ih1 : 2 * a (n + m + 1) ≡ 4 [MOD (a n)] := 
    nat.modeq.mul rfl ih,
   let ih2 : a (n + m + 1) * a (n + m + 1) ≡ 4 [MOD (a n)] := 
    nat.modeq.mul ih ih,
   let ih3 : a (n + m + 1 + 1) + 2 * a (n + m + 1) ≡
             a (n + m + 1 + 1) + 4 [MOD (a n)] := nat.modeq.add rfl ih1, 
   let ih4 : 2 + a (n + m + 1) * a (n + m + 1) ≡ 2 + 4 [MOD (a n)] := 
    nat.modeq.add rfl ih2,
   let e1 := (ih3.symm.trans e).trans ih4,
   exact nat.modeq.add_right_cancel rfl e1,
  end

lemma a_coprime_aux (n m : ℕ) : nat.coprime (a n) (a (n + m + 1)) := 
begin
 let u := a n,
 let v := a (n + m + 1),
 change (nat.gcd u v) = 1,
 let q := v / u,
 let r := v % u,
 have e0 : r + u * q = v := nat.mod_add_div (a (n + m + 1)) (a n),
 have e1 : r = 2 % (a n) := a_mod_a n m,
 have e2 : 2 % (a n) = 2 := @nat.mod_eq_of_lt 2 (a n) (a_ge_3 n),
 rw[e2] at e1,
 have e3 : nat.gcd u v = nat.gcd r u := nat.gcd_rec u v,
 rw[e1] at e3,
 have e4 : nat.gcd 2 u = nat.gcd (u % 2) 2 := nat.gcd_rec 2 u,
 have e5 : u % 2 = 1 := a_odd n,
 have e6 : nat.gcd 1 2 = 1 := by norm_num,
 rw[e5,e6] at e4,
 rw[e4] at e3,
 exact e3,
end

lemma a_coprime {n m : ℕ} : n ≠ m → nat.coprime (a n) (a m) := 
begin
 cases (lt_or_ge n m) with h h,
 {let k := m - n.succ,
  have e0 : (n + 1) + k = m := add_tsub_cancel_of_le h,
  have : (n + 1) + k = n + k + 1 := by ring,
  rw[this] at e0,
  rw[← e0],
  intro,
  exact a_coprime_aux n k,  
 },{
  intro h0,   
  let h1 := lt_of_le_of_ne h h0.symm,
  let k := n - m.succ,
  have e0 : (m + 1) + k = n := nat.add_sub_of_le h1,
  have : (m + 1) + k = m + k + 1 := by ring,
  rw[this] at e0,
  rw[← e0],
  exact (a_coprime_aux m k).symm,  
 }
end

def b (n : ℕ) : ℕ := nat.min_fac (a n)

def b_prime (n : ℕ) : nat.prime (b n) := nat.min_fac_prime (a_ne_1 n)

lemma b_inj : function.injective b := begin
 intros i j e0,
 by_cases e1 : i = j,
 {assumption},
 {exfalso,
  have e2 : nat.gcd (a i) (a j) = 1 := a_coprime e1,
  have e3 : (b i) ∣ (a i) := nat.min_fac_dvd (a i),
  have e4 : (b j) ∣ (a j) := nat.min_fac_dvd (a j),
  rw[← e0] at e4,
  let e5 := nat.dvd_gcd e3 e4,
  rw[e2] at e5,
  exact nat.prime.not_dvd_one (b_prime i) e5
 }
end

end Q21

end exercises_1
end MAS114