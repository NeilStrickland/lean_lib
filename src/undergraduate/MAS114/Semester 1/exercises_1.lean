import data.real.basic data.fintype algebra.big_operators data.nat.modeq
import tactic.find tactic.squeeze 
import MAS114.fiber

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
 have h1 : max (0 : ℝ) (n : ℝ) = n := max_eq_right h0,
 exact (pow_two (f n)).trans ((real.sqrt_prop n).right.trans h1),
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

lemma j_inj : function.injective j := 
 function.injective_of_left_inverse jj

lemma j_surj : function.surjective j := 
 function.surjective_of_has_right_inverse ⟨j,jj⟩

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
   (1 : ℤ) = (2 * m + 1 + -n) + n - 2 * m : by ring
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
   rw[int.cast_add,int.cast_add,int.cast_mul,int.cast_bit0],
   rw[int.cast_one,int.cast_neg],
   exact misc_identity (↑ m) (↑ n) half_R,
  end,
  have h3 : 2 * half_Q - 1 = 0 := dec_trivial,
  have h4 : 2 * half_R - 1 = (((2 * half_Q - 1) : ℚ) : ℝ) := 
  begin
   dsimp[half_R],
   rw[rat.cast_add,rat.cast_mul,rat.cast_bit0,rat.cast_neg,rat.cast_one],
  end,
  have h5 : 2 * half_R - 1 = 0 := by rw[h4,h3,rat.cast_zero],
  rw[h5,add_zero] at h2,
  have h6 : abs v_R = abs u_R := by rw[h2,abs_neg],
  exact h1 h6,
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
 intro e,
 replace e := fin.veq_of_eq e,
 rw[fin.succ_val,fin.z_val] at e,
 injection e,
end

lemma fin.succ_inj {n : ℕ} {a b : fin n} (e : a.succ = b.succ) : 
 a = b := 
begin 
 apply fin.eq_of_veq,
 replace e := congr_arg fin.val e,
 rw[fin.succ_val,fin.succ_val] at e,
 exact nat.succ_inj e,
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
 rcases ((mem_shift s) 0).mp h0 with ⟨b,⟨b_in_s,e⟩⟩,
 let h1 := congr_arg fin.val e,
 rw[fin.succ_val] at h1,
 injection h1,
end

lemma succ_mem_shift_iff {n : ℕ} (s : finset (fin n)) (a : fin n) : 
 a.succ ∈ shift s ↔ a ∈ s := 
begin
 rw[mem_shift s a.succ],
 split,{
   rintro ⟨b,⟨b_in_s,u⟩⟩,
   rw[(fin.succ_inj u).symm],
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
    by { apply fin.eq_of_veq,rw[fin.succ_val], },
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
    by { apply fin.eq_of_veq,rw[fin.succ_val], },
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
 rintros a ⟨a_in_shift,a_succ_in_shift⟩,
 let a_in_s : a ∈ s := (succ_mem_shift_iff s a).mp a_succ_in_shift,
 rcases (mem_shift s a.cast_succ).mp a_in_shift with ⟨b,⟨b_in_s,eb⟩⟩,
 replace eb := congr_arg fin.val eb,
 rw[fin.succ_val,fin.cast_succ_val] at eb,
 let c_is_lt : b.val < n :=
  nat.lt_of_succ_lt_succ (eb.symm ▸ a.is_lt), 
 let c : fin n := ⟨b.val,c_is_lt⟩,
 have ebc : b = fin.cast_succ c := fin.eq_of_veq (by rw[fin.cast_succ_val]),
 have eac : a = fin.succ c := fin.eq_of_veq (nat.succ_inj (by rw[← eb,fin.succ_val])),
 rw[ebc] at b_in_s,
 rw[eac] at a_in_s,
 exact s_gappy c ⟨b_in_s,a_in_s⟩, 
end

lemma unshift_gappy : ∀ {n : ℕ} {s : finset (fin n.succ)},
 is_gappy s → is_gappy (unshift s)
| 0 _ _ := trivial
| (nat.succ n) s s_gappy := begin
 rintros a ⟨a_in_unshift,a_succ_in_unshift⟩,
 let a_succ_in_s := (mem_unshift s a.cast_succ).mp a_in_unshift,
 let a_succ_succ_in_s := (mem_unshift s a.succ).mp a_succ_in_unshift,
 have e : a.cast_succ.succ = a.succ.cast_succ := 
  fin.eq_of_veq
   (by {rw[fin.succ_val,fin.cast_succ_val,fin.cast_succ_val,fin.succ_val]}),
 rw[e] at a_succ_in_s,
 exact s_gappy a.succ ⟨a_succ_in_s,a_succ_succ_in_s⟩,
end

lemma insert_gappy : ∀ {n : ℕ} {s : finset (fin n.succ.succ)}, 
 is_gappy s → (∀ (a : fin n.succ.succ), a ∈ s → a.val ≥ 2) → 
  is_gappy (insert fin.z s) := 
begin
 rintros n s s_gappy s_big a ⟨a_in_t,a_succ_in_t⟩,
 rcases finset.mem_insert.mp a_succ_in_t with a_succ_zero | a_succ_in_s,
 {exact fin.succ_ne_z a a_succ_zero},
 let a_pos : 0 < a.val :=
  nat.lt_of_succ_lt_succ ((fin.succ_val a) ▸ (s_big a.succ a_succ_in_s)),
 rcases finset.mem_insert.mp a_in_t with a_zero | a_in_s,
 {replace a_zero : a.val = 0 :=
  (fin.cast_succ_val a).symm.trans (congr_arg fin.val a_zero),
  rw[a_zero] at a_pos,
  exact lt_irrefl 0 a_pos,
 },{
  exact s_gappy a ⟨a_in_s,a_succ_in_s⟩, 
 }
end

def i {n : ℕ} (s : gappy n) : gappy n.succ := 
 ⟨shift s.val,shift_gappy s.property⟩ 

lemma i_val {n : ℕ} (s : gappy n) : (i s).val = shift s.val := rfl

lemma zero_not_in_i {n : ℕ} (s : gappy n) : fin.z ∉ (i s).val := 
 zero_not_in_shift s.val

lemma shift_big {n : ℕ} (s : finset (fin n)) : 
 ∀ (a : fin n.succ.succ), a ∈ shift (shift s) → a.val ≥ 2 := 
begin
 intros a ma,
 rcases (mem_shift (shift s) a).mp ma with ⟨b,⟨mb,eb⟩⟩,
 rcases (mem_shift s b).mp mb with ⟨c,⟨mc,ec⟩⟩,
 rw[← eb,← ec,fin.succ_val,fin.succ_val],
 apply nat.succ_le_succ,
 apply nat.succ_le_succ,
 exact nat.zero_le c.val,
end

def j {n : ℕ} (s : gappy n) : gappy n.succ.succ := 
 ⟨insert fin.z (shift (shift s.val)),
  begin 
   let h := insert_gappy (shift_gappy (shift_gappy s.property)) (shift_big s.val),
   exact h,
  end⟩

lemma j_val {n : ℕ} (s : gappy n) :
 (j s).val = insert fin.z (shift (shift s.val)) := rfl

lemma zero_in_j {n : ℕ} (s : gappy n) : fin.z ∈ (j s).val := 
 finset.mem_insert_self _ _

def p {n : ℕ} : (gappy n) ⊕ (gappy n.succ) → gappy n.succ.succ 
| (sum.inl s) := j s
| (sum.inr s) := i s

def q {n : ℕ} (s : gappy n.succ.succ) : (gappy n) ⊕ (gappy n.succ) := 
if fin.z ∈ s.val then
 sum.inl ⟨unshift (unshift s.val),unshift_gappy (unshift_gappy s.property)⟩
else
 sum.inr ⟨unshift s.val,unshift_gappy s.property⟩ 

lemma qp {n : ℕ} (s : (gappy n) ⊕ (gappy n.succ)) : q (p s) = s := 
begin
 rcases s with s | s; dsimp[p,q],
 {rw[if_pos (zero_in_j s)],congr,apply subtype.eq,
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
begin
 let e0 := fintype.card_congr (@gappy_equiv n),
 let e1 := fintype.card_sum (gappy n) (gappy n.succ),
 exact e0.symm.trans e1,
end

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
 ⟨λ h0, le_of_not_gt (λ h1, not_le_of_gt ((nat.pow_two m).symm.subst (nat.sqrt_lt.mp h1)) h0),
  λ h0, le_of_not_gt (λ h1,not_le_of_gt (nat.sqrt_lt.mpr ((nat.pow_two m).subst h1)) h0)⟩ 

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
   ... = ↑ (n.nat_abs ^ 2 : ℕ) : by rw[(nat.pow_two n.nat_abs).symm]

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
 exact calc
  n ∈ C ↔ n ∈ (int.range (-2) 3).to_finset :
   by rw[(dec_trivial : C = (int.range (-2) 3).to_finset)]
  ... ↔ n ∈ int.range (-2) 3 : by rw[list.mem_to_finset]
  ... ↔ -2 ≤ n ∧ n < 3 : int.mem_range_iff
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
 exact calc
  n ∈ D ↔ n ∈ (int.range (-3) 4).to_finset :
   by rw[(dec_trivial : D = (int.range (-3) 4).to_finset)]
  ... ↔ n ∈ int.range (-3) 4 : by rw[list.mem_to_finset]
  ... ↔ -3 ≤ n ∧ n < 4 : int.mem_range_iff
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

lemma L1 (U : Type) (A B : set U) : - (A ∪ B) = (- A) ∩ (- B) :=
 by { simp }

lemma L2 (U : Type) (A B : set U) : - (A ∩ B) = (- A) ∪ (- B) := 
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
 {rw[← sub_eq_add_neg] at x_eq_2,
  exact or.inl (sub_eq_zero.mp x_eq_2),
 },{
  rw[← sub_eq_add_neg] at x_eq_5,
  exact or.inr (sub_eq_zero.mp x_eq_5),
 }
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

lemma f_step (x : ℚ) : f (x + 1) = (x + 1) ^ 2 + f x := 
begin
 dsimp[f],
 apply sub_eq_zero.mp,
 rw[pow_two],
 ring,
end

lemma sum_of_squares : ∀ (n : ℕ), 
 (((finset.range n.succ).sum (λ i, i ^ 2)) : ℚ) = f n
| 0 := rfl
| (n + 1) := begin
  rw[finset.sum_range_succ,sum_of_squares n],
  have : (((n + 1) : ℕ) : ℚ) = ((n + 1) : ℚ ) := by simp, 
  rw[this,f_step n]
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
 /- Prove that all relevant denominators are nonzero -/
 let nz_x  : x ≠ 0     := (ne_of_lt (by linarith using [x_big])).symm,
 let nz_2x : 2 * x ≠ 0 := mul_ne_zero dec_trivial nz_x,
 let nz_x2 : x ^ 2 ≠ 0 := by {rw[pow_two], exact mul_ne_zero nz_x nz_x},
 let nz_y  : x - 1 ≠ 0 := (ne_of_lt (by linarith using [x_big])).symm,
 let nz_2y : 2 * (x - 1) ≠ 0 := mul_ne_zero dec_trivial nz_y,
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
  ... = x * (2 * (x - 1) / (2 * (x - 1))) : mul_div_comm (2 * (x - 1)) x (2 * (x - 1))
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
  ... = (x * x - x) * (x + 1) : by rw[mul_div_comm,div_self nz_2x,mul_one]
  ... = x ^ 3 - x : by ring,
 exact eq_of_mul_eq_mul_left nz_d (e4.trans e6.symm),
end

lemma product_formula : ∀ (n : ℕ), 
 (finset.range n).prod (λ k, ((1 - 1 / ((k + 2) ^ 2)) : ℚ)) = f (n + 1)
| 0 := rfl
| (n + 1) := begin
 have e0 : 1 < n + 2 := by linarith,
 have e1 : (1 : ℚ) < ((n + 2) : ℕ) := nat.cast_lt.mpr e0, 
 rw[nat.cast_add,nat.cast_bit0,nat.cast_one] at e1,
 rw[finset.prod_range_succ,product_formula n],
 let e2 := f_step (n + 2) e1,
 have e3 : (n : ℚ) + 2 - 1 = n + 1 := by ring,
 have e4 : (((n + 1) : ℕ) : ℚ) + 1 = (n : ℚ) + 2 :=
  by { rw[nat.cast_add,nat.cast_one],ring},
 rw[e3] at e2,
 rw[e2,e4],
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
 have : 2 * (n + 1) = (2 * n + 1).succ := by ring,
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
          rw[nat.pow_two],
          exact nat.mul_le_mul_left 4 (nat.le_mul_self n),} 
   ... = 8 * n ^ 2 + 1 : by ring
   ... ≤ 9 * n ^ 2 + 2 : by linarith
   ... ≤ 9 * a n + 2 : 
      by {apply (nat.add_le_add_iff_le_right _ _ _).mpr,
          exact nat.mul_le_mul_left 9 ih,}  
end

lemma square_le : ∀ n, n ^ 2 ≤ a n 
| 0 := le_refl 0
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
 rw[fibonacci_bodd_step n,fibonacci_bodd n],congr,
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
  nat.modeq.modeq_add (nat.mod_mod a p) (nat.mod_mod b p),
 rw[e0,e1],
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

end Q18

end exercises_1
end MAS114