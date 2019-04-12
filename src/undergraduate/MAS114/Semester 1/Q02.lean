import data.real.basic tactic.norm_num

namespace MAS114
namespace exercises_1
namespace Q02

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
 /- Let `n` be an arbitrary natural number -/
 intro n, 
 /- The theorem `nat.zero_le n` says that `n ≤ 0` in `ℕ`.
    To convert this to an inequality in `ℝ`, we use the 
    theorem `nat.cast_le`.  This gives a bidirectional 
    implication, and we use the suffix `.mpr` to refer
    to the right-to-left implication.
  -/
 have h0 : (0 : ℝ) ≤ (n : ℝ) := nat.cast_le.mpr (nat.zero_le n),
 /- From the inequality `h0` we can deduce that `max 0 n = n`
    using the theorem `max_eq_right`.  This is valid in any 
    linearly ordered set.  The standard library defines a 
    default linear order on `ℝ` by the typeclass instance 
    mechanism, to be discussed elsewhere.  Note that the 
    left hand side of our equation is in `ℝ` whereas the right
    hand side is apparently in `ℕ`.  Lean digests the left hand
    side first, realises that the right hand side must be 
    interpreted as a real number to ensure that everything is
    consistent, and so silently applies the standard map 
    `ℕ → ℝ` (which may be called "cast" or "coercion").
 -/
 have h1 : max (0 : ℝ) (n : ℝ) = n := max_eq_right h0,
 /- Here `pow_two (f n)` is the equation 
    `(f n) ^ 2 = (f n) * (f n)`.  On the other hand, 
    `real.sqrt_prop n` says that 
    `f n ≥ 0 ∧ (f n) * (f n) = max 0 n`.  We use the suffix
    `.right` to extract the equation `(f n) * (f n) = max 0 n`.
    Next, given equations `u : a = b` and `v : b = c`, Lean's
    notation for the resulting equality `a = c` is `u.trans v`.
    Using this syntax, we combine the three equations that we
    have proved to get `(f n) ^ 2 = n`.

    (For longer or more complicated chains of equations, it 
    would be better to use the `calc` construct, which will 
    be discussed elsewhere.)
 -/
 exact (pow_two (f n)).trans ((real.sqrt_prop n).right.trans h1),
end

/- f is injective -/
lemma f_inj : function.injective f := 
begin
 /- Let `n₀` and `n₁` be arbitrary natural numbers, and let `e` 
    be a proof that `f n₀ = f n₁` in `ℝ`.  Our goal is now to 
    prove that `n₀ = n₁`.  
 -/
 intros n₀ n₁ e,
 /- For convenience, we introduce notation for the real numbers
    corresponding to `n₀` and `n₁`.
 -/
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


/- This version suggested by Kevin Buzzard -/
lemma no_closest_integer (n m : ℤ) :
 ¬ (is_closest_integer n ((m : ℝ) + 1/2)) :=
begin
 intro h0,
 let x_R : ℝ := (m : ℝ) + 1/2,
 let k := 2 * m + 1 - n,
 by_cases e0 : k = n,
 {-- In this block we consider the possibility that k = n, and
  -- show that it is impossible.
  exfalso,
  change 2 * m + 1 - n = n at e0, -- I prefer this to dsimp
  -- every operation I make here is "natural" hence will be in mathlib somewhere
  -- and I find it using ctrl-space and name guesswork
  rw [sub_eq_iff_eq_add, ←two_mul, eq_comm, ←sub_eq_iff_eq_add', ←mul_sub] at e0,
  -- e0 : 2 * (n - m) = 1
  have e2 : (2 * (n - m)) % 2 = 0 := int.mul_mod_right _ _,
  rw [e0, @int.mod_eq_of_lt (1 : ℤ) (2 : ℤ) (dec_trivial) (dec_trivial)] at e2,
  -- e2 : 1 = 0
  cases e2, -- just showing off here
 },{
  let h1 := ne_of_gt (h0 k e0),
  apply h1,
  convert abs_neg _,
  -- get rid of k
  show (m : ℝ) + 1/2 - ((2 * m + 1 - n) : ℤ) = -(m + 1/2 - n),
  -- simp does the casts, although it's a sin to apply it when not closing a goal
  -- instead of simp one should say:
--  suffices : -(1 : ℝ) + (2⁻¹ + (↑n + (↑m + -(2 * ↑m)))) = -2⁻¹ + (↑n + -↑m),
--    simpa,
  simp,
  -- now ring finishes the job
  ring,
 }
end

lemma k_does_not_exist : ¬ ∃ (k : ℝ → ℤ), (∀ x : ℝ, is_closest_integer (k x) x) := 
begin
 rintro ⟨k,k_spec⟩,
 let x : ℝ := ((0 : ℤ) : ℝ) + 1/2, 
 exact no_closest_integer (k x) 0 (k_spec x)
end

end Q02
end exercises_1
end MAS114