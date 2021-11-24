import data.nat.gcd data.nat.prime 
import tactic.tauto tactic.squeeze tactic.find

/- --------------------------------------------------------------- -/
-- Section 2.1.1

#check 3 = 3
#check (ff && tt = ff)
#check (false ∧ true = false)

#print notation `=`
#print eq

-- #check (3 = [3]) -- ERROR
#check 3 = 4

lemma my_first_lemma : 3 = 3 := rfl
#check my_first_lemma

/- --------------------------------------------------------------- -/
-- Section 2.1.2

lemma my_add_assoc (n m k : ℕ) : m + (n + k) = (m + n) + k :=
 (nat.add_assoc _ _ _).symm

lemma my_bor_tt (b : bool) : b || tt = tt :=
 by { cases b; refl }

lemma my_bor_assoc (b1 b2 b3) : b1 || (b2 || b3) = (b1 || b2) || b3 := 
 by { cases b1; cases b2; cases b3; refl, }

-- Next example skipped because bool implication is not predefined in Lean

lemma my_bnot_and (a b : bool) : bnot (a && b) = (bnot a) || (bnot b) :=
 by { cases a; cases b; refl }

/- --------------------------------------------------------------- -/
-- Section 2.1.3

lemma my_zero_le (n : ℕ) :  0 ≤ n :=
begin
 induction n with n ih,
 exact nat.less_than_or_equal.refl,
 exact nat.less_than_or_equal.step ih,
end

def odd' (n : ℕ) : Prop := (n % 2 = 1)

lemma eq_leq (m n : ℕ) : m = n ↔ ((m ≤ n) ∧ (n ≤ m)) := sorry
lemma ne_lt (m n : ℕ) : m ≠ n ↔ ((m < n) ∨ (n < m)) := sorry
lemma le_zero (n : ℕ) : n ≤ 0 ↔ n = 0 := sorry
lemma dvd_one (d : ℕ) : (d ∣ 1) ↔ (d = 1) := sorry 
lemma odd_mul (m n : ℕ) : odd' (m * n) ↔ (odd' n) ∧ (odd' m) := sorry


/- --------------------------------------------------------------- -/
-- Section 2.1.4

lemma leq_pmull (m n : ℕ) : (n > 0) → m ≤ n * m := sorry
lemma odd_gt_zero (n : ℕ) : odd' n → n > 0 := sorry

lemma dvd_mul (d1 d2 m1 m2 : ℕ) : (d1 ∣ m1) → (d2 ∣ m2) → d1 * d2 ∣ m1 * m2 := sorry

/- --------------------------------------------------------------- -/
-- Section 2.2.1

lemma my_first_lemma' : 3 = 3 := by refl

lemma my_second_lemma : 2 + 1 = 3 := rfl

lemma add_succ (m n : ℕ) : m + (nat.succ n) = nat.succ (m + n) := rfl

lemma my_bnot_bnot (b : bool) : bnot (bnot b) = b := by {cases b; refl,}

lemma le_zero' (n : ℕ) : n ≤ 0 ↔ n = 0 := 
by { cases n with k; simp, }

lemma my_mul_eq_zero (m n : ℕ) : (m * n = 0) ↔ (m = 0) ∨ (n = 0) := 
begin
 cases n; cases m;
 try {simp [-nat.mul_eq_zero]}
end

/- --------------------------------------------------------------- -/
-- Section 2.3.1

def is_zero : ℕ → bool 
| 0 := tt
| _ := ff

def my_le (n m : ℕ) : bool := is_zero (n - m)

lemma le_zero'' (n m : ℕ) : (my_le n 0) = is_zero n := 
begin
 cases n; dsimp[my_le]; refl,
end

lemma list_ext (s₁ s₂ : list ℕ) : 
 s₁.length = s₂.length → ∀ i, s₁.nth i = s₂.nth i → s₁ = s₂ := sorry

lemma map_length {α β : Type} (f : α → β) (s : list α) : 
 list.length (list.map f s) = list.length s := sorry

def my_commutative {α β : Type} (op : α → α → β) := 
 ∀ a₁ a₂ : α, op a₁ a₂ = op a₂ a₁ 

lemma my_add_comm : my_commutative nat.add := nat.add_comm

#print associative
#print right_distrib
#print left_distrib
#print left_identity
#print function.injective
#print function.left_inverse

/- --------------------------------------------------------------- -/
-- Section 2.3.2

section chinese

variables m₁ m₂ : ℕ 
variable co_n12 : nat.coprime m₁ m₂  

lemma chinese_remainder (x y : ℕ) : 
 x % (m₁ * m₂) = y % (m₁ * m₂) ↔ x % m₁ = y % m₁ ∧ x % m₂ = y % m₂ := sorry

end chinese

/- --------------------------------------------------------------- -/
-- Section 2.3.3

lemma my_le_refl (n : ℕ) : n ≤ n := le_refl n

example (a b : ℕ) : a + b ≤ a + b := my_le_refl (a + b)

example (a b : ℕ) : a + (nat.succ b) ≤ nat.succ (a + b) := 
begin
 apply my_le_refl,
end

attribute [simp] my_le_refl 

example (a b : ℕ) : a + (nat.succ b) ≤ nat.succ (a + b) := sorry

lemma contra (c b : Prop) : (¬ c → ¬ b) → (b → c) := 
begin
 intros h hb,
 cases classical.em c with hc hnc,
 {exact hc},
 {exact false.elim (h hnc hb)}
end

example (m p : ℕ) : nat.prime p → p ∣ ((nat.factorial m) + 1) → m < p := 
begin
 intro prime_p,
 apply contra,
 intro h0,
 have leq_p_m : p ≤ m := le_of_not_gt h0,
 rw[← (@nat.dvd_add_iff_right p (nat.factorial m) 1)],
 {exact nat.prime.not_dvd_one prime_p},
 {exact nat.dvd_factorial (nat.prime.pos prime_p) leq_p_m}
end

example (m p : ℕ) : nat.prime p → p ∣ ((nat.factorial m) + 1) → m < p := 
begin
 intros prime_p d1,
 cases lt_or_ge m p, assumption, exfalso,
 rw[← (@nat.dvd_add_iff_right p (nat.factorial m) 1)] at d1,
 exact nat.prime.not_dvd_one prime_p d1,
 exact nat.dvd_factorial (nat.prime.pos prime_p) h,
end

/- --------------------------------------------------------------- -/
-- Section 2.3.4

#check @nat.rec
#check @list.rec

lemma my_add_zero (m : ℕ) : m + 0 = m := rfl
lemma my_zero_add (m : ℕ) : 0 + m = m := 
begin
 induction m with m ih,refl,exact congr_arg nat.succ ih,
end

lemma last_ind (α : Type) (P : list α → Prop) :
 (P list.nil) → (∀ s x, P s → P (s.concat x)) → ∀ s, P s := 
begin
 intros P_nil P_step,
 let C : (list α) → Prop := λ s,
  (∀ (Q : list α → Prop) (Q_nil : Q list.nil)
   (Q_step : ∀ t x, Q t → Q (t.concat x)), Q s),
 have h : ∀ s : list α, C s,
 {intro s,
  induction s with w s ih,
  {intros Q Q_nil Q_step,exact Q_nil},
  {intros Q Q_nil Q_step,
   let R := λ t, Q (w :: t),
   let R_nil : R list.nil := Q_step list.nil w Q_nil,
   let R_step : ∀ t x, R t → R (t.concat x) := 
    λ t x R_t, Q_step (w :: t) x R_t,
   exact ih R R_nil R_step,
  }
 },
 intro s,
 exact h s P P_nil P_step,
end

lemma foldl_rev (α β : Type) (f : α → β → α) (z : α) (s : list β) :
 list.foldl f z s.reverse = list.foldr (λ x z, f z x) z s := 
begin
 revert z,
 refine last_ind β _ _ _ s,
 {intro z,simp,},
 {intros t x h0 z,
  have h1 : list.reverse (list.concat t x) = x :: (list.reverse t) := by simp,
  have h2 : t.concat x = t ++ [x] := by simp,
  rw[h1,h2,list.foldl,h0 (f z x),list.foldr_append,list.foldr,list.foldr],
 }
end

/- --------------------------------------------------------------- -/
-- Section 2.4

example (m p : ℕ) : nat.prime p → p ∣ ((nat.factorial m) + 1) → m < p := 
begin
 intros prime_p,apply contra,intros h0 d1,
 exact nat.prime.not_dvd_one prime_p
  ((@nat.dvd_add_iff_right p (nat.factorial m) 1 (nat.dvd_factorial (nat.prime.pos prime_p) (le_of_not_gt h0))).mpr d1), 
end

/- --------------------------------------------------------------- -/
-- Section 2.5

-- #find nat.bodd
-- #find (_ ∣ nat.fact _)
-- #find nat.coprime
-- #find (_ * _ = _ * _)

/- --------------------------------------------------------------- -/
-- Exercises for Chapter 2

example (b1 b2 b3 : bool) : b1 || (b2 || b3) = (b1 || b2) || b3 := 
 by {cases b1; cases b2; cases b3; refl,}

-- Next example skipped as boolean implication is not predefined in Lean

example (a b : bool) : bnot (a && b) = (bnot a) || (bnot b) := 
 by {cases a; cases b; refl,}

lemma nat.sub_add : ∀ (n m k : ℕ), n - (m + k) = (n - m) - k 
| n m 0 := by {rw[add_zero,nat.sub_zero],}
| n m (nat.succ k) := by {rw[nat.add_succ,nat.sub_succ,nat.sub_add,nat.sub_succ]}

lemma nat.mul_pred (n m : ℕ) : n * (nat.pred m) = n * m - n :=
begin
 cases m,
 {rw[nat.pred_zero,mul_zero,nat.zero_sub],},
 {rw[nat.pred_succ,nat.mul_succ,nat.add_sub_cancel],}
end

lemma nat.pred_mul (n m : ℕ) : (nat.pred n) * m = n * m - m := 
 by { rw[nat.mul_comm,nat.mul_pred,nat.mul_comm], }

lemma nat.mul_sub : ∀ (n m k : ℕ), n * (m - k) = n * m - n * k
| n m 0 := by { rw[mul_zero,nat.sub_zero,nat.sub_zero],}
| n m (k + 1) := 
   by {rw[nat.sub_succ,nat.mul_pred,nat.mul_sub,nat.mul_succ,nat.sub_add],} 

lemma nat.sub_mul (n m k : ℕ) : (n - m) * k = n * k - m * k := 
 by {rw[nat.mul_comm,nat.mul_sub],congr' 1;apply nat.mul_comm}

example (n m : ℕ) : m ^ 2 - n ^ 2 = (m - n) * (m + n) := 
 begin
  rw[pow_two,pow_two,nat.sub_mul,mul_add,mul_add,nat.mul_comm m n],
  rw[nat.sub_add,nat.add_sub_cancel],
 end

lemma bodd_exp (m n : ℕ) : nat.bodd (m ^ n) = (n = 0) || nat.bodd m := 
begin
 induction n with n ih,
 {refl,},
 {rw[to_bool_ff (nat.succ_ne_zero n),ff_bor,pow_succ,nat.bodd_mul,ih],
  cases (nat.bodd m); cases (to_bool (n = 0)); refl
 }
end

def flatten {α : Type} (l : list (list α)) : list α := 
 list.foldr list.append list.nil l

lemma flatten_length {α : Type} : ∀ (l : list (list α)),
 (flatten l).length = list.sum (l.map list.length)
| list.nil := rfl
| (list.cons u l) := by {
   erw[list.length_append,flatten_length l,list.map_cons,list.sum_cons],
   }

def all_words {α : Type} : ∀ (n : ℕ) (alphabet : list α), list (list α)
| 0 _ := [list.nil]
| (nat.succ n) alphabet := 
   flatten (list.map (λ a,list.map (list.cons a) (all_words n alphabet)) alphabet)

lemma all_words_length {α : Type} (n : ℕ) (alphabet : list α) :
 (all_words n alphabet).length = alphabet.length ^ n := 
begin
 induction n with n ih,
 {refl,},
 {erw[all_words,flatten_length],
  rw[pow_succ,mul_comm],
  let f : α → list (list α) :=
   λ a, list.map (list.cons a) (all_words n alphabet),
  let g : α → ℕ := λ a, (f a).length,
  let l := alphabet.map f,
  let m := l.map list.length,
  have h0 : ∀ a : α, g a = alphabet.length ^ n :=
    λ a, (list.length_map _ _).trans ih,
  have h1 : m.length = alphabet.length := 
    (list.length_map list.length l).trans (list.length_map f alphabet),
  have h2 : ∀ i : ℕ, i ∈ m → i = alphabet.length ^ n := 
   begin
    intros i i_in_m,
    rcases list.mem_map.mp i_in_m with ⟨l0,⟨l0_in_l,l0_length⟩⟩,
    rcases list.mem_map.mp l0_in_l with ⟨a,⟨a_in_alphabet,fa_eq_l0⟩⟩,
    exact ((h0 a).symm.trans
              ((congr_arg list.length fa_eq_l0).trans l0_length)).symm,
   end,
  let h3 := (@list.eq_repeat ℕ (alphabet.length ^ n) alphabet.length
   (l.map list.length)).mpr ⟨h1,h2⟩,
  exact ((congr_arg list.sum h3).trans 
   (list.sum_const_nat (alphabet.length ^ n) alphabet.length)),
 }
end
