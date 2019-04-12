import data.nat.choose data.nat.prime data.fin
 ring_theory.matrix algebra.big_operators
import tactic.ring

/- --------------------------------------------------------------- -/
-- Section 3.1.2

#check Prop
#check Type
#check Type 5

def my_matrix (R : Type) (n m : ℕ) : Type := 
 (fin n) → (fin m) → R

def my_matrix.mul {R : Type} [ring R] {n m p : ℕ}
 (M : my_matrix R n m) (N : my_matrix R m p) : my_matrix R n p := 
  λ i k,(@fintype.elems (fin m) _).sum (λ j, (M i j) * (N j k))

lemma bool_irrelevance (P Q : bool) : ∀ e1 e2 : P = Q, e1 = e2
| _ _ := rfl

lemma proof_irrelevance (P : Prop) (h1 h2 : P) : h1 = h2 := by {refl}

/- --------------------------------------------------------------- -/
-- Section 3.1.3

inductive my_nat : Type
| O : my_nat 
| S : my_nat → my_nat

def my_pred : my_nat → my_nat
| my_nat.O := my_nat.O
| (my_nat.S n) := n

def my_nat.add : ∀ (n m : my_nat), my_nat
| my_nat.O m := m
| (my_nat.S n) m := my_nat.S (my_nat.add n m)

/- --------------------------------------------------------------- -/
-- Section 3.1.4

inductive my_and (A B : Prop) : Prop
| conj : A → B → my_and

inductive my_prod (A B : Type) : Type
| pair : A → B → my_prod

def my_fst {A B : Type} : my_prod A B → A
| (my_prod.pair a _) := a

def my_snd {A B : Type} : my_prod A B → B
| (my_prod.pair _ b) := b

inductive my_exists {A : Type} (P : A → Prop)
| intro : ∀ (a : A) (h : P a), my_exists

example : my_exists (λ n : ℕ , n * n + 1 = 2 * n) :=
 my_exists.intro 1 rfl

inductive my_or (P Q : Prop)
| intro_left : P → my_or
| intro_right : Q → my_or

def my_or.ind (P Q R : Prop) (h : my_or P Q) (p : P → R) (q : Q → R) : R := 
 by {cases h, exact p h, exact q h}


def my_or.ind' (P Q R : Prop) (h : my_or P Q) (p : P → R) (q : Q → R) : R := 
  @my_or.cases_on P Q (λ _, R) h p q

inductive my_true : Prop
| trivial

inductive my_false : Prop .

def my_not (P : Prop) := P → my_false

def my_false.elim : ∀ (P : Prop) (h : my_false), P .

inductive my_eq {A : Type} : ∀ a b : A, Prop 
| rfl : ∀ a : A, my_eq a a 

def my_eq.subst {A : Type} (P : A → Prop) : 
  ∀ {x : A} (px : P x) {y : A} (e : my_eq x y), P y
| _ px _ (my_eq.rfl x) := px

inductive my_odd : ∀ (n : ℕ), Prop 
| base : my_odd 1
| step : ∀ n, my_odd n → my_odd (n + 2)

/- --------------------------------------------------------------- -/
-- Section 3.2.2

example : ∀ (xy : ℕ × ℕ), nat.prime xy.1 → (my_odd xy.2) → 2 < xy.2 + xy.1 := 
begin
 rintros ⟨x,_⟩ pr_x (a|⟨y0,b⟩);
 dsimp[prod.fst,prod.snd,nat.add] at *;
 rw[nat.succ_add];
 apply nat.succ_lt_succ;
 apply nat.lt_of_lt_of_le pr_x.gt_one;
 apply nat.le_add_left _,
end

/- --------------------------------------------------------------- -/
-- Section 3.2.4

lemma nat.wf_ind (P : ℕ → Prop) (h : ∀ n,(∀ m, m < n → P m) → P n)
 (n : ℕ) : P n :=
begin
 let Q : ℕ → Prop := λ n,(∀ m, m < n → P m),
 have Q_zero : Q 0 := λ m h, false.elim ((nat.not_lt_zero m) h),
 have Q_step : ∀ n, Q n → Q (n + 1) := 
 begin
  intros n hn m hm,
  rcases le_iff_eq_or_lt.mp (nat.le_of_succ_le_succ hm) with h_eq | h_lt,
  {rw[h_eq],exact h n hn,},
  {exact hn m h_lt}
 end,
 exact @nat.rec Q Q_zero Q_step (n + 1) n (nat.lt_succ_self n),
end

-- def oops (n : ℕ) : false := oops n

#print nat.below
#check nat.brec_on

lemma stamps_aux (n : ℕ) : ∀ (m : ℕ), m < n → 
 ∃ s4 s5 : ℕ, s4 * 4 + s5 * 5 = m + 12 :=
begin
 induction n with n0 ih;
 intros m h,
 {exfalso,exact nat.not_lt_zero m h,},
 rcases lt_trichotomy m n0 with h0|h1|h2,
 {exact ih m h0,},
 {rw[h1],
   cases n0,{use 3, use 0, refl},
   cases n0,{use 2, use 1, refl},
   cases n0,{use 1, use 2, refl},
   cases n0,{use 0, use 3, refl},
   have h3 : n0 < n0 + 4 := nat.add_lt_add_left (dec_trivial : 0 < 4) n0,
   rcases (ih n0 h3) with ⟨s4,s5,e⟩,
   use s4 + 1,use s5,
   have e1 := calc 
    (s4 + 1) * 4 + s5 * 5 = (s4 * 4 + s5 * 5) + 4 : by { ring }
    ... = (n0 + 12) + 4 : by rw[e]
    ... = (n0 + 4) + 12 : by { ring },
   exact e1,
 },
 {exfalso, exact not_le_of_lt h2 (nat.le_of_succ_le_succ h),}
end

lemma stamps (n : ℕ) (h : 12 ≤ n) : ∃ s4 s5 : ℕ, s4 * 4 + s5 * 5 = n :=
begin
 rw[← nat.sub_add_cancel h],
 exact stamps_aux ((n - 12) + 1) (n - 12) (nat.lt_succ_self _),
end

/- --------------------------------------------------------------- -/
-- Section 3.3

def classically (P : Prop) := ¬ (¬ P)

lemma my_em (P : Prop) : classically (P ∨ ¬ P) := 
 λ h, h (or.inr (λ p, h(or.inl p)))

lemma classically.pure (P : Prop) : P → classically P := 
 λ p np, (np p)

lemma classically.bind (P Q : Prop) : (P → classically Q) → 
 (classically P) → (classically Q) := 
  λ hi pc nq, pc (λ p, hi p nq)

 