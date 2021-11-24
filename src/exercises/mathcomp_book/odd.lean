import tactic.interactive tactic.squeeze data.nat.modeq

variables n m : nat 

@[simp]
def is_odd_a : ℕ → bool
| 0 := ff
| (nat.succ n) := bnot (is_odd_a n)

#reduce is_odd_a (n + 2)

lemma odd_ss_a : is_odd_a (n + 2) = is_odd_a n := 
begin
 dsimp[is_odd_a],
 cases is_odd_a n; refl,
end

lemma odd_add_a : ∀ n m : ℕ , 
 is_odd_a (n + m) = bxor (is_odd_a n) (is_odd_a m)
| n 0 := by rw[is_odd_a,nat.add_zero,bxor_ff]
| n (m + 1) := begin
   rw[nat.add_succ,is_odd_a,is_odd_a,(odd_add_a n m)],
   cases (is_odd_a n); cases (is_odd_a m); refl,
  end

/- ------------------------------------------------------------ -/

@[simp]
def s : ℕ × bool → ℕ × bool
| ⟨n,ff⟩ := ⟨n,tt⟩
| ⟨n,tt⟩ := ⟨n.succ,ff⟩ 

@[simp]
def ss : ℕ → ℕ × bool
| 0 := ⟨0,ff⟩ 
| (nat.succ n) := s (ss n) 

def is_odd_b (n : ℕ) : bool := (ss n).2

#reduce ss (n + 2)

lemma odd_ss_b : is_odd_b (n + 2) = is_odd_b n :=
begin
 dsimp[is_odd_b,ss,s],
 rcases (ss n) with ⟨k,tt|ff⟩;refl,
end

def Nb_add : ℕ × bool → ℕ × bool → ℕ × bool 
| ⟨n,ff⟩ ⟨m,b⟩ := ⟨n+m,b⟩ 
| ⟨n,tt⟩ ⟨m,ff⟩ := ⟨n+m,tt⟩ 
| ⟨n,tt⟩ ⟨m,tt⟩ := ⟨n+m+1,ff⟩

lemma Nb_add_s (u v) : Nb_add u (s v) = s (Nb_add u v) := 
begin
 rcases u with ⟨i,ff|tt⟩; rcases v with ⟨j,ff|tt⟩; refl,
end

lemma ss_add (n m : ℕ) : ss (n + m) = Nb_add (ss n) (ss m) := 
begin
 induction m with m ih_m,
 {rw[add_zero,ss],cases (ss n) with k b; cases b; refl},
 {rw[nat.add_succ,ss,ss,ih_m,Nb_add_s],}
end

lemma odd_add_b : ∀ n m : ℕ, 
 is_odd_b (n + m) = bxor (is_odd_b n) (is_odd_b m) := 
begin
 intros n m,
 rw[is_odd_b,is_odd_b,is_odd_b,ss_add],
 rcases (ss n) with ⟨i,ff|tt⟩; rcases (ss m) with ⟨j,ff|tt⟩; refl,
end

/- ------------------------------------------------------------ -/

@[simp]
def is_odd_c (n : ℕ) : bool := if n % 2 = 0 then ff else tt

lemma odd_ss_c : is_odd_c (n + 2) = is_odd_c n :=
begin
 dsimp[is_odd_c],
 rw [nat.add_mod_right n 2]
end

/- ------------------------------------------------------------ -/

mutual def is_odd_d, is_even_d
with is_odd_d : nat → bool
| 0     := ff
| (n + 1) := is_even_d n
with is_even_d : nat → bool
| 0     := tt
| (n + 1) := is_odd_d n

#check n
#reduce is_odd_d (n + 2)

lemma odd_ss_d : is_odd_d (n + 2) = is_odd_d n :=
begin
 rw[is_odd_d,is_even_d], 
end

lemma odd_even_d : ∀ (n : ℕ), is_odd_d n = bnot (is_even_d n) 
| 0 := by {rw[is_odd_d,is_even_d],refl}
| (n + 1) := by {rw[is_odd_d,is_even_d,odd_even_d n,bnot_bnot],}

@[inline] def beq : bool → bool → bool
| tt tt  := tt
| ff ff  := tt
| _  _   := ff

lemma even_add_d : ∀ n m : ℕ, 
 is_even_d (n + m) = beq (is_even_d n) (is_even_d m) := 
begin
 intros n m,
 induction m with m ih_m,
 {rw[add_zero,is_even_d],cases is_even_d n;refl},
 {rw[nat.add_succ,is_even_d,is_even_d,odd_even_d,odd_even_d,ih_m],
  cases is_even_d n;cases is_even_d m; refl,
 }
end

lemma odd_add_d : ∀ n m : ℕ, 
 is_odd_d (n + m) = bxor (is_odd_d n) (is_odd_d m) := 
begin
 intros n m,
 rw[odd_even_d,odd_even_d,odd_even_d,even_add_d],
 cases is_even_d n;cases is_even_d m; refl,
end
