/- --------------------------------------------------------------- -/
-- Section 1.1.1
#reduce 2 + 1
#reduce λ n, n + 1
#reduce (λ n, n + 1) 2

def f := λ n, n + 1
def f' (n : ℕ) := n + 1
#check f
#print f
#check f 3

-- #check f (λ x, x + 1) -- ERROR

#eval f 3

/- --------------------------------------------------------------- -/
-- Section 1.1.2
def g (n m : ℕ) : ℕ := n + m + 2
#check g

def h (n : ℕ) : ℕ → ℕ := λ m, n + m + 2
#check h

#print g
#print h

#check g 3
#eval g 2 3

/- --------------------------------------------------------------- -/
-- Section 1.1.3

def repeat_twice (g : ℕ → ℕ) : ℕ → ℕ :=  λ n, g (g n)

#eval repeat_twice f 2
#check (repeat_twice f)

-- #check (repeat_twice f f) -- ERROR

#eval (let n := 33 in let e := n + n + n in e + e + e)

/- --------------------------------------------------------------- -/
-- Section 1.2.1

/-
inductive bool : Type
| ff : bool
| tt : bool
-/

#print bool

def two_or_three (b : bool) : ℕ := if b then 2 else 3

def two_or_three' : ∀ (b : bool), ℕ 
| tt := 2
| ff := 3

def two_or_three'' (b : bool) : ℕ := bool.cases_on b 2 3

#eval two_or_three tt
#eval two_or_three ff

/-
@[inline] def band : bool → bool → bool
| ff _  := ff
| tt ff := ff
| tt tt := tt

@[inline] def bor : bool → bool → bool
| tt _  := tt
| ff tt := tt
| ff ff := ff

-/

#check tt && tt
#check (&&)

/- --------------------------------------------------------------- -/
-- Section 1.2.2

/-
inductive nat
| zero : nat
| succ (n : nat) : nat
-/

def pred : ℕ → ℕ
| 0     := 0
| (a+1) := a

#eval (pred 5)

def pred5 : ℕ → ℕ 
| (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ u))))) := u
| _ := 0

def pred5' (n : ℕ) : ℕ := 
 match n with
  | (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ u))))) := u
  | _ := 0
 end

def three_patterns : ℕ → ℕ 
| (nat.succ (nat.succ (nat.succ (nat.succ (nat.succ u))))) := u
| (nat.succ v) := v
| 0 := 0

/-
def wrong : ℕ → bool
| 0 := true
-- ERROR, non-exhaustive match
-/

def same_bool : ∀ (b₁ b₂ : bool), bool
| tt tt := tt
| ff ff := tt
| _ _ := ff


/- --------------------------------------------------------------- -/
-- Section 1.2.3

def add : ∀ n m : ℕ, ℕ 
| (nat.succ p) m := nat.succ (add p m)
| 0 m := m

#reduce add 2 3

/-
def loop : ℕ → ℕ 
| 0 := loop 0
| _ := 0
ERROR: failed to prove recursive application is decreasing, well founded relation
-/

def eqn : ∀ n m : ℕ, bool
| 0 0 := tt
| (nat.succ n) (nat.succ m) := eqn n m
| _ _ := ff

infix ` ===  `:50 := eqn

#eval (0 === 0)
#eval (1 === nat.succ 0)
#eval (1 === 1 + 0)
#eval (2 === nat.succ 0)
#eval (2 === 1 + 1)
#eval (2 === add 1 (nat.succ 0))

#check @nat.sub_eq_zero_iff_le
#print nat.le
#print nat.less_than_or_equal

/- --------------------------------------------------------------- -/
-- Section 1.3

inductive listn
| niln 
| consn (hd : ℕ) (tl : listn) 

open listn
#check (consn 1 (consn 2 niln))
-- #check (consn true (consn false niln)) -- ERROR

inductive listb
| nilb
| consb (hd : bool) (tl : listb) 

/- --------------------------------------------------------------- -/
-- Section 1.3.1

inductive seq (α : Type) 
| nil {} : seq
| cons (hd : α) (tl : seq) : seq 

#check @seq.nil
#check @seq.cons
#check seq.nil
#check seq.cons
#check seq.cons 2 seq.nil

#check 1 :: 2 :: 3 :: list.nil
#check [10,20,30]
#check λ l, 1 :: 2 :: 3 :: l

def seq.head {α : Type} (x0 : α) : ∀ s : seq α, α 
| seq.nil := x0
| (seq.cons x _) := x

/- --------------------------------------------------------------- -/
-- Section 1.3.2

def seq.size {α} : ∀ (s : seq α), ℕ
| (seq.cons _ tl) := nat.succ (seq.size tl) 
| _ := 0 

def seq.map {α β : Type*} (f : α → β) : seq α → seq β 
| (seq.cons a tl) := seq.cons (f a) (seq.map tl)
| _ := seq.nil

def s := seq.cons 10 (seq.cons 100 seq.nil)
#eval seq.map nat.succ s

-- Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)

/- --------------------------------------------------------------- -/
-- Section 1.3.3

/-
inductive option (α : Type u)
| none {} : option
| some (val : α) : option
-/

def odd : ℕ → bool 
| (nat.succ n) := bnot (odd n)
| 0 := ff

def only_odd (n : ℕ) : option ℕ := if (odd n) then (some n) else none

def ohead {α : Type*} : (seq α) → (option α)
| (seq.cons a _) := some a
| _ := none

inductive pair (α β : Type) : Type
| mk : α → β → pair

def pair.fst {α β : Type} : pair α β → α 
| (pair.mk a b) := a 

#check pair.mk 3 ff
#eval pair.fst (pair.mk 111 222)


/- --------------------------------------------------------------- -/
-- Section 1.3.4

structure point := (x : ℕ) (y : ℕ) (z : ℕ)

def p0 : point := {x := 1, y := 2, z := 3}
def p1 : point := point.mk 11 22 33
def p2 : point := ⟨111,222,333⟩

#eval point.x p1

def xy (p : point) := let ⟨a,b,c⟩ := p in a * c

#eval xy p1

/- --------------------------------------------------------------- -/
-- Section 1.4, 1.5

section iterators

variables {τ : Type} {α : Type} (f : τ → α → α)

def iter : ℕ → (τ → τ) → τ → τ 
| (nat.succ p) op x := op (iter p op x)
| 0 _ x := x

#check iter

def foldr : α → (list τ) → α 
| a (y :: ys) := f y (foldr a ys)
| a _ := a

#check foldr

variable init : α 
variables x1 x2 : τ 

#reduce foldr f init [x1,x2]
#reduce foldr nat.add 1000 [1,2]
end iterators

/- --------------------------------------------------------------- -/
-- Section 1.6

/- --------------------------------------------------------------- -/
-- Section 1.7

#print notation `<=`

/- --------------------------------------------------------------- -/
-- Chapter 1 Exercises

inductive triple (α β γ : Type) : Type
| mk : α → β → γ → triple

section triple

variables {α β γ : Type}

def fst : (triple α β γ) → α | (triple.mk a b c) := a
def snd : (triple α β γ) → β | (triple.mk a b c) := b
def thd : (triple α β γ) → γ | (triple.mk a b c) := c

notation `T(` a `,` b `,` c `)` := triple.mk a b c
notation t `|1` := fst t
notation t `|2` := snd t
notation t `|3` := thd t

#eval T(4,5,8)|1
#eval T(tt,ff,1)|2
#eval thd T(2,tt,ff)

end triple

def iter_add (n m : ℕ) := iter n nat.succ m
def iter_mul (n m : ℕ) := iter n (iter_add m) 0

#eval iter_add 10 7
#eval iter_mul 7 9

def nth_default {α : Type} (default : α) : (list α) → ℕ → α 
| list.nil _ := default
| (list.cons a tl) 0 := a
| (list.cons a tl) (nat.succ n) := nth_default tl n

#eval nth_default 99 [3,7,11,22] 2
#eval nth_default 99 [3,7,11,22] 7

def app {α : Type} : list α → α → list α 
| list.nil y := [y]
| (list.cons x xs) y := list.cons x (app xs y)

def cat {α : Type} : list α → list α → list α 
| list.nil ys := ys
| (list.cons x xs) ys := list.cons x (cat xs ys)

def rev {α : Type} : list α → list α 
| list.nil := list.nil
| (list.cons x xs) := app (rev xs) x

#eval rev [1,22,333]

def flatten {α : Type} (l : list (list α)) : list α := 
 foldr cat list.nil l

#eval flatten [[1,2,3],[10,20,30],[100,200,300]]

def all_words {α : Type} : ∀ (n : ℕ) (alphabet : list α), list (list α)
| 0 _ := [list.nil]
| (nat.succ n) alphabet := 
   flatten (list.map (λ a,list.map (list.cons a) (all_words n alphabet)) alphabet)

#eval all_words 3 [6,7]

