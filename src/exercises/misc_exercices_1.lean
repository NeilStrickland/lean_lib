import algebra.big_operators.basic
import tactic.interactive tactic.ring tactic.fin_cases

/- Exercise 1
 Show that for every natural number n, there exists m with m > n

 Useful ingredients: 
  nat.lt_succ_self; the tactics intro, use, apply
-/

lemma exists_greater_a : ∀ (n : ℕ), ∃ (m : ℕ), m > n := 
begin
 intro n,
 use n + 1,
 apply nat.lt_succ_self,
end

lemma exists_greater_b (n : ℕ) : ∃ m, m > n := 
 exists.intro (n + 1) n.lt_succ_self

/- Exercise 2
 Show that if we append a list to itself, then the length doubles.

 Useful ingredients:
  list.length_append, two_mul
-/ 

lemma double_length_a {α : Type} (l : list α) : 
 (l ++ l).length = 2 * l.length := 
begin
 rw[list.length_append l l],ring
end

lemma double_length_b {α : Type} (l : list α) : 
 (l ++ l).length = 2 * l.length := 
 (list.length_append l l).trans (two_mul l.length).symm

/- Exercise 3
 Show that 2 * (0 + 1 + ... + n) = n * (n + 1)

 Useful ingredients:
  finset.sum_range, finset.sum_range_succ; the tactics
  induction, rw and ring
-/

lemma range_sum_a (n : ℕ) :
 2 * ((finset.range (n + 1)).sum id) = n * (n + 1) := 
begin
 induction n with n ih,
 {refl},
 {have e : nat.succ n = n + 1 := rfl,
  rw[finset.sum_range_succ id (n + 1),mul_add,ih,id,e],
  ring,
 }
end

lemma range_sum_b : ∀ n : ℕ,
 2 * ((finset.range (n + 1)).sum id) = n * (n + 1)
| 0 := rfl
| (n + 1) := begin
 rw[finset.sum_range_succ id (n + 1),mul_add,range_sum_a n,id],
 ring,
end

/- Exercise 4
 Show that every natural number can be written in the form
 2 * m or 2 * m + 1.

 This one seems harder than it should be.  

 Useful ingredients: the operations n / 2 and n % 2, the theorems
  nat.mod_add_div and nat.mod_lt, the fin_cases tactic.

 For a different approach: the functions nat.bodd and nat.div2 
  and the theorem nat.bodd_add_div2
-/

lemma even_odd_a : ∀ (n : ℕ), (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) 
| 0 := or.inl ⟨0,rfl⟩ 
| 1 := or.inr ⟨0,rfl⟩ 
| (n + 2) := begin
 rcases even_odd_a n with ⟨m,e⟩ | ⟨m,e⟩; rw[e],
 {left,use m + 1,ring}, 
 {right,use m + 1,ring}, 
end

lemma even_odd_b (n : ℕ) : (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) :=
begin
 let r := n % 2,
 let m := n / 2,
 have h : n = 2 * m + r := (nat.mod_add_div n 2).symm.trans (add_comm _ _),
 have r_lt_2 : r < 2 := nat.mod_lt n dec_trivial,
 let r0 : fin 2 := ⟨r,r_lt_2⟩,
 fin_cases r0,
 {left,
  use m,
  have hr : r = 0 := fin.veq_of_eq this,
  rw[hr, add_zero] at h,
  exact h,
 },{
  right,
  use m,
  have hr : r = 1 := fin.veq_of_eq this,
  rw[hr] at h,
  exact h,
 },
end

lemma even_odd_c_aux (n m : ℕ) (b : bool) (e : (cond b 1 0) + 2 * m = n) : 
 (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) :=
begin
 cases b, 
 {left ,exact ⟨m,(e.symm.trans (zero_add _))⟩,},
 {right,exact ⟨m,e.symm.trans (add_comm _ _)⟩,},
end

lemma even_odd_c (n : ℕ) : (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) :=
 even_odd_c_aux n n.div2 (nat.bodd n) (nat.bodd_add_div2 n)

/- Exercise 5
 Given propositions p and q, show that p → q is equivalent to
 p → (p → q)

 Useful ingredients: 
  The tactics split, intros and exact.  

 Alternatively, you can use the tauto tactic, which will do 
 all the work for you.
-/

lemma ppq_a (p q : Prop) : (p → q) ↔ (p → p → q) := 
begin
 split,
 {intros hpq hp _,exact hpq hp,},
 {intros hppq hp,exact hppq hp hp,}
end

lemma ppq_b (p q : Prop) : (p → q) ↔ (p → p → q) := 
 ⟨λ hpq hp _,hpq hp,λ hppq hp,hppq hp hp⟩

lemma ppq_c (p q : Prop) : (p → q) ↔ (p → p → q) := 
 by tauto

/- Exercise 6
 If G is a group where a^2 = 1 for all a, then G is commutative.

 Proof: for any a and b we have a^2 = 1 and b^2 = 1 and (ab)^2 = 1.
  Write the last of these as abab = 1, multiply on the left by
  a and on the right by b to get aababb = ab.  Cancel aa = 1 and
  bb = 1 to get ba = ab.

 Useful ingredients: 
  pow_two, calc, rw, mul_assoc, one_mul, mul_one
-/

lemma elem_ab_a {G : Type*} [group G] (h : ∀ a : G, a ^ 2 = 1) : 
 ∀ a b : G, a * b = b * a := 
begin
 intros a b,
 let ea : a * a = 1 := (pow_two a).symm.trans (h a),
 let eb : b * b = 1 := (pow_two b).symm.trans (h b),
 let eab : (a * b) * (a * b) = 1 :=
   (pow_two (a * b)).symm.trans (h (a * b)),
 exact calc
  a * b = (a * 1) * b : by rw[mul_one]
  ... = (a * ((a * b) * (a * b))) * b : by rw[← eab]
  ... = ((a * (a * b)) * (a * b)) * b : by rw[← (mul_assoc a (a * b) (a * b))]
  ... = (b * (a * b)) * b : by rw[← (mul_assoc a a b),ea,one_mul b]
  ... = b * (a * (b * b)) : by rw[mul_assoc b (a * b) b,mul_assoc a b b]
  ... = b * a : by rw[eb,mul_one a]
end

/- Exercise 7
 Encapsulate Exercise 6 as a typeclass instance
-/

class elementary_two_group (G : Type*) extends (group G) := 
 (square_one : ∀ a : G, a ^ 2 = 1)

instance elementary_two_group_commutes
 (G : Type*) [e : elementary_two_group G] : comm_group G := 
 { mul_comm := elem_ab_a e.square_one,
   ..e
 }

/- Exercise 8
 Define an inductive type of nonempty lists 
 (which we will call pos_list). 
 
 The basic structure will be similar to the definition of 
 arbitrary lists, which can be done like this:

 inductive list (T : Type)
| nil : list
| cons : T → T → list

 However, instead of the constructor `nil`, which constructs the
 empty list, we should have a constructor called `const`, which
 constructs a list of length one.  

 We can then give inductive definitions of functions that give 
 the first and last element of a nonempty list, the length 
 (normalised so that lists with one entry count as having length
 zero), the reverse and so on.
-/

inductive pos_list (α : Type) : Type 
| const : α → pos_list
| cons : α → pos_list → pos_list

namespace pos_list

variable {α : Type}

def length : pos_list α → ℕ 
| (const a) := 0
| (cons a p) := p.length.succ

def to_list : pos_list α → list α 
| (const a) := [a]
| (cons a p) := list.cons a (to_list p)

def head : pos_list α → α 
| (const a) := a
| (cons a p) := a

def foot : pos_list α → α 
| (const a) := a
| (cons a p) := p.foot

def append : pos_list α → pos_list α → pos_list α
| (const a) q := cons a q
| (cons a p) q := cons a (append p q)

lemma head_append : ∀ (p q : pos_list α),
 head (append p q) = head p
| (const a) q := rfl
| (cons a p) q := rfl

lemma foot_append : ∀ (p q : pos_list α),
 foot (append p q) = foot q
| (const a) q := rfl
| (cons a p) q := foot_append p q

lemma append_assoc : ∀ (p q r : pos_list α), 
 append (append p q) r = append p (append q r)
| (const a) q r := rfl
| (cons a p) q r := by {dsimp[append],rw[append_assoc p q r],}

def reverse : pos_list α → pos_list α 
| (const a) := const a
| (cons a p) := p.reverse.append (const a)

lemma head_reverse : ∀ (p : pos_list α), p.reverse.head = p.foot
| (const a) := rfl
| (cons a p) := by {dsimp[reverse,foot],rw[head_append,head_reverse p],}

lemma foot_reverse : ∀ (p : pos_list α), p.reverse.foot = p.head
| (const a) := rfl
| (cons a p) := by {dsimp[reverse,head],rw[foot_append],refl,}

lemma reverse_append : ∀ (p q : pos_list α),
 reverse (append p q) = append (reverse q) (reverse p) 
| (const a) q := rfl
| (cons a p) q := by {dsimp[append,reverse],rw[reverse_append p q,append_assoc],}

lemma reverse_reverse : ∀ (p : pos_list α), p.reverse.reverse = p
| (const a) := rfl
| (cons a p) := begin 
 dsimp[reverse],rw[reverse_append,reverse_reverse p],refl,
end

end pos_list

/- Exercise 9
 Set up some basic theory of graphs.  In more detail, suppose
 we have a type V (to be considered as the vertex set).  To 
 make this a graph, we should have a predicate E so that E a b
 is true if there is an edge from a to b.  We are considering
 simple undirected graphs with no loops, to this relation should
 be symmetric (ie E a b implies E b a) and irreflexive (so 
 E a a is always false).
 
 Then define a type of paths in a graph.  We can start by 
 defining a predicate `is_path` on nonempty lists of vertices, 
 which checks whether adjacent vertices in the list are linked
 by an edge.  Using this, we can define paths as a subtype of
 nonempty lists.

 Now define a relation `are_connected` on V, which is satisfied
 by a pair of vertices if there is a path between them.  Prove 
 that this is an equivalence relation.  
-/

class graph (V : Type) : Type := 
(edge : V → V → Prop)
(symm : ∀ {u v : V}, edge u v → edge v u)
(asymm : ∀ v : V, ¬ edge v v)

namespace graph

variables {V : Type} [graph V]

def is_path : pos_list V → Prop
| (pos_list.const _) := true
| (pos_list.cons v p) := (edge v p.head) ∧ is_path p

lemma is_path_append (p q : pos_list V) : 
 is_path (pos_list.append p q) ↔ 
  is_path p ∧ edge p.foot q.head ∧ is_path q := 
begin
 induction p with a a p ih,
 {dsimp[is_path,pos_list.foot,pos_list.append,is_path],
  rw[true_and]
 },
 {dsimp[pos_list.append,pos_list.foot,is_path],
  rw[pos_list.head_append,ih,and_assoc],
 }
end

lemma is_path_reverse : ∀ {p : pos_list V},
 is_path p → is_path p.reverse 
| (pos_list.const a) _ := by {dsimp[pos_list.reverse,is_path],trivial}
| (pos_list.cons a p) h := begin
 dsimp[pos_list.reverse,is_path],
 dsimp[is_path] at h,
 rw[is_path_append,pos_list.head,pos_list.foot_reverse,is_path,and_true],
 exact ⟨is_path_reverse h.right,symm h.left⟩, 
end
variable (V)

def path : Type := { p : pos_list V // is_path p }

variable {V}

def path_between (a b : V) : Type := 
 { p : pos_list V // is_path p ∧ p.head = a ∧ p.foot = b }

namespace path 

def head (p : path V) : V := p.val.head

def foot (p : path V) : V := p.val.foot

def length (p : path V) : ℕ := p.val.length

def cons (v : V) (p : path V) (h : edge v p.head) : path V := 
 ⟨pos_list.cons v p.val,⟨h,p.property⟩⟩ 

def const (v : V) : path_between v v := 
 ⟨pos_list.const v,⟨trivial,rfl,rfl⟩⟩ 

def reverse {u v : V} : ∀ (p : path_between u v), path_between v u
| ⟨p,⟨p_path,p_head,p_foot⟩⟩  := 
 ⟨p.reverse,⟨is_path_reverse p_path,
            (pos_list.head_reverse p).trans p_foot,
            (pos_list.foot_reverse p).trans p_head⟩⟩ 

def splice {u v w : V} :
 ∀ (p : path_between u v) (q : path_between v w), 
     path_between u w 
| ⟨p,⟨p_path,p_head,p_foot⟩⟩ ⟨pos_list.const x,⟨q_path,q_head,q_foot⟩⟩ :=
    ⟨p,begin 
        change x = v at q_head,
        change x = w at q_foot,
        replace p_foot := p_foot.trans (q_head.symm.trans q_foot),
        exact ⟨p_path,p_head,p_foot⟩
       end⟩
| ⟨p,⟨p_path,p_head,p_foot⟩⟩ ⟨pos_list.cons x q,⟨q_path,q_head,q_foot⟩⟩ := 
   ⟨pos_list.append p q,
    begin 
     change x = v at q_head,
     change q.foot = w at q_foot,
     rw[pos_list.head_append,p_head,pos_list.foot_append,q_foot],
     split, 
     {dsimp[is_path] at q_path,rw[is_path_append,p_foot,← q_head],
      exact ⟨p_path,q_path⟩},
     {split;refl,}
    end
   ⟩ 

instance are_connected : setoid V := {
  r := λ a b, nonempty (path_between a b),
  iseqv := ⟨
   λ a, nonempty.intro (const a),
   λ a b ⟨p⟩, nonempty.intro (reverse p),
   λ a b c ⟨p⟩ ⟨q⟩, nonempty.intro (splice p q)
  ⟩ 
}

end path

end graph

/-
 Exercise 10

 Construct an equivalence `ℕ ≃ E ⊕ O`, where `E` and `O` are the
 subtypes of even and odd natural numbers.  Here `E ⊕ O` is
 alternative notation for `sum E O`, which is defined in the core
 lean library to be the disjoint union of E and O.  

 Equivalences are defined in data.equiv: an equivalence from X to 
 Y is a structure with four members: functions 
 `to_fun : X → Y` and `inv_fun : Y → X`, and proofs that `inv_fun`
 is both left inverse and right inverse to `to_fun`.
-/

def E := {n : ℕ // n.bodd = ff}

def O := {n : ℕ // n.bodd = tt}

lemma bool_elim {C : Sort*} {b : bool} : b ≠ ff → b ≠ tt → C := 
 by {intros,cases b;contradiction}

def f (n : ℕ) : E ⊕ O := 
begin
 by_cases n_even : n.bodd = ff,
 {exact sum.inl ⟨n,n_even⟩},
 by_cases n_odd : n.bodd = tt,
 {exact sum.inr ⟨n,n_odd⟩},
 exact bool_elim n_even n_odd
end

def g : E ⊕ O → ℕ 
| (sum.inl n) := n.val
| (sum.inr n) := n.val

lemma fg : ∀ x : E ⊕ O, f (g x) = x 
| (sum.inl ⟨n,n_even⟩) := by {dsimp[g,f],rw[dif_pos n_even]}
| (sum.inr ⟨n,n_odd⟩) := 
   begin
    have n_not_even : n.bodd ≠ ff := 
     by {rw[n_odd],intro e,injection e,},
    dsimp[g,f],
    rw[dif_neg n_not_even,dif_pos n_odd],
   end 

lemma gf (n : ℕ) : g (f n) = n := 
begin
 dsimp[f],
 by_cases n_even : n.bodd = ff,
 {rw[dif_pos n_even],refl},
 by_cases n_odd : n.bodd = tt,
  {have n_not_even  : n.bodd ≠ ff := 
   by {rw[n_odd],intro e,injection e,},
   rw[dif_neg n_not_even,dif_pos n_odd],
   refl,
  },
 exact bool_elim n_even n_odd
end

def F : ℕ ≃ (E ⊕ O) := ⟨f,g,gf,fg⟩
