/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

In classical mathematics, if we prove that there is a unique element
x with a certain property p x, then we can treat that as a valid 
definition of x and use x as a known entity in further developments.
This does not work in quite the same way in Lean (unless we import
classical logic.)  The point is basically that Lean implements proof
irrelevance, and so erases all details of the proof of unique
existence of x, making the definition of x inaccessible to
computation.  However, if we have strong enough assumptions about 
finiteness and decidability, then these issues go away.  The point 
of this file is to set up a framework for dealing with this kind of 
thing.  
 
In more detail, at the bottom of this file we will define a function 
fintype.witness.  This accepts a decidable predicate p defined on a 
finite type α with decidable equality, together with a proof of 
(∃! x : α, p x), and it returns the relevant value of x, packaged
together with a proof that it has the expected property.

In building up to the definition of fintype.witness, we will define
a number of other functions that play similar roles in various other
contexts.
-/

import data.nat.basic
import data.list data.multiset data.finset data.fintype data.equiv.encodable

universe u

variables {α : Type u}

namespace option 

/-
 Recall that a term xo of type (option α) is either (none), or
 (some x) for some x in α.  This function accepts xo together 
 with a proof that xo ≠ none.  It returns the value x such that 
 xo = (some x), packaged together with a proof of that property.

 Note that we have defined this function in the option namespace,
 so its full global name is option.unique_element.  Later in this
 file we will define several other functions called unique_element,
 but they will all be in different namespaces, so their full global
 names will be list.unique_element, multiset.unique_element and so
 on.
-/
def unique_element (xo : option α) (xo_some : xo ≠ none) : 
 { x : α // xo = some x } := 
begin 
 rcases xo with _ | x,
 exact false.elim (xo_some rfl),
 exact ⟨ x, rfl ⟩ 
end

end option

/- -------------------------------------------------------- -/

namespace list

/-
 This function accepts a list xs of elements of α.  If the list 
 has length one, so it contains a unique element x, then this
 function returns the term (some x) of type (option α).  In all
 other cases, it returns the term (none) of type (option α).
-/
def maybe_unique_element (xs : list α) : (option α) := 
begin
 rcases xs with _ | ⟨ x , _ | ⟨ y, zs ⟩⟩,
 exact none,
 exact some x,
 exact none
end

/-
 A basic lemma saying that maybe_unique_element behaves as expected.
-/
lemma maybe_unique_element_prop (xs : list α) (a : α)
 (e : maybe_unique_element xs = some a) : xs = [a] :=
begin
 rcases xs with _ | ⟨ x , _ | ⟨ y, zs ⟩⟩;
  try {dsimp[maybe_unique_element]}; 
  try {dsimp[maybe_unique_element] at e}; 
  injection e with e1; 
  simp[e1]
end

/-
 Given that a list has length one, return its unique element, 
 packaged with a proof of a key property.
-/
def unique_element (xs : list α) (xs_length : xs.length = 1) : 
 { x : α // xs = [x]} := 
begin
 rcases xs with _ | ⟨ x,ys ⟩,
 {simp at xs_length,exact false.elim xs_length},
 {
  simp at xs_length,
  rw[nat.add_comm] at xs_length,
  have ys_length : ys.length = 0 := nat.succ_inj xs_length,
  have ys_nil : ys = [] := list.length_eq_zero.mp ys_length,
  simp[ys_nil],
  exact ⟨ x, rfl ⟩
 }
end

/-
 Another basic lemma saying that maybe_unique_element behaves as expected.
-/
lemma some_unique_element (xs : list α) : 
 maybe_unique_element xs = none ↔ xs.length ≠ 1 :=
begin
 rcases xs with _ | ⟨ x , _ | ⟨ y, zs ⟩⟩; simp; dsimp[maybe_unique_element],
 refl,
 {intro h,injection h},
 split,
 { intros u v,
   have Q : ∀ (k : ℕ ) , ¬1 + (1 + k) = 1 :=
   begin
    intros k e,
    simp at e,
    injection e with e1,injection e1
   end,
   exact Q zs.length v
 },
 {intro,refl}
end

/-
 A list with no duplicates and a unique element has length one.
-/
lemma length_one_of_prop (xs : list α) (nd : nodup xs) (u : ∃! a, a ∈ xs) :
 xs.length = 1 := 
begin
 rcases u with ⟨ a , a_in_xs , a_unique ⟩, 
 rcases xs with _ | ⟨ x , _ | ⟨y , zs⟩⟩,
 {exact false.elim (list.ne_nil_of_mem a_in_xs rfl)},
 {simp},
 {
   have x_mem : x ∈ list.cons x (list.cons y zs) := or.inl rfl,
   have y_mem : y ∈ list.cons x (list.cons y zs) := or.inr (or.inl rfl),
   have x_eq_a : x = a := a_unique x x_mem,
   have y_eq_a : y = a := a_unique y y_mem,
   have x_eq_y : x = y := x_eq_a.trans y_eq_a.symm,
   have x_in_y_zs : x ∈ list.cons y zs := eq.subst x_eq_y (or.inl rfl), 
   exact false.elim ((list.nodup_cons.mp nd).1 x_in_y_zs)
 }
end
 
/- 
 Let as and bs be lists of elements of type α.  The proposition 
 (perm as bs) is defined inductively in mathlib in data.list.perm.lean; 
 it means that bs is a permutation of as.  If so, then 
 maybe_unique_element takes the same values on as and bs, as we 
 prove here.
-/
lemma maybe_unique_element_perm (as bs : list α) (p : perm as bs) :
 (maybe_unique_element as) = (maybe_unique_element bs) := 
begin
 induction p,
 case list.perm.nil : {simp},
 case list.perm.skip : x as1 bs1 q ih {
   rcases as1 with _ | ⟨ a1, as2 ⟩ ,
   {have bs1_nil : bs1 = [] := list.eq_nil_of_perm_nil q,
   rw[bs1_nil]},{
    rcases bs1 with _ | ⟨ b1, bs2 ⟩ ,
    rcases list.eq_nil_of_perm_nil q.symm,
    dsimp[maybe_unique_element],
    refl
   }
  },
 case list.perm.swap : x y cs {
  dsimp[maybe_unique_element],refl
 },
 case list.perm.trans : cs ds es p_cd p_de ih_cd ih_de {
   exact eq.trans ih_cd ih_de
 }
end

end list

/- -------------------------------------------------------- -/

namespace multiset 

/-
 A multiset is (by definition) a permutation-equivalence class of lists.
 Above we defined a function maybe_unique_element in the list namespace.
 We have now closed that namespace, so we need to use the name 
 list.maybe_unique_element.  We proved that that function is permutation
 invariant, so now we can define an induced function on multisets.
 We call the new function maybe_unique_element again, but now we are 
 in the multiset namespace, so the full global name will be
 multiset.maybe_unique_element.
-/
def maybe_unique_element : (multiset α) → (option α) :=
 quotient.lift list.maybe_unique_element 
  (@list.maybe_unique_element_perm α)

/-
 We now prove compatibility with list.maybe_unique_element
-/
lemma maybe_unique_element_of_list (l : list α) :
 maybe_unique_element ↑l = list.maybe_unique_element l := 
 @quotient.lift_beta (list α) _ _
  list.maybe_unique_element
   (@list.maybe_unique_element_perm α) l

/-
 We now have two basic lemmas saying that the multiset version of 
 maybe_unique_element behaves as expected.
-/
lemma maybe_unique_element_prop (m : multiset α) (a : α)
 (e : maybe_unique_element m = some a) : m = [a] := 
begin
 rcases quotient.exists_rep m with ⟨ xs, xs_eq_m ⟩,
 have h : maybe_unique_element ⟦xs⟧ = list.maybe_unique_element xs :=
  maybe_unique_element_of_list xs,
 rw[xs_eq_m,e] at h,
 have xs_eq_a : xs = [a] := list.maybe_unique_element_prop xs a h.symm,
 simp[xs_eq_a.symm],
 exact xs_eq_m.symm
end

lemma some_unique_element (m : multiset α) : 
 maybe_unique_element m = none ↔ card m ≠ 1 := 
begin
 rcases quotient.exists_rep m with ⟨ as,e ⟩,
 rw[← e],
 simp[maybe_unique_element_of_list as],
 exact as.some_unique_element
end

/-
 Recall that the cardinality of any multiset is by definition the length
 of any representing list.  Thus, we have the following obvious fact 
 about multisets of cardinality one.
-/
lemma eq_singleton (m : multiset α) (x : α) :
 m = [x] ↔ (m.card = 1 ∧ x ∈ m) := 
begin
 split,
 {intro m_eq_x,simp[m_eq_x]},
 {intro e,
  rcases (exists_cons_of_mem e.2) with ⟨ t, m_eq_xt⟩ ,
  have h : 1 = t.card + 1 := calc 
   1 = m.card : e.1.symm
   ... = (x :: t).card : by rw[m_eq_xt]
   ... = t.card + 1 : by simp,
  have t_eq_0 : t = 0 := card_eq_zero.mp (nat.succ_inj h).symm,
  simp[t_eq_0] at m_eq_xt,
  exact m_eq_xt
 }
end

/-
 This function extracts the unique element of any multiset of cardinality
 one, packaged together with a proof of its key property.
-/
def unique_element (m : multiset α) (m_card : m.card = 1) : 
 {x : α // m = [x]} :=
begin
 let xo := maybe_unique_element m,
 have xo_some : xo ≠ none := 
 begin
  intro xo_none,
  exact (some_unique_element m).mp xo_none m_card
 end,
 rcases option.unique_element xo xo_some with ⟨ x, xox ⟩,
 have mx : m = [x] := 
  maybe_unique_element_prop m x xox,
 exact ⟨ x , mx ⟩ 
end

/-
 A multiset has cardinality one iff it has no duplicates and a unique element.
-/
lemma card_one_of_prop (m : multiset α) (nd : nodup m) (u : ∃! a, a ∈ m) :
 m.card = 1 := 
begin
 rcases u with ⟨ a , a_in_m , a_unique_in_m ⟩,
 rcases quotient.exists_rep m with ⟨ xs, xs_eq_m ⟩,
 rw[← xs_eq_m] at a_in_m a_unique_in_m nd ⊢,
 simp,
 have xs_nd : list.nodup xs := coe_nodup.mp nd,
 have a_in_xs : a ∈ xs := mem_coe.mpr a_in_m,
 have a_unique_in_xs :
   ∀ x : α, ∀ (x_in_xs : x ∈ xs), x = a := 
 begin
  intros,
  exact a_unique_in_m x (mem_coe.mp x_in_xs)
 end,
 exact list.length_one_of_prop xs xs_nd ⟨ a , a_in_xs , a_unique_in_xs ⟩
end

end multiset

/- -------------------------------------------------------- -/

namespace finset

/-
 A finset is a multiset with no duplicates.  We can restrict all our definitions
 and results for multisets, to get versions for finsets.
-/
def maybe_unique_element (s : finset α) : (option α) :=
 multiset.maybe_unique_element s.val

lemma maybe_unique_element_prop (s : finset α) (a : α)
 (e : maybe_unique_element s = some a) : s = singleton a := 
begin
 apply finset.eq_of_veq,
 simp,dsimp[maybe_unique_element] at e,
 exact multiset.maybe_unique_element_prop s.val a e
end

lemma some_unique_element (s : finset α) : 
 maybe_unique_element s = none ↔ s.card ≠ 1 := 
begin
 dsimp[maybe_unique_element,card],
 apply multiset.some_unique_element
end

lemma eq_singleton (s : finset α) (a : α) :
 s = singleton a ↔ (s.card = 1 ∧ a ∈ s) := 
begin
 split;intro e,
 {dsimp[card],
  let e1 := congr_arg finset.val e,
  simp at e1,
  simp[e1,e]
 },{
  dsimp[card] at e,
  apply eq_of_veq,
  exact (multiset.eq_singleton s.val a).mpr ⟨ e.1 , finset.mem_def.mp e.2⟩,
 }
end

def unique_element (s : finset α) (s_card : s.card = 1) : 
 {x : α // s = singleton x} :=
begin
 dsimp[card] at s_card,
 rcases (multiset.unique_element s.val s_card) with ⟨ x , e ⟩,
 have e1 : s = singleton x := eq_of_veq e,
 exact ⟨ x , e1 ⟩   
end

lemma card_one_of_prop (s : finset α) (h : ∃! x, x ∈ s) : s.card = 1 := 
begin
 dsimp[card],
 exact multiset.card_one_of_prop s.val s.nodup h
end

/-
 Suppose that we have a finset s and a decidable predicate p; we can then
 define a finset (s.filter p) consisting of elements of s where p is 
 satisfied.  The following function just applies our previous constructions
 to a finset of the form (s.filter p) and does a little associated 
 bookkeeping.
-/
def witness (s : finset α) (p : α → Prop) [decidable_pred p]
 (h : ∃! x, x ∈ s ∧ p x) : 
  { a : α // s.filter p = singleton a} :=
begin
 let s1 := s.filter p,
 have h1 : ∃! x, x ∈ s1 := 
 begin
  rcases h with ⟨ x , ⟨ x_in_s , p_x ⟩ , x_unique⟩, 
  have x_in_s1 : x ∈ s1 := 
   mem_filter.mpr ⟨ x_in_s , p_x ⟩, 
  have x_unique_alt : ∀ y, y ∈ s1 → y = x := 
  begin
   intros y y_in_s1,
   exact x_unique y (mem_filter.mp y_in_s1),
  end,
  exact ⟨ x , x_in_s1, x_unique_alt⟩ 
 end,
 have s1_card : s1.card = 1 := card_one_of_prop s1 h1,
 exact unique_element s1 s1_card
end

end finset

/- -------------------------------------------------------- -/

namespace fintype 
/-
 Recall that a fintype structure on α is a finset containing every element
 of α, and thus proving that α is finite.  In this section we do some 
 obvious adaptation of our results for general finsets, to put them in a
 more convenient form for use with fintypes.
-/
open finset fintype 

variables (α) [fintype α]

def maybe_unique_element : (option α) :=
 finset.maybe_unique_element univ

lemma maybe_unique_element_prop (a : α)
 (e : maybe_unique_element α = some a) :
  univ = finset.singleton a := 
  maybe_unique_element_prop univ a e

lemma some_unique_element : 
 maybe_unique_element α = none ↔ card α ≠ 1 := 
finset.some_unique_element univ

lemma eq_singleton (a : α) :
 univ = finset.singleton a ↔ (card α = 1) := 
begin
 dsimp[card],
 let e := finset.eq_singleton univ a, 
 split,
 {intro u,exact (e.mp u).1},
 {intro v,exact e.mpr ⟨ v , mem_univ a ⟩}
end

lemma card_one_of_prop (h : ∃ x : α, ∀ y : α, y = x) : card α = 1 := 
begin
 dsimp[card],
 have h1 : (∃! x : α , x ∈ (@univ α _)) := begin
  rcases h with ⟨ x , x_unique ⟩, 
  let x_in_univ := @mem_univ α _ x,
  have x_unique_alt : ∀ y : α, y ∈ (@univ α _) → y = x := 
  begin
   intros y y_in_univ,
   exact x_unique y
  end,
  exact ⟨ x , x_in_univ , x_unique_alt ⟩ 
 end,
 exact finset.card_one_of_prop univ h1
end

def witness (p : α → Prop) [decidable_pred p]
 (h : ∃! x, p x) : 
  { a : α // univ.filter p = singleton a} :=
begin
 have h1 : ∃! x, x ∈ (@univ α _) ∧ p x := 
 begin
  rcases h with ⟨ x , p_x , x_unique⟩, 
  have x_prop : x ∈ univ ∧ p x := ⟨ mem_univ x , p_x ⟩, 
  have x_unique_alt : ∀ y, y ∈ univ ∧ p y → y = x := 
   λ y y_prop, x_unique y y_prop.2,
  exact ⟨ x , x_prop , x_unique_alt ⟩  
 end,
 exact finset.witness univ p h1,
end

end fintype



