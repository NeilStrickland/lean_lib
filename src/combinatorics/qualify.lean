/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Suppose we have a list `l` in a type `α`.  Suppose we also have a
subset `s` of `α`, formalised in the usual way as a term of type 
`set α`, or equivalently a predicate `α → Prop`.  Associated to
this we have a subtype `s' = {a : α // a ∈ s}`, and coercions 
have been defined so that Lean will interpret `s` as `s'` where 
necessary.  If all elements of `l` satisfy the predicate defining
`s`, then a mathematician would say that `l` can be regarded as
an element of `list s`.  In Lean we still have a corresponding term
`l'` of type `s`, but it is not literally the same as `l`.  This 
story is not just relevant for lists; there are similar 
considerations for pairs, finsets, elements of the free group and
so on.  

In this file we use the notation `qualify h l` for `l'`, where 
`h` is a proof that the elements of `l` satisfy the relevant 
predicate.  We prove various basic lemmas about this operation
and its inverse.  We have tried to write things in a way that
could be smoothly generalised to functors other than `list`,
but there should probably be some apparatus of type classes 
which we have not yet set up.  Also, Mario has suggested that
`cod_restrict` would be a better name than `qualify`, for 
compatibility with some existing code.
-/

import data.list.basic
import data.list.nodup

variables {α : Type*} 

namespace list
open list 

def qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) : list s := 
 pmap subtype.mk l @h

lemma length_qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) :
 (qualify l @h).length = l.length := length_pmap

def unqualify {s : set α} (l : list s) : list α := l.map subtype.val 

@[simp]
lemma unqualify_nil {s : set α} : unqualify (@nil s) = nil := rfl

@[simp]
lemma unqualify_cons {s : set α} (a : s) (l : list s) : 
 unqualify (a :: l) = a.val :: (unqualify l) := rfl

lemma unqualify_eq {s : set α} {l₁ l₂ : list s} :
 l₁ = l₂ ↔ (unqualify l₁ = unqualify l₂) := 
begin
 split,
 {exact congr_arg unqualify,},
 {induction l₁ with x₁ l₁ ih generalizing l₂,
  {rw[unqualify_nil],
   rcases l₂ with _ | ⟨x₂,l₂⟩,
   {intro,refl},
   {rw[unqualify_cons],intro eu,exact false.elim (list.no_confusion eu)}
  },{
   rw[unqualify_cons],
   rcases l₂ with _ | ⟨x₂,l₂⟩,
   {intro eu,exact false.elim (list.no_confusion eu)},
   {rw[unqualify_cons],intro eu,injection eu with euh eut,congr,
    exact subtype.eq euh,exact ih eut,
   }
  }
 }
end

@[simp]
lemma length_unqualify {s : set α} (l : list s) : (unqualify l).length = l.length := 
 length_map subtype.val l

lemma mem_unqualify {s : set α} {l : list s} {a : α} : 
 a ∈ unqualify l ↔ (∃ h : s a, subtype.mk a h ∈ l) := 
begin
 rcases (@mem_map s α subtype.val a l) with ⟨h0,h1⟩,
 split,
 {intro h2,rcases h0 h2 with ⟨⟨a,a_in_s⟩,⟨a_in_l,rfl⟩⟩,exact ⟨a_in_s,a_in_l⟩ },
 {rintro ⟨a_in_s,a_in_l⟩,exact h1 ⟨⟨a,a_in_s⟩,⟨a_in_l,rfl⟩⟩}
end

lemma mem_unqualify' {s : set α} {l : list s} {a : s} : 
 a.val ∈ unqualify l ↔ a ∈ l := 
begin
 split,
 {intro h0,
  rcases (mem_unqualify.mp h0) with ⟨a_in_s,a_in_l⟩ ,
  have h1 : a = ⟨a.val,a_in_s⟩ := subtype.eq rfl,
  rw[h1],exact a_in_l,
  },
  {intro h0,exact mem_map_of_mem _ h0,}
end

@[simp]
lemma un_qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) :
 unqualify (qualify l @h) = l := 
begin 
 dsimp[qualify],
 induction l with x l ih,
 {refl},
 {rw[unqualify,pmap,map],congr,
  exact ih (λ a a_in_l, h (mem_cons_of_mem x a_in_l)),
 }
end

def requalify {s t : set α} (l : list s) (h : ∀ {u : s}, u ∈ l → t u) : list t := 
 qualify (unqualify l) 
  (λ a a_in_l,
   begin rcases (mem_unqualify.mp a_in_l) with ⟨a_in_s,a_in_l⟩, exact h a_in_l, end )

@[simp]
lemma un_requalify {s t : set α} (l : list s) (h : ∀ {u : s}, u ∈ l → t u) : 
 unqualify (requalify l @h) = unqualify l := 
begin
 dsimp[requalify],rw[un_qualify]
end

lemma nodup_unqualify {s : set α} : ∀ {l : list s}, (unqualify l).nodup ↔ l.nodup
| [] := by { rw[unqualify_nil],simp only [nodup_nil], }
| (a :: l) := begin 
   rw[unqualify_cons,nodup_cons,nodup_cons,nodup_unqualify,@mem_unqualify' α s l a],
  end 

lemma nodup_qualify {s : set α} (l : list α) (h : ∀ {a}, a ∈ l → s a) :
 (qualify l @h).nodup ↔ l.nodup := by { rw[← nodup_unqualify,un_qualify], }

end list