/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This file gives some basic definitions for graph theory.
It supports only graphs with no loops or multiple edges.

It should be refactored to use definitions and results from 
data/pos_list.lean

-/

import data.pos_list
import tactic.interactive 

namespace combinatorics 

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

/-
 For finite graphs with decidable equality:
 define valence, prove that there are two vertices with 
 the same valence. 
-/

end path
end graph
end combinatorics