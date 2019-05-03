import data.vector logic.embedding data.fin data.list.basic
import data.list_extra

namespace vector 
open vector

variables {α : Type*} {β : Type*} {n m : ℕ}

lemma head_eq_zeroth : ∀ (v : vector α (n + 1)), v.head = nth v 0 
| ⟨list.nil,l_len⟩ := by {cases l_len}
| ⟨_ :: _,_⟩ := rfl 

def single (a : α) : vector α 1 := a :: vector.nil

lemma head_single (a : α) : (single a).head = a := rfl
lemma single_val (a : α) : (single a).val = [a] := rfl

lemma single_head : ∀ v : vector α 1, v = single v.head 
| ⟨list.nil,l_len⟩ := by {cases l_len}
| ⟨[_],l_len⟩ := rfl
| ⟨_ :: _ :: _,l_len⟩ := by {cases l_len}

lemma veq_of_eq {x₀ x₁ : vector α n} (e : x₀ = x₁) :
 x₀.val = x₁.val := congr_arg subtype.val e

def concat (v : vector α n) (a : α) : vector α (n + 1) := 
 v.append (a :: vector.nil)

def trim : ∀ (v : vector α (n + 1)), vector α n 
| ⟨l,l_len⟩ := ⟨l.take n,
   by { rw[list.length_take,l_len], 
        exact min_eq_left (le_of_lt n.lt_succ_self)}⟩ 

def last (v : vector α (n + 1)) : α := v.nth ⟨n,n.lt_succ_self⟩

lemma trim_to_list : ∀ (v : vector α (n + 1)), v.trim.to_list = v.to_list.take n 
| ⟨l,l_len⟩ := rfl

lemma trim_concat : ∀ (v : vector α n) (a : α), (v.concat a).trim = v 
| ⟨l,l_len⟩ a := subtype.eq $ by {
 change (l ++ [a]).take n = l,
 rw[← l_len,list.take_append_of_le_length (le_refl l.length),list.take_all],}

lemma last_concat : ∀ (v : vector α n) (a : α), (v.concat a).last = a
| ⟨l,l_len⟩ a := by {
 have h : n < (l ++ [a]).length :=
  by {rw[list.length_append,list.length,list.length,zero_add,l_len],
      exact n.lt_succ_self,},
 have h' : (l ++ [a]).nth n = some a := l_len ▸ (l.nth_concat_length a),
 injection ((list.nth_le_nth h).symm.trans h'),}

lemma concat_trim_last : ∀ (v : vector α (n + 1)), v.trim.concat v.last = v
| ⟨l,l_len⟩ := subtype.eq $ begin
 change (l.take n) ++ [l.nth_le n _] = l,
 let h := list.take_append_drop n l,
 let h' := list.drop_eq_last l_len,
 rw[h'] at h,
 exact h,
end

def cons_inj (n : ℕ) (a : α) : vector α n ↪ vector α (n + 1) := {
 to_fun := vector.cons a,
 inj := λ ⟨l₀,l₀_len⟩ ⟨l₁,l₁_len⟩ e, 
 begin 
  apply subtype.eq,
  dsimp[vector.cons] at e,
  let f : vector α n → list α := @vector.to_list α n,
  let e' : list.cons a l₀ = list.cons a l₁ := vector.veq_of_eq e,
  injection e' with em ev
 end 
}

def concat_inj (n : ℕ) (a : α) : vector α n ↪ vector α (n + 1) := {
 to_fun := λ v, v.concat a,
 inj := λ ⟨l₀,l₀_len⟩ ⟨l₁,l₁_len⟩ e, 
 begin 
  apply subtype.eq,
  replace e := vector.veq_of_eq e,
  exact list.append_inj_right e (l₀_len.trans l₁_len.symm),
 end 
}

section prod

variable [monoid α]
variable [add_monoid β]

@[to_additive vector.sum]
def prod (v : vector α n) : α := v.val.prod

@[to_additive vector.sum_eq_val_sum]
lemma prod_eq_val_prod (v : vector α n) : v.prod = v.val.prod := rfl

@[to_additive vector.sum_cons]
lemma prod_cons : ∀ (a : α) (v : vector α n),
 (a :: v).prod = a * v.prod
| a ⟨l,l_len⟩ := list.prod_cons

@[to_additive vector.sum_append]
lemma prod_append : ∀ (v : vector α n) (w : vector α m), (vector.append v w).prod = v.prod * w.prod
| ⟨l,l_len⟩ ⟨k,k_len⟩ := list.prod_append

lemma prod_concat (n : ℕ) : ∀ (v : vector α n) (a : α),
 (v.concat a).prod = v.prod * a
| ⟨l,l_len⟩ a := by {rw[concat],change (l ++ [a]).prod = l.prod * a,
                    rw[list.prod_append,list.prod_cons,list.prod_nil,mul_one],}

lemma sum_concat (n : ℕ) : ∀ (v : vector β n) (b : β),
 (v.concat b).sum = v.sum + b
| ⟨l,l_len⟩ b := by {rw[concat],change (l ++ [b]).sum = l.sum + b,
                    rw[list.sum_append,list.sum_cons,list.sum_nil,add_zero],}


end prod
end vector

