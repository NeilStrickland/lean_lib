import data.list.basic logic.embedding
import tactic.squeeze

namespace list
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open list

def all_prop {α : Type*} (p : α → Prop) : ∀ (l : list α), Prop
| nil := true
| (a :: l) := (p a) ∧ (all_prop l)

lemma all_prop_iff {α : Type*} {p : α → Prop} : ∀ {l : list α},
 all_prop p l ↔ ∀ a, a ∈ l → p a 
| nil := by {rw[all_prop,true_iff],intros a ha,cases ha,}
| (cons m l) := 
by {rw[all_prop],split,
 {rintro ⟨hm,hl⟩ a ha,rcases ha,exact ha.symm ▸ hm,
  exact (all_prop_iff.mp hl) a ha},
 {intro h,split,
  exact h m (mem_cons_self m l),
  apply all_prop_iff.mpr,intros a ha,
  exact h a (mem_cons_of_mem m ha),
 }
}


def cons_embedding (a : α) : list α ↪ list α := ⟨cons a,cons_inj⟩

def concat_embedding (a : α) : list α ↪ list α := 
 ⟨λ l, l ++ [a],λ l₁ l₂ e, append_right_cancel e⟩

def rtake (n : ℕ) (l : list α) := l.drop (l.length - n)

def rdrop (n : ℕ) (l : list α) := l.take (l.length - n)

lemma eq_singleton : ∀ (l : list α) (h : l.length = 1),
 l = [l.nth_le 0 (by {rw[h],exact nat.lt_succ_self 0})]
| [] h := by {cases h}
| [a] h := rfl
| (_ :: _ :: _) h := by {cases h}

lemma nth_le_congr (l : list α) {n₁ n₂ : ℕ} (h₁ : n₁ < l.length) (e : n₁ = n₂) : 
 l.nth_le n₁ h₁ = l.nth_le n₂ (e ▸ h₁) := by {cases e,refl}

lemma nth_le_append' : ∀ (l₁ : list α) {l₂ : list α} {n : ℕ} (hn : n < l₂.length),
 (l₁ ++ l₂).nth_le (l₁.length + n) ((list.length_append l₁ l₂).symm ▸ (nat.add_lt_add_left hn l₁.length)) = l₂.nth_le n hn 
| list.nil l₂ n hn := by {congr,dsimp[length],rw[zero_add]}
| (a :: l₁) l₂ n hn := begin 
 let h := nth_le_append' l₁ hn,
 dsimp[append],rw[h.symm],
 have : l₁.length + 1 + n = (l₁.length + n) + 1 := by {rw[add_assoc,add_comm 1,← add_assoc],},
 rw[nth_le_congr _ _ this,nth_le],refl,  
end

lemma nth_le_take : ∀ {n m : ℕ} {l : list α} (hn : n < m) (hm : m ≤ l.length),
 (l.take m).nth_le n (by {rw[length_take,min_eq_left hm], exact hn}) = 
   l.nth_le n (lt_of_lt_of_le hn hm)
| n 0 l hn hm := by {cases hn}
| n (m + 1) [] hn hm := by {cases hm}
| 0 (m + 1) (a :: l) hn hm := rfl
| (n + 1) (m + 1) (a :: l) hn hm := 
   nth_le_take (nat.lt_of_succ_lt_succ hn) (nat.le_of_succ_le_succ hm)

lemma nth_le_drop : ∀ {n m : ℕ} {l : list α} (h : m + n < l.length),
 (l.drop m).nth_le n (by {rw[length_drop],rw[add_comm] at h,exact nat.lt_sub_right_of_add_lt h}) =
  l.nth_le (m + n) h 
| n 0 l h := (nth_le_congr l h (zero_add n)).symm
| n (m + 1) [] h := by {cases h}
| n (m + 1) (a :: l) h := begin 
   dsimp[drop],
   have : m + 1 + n = (m + n) + 1 := by {rw[add_assoc,add_comm 1,← add_assoc],},
   rw[this] at h,
   rw[nth_le_congr _ _ this],dsimp[nth_le],apply nth_le_drop,
end

lemma drop_eq_last {n : ℕ} {l : list α} (h : l.length = n + 1) :
  (l.drop n) = [l.nth_le n (h.symm ▸ n.lt_succ_self)] := 
begin
 let t := l.drop n,
 let a := l.nth_le n (h.symm ▸ n.lt_succ_self),
 change t = [a],
 let a' := t.nth_le 0 _,
 have : a = a' := begin
  dsimp[a,a',last,fin.last],
  let h := @list.nth_le_drop α 0 n l (by {rw[h,add_zero],exact n.lt_succ_self}), 
  rw[list.nth_le_congr _ _ (add_zero n)] at h,
  exact h.symm,
 end,
 rw[this],
 have t_len : t.length = 1 := by { rw[list.length_drop,h,nat.add_sub_cancel_left]},
 exact eq_singleton t t_len,
end

lemma sum_singleton [add_monoid α] (a : α) : [a].sum = a := 
 by {rw[sum_cons,sum_nil,add_zero]}
 
end list