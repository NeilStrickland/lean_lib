import data.multiset
import data.list_extra 

namespace multiset
open multiset

variables {α : Type*}

def all_prop (p : α → Prop) (s : multiset α) : Prop := 
quot.lift_on s (list.all_prop p) (λ l₁ l₂ e, by {change list.perm l₁ l₂ at e,
 apply propext,
 apply @list.perm_induction_on α 
  (λ l₁ l₂, list.all_prop p l₁ ↔ list.all_prop p l₂) l₁ l₂ e,
 {rw[iff_self],trivial},
 {intros x l₁ l₂ h,simp only[],intro h',rw[list.all_prop,list.all_prop,h']},
 {intros x y l₁ l₂ h,simp only [],intro h',
  repeat {rw[list.all_prop]},rw[← and_assoc,and_comm (p y),and_assoc,h'],},
 {intros l₁ l₂ l₃ h₁₂ h₂₃,simp only[],intros e₁₂ e₂₃,exact e₁₂.trans e₂₃}
})

lemma all_prop_coe (p : α → Prop) (l : list α) : 
 all_prop p l = list.all_prop p l := rfl

lemma all_prop_iff {p : α → Prop} {s : multiset α} :
 all_prop p s ↔ ∀ a, a ∈ s → p a := 
begin
 rcases s,
 have : quot.mk setoid.r s = (s : multiset α) := rfl, rw[this],
 rw[all_prop_coe,list.all_prop_iff],
 split; intros h a; replace h := h a; rw[mem_coe] at *; exact h,
end

lemma pairwise_zero {α : Type*} (p : α → α → Prop) : 
 pairwise p 0 := ⟨list.nil,⟨rfl,list.pairwise.nil⟩⟩

variable [decidable_eq α]

lemma eq_iff_count {s t : multiset α} : 
 s = t ↔ ∀ a, count a s = count a t := 
begin
 split,
 {intros e a,rw[e]},
 {intro h,apply le_antisymm;rw[le_iff_count]; intro a; rw[h a],}
end

lemma eq_repeat_count (s : multiset α) : 
 s.erase_dup.bind (λ a, repeat a (count a s)) = s := 
begin
 rw[eq_iff_count],intro a,
 rw[count_bind],
 let s₁ := s.erase_dup, 
 let m₁ := s₁.card,
 let c := (λ b, count a (repeat b (count b s))),
 change (s₁.map c).sum = count a s,
 by_cases h : a ∈ s, 
 {have h₁ : a ∈ s₁ := mem_erase_dup.mpr h,
  let s₂ : multiset α := s₁.erase a,
  let s₃ : multiset α := (cons a s₂),
  have : s₁ = (cons a s₂) := (cons_erase h₁).symm,
  rw[this,map_cons,sum_cons],
  have : a ∉ s₂ := λ h,
   ((mem_erase_iff_of_nodup s.nodup_erase_dup).mp h).left rfl,
  have : s₂.map c = repeat 0 (s₂.map c).card := 
   by {apply eq_repeat.mpr ⟨rfl,_⟩,intros m hm,
       rcases (mem_map.mp hm) with ⟨b,⟨h₁,h₂⟩⟩,
       rw[← h₂,count_eq_zero],intro ha,
       rw[← eq_of_mem_repeat ha] at h₁,
       exact this h₁,
   },
  rw[this,sum_repeat,smul_eq_mul,mul_zero,add_zero],
  dsimp[c],rw[count_repeat,if_pos (rfl : a = a)],
 },
 {rw[count_eq_zero.mpr h],
  have : s₁.map c = repeat 0 (s₁.map c).card := 
   by {apply eq_repeat.mpr ⟨rfl,_⟩,intros m hm,
       rcases (mem_map.mp hm) with ⟨b,⟨h₁,h₂⟩⟩,
       rw[← h₂,count_eq_zero],intro ha,
       rw[eq_of_mem_repeat ha] at h,
       exact h (mem_erase_dup.mp h₁),
   },
  rw[this,sum_repeat,smul_eq_mul,mul_zero],
 }
end

end multiset

