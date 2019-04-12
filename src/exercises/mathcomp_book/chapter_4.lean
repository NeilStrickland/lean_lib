import tactic.interactive tactic.find data.list.basic

def my_list_bexists {α : Type} (p : α → bool) : ∀ l : list α, bool 
| list.nil := ff
| (list.cons a l) := bor (p a)  (my_list_bexists l)

def my_list_pexists {α : Type} (p : α → Prop) : ∀ l : list α, Prop
| list.nil := false
| (list.cons a l) := (p a) ∨ (my_list_pexists l)

def my_list_pexists' {α : Type} (p : α → Prop) (l : list α) : Prop := 
 ∃ (i : ℕ) (i_is_lt : i < l.length), p (l.nth_le i i_is_lt)

lemma my_list_pexists_nil {α : Type} (p : α → Prop) : 
 ¬ my_list_pexists' p list.nil := by {rintro ⟨i,⟨⟨_⟩,_⟩⟩}

lemma my_list_pexists_succ {α : Type} (p : α → Prop) (a : α) (l : list α) :
 my_list_pexists' p (a :: l) ↔ (p a ∨ (my_list_pexists' p l)) := begin
 unfold my_list_pexists',
 split,
 {rintro ⟨_|i,⟨i_is_lt,pi⟩⟩,
  {left,exact pi},
  {let i_is_lt' := nat.lt_of_succ_lt_succ i_is_lt,
  right,use i,use i_is_lt',
  exact pi,}
 },{
  rintro (pa | ⟨i,⟨i_is_lt,pi⟩⟩),
  {use 0,use nat.zero_lt_succ l.length,exact pa},
  {use i.succ,use nat.succ_lt_succ i_is_lt,exact pi}
 }
end

lemma my_list_pexists_iff {α : Type} (p : α → Prop) : ∀ (l : list α),
 my_list_pexists p l ↔ my_list_pexists' p l
| list.nil := ((iff_false _).mpr (my_list_pexists_nil p)).symm
| (a :: l) := by {rw[my_list_pexists_succ,← my_list_pexists_iff l],refl,}

instance my_list_pexists_decidable 
 {α : Type} (p : α → Prop) [decidable_pred p] : ∀ (l : list α), 
  decidable (my_list_pexists p l)
| list.nil := by { dsimp[my_list_pexists],apply_instance, }
| (a :: l) := by { 
    dsimp[my_list_pexists],
    haveI := my_list_pexists_decidable l, 
    apply_instance, }

instance my_list_pexists'_decidable 
 {α : Type} (p : α → Prop) [decidable_pred p] (l : list α) :
  decidable (my_list_pexists' p l) := 
   decidable_of_iff _ (my_list_pexists_iff p l)


