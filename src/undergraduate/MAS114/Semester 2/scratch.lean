namespace list 

variables {α : Type*} [decidable_eq α] 

def erasures : list α → list (α × (list α)) 
| [] := []
| (a :: l) := ⟨a,l⟩ :: ((erasures l).map (λ x, ⟨x.1,a :: x.2⟩))

def perm' : list α → list α → Prop
| [] [] := true
| [] (b :: m) := false
| (a :: l) m := begin
  exact ((erasures m).map (λ (x : α × (list α)), a = x.1 ∧ (perm' l x.2))).foldl or false,
end

example : perm' [1,2,3] [3,1,2] := 
begin
  simp [perm', erasures],
end
namespace perm' 

lemma count_eq :
  ∀ {l m : list α} (hp : perm' l m) (x : α), l.count x = m.count x 
| [] [] _ _ := rfl
| [] (b :: m) hp _ := false.elim hp
| (a :: l) m ⟨hm,hp⟩ x := 
begin
  rw [list.count_cons, count_eq hp],
  split_ifs with hx,
  { cases hx,
    rw [list.count_erase_self a m],
    exact nat.succ_pred_eq_of_pos (list.count_pos.mpr hm) },
  { exact list.count_erase_of_ne hx m }
end

lemma mem_iff 
  {l m : list α} (hp : perm' l m) {x : α} : x ∈ l ↔ x ∈ m :=
begin
  rw [← list.count_pos, ← list.count_pos, count_eq hp ]
end

def refl : ∀ (l : list α), perm' l l 
| [] := trivial
| (a :: l) := ⟨list.mem_cons_self a l, 
              by { rw [list.erase, if_pos rfl], exact refl l} ⟩ 

def trans : ∀ {k l m : list α}, perm' k l → perm' l m → perm' k m
| [] [] [] _ _ := trivial
| [] [] (c :: m) _ hlm := false.elim hlm
| [] (b :: l) _ hkl _ := false.elim hkl 
| (a :: k) [] _ hkl _ := false.elim (list.not_mem_nil a hkl.1)
| (a :: k) (b :: l) [] _ hlm := false.elim (list.not_mem_nil b hlm.1)
| (a :: k) (b :: l) (c :: m) hkl hlm := 
begin
  rw [perm', list.mem_cons_iff, list.erase] at *,
  by_cases hba : b = a,
  { rw [if_pos hba] at hkl, cases hba,
    exact ⟨hlm.1,trans hkl.2 hlm.2⟩ },
  rw [if_neg hba] at hkl,
  by_cases hcb : c = b, 
  { rw [if_pos hcb] at hlm, cases hcb, rw [if_neg hba], },
end

def symm : ∀ {l m : list α}, perm' l m → perm' m l
| [] [] _ := trivial
| [] (b :: m) h := false.elim h
| (a :: l) m h := begin
  rcases h with ⟨hm,hp⟩,
  cases m with b m, {exfalso, exact list.not_mem_nil a hm},
  dsimp [perm'],
  by_cases hab : a = b,
  { cases hab, rw [list.erase, if_pos rfl] at hp ⊢ ,
    exact ⟨list.mem_cons_self a l,symm hp⟩ },
  { cases hm, { exfalso, exact hab hm }, 
    change a ≠ b at hab,
    rw [list.erase, if_neg hab.symm] at hp,
    rw [list.erase, if_neg hab],
    rcases symm hp with ⟨hbl,hp'⟩,
    split, { exact list.mem_cons_of_mem _ hbl },
    sorry
  }
end

end perm'

end list


lemma finset.mem2 {α : Type*} (a₀ a₁ : α) (h : list.nodup _) {x : α} : 
  x ∈ finset.mk' [a₀,a₁] h ↔ x = a₀ ∨ x = a₁ := 
begin 
  change x ∈ [a₀,a₁] ↔ _, 
  simp only [list.mem_cons_iff, list.not_mem_nil, or_false]
end

lemma finset.mem3 {α : Type*} (a₀ a₁ a₂ : α) (h : list.nodup _) {x : α} : 
  x ∈ finset.mk' [a₀,a₁,a₂] h ↔ x = a₀ ∨ x = a₁ ∨ x = a₂ := 
begin 
  change x ∈ [a₀,a₁,a₂] ↔ _, 
  simp only [list.mem_cons_iff, list.not_mem_nil, or_false]
end

lemma finset.eq2 {α : Type*} 
  (a₀ a₁ b₀ b₁ : α) 
  (ha : [a₀,a₁].nodup)
  (hb : [b₀,b₁].nodup) :
  finset.mk' [a₀,a₁] ha = finset.mk' [b₀,b₁] hb ↔ 
  (a₀ = b₀ ∧ a₁ = b₁) ∨ (a₀ = b₁ ∧ a₁ = b₀) := 
begin
  let A := finset.mk' [a₀,a₁] ha,
  let B := finset.mk' [b₀,b₁] hb,
  change A = B ↔ _,
  have hA : ∀ {x : α}, x ∈ A ↔ _ := λ x, finset.mem2 a₀ a₁ ha,
  have hB : ∀ {x : α}, x ∈ B ↔ _ := λ x, finset.mem2 b₀ b₁ hb,
  split,
  { intro h,
    have ha₀ : a₀ = b₀ ∨ a₀ = b₁ := hB.mp (h ▸ (hA.mpr (or.inl rfl))),
    have ha₁ : a₁ = b₀ ∨ a₁ = b₁ := hB.mp (h ▸ (hA.mpr (or.inr rfl))),
    have hb₀ : b₀ = a₀ ∨ b₀ = a₁ := hA.mp (h.symm ▸ (hB.mpr (or.inl rfl))),
    have hb₁ : b₁ = a₀ ∨ b₁ = a₁ := hA.mp (h.symm ▸ (hB.mpr (or.inr rfl))),
    clear hA hB,
    rcases ha₀ with ⟨⟨_⟩|⟨_⟩⟩ ; rcases ha₁ with ⟨⟨_⟩|⟨_⟩⟩ ;
    rcases hb₀ with ⟨⟨_⟩|⟨_⟩⟩ ; rcases hb₁ with ⟨⟨_⟩|⟨_⟩⟩ ; cc },
  { rintro (⟨⟨h₀⟩,⟨h₁⟩⟩ | ⟨⟨h₂⟩,⟨h₃⟩⟩); 
    ext x; simp only [hA,hB]; cc }
end
