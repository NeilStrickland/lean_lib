import data.fintype.basic
import tactic.squeeze

variable (n : ℕ)

def birange : Type := { u : ℕ × ℕ // u.1 + u.2 = n }

namespace birange 

variable {n}

def fst (u : birange n) := u.val.fst
def snd (u : birange n) := u.val.snd

lemma rel (u : birange n) : u.fst + u.snd = n := u.property

@[ext]
lemma ext (u₀ u₁ : birange n) :
 u₀ = u₁ ↔ (u₀.fst = u₁.fst ∧ u₀.snd = u₁.snd) := 
begin
 rcases u₀ with ⟨⟨i₀,j₀⟩,h₀⟩,
 rcases u₁ with ⟨⟨i₁,j₁⟩,h₁⟩,
 dsimp[fst,snd] at *,
 rw[subtype.ext_iff_val,prod.mk.inj_iff]
end

lemma ext_left (u₀ u₁ : birange n) : u₀ = u₁ ↔ u₀.fst = u₁.fst := 
 ⟨λ e, by rw[e],
  λ e, by {apply (ext u₀ u₁).mpr,split,assumption,
   let e' := u₀.rel.trans u₁.rel.symm,
   rw[e] at e',exact nat.add_left_cancel e',
  } ⟩

lemma ext_right (u₀ u₁ : birange n) : u₀ = u₁ ↔ u₀.snd = u₁.snd := 
 ⟨λ e, by rw[e],
  λ e, by {apply (ext u₀ u₁).mpr,split,
   let e' := u₀.rel.trans u₁.rel.symm,
   rw[e] at e',exact nat.add_right_cancel e',
   assumption
  } ⟩

instance : decidable_eq (birange n) := 
 λ u₀ u₁, by { apply_instance }

def swap : birange n → birange n :=
 λ ⟨⟨i,j⟩,e⟩ , ⟨⟨j,i⟩,(add_comm j i).trans e⟩ 

lemma swap_swap (u : birange n) : 
 u.swap.swap = u := 
  by { rcases u with ⟨⟨i,j⟩,h⟩, rw[ext], split; refl, } 

variable (n)

def fin_equiv : (birange n) ≃ fin n.succ := {
 to_fun := λ u, ⟨u.val.1,by {apply nat.lt_succ_of_le,
   have := nat.le_add_right u.val.1 u.val.2,
   rw[u.property] at this,exact this}⟩ ,
 inv_fun := λ i, ⟨prod.mk i.val (n - i.val),nat.add_sub_of_le (nat.le_of_lt_succ i.is_lt)⟩,
 left_inv := λ ⟨⟨i,j⟩,h⟩, begin apply (ext_left _ _).mpr,refl end,
 right_inv := λ ⟨i,i_is_lt⟩, by { apply fin.eq_of_veq, refl }
}

instance : fintype (birange n) := 
 fintype.of_equiv (fin n.succ) (fin_equiv n).symm

end birange

variable (n)
def trirange : Type :=
 { u : ℕ × ℕ × ℕ // u.1 + (u.2.1 + u.2.2) = n }

namespace trirange 

variable {n}

def fst (u : trirange n) := u.val.1
def snd (u : trirange n) := u.val.2.1
def thd (u : trirange n) := u.val.2.2

@[ext]
lemma ext (u₀ u₁ : trirange n) :
 u₀ = u₁ ↔ (u₀.fst = u₁.fst ∧ u₀.snd = u₁.snd ∧ u₀.thd = u₁.thd) := 
  by {rcases u₀ with ⟨⟨i₀,j₀,k₀⟩,h₀⟩,
      rcases u₁ with ⟨⟨i₁,j₁,k₁⟩,h₁⟩,
      dsimp[fst,snd,thd],
      rw[subtype.ext_iff_val,prod.mk.inj_iff,prod.mk.inj_iff], }

instance : decidable_eq (trirange n) := 
 λ u₀ u₁, by { apply_instance }

variable (n)

def sigma_equiv : (trirange n) ≃ Σ (i : fin n.succ), birange (n - i) := {
 to_fun := λ ⟨⟨i,j,k⟩,h⟩,begin
  simp only[] at h,
  have hi : i < n.succ := by {
    apply nat.lt_succ_of_le,
    have := nat.le_add_right i (j + k),
    rw[h] at this,
    exact this, },
  have hjk : j + k = n - i := by {rw[← h,add_comm i,nat.add_sub_cancel],},
  exact ⟨⟨i,hi⟩,⟨⟨j,k⟩,hjk⟩⟩
 end,
 inv_fun := λ ⟨⟨i,hi⟩,⟨⟨j,k⟩,hjk⟩⟩,begin
  change j + k = n - i at hjk,
  have h := calc i + (j + k) = i + (n - i) : by {rw[hjk]}
   ... = n : by rw[add_comm,nat.sub_add_cancel (nat.le_of_lt_succ hi)],
  exact ⟨⟨i,j,k⟩,h⟩
 end, 
 left_inv := λ ⟨⟨i,j,k⟩,h⟩, by {apply subtype.eq,refl,},
 right_inv := λ ⟨⟨i,hi⟩,⟨⟨j,k⟩,hjk⟩⟩, by {refl,}
}

def sigma_equiv' : (trirange n) ≃ Σ (k : fin n.succ), birange (n - k) := {
 to_fun := λ ⟨⟨i,j,k⟩,h⟩,begin
  simp only[] at h,
  have hk : k < n.succ := by {
    apply nat.lt_succ_of_le,
    have := nat.le_add_left k (i + j),
    rw[add_assoc,h] at this,
    exact this, },
  have hij : i + j = n - k := by {rw[← h,← add_assoc,nat.add_sub_cancel],},
  exact ⟨⟨k,hk⟩,⟨⟨i,j⟩,hij⟩⟩
 end,
 inv_fun := λ ⟨⟨k,hk⟩,⟨⟨i,j⟩,hij⟩⟩,begin
  change i + j = n - k at hij,
  have h := calc i + (j + k) = (n - k) + k : by {rw[← add_assoc,hij]}
   ... = n : by rw[nat.sub_add_cancel (nat.le_of_lt_succ hk)],
  exact ⟨⟨i,j,k⟩,h⟩
 end, 
 left_inv := λ ⟨⟨i,j,k⟩,h⟩, by {apply subtype.eq,refl,},
 right_inv := λ ⟨⟨i,hi⟩,⟨⟨j,k⟩,hjk⟩⟩, by {refl,}
}

instance : fintype (trirange n) := 
 fintype.of_equiv _ (sigma_equiv n).symm

end trirange
