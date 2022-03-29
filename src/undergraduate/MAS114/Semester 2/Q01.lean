import data.fintype.basic 
import algebra.power_mod 
import group_theory.group_action 
import algebra.group_power 
import algebra.big_operators 
import data.zmod.basic
import tactic.ring tactic.abel
import group_theory.self_map
import group_theory.action_instances
import group_theory.burnside_count
import group_theory.dihedral
import data.fin_extra
import data.enumeration
import order.lexicographic order.lattice order.lattice_extra

open group_theory

namespace MAS114
namespace exercises_2
namespace Q01

def finset.mk' {α : Type*} (l : list α) (h : l.nodup) : finset α := 
  finset.mk l h

lemma finset.eq_iff_veq {α : Type*} (s₀ s₁ : finset α) : 
  s₀ = s₁ ↔ s₀.val = s₁.val := 
⟨ λ h, by rw[h], λ h, finset.eq_of_veq h⟩

lemma finset.eq_iff_perm {α : Type*} (l₀ l₁ : list α) (h₀ : l₀.nodup) (h₁ : l₁.nodup) :
  finset.mk' l₀ h₀ = finset.mk' l₁ h₁ ↔ list.perm l₀ l₁ := 
begin
  rw [finset.eq_iff_veq],
  change (l₀ : multiset α) = (l₁ : multiset α) ↔ _,
  split, 
  exact quotient.exact,
  exact @quotient.sound (list α) (list.is_setoid α) l₀ l₁
end


def X := (fin 4) × (fin 4)

namespace X

instance : decidable_eq X    := by { dsimp [X], apply_instance }
instance : fintype X         := by { dsimp [X], apply_instance }
instance : has_repr X        := ⟨λ ij, ij.1.val.repr ++ ij.2.val.repr⟩ 
instance : distrib_lattice X := by { dsimp [X], apply_instance }
instance : bounded_order X   := by { dsimp [X], apply_instance }

/-
instance : linear_order X := 
  by { dsimp [X], exact lex_order }
-/

def s : self_map X := λ ij, ⟨ij.1, ij.2.reflect⟩ 
def r : self_map X := λ ij, ⟨ij.2.reflect, ij.1⟩

def p : dihedral.prehom 4 (self_map X) := 
begin 
 refine_struct {
  r := r,
  s := s
 }; funext ij; rcases ij with ⟨i,j⟩; 
 simp [self_map.one_app, self_map.mul_app, r, s, pow_succ, fin.reflect_reflect];
 refl
end

instance : mul_action (dihedral 4) X := self_map.mul_action_of_hom p.to_hom

lemma smul_s (ij : X) : (dihedral.s (0 : zmod 4)) • ij = ⟨ij.1, ij.2.reflect⟩ := rfl
lemma smul_r (ij : X) : (dihedral.r (1 : zmod 4)) • ij = ⟨ij.2.reflect, ij.1⟩ := rfl

def F : (finset (orbits (dihedral 4) X)) := finset.univ
def L (o : orbits (dihedral 4) X) : finset X :=  
  finset.univ.filter (λ x, o = orbit x)
#eval F.image L

end X

def Y := finset X

namespace Y
instance : decidable_eq Y := by { dsimp [Y], apply_instance }
instance : fintype Y      := by { dsimp [Y], apply_instance }
instance : has_repr Y     := by { dsimp [Y], apply_instance }

def bounding_box : Y → X × X := 
  λ (xs : finset X), ⟨xs.inf id,xs.sup id⟩

def size  (y : Y) : ℕ × ℕ := 
  let b := y.bounding_box in prod.mk (b.2.1 - b.1.1) (b.2.2 - b.1.2)

def is_horizontal (y : Y) : bool := y.size.2 = 0
def is_vertical   (y : Y) : bool := y.size.1  = 0

instance : mul_action (dihedral 4) Y := 
  _root_.mul_action.finset_action
end Y

@[derive decidable_eq]
inductive Z_single 
| H : (fin 3) → (fin 4) → Z_single
| V : (fin 4) → (fin 3) → Z_single

namespace Z_single

def to_string : Z_single → string
| (H i j) := "H" ++ i.val.repr ++ j.val.repr
| (V i j) := "V" ++ i.val.repr ++ j.val.repr

instance : has_repr Z_single := ⟨to_string⟩ 

def bounding_box : Z_single → X × X 
| (H i j) := ⟨⟨i.inc,j⟩,⟨i.succ,j⟩⟩
| (V i j) := ⟨⟨i,j.inc⟩,⟨i,j.succ⟩⟩

def size : Z_single → ℕ × ℕ  
| (H _ _) := ⟨1,0⟩ 
| (V _ _) := ⟨0,1⟩

instance : enumeration Z_single := {
  elems := 
   ((enumeration.elems (fin 3)).bind 
      (λ i, (enumeration.elems (fin 4)).map (Z_single.H i))) ++
   ((enumeration.elems (fin 4)).bind 
      (λ i, (enumeration.elems (fin 3)).map (Z_single.V i))),
  nodup := dec_trivial,
  complete := λ z, 
  begin
    cases z with i j i j; rw [list.mem_append],
    { left, 
      exact @list.mem_bind_of_mem (fin 3) Z_single (H i j)
        (enumeration.elems (fin 3)) 
        (λ i, (enumeration.elems (fin 4)).map (Z_single.H i))
        i (enumeration.complete i)
        (list.mem_map_of_mem (H i) (enumeration.complete j)) },  
    { right, 
      exact @list.mem_bind_of_mem (fin 4) Z_single (V i j)
        (enumeration.elems (fin 4)) 
        (λ i, (enumeration.elems (fin 3)).map (Z_single.V i))
        i (enumeration.complete i)
        (list.mem_map_of_mem (V i) (enumeration.complete j)) },  
  end
}
 
def to_Y₀ : ∀ (z : Z_single), list X 
| (H i j) := [prod.mk i.inc j, prod.mk i.succ j]
| (V i j) := [prod.mk i j.inc, prod.mk i j.succ]

lemma to_Y₀_nodup (z : Z_single) : z.to_Y₀.nodup :=
begin
 have : ∀ {n : ℕ} (k : fin n), k.inc ≠ k.succ := 
   λ n k, ne_of_lt k.inc_lt_succ,
 cases z with i j i j; dsimp[to_Y₀]; 
 simp [fin.eq_iff_veq,(nat.succ_ne_self i.val).symm, this]
end

def to_Y (z : Z_single) : Y := @finset.mk X z.to_Y₀ z.to_Y₀_nodup

lemma to_Y_card (z : Z_single) : z.to_Y.card = 2 := 
by { cases z with i j i j; refl }

lemma to_Y_bounding_box (z : Z_single) : 
  z.to_Y.bounding_box = z.bounding_box := 
begin
  cases z with i j i j, 
  focus { 
    let u : X := ⟨i.inc,j⟩, let v : X := ⟨i.succ,j⟩,
    have huv : u ≤ v := ⟨le_of_lt i.inc_lt_succ,le_refl j⟩, },
  swap, focus 
  { let u : X := ⟨i,j.inc⟩, let v : X := ⟨i,j.succ⟩,
    have huv : u ≤ v := ⟨le_refl i,le_of_lt j.inc_lt_succ⟩ },
  all_goals {  
    change prod.mk (u ⊓ (v ⊓ ⊤)) (u ⊔ (v ⊔ ⊥)) = ⟨u,v⟩,
    rw [lattice.inf_top_eq, lattice.sup_bot_eq],
    rw [lattice.inf_of_le_left huv, lattice.sup_of_le_right huv] }
end

lemma to_Y_size (z : Z_single) : 
  z.to_Y.size = z.size := 
begin
  dsimp [Y.size], rw [to_Y_bounding_box],
  rcases z with ⟨⟨i,hi⟩,⟨j,hj⟩⟩ | ⟨⟨i,hi⟩,⟨j,hj⟩⟩,
  { change prod.mk ((i + 1) - i) (j - j) = ⟨1,0⟩,
    rw [nat.sub_self, nat.add_sub_cancel_left] },
  { change prod.mk (i - i) ((j + 1) - j) = ⟨0,1⟩,
    rw [nat.sub_self, nat.add_sub_cancel_left] }
end

lemma to_Y_inj : function.injective to_Y := 
begin
  intros z₀ z₁ he,
  have hb := congr_arg Y.bounding_box he,
  rw [to_Y_bounding_box, to_Y_bounding_box] at hb, clear he,
  cases z₀ with i₀ j₀ i₀ j₀; cases z₁ with i₁ j₁ i₁ j₁,
  all_goals {
    simp only [bounding_box] at hb, 
    injection hb  with hb₀ hb₁, 
    injection hb₀ with hb₂ hb₃, 
    injection hb₁ with hb₄ hb₅ },
  { replace hb₄ := fin.succ_inj _ _ hb₄, cc },
  { exfalso, exact ne_of_lt (fin.inc_lt_succ i₀) (hb₂.trans hb₄.symm) },
  { exfalso, exact ne_of_lt (fin.inc_lt_succ j₀) (hb₃.trans hb₅.symm) },
  { replace hb₅ := fin.succ_inj _ _ hb₅, cc }
end

def s : Z_single → Z_single
| (H i j) := H i j.reflect 
| (V i j) := V i j.reflect 

def r : Z_single → Z_single
| (H i j) := V j.reflect i
| (V i j) := H j.reflect i

lemma to_Y_s (z : Z_single) :
  (s z).to_Y = (@dihedral.s 4 0) • z.to_Y :=
begin
  cases z with i j i j; dsimp[s, to_Y, to_Y₀] ;
  change finset.mk ([_,_] : multiset X) _ = _;
  ext x;
  simp only [
      mul_action.mem_smul_finset', dihedral.s_inv,
      finset.mem_mk, multiset.mem_coe, 
      list.mem_cons_iff, list.mem_singleton,
      mul_action.smul_eq_iff_eq_smul_inv];
  simp only [
      fin.reflect_inc, fin.reflect_succ, X.smul_s, or_comm],
end

lemma to_Y_r (z : Z_single) :
  (r z).to_Y = (@dihedral.r 4 1) • z.to_Y :=
begin
  cases z with i j i j; dsimp[s, to_Y, to_Y₀] ;
  change finset.mk ([_,_] : multiset X) _ = _;
  ext x;
  simp only [
      mul_action.mem_smul_finset', dihedral.r_inv, neg_neg,
      finset.mem_mk, multiset.mem_coe, 
      list.mem_cons_iff, list.mem_singleton,
      mul_action.smul_eq_iff_eq_smul_inv];
  simp only [
      fin.reflect_inc, fin.reflect_succ, X.smul_r, X.smul_r, or.comm],
end

end Z_single

end Q01
end exercises_2
end MAS114