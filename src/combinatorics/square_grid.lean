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

namespace combinatorics

variable (N : ℕ)

def square_grid := (fin N.succ) × (fin N.succ)

namespace square_grid

instance : decidable_eq (square_grid N) := 
 by { dsimp [square_grid], apply_instance }

instance : fintype (square_grid N) := 
 by { dsimp [square_grid], apply_instance }

instance : has_repr (square_grid N) := 
  ⟨λ ij, ij.1.val.repr ++ ij.2.val.repr⟩ 

instance : lattice.bounded_lattice (square_grid N) :=
  by { dsimp [square_grid], apply_instance }

variable {N} 
def s : self_map (square_grid N) := λ ij, ⟨ij.1, ij.2.reflect⟩ 
def r : self_map (square_grid N) := λ ij, ⟨ij.2.reflect, ij.1⟩
variable (N)

def p : dihedral.prehom 4 (self_map (square_grid N)) := 
begin 
 refine_struct {
  r := r,
  s := s
 }; funext ij; rcases ij with ⟨i,j⟩; 
 simp [self_map.one_app, self_map.mul_app, r, s, pow_succ, fin.reflect_reflect];
 refl
end

instance : mul_action (dihedral 4) (square_grid N) := 
  self_map.mul_action_of_hom (p N).to_hom

lemma smul_r₀ (ij : square_grid N) :
 (@dihedral.r 4 0) • ij = ij := rfl

lemma smul_r₁ (ij : square_grid N) :
 (@dihedral.r 4 1) • ij = ⟨ij.2.reflect, ij.1⟩ := rfl

lemma smul_r₂ (ij : (square_grid N)) :
  (@dihedral.r 4 2) • ij = ⟨ij.1.reflect, ij.2.reflect⟩ := 
begin
  change ((p N).to_hom) (@dihedral.r 4 2) ij = _,
  rw [dihedral.prehom.to_hom.map_r (p N) 2], 
  change r (r ij) = _,
  simp only [r, fin.reflect_reflect], 
end

lemma smul_r₃ (ij : (square_grid N)) :
  (@dihedral.r 4 3) • ij = ⟨ij.2, ij.1.reflect⟩ := 
begin
  change ((p N).to_hom) (@dihedral.r 4 3) ij = _,
  rw [dihedral.prehom.to_hom.map_r (p N) 3], 
  change r (r (r ij)) = _,
  simp only [r, fin.reflect_reflect], 
end

lemma smul_s₀ (ij : (square_grid N)) :
  (@dihedral.s 4 0) • ij = ⟨ij.1, ij.2.reflect⟩ := rfl

lemma smul_s₁ (ij : (square_grid N)) :
  (@dihedral.s 4 1) • ij = ⟨ij.2, ij.1⟩ := 
begin
  change ((p N).to_hom) (@dihedral.s 4 1) ij = _,
  rw [dihedral.prehom.to_hom.map_s (p N) 1, 
      self_map.mul_app],
  change r (s ij) = _, simp only [s, r, fin.reflect_reflect], 
end

lemma smul_s₂ (ij : (square_grid N)) :
  (@dihedral.s 4 2) • ij = ⟨ij.1.reflect, ij.2⟩ := 
begin
  change ((p N).to_hom) (@dihedral.s 4 2) ij = _,
  rw [dihedral.prehom.to_hom.map_s (p N) 2], 
  change r (r (s ij)) = _,
  simp only [s, r, fin.reflect_reflect], 
end

lemma smul_s₃ (ij : (square_grid N)) :
  (@dihedral.s 4 3) • ij = ⟨ij.2.reflect, ij.1.reflect⟩ := 
begin
  change ((p N).to_hom) (@dihedral.s 4 3) ij = _,
  rw [dihedral.prehom.to_hom.map_s (p N) 3], 
  change r (r (r (s ij))) = _,
  simp only [s, r, fin.reflect_reflect], 
end

def subsets := finset (square_grid N)

namespace subsets

instance : decidable_eq (subsets N) := 
  by { dsimp [subsets], apply_instance }

instance : has_repr (subsets N) := 
  by { dsimp [subsets], apply_instance }

instance : mul_action (dihedral 4) (subsets N) := 
  by { dsimp [subsets], apply_instance }

end subsets

@[derive decidable_eq]
structure dim := (w h : ℕ)

namespace dim

def flip : dim → dim := λ d, ⟨d.h, d.w⟩

lemma flip_h (d : dim) : d.flip.h = d.w := rfl
lemma flip_w (d : dim) : d.flip.w = d.h := rfl

lemma flip_flip (d : dim) : d.flip.flip = d := by { cases d, refl }

def smul₀ : (dihedral 4) → dim → dim
| (@dihedral.r 4 i) d := cond i.val.bodd d.flip d
| (@dihedral.s 4 i) d := cond i.val.bodd d d.flip

lemma bodd_mod4 (i : ℕ) : (i % 4).bodd = i.bodd := 
begin 
  have : nat.bodd 4 = ff := rfl,
  rw[← congr_arg nat.bodd (nat.mod_add_div i 4), 
     nat.bodd_add, nat.bodd_mul, this, ff_band, bxor_ff ]
end

lemma bodd_add (i j : zmod 4) : (i + j).val.bodd = 
  bxor i.val.bodd j.val.bodd := 
by { rw [← nat.bodd_add, zmod.add_val], exact bodd_mod4 (i.val + j.val) }

lemma bodd_sub (i j : zmod 4) : (i - j).val.bodd = 
  bxor i.val.bodd j.val.bodd := 
begin
  have := bodd_add (i - j) j, 
  rw [sub_add_cancel] at this, 
  have := congr_fun (congr_arg bxor this) j.val.bodd,
  rw [bool.bxor_assoc, bxor_self, bxor_ff] at this,
  exact this.symm
end

instance : mul_action (dihedral 4) dim := {
  smul := smul₀, 
  one_smul := λ ⟨_,_⟩, rfl,
  mul_smul := λ g h d, 
  begin
    cases d with a b,
    cases g with i i; cases h with j j;
    simp only [smul₀, bodd_add, bodd_sub,
               dihedral.rr_mul, dihedral.rs_mul, 
               dihedral.sr_mul, dihedral.ss_mul];
    cases i.val.bodd; cases j.val.bodd; 
    simp only [bxor, cond, flip_flip]; split; refl
  end
}

end dim

@[derive decidable_eq]
structure box :=
(i j k l : fin N.succ) (hik : i ≤ k) (hjl : j ≤ l) 

namespace box 

variable {N}

@[ext] lemma ext (x y : box N) : 
  x.i = y.i → x.j = y.j → x.k = y.k → x.l = y.l → x = y := 
by { cases x, cases y, simp only [], rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩, cc }

def bottom_left : (box N) → (square_grid N)
| ⟨i,j,k,l,_,_⟩ := ⟨i,j⟩ 

def bottom_right : (box N) → (square_grid N)
| ⟨i,j,k,l,_,_⟩ := ⟨k,j⟩ 

def top_left : (box N) → (square_grid N)
| ⟨i,j,k,l,_,_⟩ := ⟨i,l⟩ 

def top_right : (box N) → (square_grid N)
| ⟨i,j,k,l,_,_⟩ := ⟨k,l⟩ 

def size : (box N) → dim
| ⟨i,j,k,l,_,_⟩ := ⟨k - i, l - j⟩

def r : self_map (box N) 
| ⟨i,j,k,l,hik,hjl⟩ := 
  ⟨l.reflect, i, j.reflect, k, fin.reflect_le hjl, hik⟩

def s : self_map (box N) 
| ⟨i,j,k,l,hik,hjl⟩ := 
   ⟨i,l.reflect,k,j.reflect,hik, fin.reflect_le hjl⟩

variable (N)

def p : dihedral.prehom 4 (self_map (box N)) := 
begin 
  have hc : ((4 : ℕ+) : ℕ) = 4 := rfl,
  have hp : (r ^ 4 : self_map (box N)) = r * r * r * r := 
    by simp only [pow_succ, pow_zero, mul_assoc, mul_one],
  refine_struct {
    r := r, s := s
  }; 
  ext x; cases x with i j k l h₀ h₁;
  simp only [hc, hp, self_map.mul_app, self_map.one_app,
             r, s, fin.reflect_reflect],
end 

instance : mul_action (dihedral 4) (box N) := 
  self_map.mul_action_of_hom (p N).to_hom

lemma smul_r₀ (x : box N) : 
  (@dihedral.r 4 0) • x = x := rfl 

lemma smul_r₁ (x : box N) : 
  (@dihedral.r 4 1) • x = 
    box.mk x.l.reflect x.i x.j.reflect x.k 
          (fin.reflect_le x.hjl) x.hik :=
by { cases x, refl }

lemma smul_r₂ (x : box N) : 
  (@dihedral.r 4 2) • x = 
    box.mk x.k.reflect x.l.reflect x.i.reflect x.j.reflect 
          (fin.reflect_le x.hik) (fin.reflect_le x.hjl) :=
by { cases x, refl }

lemma smul_r₃ (x : box N) : 
  (@dihedral.r 4 3) • x = 
    box.mk x.j x.k.reflect x.l x.i.reflect
          x.hjl (fin.reflect_le x.hik) :=
by { change (r * (r * r)) _ = _, cases x, 
     simp only [self_map.mul_app, r, fin.reflect_reflect], cc }

lemma smul_s₀ (x : box N) : 
  (@dihedral.s 4 0) • x = 
    box.mk x.i x.l.reflect x.k x.j.reflect
           x.hik (fin.reflect_le x.hjl) := 
by { cases x, refl }

lemma smul_s₁ (x : box N) : 
  (@dihedral.s 4 1) • x = 
    box.mk x.j x.i x.l x.k x.hjl x.hik := 
by { change (r * s) _ = _, cases x, 
     simp only [self_map.mul_app, r, s, fin.reflect_reflect], cc }

lemma smul_s₂ (x : box N) : 
  (@dihedral.s 4 2) • x = 
    box.mk x.k.reflect x.j x.i.reflect x.l 
           (fin.reflect_le x.hik) x.hjl := 
by { change (r * r * s) _ = _, cases x, 
     simp only [self_map.mul_app, r, s, fin.reflect_reflect], cc }

lemma smul_s₃ (x : box N) : 
  (@dihedral.s 4 3) • x = 
    box.mk x.l.reflect x.k.reflect x.j.reflect x.i.reflect
          (fin.reflect_le x.hjl) (fin.reflect_le x.hik) := 
by { change (r * r * r * s) _ = _, cases x, 
     simp only [self_map.mul_app, r, s, fin.reflect_reflect], cc }

def to_subset : ∀ (x : box N), subsets N
| ⟨i,j,k,l,hik,hjl⟩ := sorry

end box

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

end square_grid
end combinatorics