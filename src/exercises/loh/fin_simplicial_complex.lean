import tactic
import data.set data.set.finite data.finset data.fintype.basic

structure fin_simplicial_complex := mk ::
(vertices : Type*)
(de : decidable_eq vertices := by apply_instance)
(ft : fintype vertices := by apply_instance)
(simplices : finset (finset vertices))
(nonempty : ∀ {σ : (finset vertices)}, σ ∈ simplices → finset.nonempty σ)
(singleton : ∀ v : vertices, {v} ∈ simplices)
(downwards : ∀ {σ τ : (finset vertices)}, σ ∈ simplices → τ ⊆ σ → τ.nonempty → τ ∈ simplices)

namespace fin_simplicial_complex

variable {K : fin_simplicial_complex}

instance : decidable_eq K.vertices := K.de
instance : fintype K.vertices := K.ft

lemma nonempty' : ¬ ((∅ : finset K.vertices) ∈ K.simplices) := λ h, 
  finset.not_nonempty_empty (K.nonempty h)

def singleton_simplex (v : K.vertices) : K.simplices := 
  ⟨{v}, K.singleton v⟩ 

def empty : fin_simplicial_complex := {
  vertices := empty,
  de := by apply_instance,
  ft := by apply_instance,
  simplices := ∅,
  nonempty := λ σ h, (set.not_mem_empty σ h).elim,
  singleton := λ v, empty.elim v,
  downwards := λ σ τ hσ hτσ hτ, (set.not_mem_empty σ hσ).elim
}

def singleton_emb (V : Type*) : V ↪ finset V := {
  to_fun := λ v, {v},
  inj' := λ a b h, finset.singleton_inj.mp h,
}

#check tactic.hint
def discrete (V : Type*) [decidable_eq V] [fintype V] : fin_simplicial_complex := {
  vertices := V,
  de := by apply_instance,
  ft := by apply_instance,
  simplices := (finset.univ : finset V).map (singleton_emb V),
  nonempty := λ σ h, begin
    rw[finset.mem_map] at h, rcases h with ⟨v, v_in_univ, rfl⟩, 
    use v, exact finset.mem_singleton_self v
  end,
  singleton := λ v, begin rw[finset.mem_map], exact ⟨v, finset.mem_univ v,rfl⟩ end,
  downwards := λ σ τ hσ hτσ hτ, begin
    rw[finset.mem_map] at hσ ⊢,
    rcases hσ with ⟨v, v_in_univ, rfl⟩,
    rcases finset.subset_singleton_iff.mp hτσ with (rfl|rfl),
    { exfalso, exact finset.not_nonempty_empty hτ },
    { exact ⟨v, finset.mem_univ v, rfl⟩ }
  end
}

def indiscrete (V : Type*) [decidable_eq V] [fintype V] : fin_simplicial_complex := {
  vertices := V,
  de := by apply_instance,
  ft := by apply_instance,
  simplices := finset.univ.filter (λ σ, σ ≠ ∅),
  nonempty := λ σ h, by { rw[finset.mem_filter] at h, exact finset.nonempty_of_ne_empty h.2 },
  singleton := λ v, by { rw[finset.mem_filter, ← finset.nonempty_iff_ne_empty], 
    exact ⟨finset.mem_univ {v}, finset.singleton_nonempty v⟩ 
  },
  downwards := λ σ τ hσ hτσ hτ, by { 
    rw[finset.mem_filter], rw[finset.nonempty_iff_ne_empty] at hτ,
    exact ⟨finset.mem_univ τ, hτ⟩ 
  }
}

def indiscrete_simplex {V : Type*} [decidable_eq V] [fintype V]
   {σ : finset V} (h : σ ≠ ∅) : simplices (indiscrete V) := 
⟨σ, by { dsimp[indiscrete], rw[finset.mem_filter], exact ⟨finset.mem_univ σ, h⟩ }⟩ 

def standard (n : ℕ) : fin_simplicial_complex := indiscrete (fin n.succ)

def standard_simplex {n : ℕ} 
   {σ : finset (fin n.succ)} (h : σ ≠ ∅ ): simplices (standard n) := 
  indiscrete_simplex h

def top_standard_simplex (n : ℕ) := 
  @standard_simplex n finset.univ (λ h, by {
    have h' := finset.mem_univ (0 : fin n.succ),
    rw[h] at h', exact finset.not_mem_empty _ h'
  })

def sphere (n : ℕ) : fin_simplicial_complex := {
  vertices := fin (n + 2),
  de := by apply_instance,
  ft := by apply_instance,
  simplices := finset.univ.filter (λ σ, σ ≠ ∅ ∧ σ ≠ finset.univ),
  nonempty := λ σ h, by { rw[finset.mem_filter] at h, exact finset.nonempty_of_ne_empty h.2.1 },
  singleton := λ v, by { rw[finset.mem_filter, ← finset.nonempty_iff_ne_empty],
    split, exact finset.mem_univ {v},
    split, exact finset.singleton_nonempty v,
    intro h,
    by_cases h' : v = 0,
    { have := finset.mem_univ (1 : fin (n + 2)), 
      rw[← h, h', finset.mem_singleton] at this,
      cases this },
    { have := finset.mem_univ (0 : fin (n + 2)), 
      rw[← h, finset.mem_singleton] at this,
      exact h' (eq.symm this)
    }
  },
  downwards := λ σ τ hσ hτσ hτ, by { 
    rw[finset.mem_filter] at hσ ⊢, rw[finset.nonempty_iff_ne_empty] at hτ,
    split, exact finset.mem_univ τ,
    split, exact hτ,
    rintro rfl, apply hσ.2.2, 
    exact subset_antisymm (finset.subset_univ σ) hτσ
  }  
}

def of_generators {V : Type*} [decidable_eq V] [fintype V] 
  (S : finset (finset V)) : fin_simplicial_complex := {
  vertices := V,
  de := by apply_instance,
  ft := by apply_instance,
  simplices := finset.univ.filter (λ σ, σ ≠ ∅ ∧ 
    (σ.card ≤ 1 ∨ ∃ τ, τ ∈ S ∧ σ ⊆ τ)
  ),
  nonempty := λ σ h, by { 
    rw[finset.mem_filter] at h, 
    exact finset.nonempty_of_ne_empty h.2.1 
  },
  singleton := λ v, by {
    rw[finset.mem_filter],
    split, exact finset.mem_univ {v},
    split, rw[← finset.nonempty_iff_ne_empty], exact finset.singleton_nonempty v,
    left, exact le_refl _
  },
  downwards := λ σ τ hσ hτσ hτ, by { 
    rw[finset.mem_filter] at hσ ⊢,
    split, exact finset.mem_univ τ,
    split, rw[← finset.nonempty_iff_ne_empty], exact hτ,
    rcases hσ with ⟨hu,hn,hc|⟨ρ,hρS,hσρ⟩⟩,
    { left, exact le_trans (finset.card_le_of_subset hτσ) hc },
    { right, exact ⟨ρ, hρS, finset.subset.trans hτσ hσρ⟩} 
  }
}

def of_fin_generators (n : ℕ) (S : finset (finset (fin n))) : fin_simplicial_complex :=
  of_generators S 

def dim (σ : K.simplices) : ℕ := (σ : finset K.vertices).card.pred

lemma simplex_card (σ : K.simplices) : 
   (σ : finset K.vertices).card = fin_simplicial_complex.dim σ + 1 := 
begin
  rcases σ with ⟨σ, hσ⟩,
  symmetry,
  apply nat.succ_pred_eq_of_pos, apply nat.pos_of_ne_zero,
  change σ.card ≠ 0,
  intro h,
  rw[finset.card_eq_zero.mp h] at hσ,
  exact fin_simplicial_complex.nonempty' hσ
end

@[derive decidable]
def subdim (K : fin_simplicial_complex) (n : ℕ) := 
  ∀ (σ : K.simplices), fin_simplicial_complex.dim σ ≤ n

@[derive decidable]
def supdim (K : fin_simplicial_complex) (n : ℕ) := 
  ∃ (σ : K.simplices), fin_simplicial_complex.dim σ ≥ n

@[derive decidable]
def dimeq (K : fin_simplicial_complex) (n : ℕ) := 
  subdim K n ∧ supdim K n

lemma dim_standard (n : ℕ) : dimeq (standard n) n := 
begin
  split,
  { rintro ⟨σ : finset (fin n.succ),hσ⟩, change σ.card.pred ≤ n,
    have := finset.card_le_univ σ,
    rw[fintype.card_fin, ← nat.pred_le_iff] at this,
    exact this
  }, {
    use top_standard_simplex n,
    change finset.univ.card.pred ≥ n,
    rw[finset.card_univ], 
    change (fintype.card (fin n.succ)).pred ≥ n,
    rw[fintype.card_fin, nat.pred_succ],
    exact le_refl n
  }
end

structure hom (K L : fin_simplicial_complex) := mk ::
(to_fun : K.vertices → L.vertices)
(map_simplex : ∀ {σ : finset K.vertices} (h : σ ∈ K.simplices), σ.image to_fun ∈ L.simplices)

namespace hom 

def to_fun' {K L : fin_simplicial_complex} (f : hom K L) : K.simplices → L.simplices := 
  λ σ, ⟨(σ : finset K.vertices).image f.to_fun, f.map_simplex σ.property⟩

def id (K : fin_simplicial_complex) : hom K K := {
  to_fun := id,
  map_simplex := λ σ h, by { rw[finset.image_id], exact h }
}

lemma id' (K : fin_simplicial_complex) : (id K).to_fun' = (_root_.id : K.simplices → K.simplices) :=
begin
  funext σ, rcases σ with ⟨σ,h⟩, ext1,
  change σ.image _root_.id = σ, rw[finset.image_id]
end

def comp {K L M : fin_simplicial_complex} (g : hom L M) (f : hom K L) : hom K M := {
  to_fun := g.to_fun ∘ f.to_fun,
  map_simplex := λ σ h,
  begin 
    rw[← finset.image_image],
    exact g.map_simplex (f.map_simplex h)
  end
}

def comp' {K L M : fin_simplicial_complex} (g : hom L M) (f : hom K L) : 
  (comp g f).to_fun' = g.to_fun' ∘ f.to_fun' := 
begin
  funext σ, rcases σ with ⟨σ,h⟩, ext1,
  rw[function.comp],
  change σ.image (g.to_fun ∘ f.to_fun) = (σ.image f.to_fun).image g.to_fun,
  rw[finset.image_image]
end

def const (K : fin_simplicial_complex) {L : fin_simplicial_complex} (w : L.vertices) : hom K L := {
  to_fun := function.const K.vertices w,
  map_simplex := λ σ h, by {
    rw[finset.image_const (K.nonempty h) w], exact L.singleton w
  }
}

lemma const' (K : fin_simplicial_complex) {L : fin_simplicial_complex} (w : L.vertices) :
  (const K w).to_fun' = function.const K.simplices (fin_simplicial_complex.singleton_simplex w) := 
begin
  funext σ, rcases σ with ⟨σ, h⟩, ext1,
  change σ.image (function.const _ w) = {w},
  rw[finset.image_const (K.nonempty h) w]
end

end hom

namespace examples

def cylinder := of_fin_generators 6 {
  {0,1,4},{0,3,4},{1,2,5},{1,4,5},{2,3,0},{2,5,3}
}

def mobius_strip := of_fin_generators 6 {
  {0,1,4},{0,3,4},{1,2,5},{1,4,5},{2,3,0},{2,5,0}
}

def octahedron := of_fin_generators 6 {
  {0,1,4},{0,1,5},{0,3,4},{0,3,5},{1,2,4},{1,2,5},{2,3,4},{2,3,5}
}

def torus := of_fin_generators 9 {
  {0, 1, 4}, {0, 3, 4}, {1, 2, 5}, {1, 4, 5}, {2, 0, 3}, {2, 5, 3},
  {3, 4, 7}, {3, 6, 7}, {4, 5, 8}, {4, 7, 8}, {5, 3, 6}, {5, 8, 6},
  {6, 7, 1}, {6, 0, 1}, {7, 8, 2}, {7, 1, 2}, {8, 6, 0}, {8, 2, 0}
}

def klein_bottle := of_fin_generators 9 {
  {0, 1, 4}, {0, 3, 4}, {1, 2, 5}, {1, 4, 5}, {2, 0, 6}, {2, 5, 6},
  {3, 4, 7}, {3, 6, 7}, {4, 5, 8}, {4, 7, 8}, {5, 3, 6}, {5, 8, 3},
  {6, 7, 1}, {6, 0, 1}, {7, 8, 2}, {7, 1, 2}, {8, 3, 0}, {8, 2, 0}
}

def projective_plane  := of_fin_generators 9 {
  {0, 1, 5}, {0, 4, 5}, {1, 2, 6}, {1, 5, 6}, {2, 3, 6}, {3, 6, 7},
  {4, 5, 8}, {4, 7, 8}, {5, 6, 9}, {5, 8, 9}, {6, 7, 4}, {6, 4, 9},
  {7, 8, 2}, {7, 3, 2}, {8, 9, 1}, {8, 2, 1}, {9, 4, 0}, {9, 1, 0}
}

end examples
end fin_simplicial_complex




