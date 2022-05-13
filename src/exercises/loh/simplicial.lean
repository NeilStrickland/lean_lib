import tactic
import data.set data.set.finite data.finset

structure simplicial_complex := mk ::
(vertices : Type*)
(deceq : decidable_eq vertices)
(simplices : set (finset vertices))
(nonempty : ∀ {σ : (finset vertices)}, σ ∈ simplices → finset.nonempty σ)
(singleton : ∀ v : vertices, {v} ∈ simplices)
(downwards : ∀ {σ τ : (finset vertices)}, σ ∈ simplices → τ ⊆ σ → τ.nonempty → τ ∈ simplices)

namespace simplicial_complex

variable {K : simplicial_complex}

instance : decidable_eq K.vertices := K.deceq

lemma nonempty' : ¬ ((∅ : finset K.vertices) ∈ K.simplices) := λ h, 
  finset.not_nonempty_empty (K.nonempty h)

def singleton_simplex (v : K.vertices) : K.simplices := 
  ⟨{v}, K.singleton v⟩ 

def empty : simplicial_complex := {
  vertices := empty,
  deceq := by apply_instance,
  simplices := ∅,
  nonempty := λ σ h, (set.not_mem_empty σ h).elim,
  singleton := λ v, empty.elim v,
  downwards := λ σ τ hσ hτσ hτ, (set.not_mem_empty σ hσ).elim
}

def discrete (V : Type*) [decidable_eq V] : simplicial_complex := {
  vertices := V,
  deceq := by apply_instance,
  simplices := (set.univ : set V).image (λ (v : V), {v}),
  nonempty := λ σ h, begin
    rw[set.mem_image] at h, rcases h with ⟨v, v_in_univ, rfl⟩,
    use v, exact finset.mem_singleton_self v
  end,
  singleton := λ v, ⟨v,set.mem_univ v,rfl⟩,
  downwards := λ σ τ hσ hτσ hτ, begin
    rw[set.mem_image] at hσ ⊢,
    rcases hσ with ⟨v, v_in_univ, rfl⟩,
    rcases finset.subset_singleton_iff.mp hτσ with (rfl|rfl),
    { exfalso, exact finset.not_nonempty_empty hτ },
    { exact ⟨v, set.mem_univ v, rfl⟩ }
  end
}

def indiscrete (V : Type*) [decidable_eq V] : simplicial_complex := {
  vertices := V,
  deceq := by apply_instance,
  simplices := { σ : finset V | σ.nonempty },
  nonempty := λ σ h, h,
  singleton := λ v, finset.singleton_nonempty v,
  downwards := λ σ τ hσ hτσ hτ, hτ 
}

def standard (n : ℕ) : simplicial_complex := indiscrete (fin n.succ)

def dim (σ : K.simplices) : ℕ := (σ : finset K.vertices).card.pred

lemma simplex_card (σ : K.simplices) : 
   (σ : finset K.vertices).card = simplicial_complex.dim σ + 1 := 
begin
  rcases σ with ⟨σ, hσ⟩,
  symmetry,
  apply nat.succ_pred_eq_of_pos, apply nat.pos_of_ne_zero,
  change σ.card ≠ 0,
  intro h,
  rw[finset.card_eq_zero.mp h] at hσ,
  exact simplicial_complex.nonempty' hσ
end

def subdim (K : simplicial_complex) (n : ℕ) := 
  ∀ (σ : K.simplices), simplicial_complex.dim σ ≤ n

def supdim (K : simplicial_complex) (n : ℕ) := 
  ∃ (σ : K.simplices), simplicial_complex.dim σ ≥ n

def dimeq (K : simplicial_complex) (n : ℕ) := 
  subdim K n ∧ supdim K n

lemma dim_standard (n : ℕ) : dimeq (standard n) n := 
begin
  split,
  { rintro ⟨σ : finset (fin n.succ),hσ⟩, change σ.card.pred ≤ n,
    have := finset.card_le_univ σ,
    rw[fintype.card_fin, ← nat.pred_le_iff] at this,
    exact this
  }, {
    let σ : { s : finset (fin n.succ) | s.nonempty } := 
      ⟨finset.univ, ⟨0, finset.mem_univ 0⟩⟩,
    use σ,
    change finset.univ.card.pred ≥ n,
    rw[finset.card_univ], 
    change (fintype.card (fin n.succ)).pred ≥ n,
    rw[fintype.card_fin, nat.pred_succ],
    exact le_refl n
  }
end

structure hom (K L : simplicial_complex) := mk ::
(to_fun : K.vertices → L.vertices)
(map_simplex : ∀ {σ : finset K.vertices} (h : σ ∈ K.simplices), σ.image to_fun ∈ L.simplices)

namespace hom 

def to_fun' {K L : simplicial_complex} (f : hom K L) : K.simplices → L.simplices := 
  λ σ, ⟨(σ : finset K.vertices).image f.to_fun, f.map_simplex σ.property⟩

def id (K : simplicial_complex) : hom K K := {
  to_fun := id,
  map_simplex := λ σ h, by { rw[finset.image_id], exact h }
}

lemma id' (K : simplicial_complex) : (id K).to_fun' = (_root_.id : K.simplices → K.simplices) :=
begin
  funext σ, rcases σ with ⟨σ,h⟩, ext1,
  change σ.image _root_.id = σ, rw[finset.image_id]
end

def comp {K L M : simplicial_complex} (g : hom L M) (f : hom K L) : hom K M := {
  to_fun := g.to_fun ∘ f.to_fun,
  map_simplex := λ σ h,
  begin 
    rw[← finset.image_image],
    exact g.map_simplex (f.map_simplex h)
  end
}

def comp' {K L M : simplicial_complex} (g : hom L M) (f : hom K L) : 
  (comp g f).to_fun' = g.to_fun' ∘ f.to_fun' := 
begin
  funext σ, rcases σ with ⟨σ,h⟩, ext1,
  rw[function.comp],
  change σ.image (g.to_fun ∘ f.to_fun) = (σ.image f.to_fun).image g.to_fun,
  rw[finset.image_image]
end

def const (K : simplicial_complex) {L : simplicial_complex} (w : L.vertices) : hom K L := {
  to_fun := function.const K.vertices w,
  map_simplex := λ σ h, by {
    rw[finset.image_const (K.nonempty h) w], exact L.singleton w
  }
}

lemma const' (K : simplicial_complex) {L : simplicial_complex} (w : L.vertices) :
  (const K w).to_fun' = function.const K.simplices (simplicial_complex.singleton_simplex w) := 
begin
  funext σ, rcases σ with ⟨σ, h⟩, ext1,
  change σ.image (function.const _ w) = {w},
  rw[finset.image_const (K.nonempty h) w]
end

end hom

end simplicial_complex