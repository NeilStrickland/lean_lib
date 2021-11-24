import algebra.ring group_theory.subgroup.basic tactic.ring data.finsupp

variables (A : ℤ → Type*) [∀ n, add_comm_group (A n)]

def tot := Σ (n : ℤ), A n

variable {A}

def deg : tot A → ℤ := λ x, x.1

variable (A)

class dga' := 
(mul : tot A → tot A → tot A)
(deg_mul : ∀ a b, deg (mul a b) = deg a + deg b)
(mul_comm : ∀ a b, mul a b = mul b a)

instance LZ : dga' (λ (n : ℤ), ℤ) := 
{ mul := λ a b, ⟨a.1 + b.1, a.2 * b.2⟩,
  deg_mul := λ a b, rfl,
  mul_comm := λ a b, 
  begin
    have h : ∀ {u v : tot (λ (n : ℤ), ℤ)}, u = v ↔ u.1 = v.1 ∧ u.2 = v.2 := 
    λ u v, begin
      split,
      {intro huv, rw[huv], split; refl},
      {rcases u with ⟨i,a⟩,
       rcases v with ⟨j,b⟩,
       change i = j ∧ a = b → _,
       intro hh, rw[hh.1,hh.2] }
    end,
    apply h.mpr,
    split,
    exact add_comm a.1 b.1,
    exact mul_comm a.2 b.2,
  end

}