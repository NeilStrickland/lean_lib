import algebra.ring group_theory.subgroup.basic tactic.ring data.finsupp

variables (A : ℤ → Type*) [∀ n, add_comm_group (A n)]

def tp {n m : ℤ} (h : n = m) : A n →+ A m := {
  to_fun := (congr_arg A h).mp,
  map_zero' := by { cases h, refl },
  map_add' := by { cases h, intros, refl }
}

class dga := 
(one : A 0)
(mul : ∀ {i j : ℤ}, (A i) → (A j) → A (i + j))
(diff : ∀ {i : ℤ}, A i →+ A (i - 1))
(mul_one : ∀ {i : ℤ} (a : A i), mul a one = tp A (add_zero i).symm a)
(one_mul : ∀ {i : ℤ} (a : A i), mul one a = tp A (zero_add i).symm a)
(mul_assoc : ∀ {i j k : ℤ} (a : A i) (b : A j) (c : A k), 
  mul (mul a b) c = tp A (add_assoc i j k).symm (mul a (mul b c)))
(mul_zero : ∀ {i j : ℤ} (a : A i), mul a (0 : (A j)) = 0)
(zero_mul : ∀ {i j : ℤ} (b : A j), mul (0 : (A i)) b = 0)
(mul_add  : ∀ {i j : ℤ} (a : A i) (b c : A j), mul a (b + c) = (mul a b) + (mul a c))
(add_mul  : ∀ {i j : ℤ} (a b : A i) (c : A j), mul (a + b) c = (mul a c) + (mul b c))
(diff_mul : ∀ {i j : ℤ} (a : A i) (b : A j), 
  diff (mul a b) = tp A (by ring) (mul (diff a) b) + 
                   tp A (by ring) (mul a (diff b)))
(diff_diff : ∀ {i : ℤ} (a : A i), diff (diff a) = 0)

variable [dga A]

variable {A}

def dga.diff' {n : ℤ} : A (n + 1) →+ A n := 
 (tp A (by ring_nf)).comp (@dga.diff A _ _ (n + 1))

variable (A)

def cycles (n : ℤ) := (dga.diff : A n →+ A (n - 1)).ker

def boundaries (n : ℤ) := (dga.diff' : A (n + 1) →+ A n).range

def diff_as_cycle {n : ℤ} (a : A n) : cycles A (n - 1) :=
 ⟨dga.diff a,dga.diff.mem_ker.mpr (dga.diff_diff a)⟩

-- def boundaries (n : ℤ) := { a : A n | ∃ }

class grading (B : Type*) [add_comm_group B] := 
(parts : B → finsupp ℤ B)
(parts_parts : ∀ (b : B) (i j : ℤ), i ≠ j → parts (parts b i) j = 0)
(sum_parts : ∀ (b : B), (parts b).sum (λ n x, x) = b)

def tot := Σ (n : ℤ), A n

variable {A}

def deg : tot A → ℤ := λ x, x.1

variable (A)

class dga' := 
(mul : tot A → tot A → tot A)
(deg_mul : ∀ a b, deg (mul a b) = deg a + deg b)
(mul_comm : ∀ a b, mul a b = mul b a)

