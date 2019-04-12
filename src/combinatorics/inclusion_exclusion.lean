import data.fintype algebra.big_operators

/-
 Prove the inclusion-exclusion principle
-/

def card_sign {I : Type*} (J : finset I) : ℤ := (-1) ^ J.card

/- Key lemma -/

lemma alt_count (I : Type*) [fintype I] :
 (@finset.univ (finset I) _).sum (card_sign : finset I → ℤ) = 
  ite (fintype.card I = 0) (1 : ℤ) (0 : ℤ) := sorry


