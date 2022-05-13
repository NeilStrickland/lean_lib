/- -/

import analysis.normed.group.hom

class homogeneous_semi_normed_group (E : Type*) extends semi_normed_group E :=
(is_homogeneous : ∀ (n : ℤ) (x : E), ∥ n • x ∥ = (abs n) * ∥ x ∥)






