import logic.relation

namespace relation

open relation 

lemma refl_trans_gen_symm (α : Type*) (r : α → α → Prop) (r_symm : symmetric r)  
 {a b : α} (h : refl_trans_gen r a b) : (refl_trans_gen r b a) := 
  @refl_trans_gen.trans_induction_on α r (λ x y _, refl_trans_gen r y x)
   a b h
   (λ x, refl_trans_gen.refl)
   (λ x y h,refl_trans_gen.single (r_symm h))
   (λ x y z hxy hyz hyx hzy, refl_trans_gen.trans hzy hyx)

end relation