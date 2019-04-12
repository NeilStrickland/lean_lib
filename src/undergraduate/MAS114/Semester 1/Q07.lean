import data.set

namespace MAS114
namespace exercises_1
namespace Q07

local attribute [instance] classical.prop_decidable

lemma L1 (U : Type) (A B : set U) : - (A ∪ B) = (- A) ∩ (- B) :=
 by { simp }

lemma L2 (U : Type) (A B : set U) : - (A ∩ B) = (- A) ∪ (- B) := 
begin
 ext x,
 rw[set.mem_union,set.mem_compl_iff,set.mem_compl_iff,set.mem_compl_iff],
 by_cases hA : (x ∈ A); by_cases hB : (x ∈ B); simp[hA,hB], 
end

end Q07

end exercises_1
end MAS114