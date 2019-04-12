import data.finset

namespace MAS114
namespace exercises_1
namespace Q06

def A : finset ℕ := [1,2,4].to_finset
def B : finset ℕ := [2,3,5].to_finset
def C : finset ℕ := [1,2,3,4,5].to_finset
def D : finset ℕ := [2].to_finset
def E : finset ℕ := [3,4].to_finset

lemma L1 : A ∪ B = C := dec_trivial
lemma L2 : A ∩ B = D := dec_trivial 
lemma L3 : D ∩ E = ∅ := dec_trivial 

end Q06
end exercises_1
end MAS114