import data.int.basic
import tactic.ring

namespace MAS114
namespace exercises_1
namespace Q09

def even (n : ℤ) := ∃ k : ℤ, n = 2 * k

def odd (n : ℤ) := ∃ k : ℤ, n = 2 * k + 1

lemma L1 (n : ℤ) : even n → even (n ^ 2) := 
begin
 rintro ⟨k,e⟩,
 use n * k,
 rw[e,pow_two],ring,
end

lemma L2 (n m : ℤ) : even n → even m → even (n + m) := 
begin
 rintros ⟨k,ek⟩ ⟨l,el⟩,
 use k + l,
 rw[ek,el],
 ring,
end

lemma L3 (n m : ℤ) : odd n → odd m → odd (n * m) := 
begin
 rintros ⟨k,ek⟩ ⟨l,el⟩,
 use k + l + 2 * k * l,
 rw[ek,el],
 ring,
end

/- Do the converses -/

end Q09
end exercises_1
end MAS114