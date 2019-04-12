import data.int.basic tactic.ring

namespace MAS114
namespace exercises_1
namespace Q18

variables (a b c d : ℤ)

lemma L_i : a ∣ b → b ∣ c → a ∣ c := 
begin
 rintros ⟨uab,hab⟩ ⟨ubc,hbc⟩,
 use uab * ubc,
 rw[← mul_assoc,← hab,← hbc],
end

lemma L_ii : a ∣ b → a ∣ c → a ∣ (b + c) := 
begin
 rintros ⟨uab,hab⟩ ⟨uac,hac⟩,
 use uab + uac,
 rw[mul_add,hab,hac],
end

lemma L_iii_false : ¬ (∀ a b c : ℤ, (a ∣ (b + c)) → (a ∣ b) ∧ (a ∣ c)) := 
begin
 intro h0,
 have h1 : (2 : ℤ) ∣ 1 := (h0 2 1 1 dec_trivial).left,
 have h2 : ¬ ((2 : ℤ) ∣ 1) := dec_trivial,
 exact h2 h1,
end

lemma L_iv : a ∣ b → a ∣ c → a ∣ (b * c) := 
begin
 rintros ⟨uab,hab⟩ ⟨uac,hac⟩,
 use uab * c,
 rw[← mul_assoc,hab]
end

lemma L_v_false : ¬ (∀ a b c : ℤ, (a ∣ (b * c)) → (a ∣ b) ∧ (a ∣ c)) := 
begin
 intro h0,
 have h1 : (4 : ℤ) ∣ 2 := (h0 4 2 2 dec_trivial).left,
 have h2 : ¬ ((4 : ℤ) ∣ 2) := dec_trivial,
 exact h2 h1,
end

lemma L_vi : a ∣ b → c ∣ d → (a * c) ∣ (b * d) := 
begin
 rintros ⟨uab,hab⟩ ⟨ucd,hcd⟩,
 use uab * ucd,
 rw[hab,hcd],
 ring
end

end Q18
end exercises_1
end MAS114