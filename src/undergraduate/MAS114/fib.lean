import tactic.norm_num

def FP_step' : ℕ × ℕ → ℕ × ℕ := 
 λ ⟨a,b⟩, ⟨b,(a + b) % 89⟩ 

def FP_step : ℕ × ℕ → ℕ × ℕ := 
 λ c, ⟨c.snd,(c.fst + c.snd) % 89⟩ 

def FP : ℕ → ℕ × ℕ 
| 0 := ⟨0,1⟩ 
| (n + 1) := FP_step (FP n)

def F (n : ℕ) : ℕ := (FP n).fst

#eval F 25

lemma L : F 25 = 87 := by { unfold F FP FP_step; norm_num }