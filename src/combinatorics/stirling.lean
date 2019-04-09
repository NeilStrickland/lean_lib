import algebra.big_operators

namespace partition.number

def stirling1 : ∀ (n r : ℕ), ℕ 
| 0 0 := 1
| 0 (r + 1) := 0
| (n + 1) 0 := 0
| (n + 1) (r + 1) := (stirling1 n r) + (stirling1 n (r + 1)) * n

def stirling2 : ∀ (n r : ℕ), ℕ 
| 0 0 := 1
| 0 (r + 1) := 0
| (n + 1) 0 := 0
| (n + 1) (r + 1) := (stirling2 n r) + (stirling2 n (r + 1)) * (r + 1)

def bell (n : ℕ) : ℕ := 
 list.sum ((list.range n.succ).map (stirling2 n))

end partition.number