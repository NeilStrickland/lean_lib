/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This is about the Stirling numbers (of the first and second kinds)
and the Bell numbers, which arise in various places in combinatorics.

The file combinatorics/partition/fin_map.lean contains the basic 
theorems about the combinatorial interpretation of `stirling2` and
`bell`.  We have not yet proved anything about `stirling1`.
-/

import algebra.big_operators.basic

namespace partition.number

/- https://en.wikipedia.org/wiki/Stirling_numbers_of_the_first_kind
   https://oeis.org/A008275 

   OEIS defines a signed integer s(n,r); our (stirling 1 n r) is 
   OEIS's |s(n,r)|.  The command below gives an initial segment
   of the list of values as given by OEIS.

   #eval (list.Ico 1 7).bind (λ n, (list.Ico 1 (n + 1)).map (stirling1 n))
-/
def stirling1 : ∀ (n r : ℕ), ℕ 
| 0 0 := 1
| 0 (r + 1) := 0
| (n + 1) 0 := 0
| (n + 1) (r + 1) := (stirling1 n r) + (stirling1 n (r + 1)) * n


/- https://en.wikipedia.org/wiki/Stirling_numbers_of_the_second_kind
   https://oeis.org/A008277 

   Our (stirling2 n r) is OEIS's S2(n,r).  The command below gives 
   an initial segment of the list of values as given by OEIS. 

   #eval (list.Ico 1 7).bind (λ n, (list.Ico 1 (n + 1)).map (stirling2 n))
-/
def stirling2 : ∀ (n r : ℕ), ℕ 
| 0 0 := 1
| 0 (r + 1) := 0
| (n + 1) 0 := 0
| (n + 1) (r + 1) := (stirling2 n r) + (stirling2 n (r + 1)) * (r + 1)


/- https://en.wikipedia.org/wiki/Bell_number
   https://oeis.org/A000110

   #eval (list.range 5).map bell
-/
def bell (n : ℕ) : ℕ := 
 list.sum ((list.range n.succ).map (stirling2 n))


end partition.number