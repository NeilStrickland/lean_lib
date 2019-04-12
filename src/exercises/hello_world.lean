theorem one_plus_one : 1 + 1 ≤ 2 :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line states a theorem.  Note that we need a colon between the
name of the theorem, and a := between the statement and the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin 
 refl,
end 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This is the body of the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

theorem one_plus_one_alt : 1 + 1 = 2 := rfl
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 The above proof was written in tactic mode, as indicated by
 the keywords `begin` and `end`.  This mode is most appropriate 
 for long proofs with complex logical flow and many local 
 definitions, which is of course not the case here.  It would 
 be more efficient to use term mode, as shown here.
 Note that the previous proof uses the word `refl`, which is
 the name of a proof tactic.  The current proof uses the word 
 `rfl`, which is the name of the fact that `x = x` for all `x`.
 The word `rfl` counts as a proof here, because we can just
 unwind the definitions of `1`, `2` and `+` and then the two
 sides of our equation become identical.  The proof tactic 
 called `refl` just applies the fact called `rfl` together with
 some similar facts (such as the fact that `n ≤ n` for all
 natural numbers `n`).
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/



