/-
 This file shows how to use Lean to perform various kinds of 
 calculations.  The primary purpose of Lean is to deal with proofs,
 but nonetheless these calculations serve as a gentle introduction
 to some aspects of the system.

 All comments in this file assume that you have opened it in the
 VS Code editor with the Lean extension installed, and that Lean
 and mathlib are also installed in appropriate places.

 When you first open this file, you may see orange bars in the 
 left margin, indicating that Lean is thinking about things.  
 This can take some time, especially if this is the first time you
 have run Lean.  You should wait for the orange bars to go away 
 before you try to do anything.

 Next, Lean's output will appear in the Lean messages window, which 
 is not shown by default when VS Code initially starts.  You should
 enter Ctrl+Shift+Enter to make the window appear. (Alternatively, 
 you can type Ctrl+Shift+Alt+Enter to give a similar window with 
 slightly different behaviour.)  There are also icons that one can
 click at the top right of the window in which this file is shown.

 To see the result of any of the #eval statements below, just place
 your cursor anywhere in the relevant line; then the result will be
 shown in the Lean messages window.
-/

import data.nat.prime
import data.rat 

-- Some basic calculations with natural numbers
#eval 2 + 2
#eval 2^10 - 10^3
#eval ((3 + 7 + 10) * (1000 - 8)) / 992 - 17

/-
 Warning: Lean evaluates 5 - 7 as zero. 

 Explanation: in Lean and similar systems, natural numbers are separate
 from integers.  Under some circumstances Lean will interconvert silently
 between the two types.  There are systematic rules for when this does or
 does not happen, but they are not always what one might expect before 
 one is familiar with the general conceptual framework.  

 Here Lean is interpreting 5 and 7 as natural numbers, and interpreting
 the minus sign as referring to the operation of truncated subtraction 
 of natural numbers, which is defined so that `n - m = 0` if `m ≥ n`.

 On the other hand, if we type `(5 - 7 : int)` then Lean will understand
 that we want an integer answer.  Working from the outside in, it will
 first deduce that the minus sign should refer to integer subtraction,
 and then that the operands 5 and 7 should be interpreted as integers.

 The primary name for the type of integers is `int`, but `ℤ` is also 
 defined to be an alias for `int`.  To enter `ℤ` one can type `\int` 
 followed by a space, and then the `\int` will magically turn into `ℤ`.
 It also works to type `\Z` rather than `\int`.  If you see a symbol 
 such as this in a Lean file, you can get help on how to enter it by 
 simply hovering over it with your mouse.
-/

#eval 5 - 7
#eval (5 - 7 : ℤ)

/-
 Similarly, Lean interprets `5 / 7` as truncated division of natural 
 numbers, but `(5 / 7 : ℚ)` gives a rational number.
-/
#eval (5 / 7)
#eval (5 / 7 : ℚ) 

/-
 Note that `x / 0` is defined to be zero.  This is less harmful, and
 makes less difference, than you might think.  The alternatives would
 be as follows:
 (a) You could set things up so that `x / y` is only defined if `y ≠ 0`.
     In more detail, the division function would have three arguments:
     the numerator, the denominator, and a proof that the denominator
     is nonzero.
 (b) You could define `x / y` to lie in `ℚ ∪ {∞}`, and make some 
     arbitrary decision about how to define `0 / 0`.  
 Either way, to do anything serious you will need to have lots of code
 passing around proofs that various denominators are nonzero.  It has
 been found that the bookwork is minimized by making division a total
 operation so that all divisions are defined, and then one can worry 
 about the denominators later.
-/
#eval (5 / 0 : ℚ)

/-
 Notation for five factorial is `nat.fact 5`.  Alternatively, we 
 could enter `open nat` and then `fact 5` would work instead of
 `nat.fact 5`.  However, `5!` is not recognised.  (It would be
 perfectly possible to tell Lean to interpret this notation, but
 the mathlib library does not do so.)

 All of this relies on the fact that we have loaded the file
 data/nat/basic.lean from the mathlib library, where the factorial
 function is defined.  You can see this definition by holding the 
 Ctrl key and clicking on the word `fact`.  We did not explicitly
 load this file, but we did have `import data.nat.prime` at the
 top of this file, which loads the file data/nat/prime.lean, and
 that in turn loads various other files, including 
 data/nat/basic.lean.
-/
#eval (nat.fact 5)

/-
 We can also evaluate logical expressions.  For example, `5 < 7`
 evaluates to the boolean value `tt`, which means true, whereas 
 `7 < 5` evaluates to `ff`, which means false.  For this to work
 we need to append `: bool` to tell Lean to evaluate to a boolean
 value rather than just a proposition.  We will not explore the
 difference between propositions and booleans here, but you should
 at least be aware that the difference exists.
-/
#eval (5 < 7 : bool)
#eval (7 < 5 : bool)

/-
 Here we define a proposition P, using the keyword `def` to
 indicate a definition.  (Various other keywords can be used in 
 various circumstances, notably `let` and `have`.  We will not 
 explain the detailed rules here except to note that `let` 
 cannot be used in this context.  Roughly speaking, we use 
 `let` for local definitions inside proofs, but `def` for 
 top-level definitions that stand on their own.)

 Note that quantified statements in Lean always need a comma
 after the quantifier.
-/
def P : Prop := (∀ n : ℕ, n = 0)

/-
 The following line is commented out because it is invalid.

 If you remove the initial -- then you should see an error
 message as follows:

   failed to synthesize type class instance for
   ⊢ decidable P

 This means that Lean cannot convert the proposition P to a 
 boolean value.  It is easy to write a proof that P is false,
 but Lean's evaluator cannot do that in a completely automatic
  way.
-/
-- #eval (P : bool)

/-
 The function `nat.prime` determines whether or not a natural number
 is prime.
-/
#eval (nat.prime 10 : bool)
#eval (nat.prime 11 : bool)

/-
 The first line below prints the actual definition of `nat.prime`,
 which is easy to understand and more-or-less self-contained.  
 However, the bare definition does not immediately give Lean a way
 to calculate whether a given natural number is prime or not.  For
 that, we need the function `nat.decidable_prime`.  The second line
 below prints the definition of that function, but the definition is
 in terms of other non-obvious functions and so is not immediately
 illuminating.  Above, when we asked Lean to convert `nat.prime 10`
 to a boolean value, it actually used `nat.decidable_prime` to do 
 so.  You might ask how Lean knew that `nat.decidable_prime` was an
 appropriate function to use.  The explanation involves the
 machinery of type classes (in particular, the `decidable` type
 class for propositions) and instances.  Details will not be 
 discussed here.
-/
#print nat.prime
#print nat.decidable_prime

/-
 Lists are one of the most basic types in Lean.  Here we define
 `l` to be a certain list of natural numbers.
-/
def l := [10,11,12,13,14,15]

/-
 Unlike the `#eval` command, the `#check` command only reports
 the type of `l`, not its value.
-/
#check l

/- 
 The next two lines are synonymous.  They both apply the function
 `list.length` to `l` and return `6`.  Roughly speaking, if `x`
 is of type `foo` and `foo.f` is a function that can be applied to
 terms of type `foo` then `x.f` is an alternative notation for 
 `foo.f x` (but the full story involves some extra complications).
 This alternative notation can be very convenient, especially if
 `foo` is replaced by a long, compound name.  Part of the reason 
 is that terms using the alternative notation often need fewer
 parentheses.
-/
#eval list.length l
#eval l.length

/-
 Here `λ n, n^2` is notation for the squaring function `ℕ → ℕ`,
 and `list.map (λ n, n^2) l` applies this function to every 
 element in the list `l`.  We could also have written 
 `l.map (λ n, n^2)`.
-/
#eval (list.map (λ n, n^2) l)

/-
 This function returns the list obtained from `l` by retaining
 the prime entries and discarding the non-prime ones.
-/
#eval l.filter nat.prime

/-
 This reverses the order of the list `l`.
-/
#eval (l.reverse)

/-
 This returns `tt` because 15 appears as an entry in `l`.
-/
#eval (15 ∈ l : bool)

/-
 We now define two finite subsets of natural numbers.  Note that 
 finite subsets in Lean are separate from general subsets, and
 both are different from types.  There are various constructions
 that convert these three things to each other, and Lean will
 silently apply such functions in many cases where you might 
 need this, but not in all cases.  
-/
def s : finset ℕ := {11,22,33}
def t : finset ℕ := {11,111,1111}

/-
 We can enter the union and intersection operators by typing 
 `\cup` or `\cap`.  The notation `finset.card u` or `u.card`
 gives the cardinality of `u`.
-/
#eval s ∪ t
#eval (s ∩ t).card 


variables {i n : ℕ} (h : i < n)
variables {m : ℕ} (e : n = m)

#check @eq.rec_on
#reduce (eq.rec_on e (fin.mk i h) : fin m).val