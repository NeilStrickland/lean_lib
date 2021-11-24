import data.nat.prime

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We will use basic definitions about primes and divisibility taken from the mathlib
 library.  The home page of the library is
 <a href="https://github.com/leanprover/mathlib">https://github.com/leanprover/mathlib</a>
 and you can browse and search the source code there.  If you set things up in a standard
 way, you should have a copy of the library in more or less the same place as your own
 Lean files, with directory structure like this:
 <ul>
  <li><span class="path">.git</span>: a director that we can ignore. </li>
  <li><span class="path">.gitignore</span>,
      <span class="path">leanpkg.path</span>,
      <span class="path">leanpkg.toml</span>: files that we can ignore</li>
  <li>_target
   <ul>
    <li>deps
     <ul>
      <li>mathlib
       <ul>
        <li>Subdirectories algebra, analysis, category, computability, data, ....
         These contain uncompiled, human-readable files with extension .lean,
	 and also compiled files with extension .olean.
        </li>
       </ul>
      </li>
     </ul> 
    </li>
   </ul>
  </li>
  <li>src
   <ul>
    <li>Your own Lean files, such as the one shown here.</li>
   </ul>
  </li>
 </ul>
 <br/><br/>
 The line `import data.nat.prime` allows us to use definitions
 and results from the file <span class="mathlib">data/nat/prime.lean</span>.  For
 example, that file proves that $2$ is prime, and gives the name
 `prime_two` to that fact.  (However, see the comment on the next line.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
open nat
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  The file <span class="mathlib">data/nat/prime.lean</span> proves
  a number of facts.  For example, it proves that $2$
  is prime, and gives the name `prime_two` to that fact.
  However, the same file also says `namespace nat` near the top.
  Because of this, the full name of the relevant theorem is really
  `nat.prime_two`.  The line `open nat`
  in the current file allows us to drop the `nat` prefix.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma larger_prime : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  This line states the result that we want to prove, and attaches the name
  `larger_prime` to the result.
  <ul>
    <li>There are various symbols that do not appear on your keyboard.  These
    can usually be entered in Visual Studio Code using LaTeX syntax.  For example,
    you can type `\forall` followed by a space, and the
    `\forall` will automatically turn into into
    `∀`.  For `ℕ`, `ℤ`, `ℚ` and `ℝ` one can enter `\nat`, `\int`, `\rat` and `\real`.
    Alternatively, one can enter `\N`, `\Z`, `\Q` and `\R`.
   </li>
   <li>To indicate that $n$ is in $ℕ$ we write `n : ℕ`
    rather than `n ∈ ℕ`, following the conventions of type
    theory rather than set theory.
   </li>
   <li>The expression `prime p` refers to the definition of primality
    taken from the file <span class="mathlib">data/nat/prime.lean</span>.
    That definition essentially gives a function from natural numbers to
    truth values.  To apply that function to the argument $p$, we write `prime p`
    (following the conventions of Lisp-like programming languages) rather than
    `prime(p)` as in traditional functional notation.  Note that if we
    had not had the line `open nat`, we would have had to say
    `nat.prime p` instead of `prime p`.  If you did not already know
    where to find the definition of primality, you could enter "prime"
    in the search boxes at
    <a href="https://github.com/leanprover/mathlib">github.com/leanprover/mathlib</a> 
    and
    <a href="https://github.com/leanprover/mathlib">github.com/leanprover/lean</a>. 
   </li>
   <li>Note the commas associated with the quantifiers, and the
    `:=` at the end of the line.  If you have this file
    open in Visual Studio Code, and you take out the first comma, then you should
    see three error messages in the Lean messages window.  (If you do not see the
    relevant window, you should press CTRL-SHIFT-ENTER, or click the
    <img src="../../images/left_msg_icon.png"/> icon near the top of the screen.)
    None of those error messages is optimal, but
    <span class="error">unknown identifier 'n'</span> gives some indication of
    the location of the problem.  On the other hand, if you leave out the
    <span class="error">:=</span> then the error messages are completely opaque.
   </li>
  </ul>
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  This marks the beginning of the proof.  For some simple kinds of proofs
  it is not necessary to have a `begin ... end` wrapper.  For some
  complicated proofs there will be nested `begin ... end` blocks to
  prove various intermediate claims that arise in the course of the proof.
  <br/><br/>
  Inside the `begin ... end` block, we enter
  "tactic mode", as discussed in Chapter 5 of the book
  <a href="https://leanprover.github.io/theorem_proving_in_lean/">Theorem
  Proving in Lean</a>.  (References to "Chapter n" or "Section p.q" below
  will always refer to this book.)  This can be explained as follows.  A
  Lean proof is a kind of complex data structure.  Outside of tactic mode,
  we can construct a proof by programming methods, in which we explicitly
  apply various functions to simpler structures that we have already defined.
  Inside tactic mode, we can construct proofs by a kind of dialogue with
  the proof assistant, which is much more similar to a traditional
  writer's imagined dialogue with the reader.
  <br/><br/>
  If you have this file open in Visual Studio Code, and you click at the
  end of the word `begin`, you should see a message like this in the
  Lean messages window:
  <div class="lean_messages">
   ⊢ ∀ (n : ℕ), ∃ (p : ℕ), prime p ∧ p > n
  </div>
  This states our current proof goal.  (If you do not see the relevant
  window, you should press CTRL-SHIFT-ENTER, or click the
  <img src="../../images/left_msg_icon.png"/> icon near the top of the
  screen.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 intro n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We are aiming to prove a statement that is universally quantified over the
  natural numbers.  In traditional writing, we would start by saying "let $n$
  be an arbitrary natural number", or some similar phrase.  The line
  `intro n,` plays a similar role in Lean.
  <br/><br/>
  If you click on the end of this line in VS Code, you will see that the tactic
  state has changed to 
  <div class="lean_messages">
    n : ℕ
    ⊢ ∃ (p : ℕ), prime p ∧ p > n
  </div>
  This means, essentially, that we are working in a context where we have a given
  natural number $n$, and we aim to prove that there is a prime $p$ with $p>n$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let m := factorial n + 1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  We now define $m$ to be $n!+1$.  Again note the terminating comma.  The tactic
  state changes to
  <div class="lean_messages">
   n : ℕ,
   m : ℕ := factorial n + 1
   ⊢ ∃ (p : ℕ), prime p ∧ p > n
  </div>
  incorporating the definition of $m$ in the context.
  <br/><br/>
  In VS Code you can hover over the word `fact` with your mouse to see
  that the full name is `nat.fact` and that the type is `ℕ → ℕ`, and
  there is also a comment explaining that `fact` is the factorial
  function.  If you hold the CTRL key while hovering, you will see the
  actual recursive definition of the function.  If you hold the CTRL
  key and click, then you will jump to the file where that definition
  appears.  Alternatively, you can right-click and then type F12 or
  Alt-F12.  For this particular definition, the relevant file is <span
  class="mathlib">data/nat/basic.lean</span>.  Note that we did not
  explicitly import `data.nat.basic`, but we imported
  `data.nat.prime`, which imports `data.nat.sqrt`, which imports
  `data.nat.basic`.  Some standard properties of factorials are proved
  in the same place.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let p := min_fac m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 This line defines $p$ using the function `min_fac` defined in <span
 class="mathlib">data/nat/basic.lean</span>.  This is supposed to be
 defined by the requirement that `min_fac k` is the smallest $d>1$
 such that $d$ divides $k$.  This makes sense for $k=0$ (with
 `min_fac 0 = 2`) and for $k>1$, but this characterisation would leave
 `min_fac 1` undefined.  The approach taken by the Lean library is to
 arbitrarily define `min_fac 1 = 1`.  This of course means that some
 theorems about the properties of `min_fac` will need auxiliary
 hypotheses.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 use p,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove that there exists a number with certain 
properties.  The tactic `use p` converts this to the goal of proving
that the specific number `p` has those properties.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_prime : prime p,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove `prime p ∧ p > n`.  The most obvious thing to do
next would be to split this into two goals: the proof that `p` is 
prime, and the proof that `p > n`.  However, it is convenient to use
the fact that `p` is prime as part of the proof that `p > n`, and the
obvious structure would not allow for that.  We need to attach a name
to the claim that `p` is prime, then prove it, then return to the 
main goal.
<br/><br/>
The effect of the current line is to add `prime p` as a new current
goal, with `prime p ∧ p > n` retained as a secondary goal to be 
addressed later.  The current line also ensures that the name `p_prime` 
will be attached to our proof that `p` is prime, once we have provided
it.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 {
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We open a set of curly brackets in which to deal with the first goal
(of proving that `p` is prime).  This is not strictly necessary: we
could just give a sequence of tactics, and Lean would apply them to
the first goal until that goal was solved, and then apply any 
subsequent tactics to the second goal.  However, it is usually clearer
to use brackets.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  apply min_fac_prime,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now apply the theorem named `min_fac_prime` from
 <span class="mathlib">data/nat/prime.lean</span>.
 <br/><br/>
 Recall that `min_fac n` was arbitrarily defined to be $1$ when $n=1$,
 so the theorem that `min_fac n` is prime is only valid with the side
 condition that $n\neq 1$.  (In more detail, the theorem 
 `min_fac_prime` is stated as 
 <div class="code">
  ∀ {n : ℕ}, n ≠ 1 → prime (min_fac n),
 </div>
 so it is essentially a function that takes as input a natural number
 $n$ together with a proof that $n\neq 1$, and produces a proof that
 `min_fac n` is prime.  The `apply` tactic works out that the relevant
 value of `n` is $m = n!+1$, so it replaces the goal of proving that 
 $p$ is prime by the goal of proving that $n!+1≠1$.  Unfortunately we
 will need to supply a few fiddly details to achieve this goal.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
apply ne_of_gt,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
First, we apply the theorem `ne_of_gt`, which says that 
`a > b → a ≠ b`.  The `apply` tactic works out which values of `a` and
`b` are relevant (this process is called "unification").  Also, the
theorem is valid for any type with a preorder, and the `apply` tactic
knows that by default it should use the standard order on `ℕ`; this
is handled using the mechanism of typeclass instances as described in
<span class="tpil">Chapter 10</span>.  Thus, the goal changes to 
proving that $n!+1>1$.
<br/><br/>
The name `ne_of_gt` illustrates the standard naming conventions for 
the mathlib library: the string `ne` indicates the conclusion `a ≠ b`, 
the string `gt` indicates the hypothesis `a > b`, and the string 
`_of_` indicates an implication.  This is designed to work well with
auto-completion in VS Code: you know you want to prove a statement of 
the form `a ≠ b`, so you can start typing `apply ne_of_...` and Lean 
will suggest things that might be helpful.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
apply succ_lt_succ,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now apply the theorem `succ_lt_succ`, which says that
`i < j → (i + 1) < (j + 1)`; this converts the goal to $0<n!$.  
Here `lt` stands for "less than", and `succ` refers to the successor 
operation $a\mapsto a+1$.  As in Peano arithmetic, addition is 
actually defined in terms of the successor operation rather than the 
other way around.  The hypothesis of this theorem is easy to guess, 
so the name is just based on the conclusion.
<br/><br/>
You might think that we would instead need a theorem saying 
`i > j → (i + 1) > (j + 1)` instead, and this would presumably be
called `succ_gt_succ`.  However, Lean defines `a > b` to mean `b < a`,
and it applies this transformation quite eagerly.  Theorems are 
generally written with hypotheses and conclusions in the form `b < a`,
and Lean applies any required translations automatically.  There is
not in fact a theorem named `succ_gt_succ`, but we do not need one.
<br/><br/>
Note also that the `apply` tactic has unfolded the definition 
$m:=n!+1$ in order to see that `succ_lt_succ` is applicable.  We 
could have helped with this by writing `dsimp [m],` before 
`apply succ_lt_succ`; this would have changed the goal to say 
explicitly that `(factorial n) + 1 > 1`.  This kind of help is sometimes
necessary, but not in this particular case.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
apply factorial_pos,
},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The theorem `fact_pos` says that $k! > 0$ for all $k$, so we can apply 
it to solve the current goal.  We have added a comma after `fact_pos`
just to persuade Lean to give an explicit message saying "no goals".
This message is potentially misleading; we still need to prove that
$p > n$, but that goal is hidden while we are inside the curly 
brackets that enclose the proof that $p$ is prime.  If we move the 
cursor outside those curly brackets, then the goal $p > n$ becomes
visible again.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove `prime p ∧ p > n`.  The tactic `split` converts 
this into two goals, namely `prime p` and `p > n`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 {assumption},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The current goal is to prove that `p` is prime.  The context already
contains a term (named `p_prime`) that `p` is prime, so we can just
use the `assumption` tactic to complete the proof.  We have placed this
in curly brackets to separate it from the proof of the other goal 
(that `p > n`) but this is not strictly necessary.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
{
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now open a second pair of curly brackets, within which we will 
prove that $p > n$.  Again, these brackets are not strictly necessary,
but they help to make the structure of the proof visible.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 apply lt_of_not_ge,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove that `p > n`, which Lean converts automatically 
to `n < p`.  The theorem `lt_of_not_ge` converts this goal to 
`¬ n ≥ p`.  As with the theorem `ne_of_gt` mentioned previously, 
 this conversion rule is not proved
 directly for `ℕ`.  Instead, the standard library defines the standard
 order on `ℕ` and proves that it is a linear order, using a definition
 for which the above rule is not an axiom; instead, it is proved as a
 simple lemma valid for any type equipped with a linear order.  When
 we invoke `lt_of_not_ge` here, Lean needs to remember that we have
 given `ℕ` a linear order that it should use by default unless we say
 otherwise.  This is handled by the mechanism of typeclass instances,
 as described in <span class="tpil">Chapter 10</span>.  (In fact, this
 same mechanism is also used to interpret expressions such as
 `n + m`: the symbol `+` has different meanings in different places,
 and typeclasses are used to supply the relevant definition in any
 given context.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  intro p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 It is part of the basic logical framework of Lean that a proof of 
 `¬ n ≥ p` is the same as a procedure that takes a hypothetical proof 
 of `n ≥ p` (or equivalently `p ≤ n`) and produces a contradiction, or 
 in other words a proof of the proposition `false`.
 <br/><br/> 
 The current line means: "let `p_le_n` be a hypothetical proof that
 $p\leq n$".  The meaning of the assumption is forced by the nature
 of the goal.  By contrast, the name of the assumption is arbitrary; 
 we have chosen to call it `p_le_n` to indicate its meaning, but we
 could equally well have written `intro foo,` instead.  In fact, we
 could just have written `intro`, and then Lean would choose an 
 arbitrary name.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_gt_0 : p > 0, {apply min_fac_pos},
-- (b) have p_gt_0 : p > 0, exact min_fac_pos m,
-- (c) have p_gt_0 : p > 0 := min_fac_pos m,
-- (d) have p_gt_0 : p > 0 := min_fac_pos _,
-- (e) have p_gt_0 :=  min_fac_pos m,
-- (f) have p_gt_0 : p > 0 := by {apply min_fac_pos},
-- (g) let p_gt_0 :=  min_fac_pos m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now state that $p>0$, attach the name `p_gt_0` to this claim, and
 prove it by applying the theorem named `min_fac_pos` from
 <span class="mathlib">data/nat/prime.lean</span>.  In more detail, 
 the phrase `have p_gt_0 : p > 0,` adds `p > 0` as a new goal, and
 the phrase `{apply min_fac_pos},` gives a proof; the new goal 
 therefore disappears, and the context gains a term named `p_gt_0`
 of type `p > 0`.
 <br/><br/>
 The following five lines all start with a double dash; this converts
 them to comments which are ignored by Lean.  In each case we could 
 remove the double dash and the initial label to get a line of Lean 
 code which would have the same effect as the current line.
 <br/><br/>
 Version (b) uses the `exact` tactic instead of `apply`.  After 
 `exact` we must supply a term that represents a proof of `p > 0`.
 We can again use `min_fac_pos` for this, except that we now need to 
 supply the argument `m`.  Versions (c) to (g) all involve a ":=", 
 and on the right hand side of that symbol we must work in term mode 
 by default, rather than using tactics.  Thus, version (c) is 
 essentially the same as (b).   In this situation we have to supply
 something as an argument to `min_fac_pos`, but we are allowed to 
 write the symbol `_`, which instructs Lean to work out what is 
 required; this is version (d).  Lean can only do this because it
 knows that `p_gt_0` is supposed to have type `p > 0`.  We can leave
 out that type annotation as in version (e), but in that case we need
 to give the argument explicitly.  In version (f) we use the 
 construct `by { ... }` to switch back into tactic mode.  Version
 (g) illustrates the fact that `have` is essentially a synonym for
 `let`; it is standard to use `have` for propositions and `let` for
 other types, but this is not enforced.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have d0 : p ∣ factorial n := dvd_factorial p_gt_0 p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now prove that $p$ divides $n!$.  The proof appeals to the fact
 (named `dvd_fact`) that $a$ divides $b!$ whenever $a>0$ and
 $a\leq b$.  We supply the explicit arguments `p_gt_0` and `p_le_n` to
 verify the hypotheses; the implicit arguments $p$ and $n$ are deduced
 from the context.
 <br/><br/>
 One needs to be careful about the symbol for divisibility.  If you
 just type `|` then you will get a tall vertical bar, which is used
 by Lean for syntax related to pattern matching, and which does not
 relate to divisibility.  If you type `\|` you will get a shorter 
 vertical bar, which is the one that you need.  Alternatively, one
 could write `has_dvd.dvd a b` instead of `a ∣ b`.  (The full 
 explanation for this slightly awkward syntax involves typeclasses;
 we will not give details here.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have d1 : p ∣ factorial n + 1 := min_fac_dvd m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now claim that $p$ divides $m=n! + 1$.  As $p$ was defined to be
 `min_fac m`, this amounts to the claim that the `min_fac` function
 was correctly defined.  This was proved in `prime.lean` under the
 name `min_fac_dvd`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have d : p ∣ 1 := (nat.dvd_add_iff_right d0).mpr d1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 We now want to prove that `p` divides `1`.  For this, we appeal 
 to the fact that if $a$ divides $b$, then $a$ divides $c$ iff $a$ 
 divides $b+c$.  This fact has the name `dvd_add_iff_right`.  
 Unfortunately, there are two versions of this fact that are currently
 visible.  One of them comes from the file
 <span class="library">init/algebra/ring.lean</span>, and applies to
 an arbitrary commutative ring.  The other comes from
 <span class="library">init/data/nat/lemmas.lean</span>, and applies
 only to `ℕ` (which is a semiring rather than a ring).  Note that both
 of these are in the core Lean library, not in mathlib.  We need to
 use the version for `ℕ`, so we need to resolve the ambiguity by
 providing the explicit prefix in `nat.dvd_add_iff_right`.  <br/><br/>
 By applying `nat.dvd_add_iff_right` to `d0`, we obtain a proof that
 $p$ divides $n!+1$ iff $p$ divides $1$.  The syntax `(...).mpr`
 extracts the right-to-left half of this equivalence, which we can
 then apply to the fact `d1` to obtain a proof that $p$ divides $1$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact prime.not_dvd_one p_prime d
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 Our goal is to produce a contradiction, or equivalently to prove the
 proposition `false`.  We do this using the keyword `exact` (which is
 the name of a kind of tautological tactic) followed by an expression
 that evaluates to `false`.  The theorem `prime.not_dvd_one` says that
 no prime divides $1$.  Equivalently, it is a function that accepts a
 proof that a number is prime, together with a proof that that number
 divides $1$, and produces `false`.  We can thus apply
 `prime.not_dvd_one` to the ingredients `p_prime` and `d` to obtain
 the required contradiction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 },
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The proof is now complete.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

#check larger_prime
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Lean accepts correct proofs without explicit acknowledgement.  To
get more positive feedback, we can enter
`#check larger_prime`: this will restate
the fact that we have proved in the message window.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma larger_prime' : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start again and give essentially the same proof in a different 
style.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 intro n,
 let m := factorial n + 1,
 let p := min_fac m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
These lines are the same as before.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have : m ≠ 1 := ne_of_gt (nat.succ_lt_succ (factorial_pos n)),
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here we have a slight variation.  Previously, in every `have` statement
there was a name before the colon, which could be used to refer to the
relevant fact after it had been proved.  Here we omit the name.  On
the next line, we will need to refer back to the fact that `m ≠ 1`, 
but we will just use the keyword `this`, which refers back to the most
recent anonymous `have`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have p_prime : prime p := min_fac_prime this,
 have p_gt_0 : p > 0 := min_fac_pos m,
 have not_p_le_n : ¬ p ≤ n, {
  intro p_le_n,
  have d0 : p ∣ factorial n := dvd_factorial p_gt_0 p_le_n,
  have d1 : p ∣ factorial n + 1 := min_fac_dvd m,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
These lines are much the same as before, but with proof terms instead
of tactics.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have : p ∣ 1 := (nat.dvd_add_iff_right d0).mpr d1,
  exact prime.not_dvd_one p_prime ‹p ∣ 1›
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here is another anonymous `have`.  We could again use the keyword 
`this` to refer to the result, but instead we illustrate another 
possible syntax.  Because the context contains a unique term of type 
`p ∣ 1`, we can use the notation `‹p ∣ 1›` to refer to it.  This 
notation involves "French quotes", which can be entered as \f< and 
\f>. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 },
 have p_gt_n : p > n := lt_of_not_ge not_p_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As before, we use `lt_of_not_ge` to get a proof of `p > n`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact (exists.intro p (and.intro p_prime p_gt_n)),
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The function `and.intro` can be used to combine `p_prime` and `p_gt_n`
into a proof of `prime p ∧ p > n`, then the function `exists.intro`
can be used to generate a proof of `∃ p, prime p ∧ p > n`.  We can 
feed this into the `exact` tactic to finish the proof.
<br/><br/>
Usually we would not write `exists.intro p (and.intro p_prime p_gt_n)`,
but instead would use the terser expression `⟨p,⟨p_prime,p_gt_n⟩⟩`. 
The brackets here are angle brackets, entered as \< and \> or
\langle and \rangle.  With the default fonts, they can be hard to 
distinguish visually from ordinary round brackets, and they are also
different from the French quotes that we used earlier.  Anyway, angle
brackets can be used in many situations to combine terms, provided 
that Lean already knows the expected type of the combination.  Here
we are using the `exact` tactic so the argument must match the type
of the goal `∃ p, prime p ∧ p > n`, and Lean can work everything out 
from this.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma larger_prime'' : ∀ n : ℕ, ∃ p, (prime p) ∧ (p > n) := 
λ n, 
 let m := factorial n + 1 in
 let p := min_fac m in 
 let p_prime :=
  min_fac_prime (ne_of_gt (nat.succ_lt_succ (factorial_pos n))) in
  ⟨p,⟨p_prime,
     (lt_of_not_ge
      (λ p_le_n,
        prime.not_dvd_one
         p_prime
          ((nat.dvd_add_iff_right
            (dvd_factorial p_prime.pos p_le_n)).mpr
              (min_fac_dvd m))))⟩⟩
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Finally, we give a third proof written as a single proof term with no
tactics of any kind.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

