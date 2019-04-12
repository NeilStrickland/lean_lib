import algebra.ring
import algebra.group_power
import ring_theory.ideals
import data.nat.choose
import data.zmod.basic

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We start by importing various things, mostly from the
<span class="path">mathlib</span> library.  Specifically:
<ul>
 <li>We need <span class="mathlib">algebra.ring</span> for some
  background ideas about rings.  Note, however, that this is not where
  the most basic definitions are given.  Instead, they appear in the
  file <span class="library">init/algebra/ring.lean</span> in the
  core Lean library, rather than in mathlib.  Definitions from the core
  library are available even without any `import` statement.
 </li>
 <li>We need <span class="mathlib">algebra.group_power</span> for basic
  facts about the operation $(a,n)\mapsto a^n$.  The framework for this
  is dependent on the apparatus of type classes as discussed in 
  <span class="tpil">Chapter 10</span>.  Various things are proved for
  the power operation in an arbitrary monoid or commutative monoid, and
  type classes are used to encode the fact that any commutative ring
  can be regarded as a monoid under multiplication.
 </li>
 <li>We need <span class="mathlib">ring_theory.ideals</span> for the
  definition of ideals and quotient rings.  Some of this is done as a
  special case of the theory of quotient modules, which is covered
  in <span class="mathlib">linear_algebra/basic.lean</span>.
 </li>
 <li>To prove that the sum of nilpotent elements is again nilpotent,
  we need the binomial theorem, from
  <span class="mathlib">data.nat.choose</span>.
 </li>
 <li>At the bottom of this file we will prove some general facts about
  nilpotent elements of $ℤ/n$, and in particular we will show that 
  $\sqrt{0}=\{0,2\}$ in $ℤ/4$.  To support this, we need to import
  <span class="mathlib">data.zmod.basic</span>.
 </li>
</ul>

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
open nat finset
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line allows us to refer to definitions from the `nat` and
`finset` packages without an explicit prefix of `nat` or `finset`.
<br/><br/>
The package `finset` (for finite sets) is relevant here because the
binomial theorem is formulated in terms of a general theory of indexed
sums over finite indexing sets. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

universe u
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line is part of the framework used by Lean and similar systems to
avoid Russell-type paradoxes.  We want to consider an arbitrary
commutative ring.  Classically we would say that the ring has an
underlying set.  In Lean and similar systems we have types rather
than sets, and each type is associated to a universe, and the Russell
paradox is avoided because the relation $x\not\in x$ cannot be
formulated in a way that is consistent with the rules for universes.
<br/><br/>
It is usually possible to leave Lean to work out for itself what to
say about universes.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

section nilpotents
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line opens a section.  It is closed by the `end nilpotents`
command towards the bottom of the file.  The main point about having a
section will be explained on the next line.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 variable {R : Type u}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line says that $R$ will denote a type in the universe $u$.
Because the declaration is in curly brackets, $R$ will be treated as
an implicit argument, and Lean will deduce the value of $R$ from the
context.  For example, it is part of the foundational framework that
every term has a well-defined type, so if we have any definition that
depends on an element $x$ of $R$, then Lean can tell what $R$ is by
inspecting $x$.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 variable [R_comm_ring : comm_ring R]
 include R_comm_ring
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This means, roughly speaking, "assume that we have a given commutative
 ring structure on $R$, and use the symbol `R_comm_ring` to refer to
 that structure". 
<br/><br/>
In more detail, one should think of `comm_ring R` as denoting the set
of commutative ring structures on $R$.  The definition of
`comm_ring R` appears in the file
<span class="library">init/algebra/ring.lean</span> in the core
Lean library.  There are similar types for other kinds of algebraic
structures, including the type `discrete_field R` of field structures
on $R$. 
<br/><br/>
Taking the rationals as an example, the underlying type `rat` is
defined in <span class="mathlib">data/rat.lean</span> in mathlib, and
$\mathbb{Q}$ is declared as an alternative notation for `rat`.  The
addition, multiplication and negation maps are defined in the same
file, with names like `rat.add`.  The standard properties of these
operations and constants are proved as a long list of theorems, with
names like `rat.mul_assoc` (for the associativity of multiplication).
There is then a block starting 
<br/>
`
 instance : discrete_field ℚ := { zero := 0, add := rat.add, ... }
`
<br/>
which packages everything together as a term of type
`discrete_field ℚ`, or in other words a field structure on
$\mathbb{Q}$.  One does not usually need to refer to this field
structure directly, but if necessary one can do so using the notation
`rat.discrete_field`.  It works out that `rat.discrete_field.add`
and `rat.discrete_field.mul_assoc` are the same as `rat.add` and
`rat.mul_assoc`, for example. 
<br/><br/>
There are mechanisms that allow Lean to obtain a commutative ring
structure automatically from a field structure where necessary,
but the resulting commutative ring structure is anonymous.  It has
been found convenient to include the line
<br/>
`
 instance : comm_ring ℚ          := by apply_instance
`
<br/>
in <span class="mathlib">data/rat.lean</span>, which makes it faster
for Lean to find the commutative ring structure on $\mathbb{Q}$, and
also allows us to use the notation `rat.comm_ring` for that structure.
<br/><br/>
The keyword `instance`, and the tactic `apply_instance`, are part of
the apparatus of type classes, as discussed in
<span class="tpil">Chapter 10</span>.
<br/><br/>
The line
<div class="code">variable [R_comm_ring : comm_ring R]</div>
declares a variable `R_comm_ring` of type `comm_ring R`, or in other
words a commutative ring structure on $R$.  The square brackets
indicate that this variable should be handled by various specialised
mechanisms for type classes.  Because of the way that these mechanisms
work, it is almost never necessary to refer to `R_comm_ring`
explicitly.  It is therefore not really necessary to give this
variable a name; we could instead have just written
<div class="code">variable [comm_ring R]</div>
Indeed, it is more standard Lean style to leave the structure
anonymous.  For technical reasons the line `include R_comm_ring` is
required if we give the ring structure a name, but no such line is
required if we leave it anonymous.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 def next_pow_zero (x : R) (n : ℕ)  := (x ^ (n + 1)) = 0
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Recall that $x$ is nilpotent if there exists $p\in\mathbb{N}$ with
$x^p=0$.  As $x^0$ is $1$ by definition, the case $p=0$ can only occur
if the ring is trivial.  It is therefore convenient to require $p>0$
in the definition (which does not really make any difference at the
end of the day).  Rather than incorporating $p>0$ as a separate
condition, it is convenient to write $p$ as $n+1$ for some
$n\in\mathbb{N}$.  So we will say that $x$ is nilpotent if $x^{n+1}=0$
for some $n\in\mathbb{N}$.
<br/><br/>
We will need to show that if $x$ and $y$ are nilpotent, then so is
$x+y$.  Sometimes one needs the sharper statement that if $x^{n+1}=0$
and $y^{m+1}=0$ then $(x+y)^{n+m+1}=0$, so we will arrange to prove
that first.  
<br/><br/>
We have chosen to give an auxiliary definition to support this,
defining `next_pow_zero x n` to mean that $x^{n+1}=0$.  This does not
really have much benefit in the present situation, but it would
certainly be useful if the definition was somewhat more complicated,
so we do it here as an example of the required mechanisms.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 def is_nilpotent (x : R) : Prop := ∃ n : ℕ, (next_pow_zero x n)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define `is_nilpotent x` to mean that $x$ is nilpotent, building
on the definition of `next_pow_zero` in the obvious way.  Note that a
comma is needed after the quantifier.  We have chosen to write 
`∃ n : ℕ`, but it would also be acceptable to just write `∃ n`,
because the type of $n$ can be inferred from the definition of
`next_pow_zero`.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma npz_zero : next_pow_zero (0 : R) (0 : ℕ) := 
   by {simp[next_pow_zero],}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state and prove that `next_pow_zero 0 0` holds, or in other
words that $0^{0+1}=0$.  The proof just uses a single tactic, so we
can use the keyword `by` with no `begin ... end` block.  We use the
`simp` tactic, which just tries to simplify everything.  In square
brackets we can supply some ingredients to be used by the simplifier.
These ingredients are usually names of theorems, or facts that have
been proved in the current context.  One can also include names of
defined terms, to indicate that the simplifier should apply the
definitions; that is what we are doing here by including
`next_pow_zero`.
<br/><br/>
Throughout the Lean core library and the mathlib library, many results
are annotated with `@[simp]` just before the statement of the result.
This indicates that the simplifier should use the relevant result by
default.
<br/><br/>
Although the `simp` tactic is powerful and convenient, it has some
disadvantages. 
<ul>
 <li>It asks Lean to search through a large body of lemmas, most
  of which are irrelevant in any given context.  This can slow
  things down, especially when compiling a large body of code.
 </li>
 <li>It sometimes leads Lean to apply transformations that are not
  in fact helpful in the relevant context.
 </li>
 <li>If the tactic does not succeed in finishing the proof of the
  current goal, then it will leave us in a state that may be 
  highly sensitive to the set of available `simp` lemmas.  If we rely
  on details of the state when writing subsequent steps of the proof,
  then improvements to the library can cause the proof to fail.
 </li>
</ul>
For these reasons, one may prefer to minimise use of the `simp`
tactic.  If we simply want to replace the left hand side of a known
equation by the right hand side, we can use the `rewrite` or `subst`
tactics.  In more complicated situations, we can use the `simp only`
tactic, which only applies lemmas taken from the list explicitly
provided as an argument to the tactic.
<br/><br/>
We could prove the present result without `simp` using
<div class="code">
 lemma npz_zero : next_pow_zero (0 : R) (0 : ℕ) := pow_one (0 : R)
</div>
or 
<div class="code">
 lemma npz_zero : next_pow_zero (0 : R) (0 : ℕ) := zero_mul 1
</div>
However,
<div class="code">
 lemma npz_zero : next_pow_zero (0 : R) (0 : ℕ) := rfl
</div>
does not work.  We leave it as an exercise to analyse these 
approaches in more detail.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma npz_shift
  {x : R} {n m : ℕ}
   (xR : (next_pow_zero x n)) (Sn_le_m : n + 1 ≤ m) : 
     x ^ m = 0 := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state the lemma that if $x^{n+1}=0$ and $n + 1\leq m$ then
$x^m=0$, and give the name `npz_shift` to this fact.
<br/><br/>
In more detail, `npz_shift` takes as arguments a proof (denoted `xR`)
that `next_pow_zero x n` holds (for some $x\in R$ and
$n\in\mathbb{N}$), and a proof (denoted `Sn_le_m`) that $n+1\leq m$
(for some $n\in\mathbb{N}$).  It produces a proof that $x^m=0$.  
The term `next_pow_zero x n` is of course interpreted using the
implicitly supplied type $R$ and the implicitly supplied ring
structure on $R$.  The arguments $x$, $n$ and $m$ are given in curly
brackets, indicating that they are implicit and should be deduced from 
`xR` and `Sn_le_m`.  If we want to specify these arguments explicitly
for some reason, we can use the notation `@npz_shift x n m xR Sn_le_m`.
<br/><br/>
One might find it more natural to write the inequality as $m\geq n$.
However, Lean and similar systems take the definitions of $a&lt;b$ and
$a\leq b$ as primary, and they convert $a&gt;b$ to $b&lt;a$ and $a\geq b$
to $b\leq a$.  There is a small gain in convenience if we use the
primary form from the start.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 begin
  unfold next_pow_zero at xR,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line applies the definition of `next_pow_zero` to `xR`, to make
it say explicitly that $x^{n+1}=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  rw[← (nat.add_sub_of_le Sn_le_m),_root_.pow_add,xR,zero_mul],
 end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now want to say that $x^m=x^{n+1}x^{m-(n+1)}=0 x^{m-(n+1)}=0$.  The
detailed structure of this argument in Lean is a little different from
what one might expect.  In Lean, natural numbers are not actually a
subset of integers, but are a separate type.  There is a function
called `int.of_nat` that converts natural numbers to integers, and
there is also a long list of lemmas giving properties of this
function.  In many contexts Lean will silently invoke this function
when needed.  However, this function is not just the identity.
<br/><br/>
This now leads us to ask: given natural numbers $p$ and $q$, what is
the type and value of $p-q$?  It is not technically possible for the
type to depend on the values of $p$ and $q$.  It has been found
convenient to use the minus sign to denote truncated subtraction
operation on natural numbers, so that $p-q=0$ when $q≥p$.  (If we need
to refer to integer-valued genuine subtraction, we can instead write
`(int.of_nat p) - (int.of_nat q)` or `(p - q) : ℤ`.)  With this
convention, the expression $x^{p-q}$ is meaningful for all $p$ and
$q$, which would not be true if we allowed $p-q$ to be negative.
However, the relations $q + (p - q) = p$ and $x^qx^{p-q}=x^p$ are only
true if $q≤p$.
<br/><br/>
We have a proof named `Sn_le_m` of $n+1≤m$, and the theorem
`nat.add_sub_of_le` converts this to a proof of $(n+1)+(m-(n+1))=m$.
 By default, Lean uses equations to replace the left hand side by the
right hand side.  Here, however, our goal involves $m$, and we want 
to replace it by $(n+1)+(m-(n+1))$, using our equation from right to
 left.  For this, we need to write  `rw[← (nat.add_sub_of_le Sn_le_m)]`.
(The leftwards arrow can be entered as `\left` or `\l`.)
<br/><br/>
We now want to use the rule $x^{p+q}=x^px^q$.  The general name of
this rule is `pow_add`.  However, there are two variants that are
currently in view.  One is called `nat.pow_add`; it was defined in
<span class="path">data/nat/basic.lean</span> and only applies for
$x\in\mathbb{N}$.  The other is just called `pow_add`; it was defined
in <span class="path">algebra/group_power.lean</span>, and applies in
a much more general framework of abstract algebra.  Because we have
opened the `nat` package, if we just write `pow_add` then we will get
`nat.pow_add`.  To refer to the more general version, we need to write
`_root_.pow_add`.  Note that there is some type class resolution going
on in the background to connect the theorem `_root_.pow_add` to the
axioms for the ring structure on $R$.
<br/><br/>
Finally, we use the fact named `xR` to convert $x^{n+1}x^{m-(n+1)}$ to
$0 x^{m-(n+1)}$, and then the theorem named `zero_mul` to convert this
to zero.  All of the above steps are rewrites, so they can all be
carried out by a single invocation of the `rw` tactic.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma npz_add {x y : R} {n m : ℕ}
  (xR : next_pow_zero x n) (yR : next_pow_zero y m) :
  next_pow_zero (x + y) (n + m) :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state the key fact that if $x^{n+1}=y^{m+1}=0$ then 
$(x+y)^{n+m+1}=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
  unfold next_pow_zero at xR yR ⊢,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We start the proof by unfolding the definition of `next_pow_zero`, in
the hypotheses `xR` and `yR`, and also in the goal that we are
trying to prove (indicated by the symbol `⊢`).
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  let p := n + m + 1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We define $p=n+m+1$ for convenience.  We will use the binomial
expansion of $(x+y)^p$.  This expresses $(x+y)^p$ as a sum of terms.
We will be using a general framework for sums indexed by finite sets,
which comes from
<span class="mathlib">algebra/big_operators.lean</span>.  The
underlying theory of finite sets is from
<span class="mathlib">data/finset.lean</span>.  In particular, that
file defines the set `range n` to be $\{i\in\mathbb{N}:i&lt;n\}$, so
the indexing set for the binomial expansion is `range (succ p)`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  suffices : ∀ (k : ℕ) (h : k ∈ (range (succ p))),
    x ^ k * y ^ (p - k) * ↑(choose p k) = 0,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line claims that it will be sufficient to prove that all terms
in the binomial expansion of $(x+y)^p$ are zero.  The next few lines
will justify this claim of sufficiency, and then we will turn to 
proving that the terms are indeed zero.
<br/><br/>
Note that a generic index is not represented directly as a term of
type `range (succ p)`, but as a term `k : ℕ` together with a proof
(labelled `h`) that `k` lies in `range (succ p)`.  Indeed,
`range (succ p)` is not, strictly speaking, a type at all.  There is
quite a long story about subtle distinctions between types and subsets
and finite subsets; see <a href="../lean_sets.html">here</a> for
some discussion.
<br/><br/>
Note also that `choose p k` is a binomial coefficient, and in
particular is a natural number.  The upward arrow symbol refers to a
"coercion", which converts a natural number to an element of the ring
$R$.  Coercions are discusssed in 
<span class="tpil">Section 6.7</span>
<span class="tpil">Section 10.6</span>.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  { exact calc (x + y)^p
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have formulated a certain proposition $A$ (the vanishing of all 
terms) and claimed that it will suffice to prove our goal (that 
$(x+y)^p=0$).  To justify this, we give a proof of $(x+y)^p=0$
assuming $A$.  The keyword `this` is used to refer to $A$.  The proof
uses the `calc` tactic, which has syntax like
<div class="code">
 calc W = X : M
 ... = Y : N
 ... = Z : P
</div>
where `M` is a proof that `W=X` and `N` is a proof that `X=Y` and `P`
is a proof that `Y=Z`.  Note that there are no commas.
<br/><br/>

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
        = (range (succ p)).sum (λ k, x ^ k * y ^ (p - k) * ↑(choose p k))
        : add_pow x y p 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The first step is the binomial theorem.  In Lean this is called
`add_pow`, and it is proved (for an arbitrary commutative semiring) in
<span class="mathlib">data/nat/choose.lean</span>.
<br/><br/>
Take note of the notation used on the right hand side.  Sums are
defined for a finite set $I$ and a map $u\colon I\to R$.  Here
we use the "lambda calculus" notation
`λ k, x ^ k * y ^ (p - k) * ↑(choose p k)`
for the map $k\mapsto x^ky^{p-k}{p\choose k}$.  The sum can be written
as `I.sum u` or as `finset.sum I u`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
    ... = (range (succ p)).sum (λ k, (0 : R))
        : finset.sum_congr rfl this 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now use the theorem `finset.sum_congr`, which says that
$\sum_Ia_i=\sum_Jb_j$ provided that $I=J$ and $a_i=b_i$ for all $i$.
In our case the two indexing sets are visibly equal, so we can just
supply `rfl` as the first argument.  The fact named `this` shows 
that each binomial term is zero, so we can pass it to
`finset.sum_congr` and conclude that the sum of binomial terms is the
sum of zeros. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
    ... = 0 : sum_const_zero },
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Finally, the theorem `sum_const_zero` says that any sum of zeros is
zero.  This completes our proof of sufficiency.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

  intros k k_in_range,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now turn to the proof that all terms in the binomial expansion are
zero.  An arbitrary term is indexed by a natural number `k` with a
proof (denoted by `k_in_range`) that `k` lies in `range (succ p)`.
<br/><br/>
Note that in various situations Lean might need to generate an
arbitrary name for the fact that `k` lies in `range (succ p)`.  In
particular, if we just wrote `intros` rather than
`intros k k_in_range` then Lean would use the generic name `h` for
this fact.  However, it is better to supply a more expressive name
explicitly.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
have k_lt_Sp : k < p + 1 := mem_range.mp k_in_range,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The theorem `mem_range` says that `k` lies in `range (succ p)` iff
$k &lt; p+1$ (or in other words, that the definition of `range` is
correct).  This is a bidirectional implication; we use the suffix
`.mp` (for <em>modus ponens</em>) to extract the forward implication.
By applying this to `k_in_range`, we obtain a proof that $k&lt;p+1$,
which we call `k_lt_Sp`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
have k_le_p : k ≤ p := le_of_lt_succ k_lt_Sp,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now use the theorem `le_of_lt_succ` to convert the inequality
$k&lt;p+1$ to $k\leq p$.  This is a good example of the naming
conventions used by the Lean libraries: the substring after `_of_`
indicates the hypothesis, and the substring before `_of_` indicates
the conclusion.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
rcases le_or_gt (n + 1) k with Sn_le_k | Sn_gt_k,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now need to distinguish between the cases $k\leq n$ and $k&gt;n$.
For technical reasons it is slightly more convenient to express these
as $n+1&gt; k$ and $n+1\leq k$.  Case splitting can be performed using
the `cases` tactic, or the `rcases` tactic, both of which we mentioned
previously.
<br/><br/>
The way that the `rcases` tactic works here is as follows.  The
theorem `le_or_gt` applied to $k+1$ and $n$ proves that
`((n + 1) ≤ k) ∨ ((n + 1) &gt; k)` holds.  The `rcases` tactic
converts the current goal (of proving that the $k$th binomial term is
zero) into two identical goals with different hypotheses.  In the
first goal, we have the additional hypothesis that `(n + 1) ≤ k`, and
the name `Sn_le_k` is attached to this hypothesis.  In the second
goal, we have the additional hypothesis `(n + 1) &gt; k`, named
`Sn_gt_k`.  The lines below give a proof of the first goal in one set
of curly brackets, and a proof of the second goal in another set of
curly brackets.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
{ have : x ^ k = 0 := npz_shift xR Sn_le_k,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We are now dealing with the case where $(n + 1)\leq k$.  We can
therefore appeal to the lemma `npz_shift` to see that $x^k=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
simp [this],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It now follows by standard simplification rules that
$x^k y^{(p-k)}{p\choose k}$.  (We could have combined this with the
previous step and just written `simp[npz_shift xR Sn_le_k]`.)
<br/><br/>
This completes our discussion of the case $k&gt;n$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
}, { have k_le_n : k ≤ n := lt_succ_iff.mp Sn_gt_k,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We are now dealing with the case where $(n + 1)&gt;k$.  We can convert
this hypothesis to the form $k\leq n$ using the left-to-right half
(indicated by the suffix `.mp`) of the lemma `lt_succ_iff`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
let j := n - k,
have Z1 : k + j = n := add_sub_of_le k_le_n,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define $j$ to be $n - k$.  Recall that the minus sign here
denotes truncated subtraction of natural numbers.  However, because
$k≤n$ we know that the subtraction is not really truncated and so
$k+j=n$.  Just as in the proof of `npz_shift`, we use the theorem
`add_sub_of_le` to prove this fact.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
have Z2 : p - k = (m + 1) + j,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now want to prove that $p-k=(m+1)+j$.  For the sake of example, we
use a slightly different syntax for the proof than in previous steps.
We have no `:=` before the comma, so the claim that $p-k=(m+1)+j$ just
gets added at the beginning of the list of goals, as we can see in the
Lean messages window.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
{ apply nat.sub_eq_of_eq_add,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start to prove the first of our two current goals, namely that
$p-k=(m+1)+j$.  By putting the proof in curly brackets we temporarily
hide the second goal, and make it easier to separate the proofs of the
two goals.  <br/><br/> The lemma `nat.sub_eq_of_eq_add` can be used to
convert a proof of $a=b+c$ (in $\mathbb{N}$) to $a-b=c$.  The `apply`
tactic works backwards from the end, and uses the indicated lemma to
convert the goal $p-k=(m+1)+j$ to $p=k+((m+1)+j)$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
simp [p, Z1.symm]
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The simplifier can now prove the converted goal, with a little help.
We need to tell it to use the definition of $p$ and the equation
$k+j=n$ (named `Z1`) in the backwards direction, together with the
commutativity and associativity of addition that are used by default.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have now proved claim `Z2`, so we can close the curly brackets and
bring the previous goal (of proving that $x^ky^{p-k}{p\choose k}=0$)
back into view.  We could equally well have written the last few lines
in the form
<div class="code">
have Z2 : p - k = (m + 1) + j :=
 begin apply nat.sub_eq_of_eq_add,simp [p, Z1.symm] end,
</div>

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
    have : y ^ (p - k) = 0 := 
     by { rw [Z2, _root_.pow_add, yR, zero_mul] },
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A series of rewrites now proves that $y^{p-k}=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
    simp [this],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It now follows by standard simplification rules that 
$x^k y^{(p-k)}{p\choose k}$.  This completes our discussion of the case
$k\leq n$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 }
end

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
lemma npz_add' {x y : R} {n m : ℕ}
  (xR : next_pow_zero x n) (yR : next_pow_zero y m) :
  next_pow_zero (x + y) (n + m) :=
begin
  unfold next_pow_zero at xR yR ⊢,
  let p := n + m + 1,
  suffices : ∀ (k : ℕ) (h : k ∈ (range (succ p))),
    x ^ k * y ^ (p - k) * ↑(choose p k) = 0,
  { exact ((add_pow x y p).trans
       (finset.sum_congr rfl this)).trans sum_const_zero,},
  intros k k_in_range,
  have k_lt_Sp : k < p + 1 := mem_range.mp k_in_range,
  have k_le_p : k ≤ p := le_of_lt_succ k_lt_Sp,
  rcases le_or_gt (n + 1) k with Sn_le_k | Sn_gt_k,
  { rw[npz_shift xR Sn_le_k,zero_mul,zero_mul],},
  { let j := n - k,
    let e0 : p = (m + n) + 1 :=
     congr_fun (congr_arg nat.add (nat.add_comm n m)) 1,
    let e1 : (m + n) + 1 = (m + 1) + n :=
       ((nat.add_assoc m n 1).trans
         (congr_arg (nat.add m) (nat.add_comm n 1))).trans
        (nat.add_assoc m 1 n).symm,
    let e2 : n = j + k :=
       (add_sub_of_le (lt_succ_iff.mp Sn_gt_k)).symm.trans
          (nat.add_comm k j),
    let e3 : (m + 1) + n = (m + 1 + j) + k :=
     (congr_arg (nat.add (m + 1)) e2).trans
       (nat.add_assoc (m + 1) j k).symm,
    let e4 : p = k + (m + 1 + j) :=
     (e0.trans (e1.trans e3)).trans (nat.add_comm (m + 1 + j) k),
    let e5 : p - k = m + 1 + j := nat.sub_eq_of_eq_add e4,
    let e6 : y ^ (p - k) = y^(m + 1) * y^j :=
     (congr_arg (pow y) e5).trans (_root_.pow_add y (m + 1) j),
    let e7 : y^(p - k) = 0 := e6.trans
     ((congr_fun (congr_arg R_comm_ring.mul yR) (y ^ j)).trans
        (zero_mul (y ^ j))),
    let e8 : x^k * y^(p - k) = 0 := 
     (congr_arg (@comm_ring.mul R R_comm_ring (x ^ k)) e7).trans
        (mul_zero (x ^ k)),
    let e9 : x^k * y^(p - k) * ↑(choose p k)  = 0 :=
     (congr_fun (congr_arg R_comm_ring.mul e8) ↑(choose p k)).trans
       (zero_mul ↑(choose p k)),
    exact e9,
 }
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now prove the same result again, writing the main step of the proof
in a different style.  This is just intended to illuminate what is done
by the `simp` tactic and other tactics.  The key point is construct
`e9`, which is a proof that $x^k y^{p-k} {p \choose k}=0$.  As a minor
concession to readability we have broken this down into steps `e0` to
`e8`, but one could condense everything down into a single term by
replacing `e8` by its definition when defining `e9`, and so on.  The
resulting term is similar to the one constructed in the background by
the previous tactic proof.  The main ingredients are as follows:
<ul>
 <li>If `eab` and `ebc` are proofs of $a=b$ and $b=c$ then `eab.symm`
  and `eab.trans abc` are proofs of $b=a$ and $a=c$.
 </li>
 <li>If `ebc` is a proof of $b=c$ then `congr_arg f ebc` is a proof of
  $f(b)=f(c)$.   However, we really want a version of this for a
  binary operation $g$ rather than a unary function.  After thinking a
  little about how currying works we see that `congr_arg g a ebc`
  proves $g(a,b)=g(a,c)$.  To prove $g(b,d)=g(c,d)$ we need a similar
  but slightly different construction such as
  `congr_fun (congr_arg g ebc) d`.
 </li>
</ul>
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma npz_mul_left (x : R) {y : R} {m : ℕ} (yR : next_pow_zero y m): 
  (next_pow_zero (x * y) m) :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state that if $y^{m+1}=0$ then $(xy)^{m+1}=0$.  Note that we
need to supply $x$ as an explicit argument, but $y$ and $m$ can be
deduced from `yR`.  Thus, our theorem will usually invoked in the form 
`npz_mul_left x yR`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 begin
  unfold next_pow_zero at yR ⊢,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We unfold the definition of `next_pow_zero` in the hypothesis and in
the conclusion. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  rw[_root_.mul_pow,yR,mul_zero],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now perform a series of rewrites.  The identity $(xy)^p=x^py^p$ is
called `mul_pow`.  We need the prefix `_root_` to ensure that we refer
to a version for arbitrary commutative monoids, rather than the version
`nat.mul_pow` that applies only to $\mathbb{N}$.  After using that, we
can just use the unfolded version of `yR` to get $x^{m+1}0$, and then
the ring axiom `mul_zero` to get $0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 lemma npz_mul_right {x : R} {n : ℕ} (xR : next_pow_zero x n) (y : R):
  (next_pow_zero (x * y) n) := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state the symmetric claim, that if $x^{n+1}=0$ then
$(xy)^{n+1}=0$.  We could either give a proof that is very similar
to the previous one, or we could use commutativity to reduce to the
previous claim.  For the sake of variety, we will do the latter.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 calc
   (x * y) ^ (n + 1) = (y * x)^(n + 1) : by rw[mul_comm x y]
   ... = 0 : npz_mul_left y xR.
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We write the proof using the `calc` tactic.  This is a little fragile:
the second step only works because `npz_mul_left y xR` reduces by 
definition to precisely the identity that we need.  In other contexts 
we might need to start by unfolding the definitions of `next_pow_zero`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma npz_chain {x : R} {n m : ℕ}
   (xR : next_pow_zero (x ^ (n + 1)) m) :
      next_pow_zero x (n * m + n + m) :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state that if $(x^{n+1})^{m+1}=0$ then $x^{p+1}=0$, where
$p=nm+n+m$.  Note that we have made all arguments implicit, except
for `xR`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 begin
  unfold next_pow_zero at xR ⊢,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We unfold the definition of `next_pow_zero` in the hypothesis and in
the conclusion. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have Z0 : x^((n + 1) * (m + 1)) = 0, by rw[pow_mul,xR],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We rewrite the hypothesis using the standard index law, which is
called `pow_mul`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have Z1 : (n * m + n + m) + 1 = (n + 1) * (m + 1) := 
    by simp[add_mul,mul_add,mul_one,one_mul,add_assoc],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We perform the obvious manipulation on the exponent.  For some
reason it is necessary to supply a list of simplification rules here;
it is not clear to me why this is not dealt with automatically.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  by rw[Z1,Z0],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The goal can now be proved by substituting the equations `Z1` and `Z0`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma nilpotent_zero : is_nilpotent (0 : R) := ⟨0,npz_zero⟩
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have so far proved all our results with specific exponents of
nilpotence.  We now start to prove the corresponding results where
we do not bother to keep track of exponents.  In general, if `h` is
a proof of `next_pow_zero x n` then we can write the resulting proof
of `is_nilpotent x` as `exists.intro n h` or just `⟨n,h⟩` (with 
angle brackets).  Here we just record the obvious proof that `0`
is nilpotent.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma nilpotent_add {x y : R} :
   is_nilpotent x → is_nilpotent y → is_nilpotent (x + y)
| ⟨n,xR⟩ ⟨m,yR⟩ := ⟨n+m,npz_add xR yR⟩
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now need to show that if $x$ and $y$ are nilpotent then so is
$x+y$.  This clearly follows from the theorem `npz_add`; the problem
is just to find the right way to express this.  It is convenient to
use pattern matching syntax as in
<span class="tpil">Section 8.1</span>.  This allows us to say that the
assumed proof of `is_nilpotent x` is given as a pair consisting of a
natural number `n` together with a proof (named `xN`) of
`next_pow_zero x n`.  Similarly, we can say that the assumed proof of
`is_nilpotent y` is given as a pair consisting of a natural number `m`
together with a proof (named `yN`) of `next_pow_zero y m`.  We can
then just use `npz_add` in an obvious way.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma nilpotent_mul_left (x : R)  {y : R} : 
  is_nilpotent y → is_nilpotent (x * y)
| ⟨m,yN⟩ := ⟨m,npz_mul_left x yN⟩ 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now need to show that if $y$ is nilpotent then so is $xy$.  We
reduce this to our earlier theorem `npz_mul_left` by the same kind of
process as in the previous proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma nilpotent_mul_right : ∀ {x : R} (xN : is_nilpotent x) (y : R),
  (is_nilpotent (x * y)) 
| x ⟨m,xN⟩ y := ⟨m,npz_mul_right xN y⟩ 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now show that the set of nilpotents is also closed under right 
multiplication.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 lemma unit_not_nilpotent (x y : R) (e0 : x * y = 1) (e1 : (1 : R) ≠ 0) :
  ¬ is_nilpotent x := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now want to show that no invertible element can be nilpotent.  
However, this claim is actually false for the trivial ring, so we need
to exclude that case explicitly, by adding the hypothesis `1 ≠ 0`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 begin
  rintro ⟨m,e2⟩,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to assume that we are given a proof that `x` is nilpotent, 
and derive a contradiction.  The most obvious way to do this would 
be to use `intro h` to get an assumption `h` of type 
`is_nilpotent x`.  We could then use `cases h with m e2` or 
`rcases h with ⟨m,e2⟩` to get a natural number `m` and a proof `e2`
that $x^{m+1}=0$.  These two steps can be combined by using the 
`rintro` tactic instead of `intro` and `rcases`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  apply e1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The current goal is `false` but the assumption `e1` has type 
`1 ≠ 0` or equivalently `1 = 0 → false`, so we can use `apply e1`
to change the goal to `1 = 0`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  exact calc 
   (1 : R) = 1 ^ (m + 1) : (_root_.one_pow (m + 1)).symm
    ... = (x * y) ^ (m + 1) : by rw[← e0]
    ... = 0 : npz_mul_right e2 y,
 end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now use the calculation $1=1^{m+1}=(xy)^{m+1}=0$.  The first step
is called `one_pow`, but we have to write `_root_.one_pow` to avoid
confusion with the version `nat.one_pow` that applies only to 
natural numbers.  Also, to the right of the colon we just have a
proof term with no `by ...` or `begin ... end`.  Because of this we
need to supply the argument `m + 1`, and the suffix `.symm` to switch
the left and right sides of the identity, so as to produce a proof
term that exactly matches what is required.  By contrast, the second
step uses the rewrite tactic.  This still needs the left arrow to 
indicate that we are replacing $1$ by $xy$ rather than vice-versa,
but the tactic then deduces $1^{m+1}=(xy)^{m+1}$ from $1=xy$ without
further instruction.  For the third step we again give a proof term.
This has type `next_pow_zero (x * y) (m + 1)`, and Lean is doing a 
little work to unfold the definition and see that it matches the 
proposition $(xy)^{m+1}=0$ as required. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  
 lemma nilpotent_chain {x : R} {n : ℕ} :
   is_nilpotent (x ^ (n + 1)) →  is_nilpotent x 
| ⟨m,xN⟩ := ⟨n*m+n+m,npz_chain xN⟩  
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now need to show that if $x^{n+1}$ is nilpotent then so is $x$.
The proof uses the same kind of framework as `nilpotent_add`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 
 def is_reduced
   (R : Type*) [R_comm_ring : comm_ring R] : Prop :=
     ∀ x : R, (is_nilpotent x) → (x = 0)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define what it means for the ring $R$ to be reduced.
<br/><br/>
Recall that at the top of the current section, we had a `variable`
declaration making $R$ into an implicit parameter for everything in
the section that involves $R$.  However, because `is_reduced` is a
property of the ring as a whole, it is not reasonable for $R$ to be an
implicit parameter.  We therefore specify it as an explicit parameter
in our declaration of `is_reduced`.  The ring structure on $R$ remains
an implicit argument handled by typeclass inference, however.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 def nilradical
   (R : Type*) [R_comm_ring : comm_ring R] : ideal R :=
{
  carrier := is_nilpotent,
  zero := nilpotent_zero,
  add  := @nilpotent_add _ _ ,
  smul  := nilpotent_mul_left
}      
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now want to define the nilradical as an ideal in $R$.  Ideals are
defined in <span class="mathlib">ring_theory/ideals.lean</span> as
$R$-submodules of $R$, and submodules are defined in 
<span class="mathlib">algebra/module.lean</span>.  After unwrapping
this we see that an ideal is a structure consisting of a carrier 
together with three properties.  The carrier must be a subset of $R$,
which is encoded in Lean as a map `R → Prop`, which is supposed to
send elements of the carrier to `true` and everything else to 
`false`.  The three properties say that the carrier contains zero and
is closed under addition and scalar multiplication.  There are
coercions (defined in
<span class="mathlib">algebra/module.lean</span>) that allow us to 
elide the difference between the whole structure and the carrier,
and so write expressions such as $x∈I$, just as in ordinary
mathematical writing.  There is also a further coercion that converts
subsets to types. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 def reduced_quotient (R : Type*) [R_comm_ring : comm_ring R] := 
  (nilradical R).quotient 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define `reduced_quotient R` to be the quotient of $R$ by the
nilradical.  The general theory of quotient rings is set up in the file
<span class="path">ring_theory/ideals.lean</span>.  It is partly a
specialisation of the theory of quotient modules, which is established
in <span class="path">linear_algebra/basic.lean</span>.
This in turn relies on a more general framework for quotient objects,
for which the most important files are 
<span class="path">init/data/quot.lean</span> and 
<span class="path">init/data/setoid.lean</span>in the core Lean
library.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance reduced_quotient_ring_structure
   (R : Type*) [R_comm_ring : comm_ring R] : 
     comm_ring (reduced_quotient R) := 
      by { dsimp[reduced_quotient]; apply_instance }
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now have several things where we take something that works 
for an arbitrary ideal $I$, and restate it with a new name for the
special case where $I$ is the nilradical.  It is not entirely clear
why this is necessary; there seems to be some issue with Lean not
unfolding definitions in the way that one might expect.  
<br/><br/>
For the first of these things, we introduce the ring structure on
the reduced quotient.  We use the keyword `instance` rather than `def`
because we are defining a typeclass instance; this allows us to apply
ring-theoretic constructions to the reduced quotient without referring
explicitly to the relevant ring structure.  To define the required
ring structure, we just use `dsimp[reduced_quotient]` to expose the
definition of the reduced quotient as $R/I$, and then `apply_instance`
to invoke the general rule for ring structures on quotient rings.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def reduced_quotient_mk {R : Type*} [R_comm_ring : comm_ring R] :
   R → reduced_quotient R := ideal.quotient.mk (nilradical R)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Lean notation for the projection map $R→R/I$ is 
`ideal.quotient.mk I`.  We find it convenient to introduce the 
name `reduced_quotient_mk` for this in the case where $I$ is the
nilradical.
<br/><br/>
Note that `R` and its ring structure are implicit arguments.  Thus,
if $a∈R$ we can write `reduced_quotient_mk a` for the image in 
$R/\sqrt{0}$.  However, if we want to refer to the map as a whole
then we need to write `@reduced_quotient_mk R _`.  (In principle, 
if we have an explicit name `c` for the ring structure on `R` then 
we could write `@reduced_quotient_mk R c`, but it is generally better
to use an underscore and leave Lean to work out the required 
structure.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance reduced_quotient_mk_is_ring_hom :=
  ideal.quotient.is_ring_hom_mk (nilradical R)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need to know that the projection map
`reduced_quotient_mk` is a ring homomorphism.
It is true in general that the projection map to a quotient ring is
a ring homomorphism; this fact is called
`ideal.quotient.is_ring_hom_mk`.  We again 
find it convenient to introduce a separate name for the case of the
reduced quotient.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma reduced_quotient_is_reduced : is_reduced (reduced_quotient R) :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now claim that the reduced quotient really is a reduced ring.
The key point is that if $x$ is nilpotent modulo the nilradical, then
it is actually nilpotent and so lies in the nilradical.  We proved this
as the lemma `nilpotent_chain`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 let π := @reduced_quotient_mk R _,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We introduce abreviated notation for the quotient map.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 rintros ⟨x0⟩ ⟨n,e0⟩,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We assume given an element of $R/\sqrt{0}$ and a proof that it is 
nilpotent.  The `rintros` tactic allows us to do these introductions
in a structured form, so we get an element `x0` in `R`, a natural 
number `n`, and a proof `e0` that `(π x0)^(n + 1) = 0`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  let e1 := calc 
   π (x0 ^ (n + 1)) = (π x0) ^ (n + 1) :
    by simp[π,reduced_quotient_mk,is_semiring_hom.map_pow]
    ... = 0 : e0,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now perform the calculation `π (x0^(n+1)) = (π x0)^(n+1) = 0`.
The first step uses the lemma `is_semiring_hom.map_pow`, which says
that semiring homomorphisms preserve powers.  For some reason we need
to unfold the definitions of `pi` and `reduced_quotient_mk` before
Lean can see that this lemma is applicable.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  have : is_nilpotent (x0 ^ (n + 1)) :=
    ideal.quotient.eq_zero_iff_mem.mp e1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The theorem `quotient_ring.eq_zero_iff_mem`
shows that elements map to zero in $R/I$ iff they lie in $I$.  This
is a bidirectional implication, and we need the suffix
`.mp` to refer to the forward implication.
Applying this to `e1` gives us a proof that $x_0^{n+1}$ lies in
the nilradical, or equivalently, that it is nilpotent.  We have 
not given a name to this conclusion; at the next step we will just
use the keyword `this`, which refers to the conclusion of the most 
recent anonymous `have`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have : is_nilpotent x0 := nilpotent_chain this,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The theorem `nilpotent_chain` (which we
proved earlier) allows us to conclude that
`x0` is nilpotent.  We again leave this
conclusion unnamed, and use the keyword `this` to refer to it.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact ideal.quotient.eq_zero_iff_mem.mpr this,
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We can now use the opposite direction in
`quotient_ring.eq_zero_iff_mem`
to conclude that `π x0 = 0`, as required.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
end nilpotents 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now close the section in which we develop the general theory of
nilpotents.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

section Z_is_reduced
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now open a new section in which we will prove that the ring ℤ is
reduced.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma N_reduced (n k : ℕ) : n^(k+1) = 0 → n = 0 :=
begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We first prove that ℕ is reduced in the obvious sense.  We cannot use
the general theory for that, because we developed it in the context of
commutative rings, and ℕ is only a semiring.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 cases n with n0,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We split into two cases: where `n = 0`, and where `n = n0 + 1` 
for some `n0`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 {intro,refl},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line deals with the case where `n = 0`.  Our goal is to prove 
`0 ^ (k + 1) = 0` implies `0 = 0`.  We use the `intro` tactic to 
convert the goal to `0 = 0` (while also giving us a proof of 
`0 ^ (k + 1) = 0`, which we ignore).  Then `refl` proves `0 = 0`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 {
   intro h0,
   exfalso,
   exact
    (ne_of_lt (nat.pow_pos (nat.zero_lt_succ n0) (k + 1))).symm h0,
 }
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now deal with the case `n = n0 + 1`.  After `intro h0` we have a
hypothetical proof `h0` of `(n0 + 1)^(k + 1) = 0`, and our goal is
in principle to prove `n0 + 1 = 0`.  However, the point is that 
assumption `h0` leads to a contradiction so this case cannot really 
occur.  The `exfalso` tactic converts the goal to `false`, leaving
us with the task of deriving a contradiction.
<br/><br/>
We use `nat.zero_lt_succ` to show that `n0 + 1 > 0`, then 
`nat.pow_pos` to deduce that `(n0 + 1)^(k + 1) > 0`, then 
`ne_of_lt` to get `(n0 + 1)^(k + 1) ≠ 0`.  This can be combined with
`h0` to get the required contradiction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma nat_abs_pow : ∀ (n : ℤ) (k : ℕ),
      int.nat_abs (n ^ k) = (int.nat_abs n) ^ k 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The standard library proves that the absolute value map ℤ → ℕ 
preserves products.  However, it does not record the consequence that
it also preserves powers, so we prove that here.  This could be done
using the `induction` tactic in a `begin ... end` block, but we have
instead given an essentially equivalent proof using pattern matching.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
| n 0 := rfl
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For the case `k = 0` both $n^k$ and $|n|^k$ are definitionally equal 
to $1$, so `rfl` counts as a proof of the required equality.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
| n (k + 1) := 
  begin
   let na := int.nat_abs n,
   exact calc
    int.nat_abs (n ^ (k + 1)) = 
          int.nat_abs (n * n^k) : rfl
    ... = na * (int.nat_abs (n ^ k)) : by rw[int.nat_abs_mul]
    ... = na * na ^ k : by rw[nat_abs_pow n k]
    ... = na ^ k * na : by rw[nat.mul_comm]
    ... = na ^ (k + 1) : rfl
  end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The induction step is proved by an obvious kind of calculation.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma Z_reduced : is_reduced ℤ := 
begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We can now give the proof that ℤ is reduced.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 rintros x ⟨k,e⟩,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The `rintros` tactic gives us $x∈ℤ$ and $k∈ℕ$ and a proof `e` that 
$x^{k+1}=0$; the goal is then to prove that $x=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let x0 := int.nat_abs x,
 have : (int.nat_abs x)^(k + 1) = 0
  := (nat_abs_pow x k.succ).symm.trans (congr_arg int.nat_abs e),
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We define $x0=|x|∈ℕ$.  Assumption `e` says that $x^{k+1}=0$, and we 
can take absolute values to get $|x^{k+1}|=|0|$ (and $|0|$ is 
definitionally equal to $0$).  Lean notation for this is 
`congr_arg int.nat_abs e`.  The term `nat_abs_pow x k.succ` gives 
a proof of $|x^{k+1}|=|x|^{k+1}$.  We use the suffix `.symm` to swap 
the sides of this identity, and then `.trans` to combine it with our 
proof of $|x^{k+1}|=0$, resulting in a proof of $|x|^{k+1}=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have : x0 = 0 := N_reduced (int.nat_abs x) k this,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The result called `N_reduced` now shows that $|x|=0$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact int.eq_zero_of_nat_abs_eq_zero this,
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The result called `int.eq_zero_of_nat_abs_eq_zero` now shows that 
$x=0$, completing the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

end Z_is_reduced
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now close the section in which we proved that ℤ is reduced.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

section Z4_nilpotents
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start a new section in which we will prove that $0$ and $2$ are
the only nilpotent elements of ℤ/4.  Here we use the type `zmod n`,
which is defined in <span class="mathlib">data/zmod/basic.lean</span>.
It is actually defined to be equal to `fin n = {k : ℕ // k < n}`, but
by giving it a new name we are able to attach a ring structure using
modular addition and multiplication (as is done in the above file).
The reduction map ℤ → ℤ/n is just a special case of the coercion from
ℤ to any ring, so we can just write `k : zmod n` for the image of 
`k` in ℤ/n.  On the other hand, given `j : zmod n` we can write 
`j.val` for the representative in `{0,...,n-1}`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma zmod.pow_val {n : ℕ+} (a : zmod n) (m : ℕ) :
 (a ^ m).val = (a.val ^ m) % n :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We start with a lemma that should really be in the standard library,
showing that powers in `zmod n` behave in the expected way.  Note that
we have placed this in the `zmod` namespace even though we have not
opened that namespace.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 induction m with m0 ih,
 {simp[has_one.one,monoid.one,ring.one,has_mod.mod,comm_ring.one],},
 {exact calc
   (a ^ (m0 + 1)).val = (a * a^m0).val : rfl
  ... = (a.val * (a^m0).val) % n : by rw[zmod.mul_val]
  ... = (a.val * ((a.val ^ m0) % n)) % n : by rw[ih]
  ... = (a.val * a.val ^ m0) % n :
   modeq.modeq_mul (modeq.refl a.val) (mod_mod (a.val ^ m0) n)
  ... = (a.val ^ m0 * a.val) % n : by rw[mul_comm]
  ... = (a.val ^ (m0 + 1)) % n : rfl 
 }
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have written the proof using the `induction` tactic.  It is an 
exercise to rewrite this proof using pattern matching as we did for
`nat_abs_pow`, or alternatively to rewrite `nat_abs_pow` using the
`induction` tactic.  
<br/><br/>
The `induction` tactic gives us two goals: the case `m=0` and the 
case `m=m0+1`.  In the latter case, we can use the symbol `ih` to 
refer to the induction hypothesis.  We specified the names `m0` and
`ih` using the `with` clause attached to the `induction` tactic.
If we omit the `with` clause then Lean will generate its own names,
but it usually adds clarity to provide them explicitly.  One 
ingredient in the calculation is `zmod.mul_val`, which says that 
`(a * b).val = (a.val * b.val) % n`.  We also use `mod_mod`, which
says that `(a % n) % n = a % n`, and various properties of modular
equality from the `modeq` namespace. 
<br/><br/>
It is not clear to me why `rfl` does not succeed in proving the case
`m=0`.  For some reason we need to help Lean to unwind several nested
interpretations of the symbol `1`.  This is probably related to the 
fact that `n` could be `1`, in which case `1.val` would be `0`; this
prevents other things from working in a nicely uniform way.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma zmod.nilpotent_iff (n : ℕ+) (k : ℕ) (k_is_lt : k < n) :
 @is_nilpotent (zmod n) _ ⟨k,k_is_lt⟩ ↔ 
  ∃ m : ℕ, k ^ (m + 1) % n = 0 :=
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now reformulate nilpotence in ℤ/n in terms of equations in ℕ.
Because ℕ is not a dependent type and involves no propositional 
side conditions, it is easier to work there than in ℤ/n.  We have
again placed this lemma in the `zmod` namespace.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 split,
 {
   rintro ⟨m,h1⟩,
   use m,
   exact 
    (@zmod.pow_val n ⟨k,k_is_lt⟩ (m + 1)).symm.trans 
    (congr_arg fin.val h1),
 },{
   rintro ⟨m,h1⟩,
   use m,
   let k0 : zmod n := ⟨k,k_is_lt⟩,
   let z0 : zmod n := 0,
   let h2 : (k0 ^ (m + 1)).val = z0.val :=
    (@zmod.pow_val n ⟨k,k_is_lt⟩ (m + 1)).trans h1,
   exact fin.eq_of_veq h2,
 }
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The core of the proof is `zmod.pow_val`; the rest is mundane 
bookkeeping.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma Z4_nilpotents : (nilradical (zmod 4)).carrier = {0,2} := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now want to calculate the nilradical of ℤ/4.  Recall that the 
nilradical is defined as an ideal, which is a structure with several
members.  The most important member is the carrier, which is a 
subset of `zmod 4`, encoded as a map `zmod 4 → Prop`.  On the other
hand, `{0,2}` is initially interpreted as a `finset` on `zmod 4`,
which is then coerced to a subset.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 have h0 : is_nilpotent (0 : zmod 4) := ⟨0,rfl⟩,
 have h2 : is_nilpotent (2 : zmod 4) := ⟨1,rfl⟩,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A proof that $0$ is nilpotent consists of a natural number $k$ together
with a proof that $0^{k+1}=0$.  We can just take $k=0$ and then 
`rfl` counts as the required proof.  To prove that $2$ is nilpotent
we can instead take $k=1$.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have nt : (1 : zmod 4) ≠ 0 := dec_trivial,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need to record a proof that `1 ≠ 0` in `zmod 4`.  Because `zmod 4`
has decidable equality, we can write `dec_trivial` for the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have h1 : ¬ is_nilpotent (1 : zmod 4) :=
  unit_not_nilpotent 1 1 rfl nt,
 have h3 : ¬ is_nilpotent (3 : zmod 4) :=
  unit_not_nilpotent 3 3 rfl nt,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We can now use the lemma `unit_not_nilpotent` (proved earlier in this
file) to check that $1$ and $3$ are not nilpotent.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have e1 : ∀ j0 : ℕ, ¬ (j0.succ.succ.succ.succ < 4) :=
   λ j0, dec_trivial,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We will need to step through the elements of `zmod 4`.  There is a 
tactic called `fin_cases` that is supposed to handle this sort of 
thing, but it does not seem to work here for reasons that are unclear.
We will therefore use an argument that splits the natural numbers
by cases, together with the lemma `e1` defined here that will discard
numbers $4$ and above.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 ext j,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove that two sets `A` and `B` are equal.  The tactic 
`ext j` reduces this to proving that `j ∈ A ↔ j ∈ B`.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 simp[nilradical],
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This tactic unfolds the definition of the nilradical, and also converts
`j ∈ {0,2}` to `j = 0 ∨ j = 2`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We are proving a bidirectional implication; we use the `split` tactic
to give one goal for each direction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 {intro j_nil,
  rcases j;
  rcases j_val with _ | _ | _ | _ | j0,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Using `intro` and `rcases` we give ourselves five goals: one for each
element of `zmod 4`, and one vacuous case for natural numbers `j0`
with `j0+4 < 4`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exact dec_trivial,},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here we must prove that `0 = 0 ∨ 0 = 2`, which we do using `dec_trivial`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exfalso,exact h1 j_nil,},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here we are supposedly given a proof (named `j_nil`) that `1` is 
nilpotent, and we are supposed to prove that `1 = 0 ∨ 1 = 2`.  We 
instead use `h1` to show that this case cannot occur.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exact dec_trivial,},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here we must prove that `2 = 0 ∨ 2 = 2`, which we do using `dec_trivial`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exfalso,exact h3 j_nil,},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here we are supposedly given a proof (named `j_nil`) that `3` is 
nilpotent, and we are supposed to prove that `3 = 0 ∨ 3 = 2`.  We 
instead use `h3` to show that this case cannot occur.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exfalso,exact e1 j0 j_is_lt,}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here we are supposedly given `j0` with `j0 + 4 < 4`; we use `e1` to 
show that this case cannot occur.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 },{
  intro j_eq, cases j_eq; rw[j_eq],
  exact h2,
  exact h0,
 }
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The tactic `intro j_eq` gives us a proof that `j = 0 ∨ j = 2`, and
we need to use it to prove that `j` is nilpotent.  The tactic
`cases j_eq` gives us one goal for `j = 2` and one for `j = 0`.
We then use `rw[j_eq]` to set `j` equal to the relevant value in the
goal.  Because we have a semicolon before `rw[j_eq]` instead of a 
comma, this rewrite is performed in both goals rather than just the
first one.  We now use `h2` to solve the first goal, and `h0` to
solve the second one.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
end

end Z4_nilpotents

