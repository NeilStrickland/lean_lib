import data.fintype tactic.squeeze tactic.fin_cases
import data.finset_transfer data.unique_element 

namespace combinatorics

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This file sets up some basic theory of partitions of finite sets. 
It relies on some theory of finite sets, and we need the line 
<span class="code">import data.fintype</span> to load that theory
from the <span class="code">mathlib</span> library.  We also need
some auxiliary results from the files 
<span class="path">finset_transfer.lean</span>,
<span class="path">unique_element.lean</span>, so we have import statements
for these as well.  Note, however, that these three files are not in a
standard library; they were written in parallel with this file and live 
in the same directory.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

universes u v
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Universes are a mechanism used in Lean and similar systems to avoid
Russell-type paradoxes.  Lean will usually handle all related 
bookkeeping by itself, so it is rarely necessary for users to think
about the details.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

variable {α : Type u} 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to consider partitions of a finite set, which will be called 
α.  In Lean, this will be represented as a type α together with some 
extra data to be discussed shortly.  The line 
`variable {α : Type u}` declares that for the rest of this file, the 
symbol α will represent a type.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
variable [fintype α] 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This line essentially declares that α is finite.  In more detail, it 
declares an assumption that we have a term of the type `fintype α`, 
which is defined in <span class="mathlib">data/fintype</span>.  It 
would be possible to give this a name, with a declaration like 
<span class="code">variable [P : fintype α]</span>.  However, we will
not need to refer to it explicitly, so we omit the name.  Instead,
we put the declaration in square brackets, indicating that Lean
should treat the term as a typeclass instance, an supply it as an
implicit argument in any situation where it is required.

In a little more detail, a term of type `fintype α` consists of an 
equivalence class of lists of elements of α, together with a proof 
that no two terms in the list are the same, and a proof that every 
element of α appears in the list.  Here lists are considered 
equivalent if one is a permutation of the other.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
variable [decidable_eq α]  
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We also assume that we are given a term of the type 
<span class="code">decidable_eq α</span>, which is a procedure that
decides unambigously whether two elements of α are equal.  Such 
procedures can be defined explicitly for many types, including ℕ, 
ℤ and ℚ, and types constructed from those by finitary means such
as <span class="code">list (list ℚ)</span>.  Below we will explain
the framework in more detail when we deduce that the set of partitions
itself has decidable equality.

The situation is different for ℝ, for example: if two reals are 
presented as Cauchy sequences then we can only conclude that they are 
equal by examinining infinitely many terms, and there is no 
computational procedure for that.  However, we could include the
line `import classical` at the top of the file.  This would cause 
Lean to allow classical non-constructive logic, and gives us an 
axiomatically posited term of class `decidable_eq α` for every type 
`α`, but without the ability to compute with it explicitly.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

open finset fintype
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
By opening the namespaces `finset` and `fintype`, we allow ourselves
to use definitions and theorems from the files 
<span class="mathlib">data/finset.lean</span>
<span class="mathlib">data/fintype.lean</span> without a prefix
(e.g. `subset_def` rather than `finset.subset_def`).  Strictly 
speaking, this operation works on definitions in the `finset`
namespace rather than file 
<span class="mathlib">data/finset.lean</span>.  In that file there
are a few lines before `namespace finset` and a few lines after
`end finset` that are not covered.  Also, the namespace is reopened
and extra definitions added in various other mathlib files such 
as <span class="mathlib">algebra/big_operators.lean</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def is_partition (block : α → finset α) := 
 (∀ a : α, a ∈ block a) ∧  
 (∀ a1 a2 : α, a1 ∈ block a2 → block a1 = block a2)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define what it means for someting to be a partition.  There are
several different definitions that one could use.  Below we will have
some theorems showing that some other approaches are equivalent to the
one that we have preferred.  We have chosen to encode a partition as 
a map that sends each element `a` to the block of the partition that 
contains `a`.  We have also chosen to encode the required properties 
as a single axiom which is a logical conjunction of two clauses.  There
would be some advantages and some disadvantages if we replaced this
with two separate axioms.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance decidable_partition (block : α → finset α) :
 decidable (is_partition block) :=
   by dsimp[is_partition]; apply_instance
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We next need a decision procedure to decide whether the proposition
`is_partition b` is true, for a given map `b : α → finset α`.  Lean 
can deal with this automatically using the assumed decision procedure
for equality on α and a range of previously established results about
decidability for finite sets, maps with finite domain and so on;
this is achieved by the `apply_instance` tactic.  However, we need 
to use `dsimp` to unfold the definition of `is_partition` before we 
can use `apply_instance`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

variable (α)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For most definitions and theorems in this file, it is appropriate to
treat the underlying type `α` as an implicit parameter, because it can
be inferred from other ingredients.  However, if we just want to refer
to the type of all partitions of `α` then there are no other 
ingredients so we need to switch to treating `α` as an explicit 
argument.  That is achieved by the current line.  We will reverse
this a few lines down.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

structure partition :=
(block : α → finset α)
(ispart : is_partition block)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define a partition of `α` to be a structure consisting of a map
`α → finset α` together with a proof that it has the required 
properties.  If `p` is a partition, then the map and the proof can 
be referred to as `p.block` and `p.ispart` respectively.  Conversely,
if we have constructed an appropriate map `b` and proof `h` then we 
can package them as a structure using the notation `⟨b,h⟩` or 
`{block := b, ispart := p}`.  Note that the first version uses angle
brackets, not ordinary parentheses; they can be entered in VSCode
as `\<` and `\>`. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

variable {α}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We revert to treating `α` as an implicit argument.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
namespace partition
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start a new namespace.  The very last line of this file is 
`end partition`, so everything up until then is in the `partition`
namespace.  Thus, in any other file the definition below will need
to be referred to as `partition.block_set` rather than just 
`block_set`, unless that file also includes the directive 
`open partition`.

However, there is a further wrinkle to this.  If `p` is a term of
type `partition α`, then we can use the "object notation"
`p.block_set` as a synonym for `block_set p` or 
`partition.block_set p`.  This works for any function in which 
`p` is the first non-implicit argument, and in this context, the
namespace prefix is never required.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def block_set (p : partition α) : finset (finset α) := 
 image p.block univ
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given a partition `p`, we define the associated block set to be the 
image of the associated map `α → finset α`, so the block set is an 
element of `finset (finset α)`.  For this to work properly, we need
to start with the finset of all elements of `α`, which is called 
`univ`.  This implicitly refers to the term of type 
`fintype α` which we posited near the top of this file.  Lean finds
this by the mechanism of typeclass inference, so we do not need to 
refer to it explicitly.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def block_type (p : partition α) : Type* := 
 { b : finset α // b ∈ block_set p }
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The block set `B` (as defined above) is of type `finset (finset α)`, 
which means that it is a permutation-equivalence class of lists with 
entries in `finset α`.  In particular, it is not a type, so it is not
meaningful to write `b : B` or to consider maps `B → γ` for some 
other type `γ`.  It is meaningful to write `b ∈ B` (provided that
`b` is of type `finset α`), but this is not a primitive notion; it 
is defined in <span class="mathlib">data/finset.lean</span> in terms
of other ingredients.  The current line defines a type that is 
a counterpart of `B`.  The relevant framework is described 
briefly in <span class="tpil">Section 7.3</span>.  Note the use of 
`//` where in traditional notation we would have a colon or vertical 
bar; those symbols are already used for too many other things.  If 
`b` is of type `p.block_type`, then `b.val` is of type `finset α`,
and `b.property` is a proof that `b.val` lies in `p.block_set`.
Conversely, if we have a subset `b0` and a proof `h0` that `b0` 
lies in the block set, then we can use the notation `⟨b0,h0⟩` to
construct a term of type `p.block_type`. Note that this uses angle
brackets, not ordinary parentheses; they can be entered in VSCode
as `\<` and `\>`. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def block_alt (p : partition α) (a : α) : p.block_type := 
 ⟨p.block a,mem_image_of_mem p.block (mem_univ a)⟩
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define a function which takes as input a partition `p` and an
element `a`, and returns the block containing `a` as a term of type
`p.block_type` rather than just a finite subset of `α`.  For this, 
we need to package the finite subset `b := p.block a` together with
a proof that `b` lies in `p.block_set`.  Now `p.block_set` was 
defined as the image of `univ` under the map `p.block`.  The fact
that every element lies in `univ` is recorded as the theorem `mem_univ` 
from <span class="mathlib">data/fintype.lean</span>. (Of course the
proof of `mem_univ` just consists of extracting part of the definition
of `fintype α`; the real work is done by the typeclass inference
mechanism that retrieves our posited instance of `fintype α`.)
The theorem `mem_univ_of_mem` just refers back to the definition of
image to conclude that `p.block a` lies in the image, as required.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

@[simp] 
lemma block_alt_val (p : partition α) (a : α) :
 (p.block_alt a).val = p.block a := rfl
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Clearly, the underlying finite set `(p.block_alt a).val` of 
`p.block_alt a` is just the same as `p.block a`.  It is convenient 
to record this fact as a lemma and mark it with the attribute 
`@[simp]`.  This ensures that when we use the `simp` tactic in
subsequent proofs, `(p.block_alt a).val` will be replaced by 
`p.block a` whenever it occurs.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_eq_of_veq {p : partition α} {b0 b1 : p.block_type} 
 (e : b0.val = b1.val) : b0 = b1 := subtype.eq e
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now record the fact that any two terms of type `p.block_type`
are equal if their underlying sets are equal.  This is because
Lean implements the principle of "proof irrelevance": it treats
any two proofs of the same proposition as equal.  Our proof simply
refers to the more general fact `subtype.eq` from 
<span class="library">init/data/subtype/basic.lean</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_veq_of_eq {p : partition α} {b0 b1 : p.block_type} 
 (e : b0 = b1) : b0.val = b1.val := congr_arg _ e
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This is the converse of the previous lemma.  We are given a proof 
`e` of `b0 = b1`, and we need to deduce that `f b0 = f b1`, where 
`f` is the function sending `b` to `b.val`.  For this we need 
`congr_arg f e`.  If we wanted to name the relevant function `f` 
explicitly we could write `λ b : p.block_type, b.val`, but it 
also works to just write `_` and let Lean work it out.  This is 
certainly shorter and perhaps more natural.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_alt_eq {p : partition α} {a0 a1 : α} :
 p.block a0 = p.block a1 ↔ p.block_alt a0 = p.block_alt a1 := 
begin
 split; intro e,
 {exact @block_eq_of_veq α _ _ p (p.block_alt a0) (p.block_alt a1) e},
 {exact @block_veq_of_eq α _ _ p (p.block_alt a0) (p.block_alt a1) e} 
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For convenience, we combine the last two results into a bidirectional
implication.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma mem_block_set {p : partition α} {b : finset α} :
 b ∈ p.block_set ↔ ∃ a, p.block a = b :=
by simp[block_set]
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now record the obvious criterion for a set `b` to lie in 
`p.block_set`.  We prove that this criterion is correct using the 
`simp` tactic.  This tactic tries to apply all the theorems that 
Lean knows that have been marked with the `@[simp]` attribute,
together with any extra things that we put in square brackets as
arguments for the tactic.  Often the extra arguments are names
of theorems.  Sometimes (as here) they are the names of definitions
that should be unfolded during simplification.  There are numerous
options for modifying the behaviour of `simp`, which are discussed
in <span class="tpil">Section 5.7</span>.

Note that this tactic is mildly deprecated in all cases, because it
causes Lean to search through a large space of results that are
mostly irrelevant.  It is also more strongly deprecated in cases
where it does not finish the job of proving the current goal.  This
is because the set of `simp` lemmas changes frequently as `mathlib`
expands, so the exact amount of progress that `simp` can make is
volatile.  If you write additional steps on the assumption that
`simp` has reached a particular point, then your proof may get broken
if `simp` later learns to make more progress.  

One possibility is to add `import tactic.squeeze` at the top of the
file, and then replace `simp` by `squeeze_simp`.  This will print
a message reporting a modified `simp` command that specifies the
results that are actually needed.  For example, in this proof 
`squeeze_simp` suggests replacing `simp[block_set]` by 
`simp only [block_set, finset.mem_univ, iff_self, 
exists_prop_of_true, finset.mem_image]`, which is more efficient.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_not_empty {p : partition α} {b : finset α} : 
 b ∈ p.block_set → b ≠ ∅ :=
begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We state the lemma that all blocks are nonempty.  Note that the only
explicit argument is the proof that `b ∈ p.block_set`, because
`p` and `b` can be inferred from this.

The symbol ∅ can be entered as \empty or \emptyset.  The thing that it
refers to here can be named more explicitly as `@finset.empty α`.
However, this is an indirect reference via the typeclass `has_emptyc`.
This is a fairly common pattern.  Whenever a type `α` has an element 
that deserves to be called `0`, this will be encoded as an instance
of the typeclass `has_zero α`.  Similarly, elements that deserve 
to be called `1` are encoded as instances of `has_one α`, and 
elements that deserve to be called `∅` are encoded as instances of 
`has_emptyc α`.  (I am not sure why it is `has_emptyc` rather than 
`has_empty`.)  There is a separate framework for not-necessarily-finite
subsets of types, which has a separate definition of `∅`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 intros b_in_blocks b_empty,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We assume given proofs that `b ∈ p.block_set` and that `b = ∅`;
the goal then becomes to derive a contradiction, or in other words,
to give a proof of `false`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 cases (mem_block_set.mp b_in_blocks) with a a_block,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Above we proved a result called `mem_block_set`, which is a 
bidirectional implication.  The suffix `.mp` (for "modus ponens") 
picks out the left-to-right implication.  We pass this our proof
that `b ∈ p.block_set` to get a proof that `∃ a, p.block a = b`.
The `cases` tactic then introduces names for the element `a` and
the proof that `p.block a = b`.

It is important to note some restrictions on this kind of use of the
`cases` tactic.  At the moment we are trying to prove a proposition, 
not to define a function.  Lean implements the principle of "proof
irrelevance", so any two proofs of the same proposition are regarded
as equal.  Because of this, Lean does not worry that what we are 
doing might depend on the choice of `a`.  However, if we tried to
do this while defining a function to a `Type` rather than a `Prop` 
we would get an error message as follows:
`induction tactic failed, recursor 'Exists.dcases_on' can only eliminate into Prop`.
We postpone any discussion of what to do about this.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have block_empty : p.block a = ∅ := a_block.trans b_empty,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given proofs `P : x = y` and `Q : y = z`, we can combine them to get 
a proof of `x = z` using the notation `eq.trans P Q` or `P.trans Q`.
Here we use the latter to produce a proof that `p.block a = ∅`. 
(For more complicated strings of equalities one would use the `calc`
tactic, which would produce terms like `P.trans Q` automatically,
but here it is easy to just write the proof term explicitly.) 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

 have a_in_block : a ∈ p.block a := p.ispart.left a,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Recall that `p` is a structure consisting of a map 
`p.block : α → finset α` together with a proof `p.ispart` of the 
required property of this map.  Here `p.ispart` is a logical 
conjunction of two propositions, and we can select the first of 
these with the notation `p.ispart.left` or `p.ispart.1`.  This is
a universally quantified proposition like `∀ x, x ∈ p.block x`.
We specialise to `x = a` by simply supplying `a` as an argument.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 rw[block_empty] at a_in_block,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
At this point we have a proof `a_in_block : a ∈ p.block a` and also 
a proof `block_empty : p.block a = ∅`.  The `rw` tactic (which can
also be written as `rewrite`) allows us to convert `a_in_block` to 
a proof that `a ∈ ∅`.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact not_mem_empty a a_in_block,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The library theorem `not_mem_empty` (from 
<span class="mathlib">data/finset.lean</span>) proves that the 
empty set has no elements.  In more detail, it accepts as explicit
arguments a term `x` and a proof that `x ∈ ∅`, and produces a proof
of `false`.  We can thus pass `a` and `a_in_block` to `not_mem_empty`
to produce the required contradiction.

In even more detail, the current goal is `false` and the term 
`not_mem_empty a a_in_block` has type false.  If we were in term
mode we could just write `not_mem_empty a a_in_block` to satisfy
the goal.  However, we are in a `begin ... end` block and thus in 
tactic mode, so we need to use the `exact` tactic rather than
just writing the relevant term.

Note also that we have an extra comma at the end of the line.  This
is not required, but it causes Lean to give an explicit message 
saying "no goals", which can be comforting.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_val_eq_of_mem {p : partition α} {b : p.block_type}
 {a : α} (a_in_b : a ∈ b.val) : b.val = p.block a := 
begin
 cases mem_block_set.mp b.property with a0 e0,
 rw[← e0] at a_in_b ⊢ ,
 exact (p.ispart.right a a0 a_in_b).symm,
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If `b` is a block of `p` and `a` lies in `b` then `b` must be equal
to `p.block a`.  
<br/><br/>
The term `h := mem_block_set.mp b.property` gives a proof that 
there exists `a0` and `e0 : p.block a0 = b.val`, and one could hope
to use `cases h with a0 e0` to get a choice of `a0` and `e0`.  For 
reasons that are not clear to me, this does not work well if we 
introduce `h` explicitly.  However, if we instead write
`cases mem_block_set.mp b.property with a0 e0`, then things work
as expected.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_eq_of_mem {p : partition α} {b : p.block_type}
 {a : α} (a_in_b : a ∈ b.val) : b = p.block_alt a := 
  block_eq_of_veq (block_val_eq_of_mem a_in_b)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This lemma is deduced from the previous one and is more or less the 
same, except that it proves an equality in `p.block_type` rather than
`finset α`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def rank (p : partition α) : ℕ := card (p.block_set)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The rank of a partition is the number of blocks.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance partition_repr [has_repr α] : has_repr (partition α) :=
⟨λ p, has_repr.repr p.block_set⟩
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This definition tells Lean how to produce a string representation
of a partition.  For example, the string `"{{1,4},{2,3}}"` represents
a partition of `{1,2,3,4}` in an obvious way.  For this to work, we
obviously need to know how to generate string representations for 
individual elements of `α`.  Assuming that, Lean already knows how
to print finite subsets of `α`, and finite subsets of finite subsets
of `α`, so it knows how to print the set of blocks of a partition.
This definition tells Lean that it should use that as the string
representation of the partition itself.
<br/><br/>
All of this is handled by the typeclass mechanism.  The word 
`instance` is essentially the same as `def` except that it tells Lean
that the thing we are defining is a typeclass instance that should
be remembered and used without explicit mention in various other 
places.  Next, `partition_repr` is the name of the instance that we
are about to define.  We could have just left it out and defined 
an anonymous instance; that is a fairly common pattern.  Then 
`[has_repr α]` indicates that our definition will depend on an 
argument of type `has_repr α`, which is essentially the same as 
a function `α → string`.  We have left this argument unnamed, and
enclosed it in square brackets to indicate that the argument will
not be given explicitly and should be found by typeclass inference.
We then declare that we are going to define a term of type 
`has_repr (partition α)`.  If `u0` is our function `α → string`,
and `u1` is the resulting function `finset (finset α) → string`,
then the required function `partition α → string` is 
`u2 := λ p,u1 p.block_set`.  However, there is a little extra
wrapping and unwrapping to worry about.  A term of type 
`has_repr (partition α)` is not actually a function 
`partition α → string`, but rather a structure with one member 
(called `repr`) which is a function `partition α → string`.
We can turn our function into a structure just by enclosing it
in angle brackets (entered as \< and \>).  Also, we did not 
name the map `u0` or discuss exactly how `u1` is defined in
terms of `u0`.  It turns out that we can just write `has_repr.repr` 
instead of `u1` and everything works out automatically.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma mem_block (p : partition α) (a : α) : a ∈ p.block a := 
 (p.ispart.left a)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For convenience, we make a lemma that just restates the first half
of the definition of what it means to be a partition.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_symm {p : partition α} {a0 a1 : α}
 (e : a0 ∈ p.block a1) : a1 ∈ p.block a0 := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If `a0` lies in `a1`'s block, then `a1` lies in `a0`'s block.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 let h0 : p.block a0 = p.block a1  := p.ispart.right a0 a1 e,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In fact the two blocks are the same, by the second half of the 
definition of what it means to be a partition.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let h1 : a1 ∈ p.block a1 := p.ispart.left a1,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
`a1` lies in its own block by the first half of the definition.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact h0.symm.subst h1,
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Equation `h0` says that `p.block a0 = p.block a1`, and `h0.symm` is 
notation for the reversed equation `p.block a1 = p.block a0`.  We can
substitute this in fact `h1` using the notation `h0.symm.subst h1` to 
get the desired conclusion `a1 ∈ p.part a0`.  However, we are in a
`begin ... end` block and so in tactic mode, so we need to use the
keyword `exact` rather than just writing `h0.symm.subst h1`.
<br/><br/>
(This last sentence is an oversimplification, because there are 
various ways in which we can switch back into term mode inside a
`begin ... end` block.  For example, we could write 
`lemma russell : 1 + 1 = 2 := <br/>
begin <br/>
 let n : ℕ := 42,<br/>
 refl<br/>
end`<br/>
Before `let n : ℕ :=` we are in tactic mode.  After ` := ` we are in
term mode, and our current goal is to produce a term of type `ℕ`.  
We can do that directly, by entering `42` or `2 * 3 + 6` or 
`min 10 11` or some other formula.  Alternatively, if we needed a
complex combination of logical steps to produce the required 
natural number, then we could write `let n : ℕ := begin ... end,`
and then replace the `...` by a sequence of tactics.  As this 
illustrates, we can have fragments of term mode and fragments of
tactic mode nested arbitrarily deep inside each other.
)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

@[simp] theorem eq_of_block_eq :
 ∀ {p1 p2 : partition α}, p1 = p2 ↔ p1.block = p2.block
| ⟨_,_⟩  ⟨_,_⟩ := by simp
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now prove that two partitions `p1` and `p2` are equal iff the maps
`p1.block, p2.block : α → finset α` are equal.  This is just because
`p1.ispart` and `p2.ispart` are then proofs of the same proposition
and so automatically count as being equal, by proof irrelevance.
<br/><br/>
To get Lean to accept this argument, we must persuade it to take the
right point of view.  Rather than thinking of `p1` and `p2` as being
packages that it could potentially unwrap to reveal `p1.block`,
`p2.block`, `p1.ispart` and `p2.ispart`, it must suppose that it 
has been given these four ingredients and used them to build `p1` and
`p2`.  We could do this with a proof like 
`begin rcases p1, rcases p2, simp, end`, but here we take a slightly
different approach, using pattern matching.  For this to work we 
need to formulate the statement with an explicit `∀` after the
colon, rather than placing arguments before the colon as we have 
done previously.  Note also that there is no `:=` directly after 
the statement.  Instead, we would typically have a number of lines
consisting of a vertical bar, a pattern that might or might not be 
matched by the arguments, then `:=` followed by a proof that works
when the arguments match the relevant pattern.  Many examples are
given in <span class="tpil">Section 8.1</span>.  The present 
example is rather degenerate: there is only one pattern, and the 
point is just that matching the pattern forces Lean to think of
`p1` and `p2` as being built up from their two constituents.  Given
this, the `simp` tactic is enough to finish the proof.
<br/><br/>
Note also that we have used the annotation `@[simp]` to give this
theorem the `[simp]` attribute, so that the `simp` tactic will use
it by default.  Attributes are discussed in more detail in 
<span class="tpil">Section 6.4</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

@[extensionality] theorem ext 
 {p1 p2 : partition α} (e : ∀ a, p1.block a = p2.block a) : p1 = p2
  := eq_of_block_eq.mpr (funext e) 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This theorem is closely related to the previous one, but different 
in some details.  It is marked with the `[extensionality]` attribute
so that it will be used by the `ext` tactic, and the details are 
arranged so as to make that work smoothly.  The previous theorem was 
a bidirectional implication, but here we pick out one direction only.
Also, the hypothesis is that the maps 
`p1.block, p2.block : α → finset α` are pointwise equal, so we use
the theorem `funext` to deduce that `p1.block = p2.block` as 
functions.  (There are some subtle foundational issues related to 
`funext` as discussed in <span class="tpil">Section 11.3</span>.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance has_decidable_eq : decidable_eq (partition α) := 
λ p1 p2, decidable_of_iff (p1.block = p2.block) eq_of_block_eq.symm
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We are now ready to provide a decision procedure for equality of 
partitions.  In more detail, we need to define a function that accepts
two partitions `p1` and `p2` as arguments, and returns a decision 
procedure for the proposition `p1 = p2`.  We have assumed that we are 
given such a decision procedure for `α` itself, and the library 
defines a rich set of rules for deriving decision procedures for other 
types defined in terms of `α`.  In particular, these rules suffice to 
give a decision procedure for a proposition of the form 
`p1.block = p2.block` in `α → finset α`.  The theorem 
`eq_of_block_eq` tells us that `p1 = p2` is equivalent to 
`p1.block = p2.block` so we can use the function `decidable_of_iff`
to convert a decision procedure for the latter to a decision 
procedure for the former.  In the conclusion of `eq_of_block_eq`,
the implications are written the opposite way around from what is
expected by `decidable_of_iff`, so we have two write 
`eq_of_block_eq.symm` to reverse them.  
<br/><br/>
Note that in the expression we have written here, both `eq_of_block_eq` 
and `decidable_of_iff` have implicit arguments, and one of the 
implicit arguments for `decidable_of_iff` is an equality decision
procedure for `α → finset α` which is provided by a complex chain
of typeclass inferences, so there is quite a lot going on in the 
background.
<br/><br/>
The approach that we have taken here is not in fact the preferred one.
When we gave the original definition of `partition α`, we could
have prefixed it with the annotation `@[derive decidable_eq]`.  Lean
would then have silently generated the required decision procedure
in the background.  However, we decided to avoid explaining all that
at the relevant time.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_set_rep (p : partition α) : ∀ (b ∈ p.block_set), ∀ (a ∈ b), 
 b = p.block a := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If `b` is a block and `a ∈ b` then `b` is `a`'s block.  Note that there
is a little notational magic going on with the fragment 
`∀ (b ∈ p.block_set)`: we are usually only allowed things like 
`∀ x : X`, but the above fragment is automatically translated to 
`∀ (b : finset α), ∀ (h : b ∈ p.block_set)`.   Similarly, `∀ (a ∈ b)`
becomes `∀ (a ∶ α), ∀ (k : a ∈ b)`. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 intros b b_in_block_set a a_in_b,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Because of the notational magic mentioned above, applying the `intros`
tactic to the first quantifier gives us two arguments: a finite set
`b` and a proof that `b` lies in the block set.  Similarly, the 
second quantifier gives a term `a` and a proof that it lies in `b`. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 rcases (mem_image.mp b_in_block_set) with ⟨a1,a1_in_univ,a1_block⟩, 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here `b_in_block_set` says that `b` is in the image of the map 
`p.block`, and we can apply the theorem `mem_image.mp` to unwrap the
definition of the image and conclude that there exists `a1` with 
`b = p.block a1`.  We can then use the `rcases` tactic to give us 
`a1` together with a proof that `p.block a1 = b`.
<br/><br/>
There is a slight wrinkle here.  Images are defined for finite sets, 
which need not fill the whole domain type of the function whose image
we consider.  In the current case we define the block set to be the 
image of the universal finite subset of `α`, given by the posited 
`fintype` instance for `α`.  Because of this, the `rcases` tactic
also gives us a proof of the uninteresting fact that `a1 ∈ univ` 
as well as the interesting fact that `p.block a1 = b`.
<br/><br/>
As we have discussed previously, this kind of use of the `rcases`
tactic is only valid when we are proving a theorem rather than 
defining a function, so that dependence on the choice of `a1` is
harmless.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have : a ∈ p.block a1 := a1_block.symm.subst a_in_b,
 exact (eq.subst a1_block (p.ispart.right a a1 this).symm)
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now have `a ∈ b = p.block a1` which gives `p.block a = p.block a1`
by the partition axiom, and we can put this together to get 
`b = p.block a`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance block_set_deceq (p : partition α) : decidable_eq p.block_type :=
 by apply_instance
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We need a decision procedure for equality in the type `p.block_type`.
The `apply_instance` tactic is clever enough to deal with this
automatically.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance block_set_fintype (p : partition α) : fintype p.block_type := 
 { elems := attach p.block_set,
   complete := mem_attach p.block_set
 }

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now construct an instance of `fintype p.block_type`, showing that 
`p.block_type` is finite.  This is completely formal because 
`p.block_type` was constructed by starting with the finite set 
`p.block_set` and converting it to a separate type.  The relevant 
function `finset.attach` and theorem `finset.mem_attach` come from
<span class="mathlib">data/finset.lean</span>.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma block_type_card (p : partition α) : 
 fintype.card p.block_type = p.rank := 
  @finset.card_attach (finset α) p.block_set
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We defined the rank to be the cardinality of `p.block_set`.  Here we
just record that that is the same as the cardinality of `p.block_type`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

theorem eq_of_block_set_eq {p1 p2 : partition α} :
 ((p1 = p2) ↔ (p1.block_set = p2.block_set)) :=
begin 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now show that two partitions are equal iff they have the same 
block set.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove a bidirectional implication.  The `split` tactic
converts this to two goals, one for each direction.  Below we will 
deal with the first goal in one set of curly brackets, and with the 
second in another set of curly brackets.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 { intro e, rw[e] },
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The left-to-right direction is trivial: the `intro` tactic gives us 
a term `e : p1 = p2` and leaves us with the goal of proving 
`p1.block_set = p2.block_set`, which we do by rewriting with `e`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 { 
   intro block_set_eq,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We assume given a proof that `p1.block_set = p2.block_set`; the goal
is now to prove that `p1 = p2`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
   apply eq_of_block_eq.mpr,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We apply the right-to-left direction of the theorem `eq_of_block_eq`
that we proved earlier.  The `apply` tactic works backwards from the 
goal rather than forwards from the facts that we have already 
established or assumed.  In the present case, it changes the goal so
that we now need to prove that `p1.block = p2.block`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
   funext a,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove that the functions `p1.block` and `p2.block` are 
equal.  It will suffice to show that `p1.block a = p2.block a` for 
all `a`, and the tactic `funext a` changes the goal in this way.
(We could just have written `funext`, but then the arbitrary element
of `α` would be called `x` rather than `a`, which is less natural 
here.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
   let b1 := p1.block a,
   have b1_in_block_set : b1 ∈ p1.block_set :=
     (mem_image_of_mem p1.block (mem_univ a)),
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We define `b1` to be the block of `a` with respect to `p1`, and we 
prove that this lies in the block set for `p1`.  The proof uses the
theorem `mem_univ` (saying that everything is in the universal 
subset of `α`) and the theorem `mem_image_of_mem` (saying that 
images behave in the way that they are supposed to).
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
   rw[block_set_eq] at b1_in_block_set,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have seen that `b1` is in the block set for `p1`, and we now 
rewrite this fact using the assumed equality 
`p1.block_set = p2.block_set`.  The same name `b1_in_block_set` now
refers to a proof that `b1 ∈ p2.block_set`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
   exact block_set_rep p2 b1 b1_in_block_set a (p1.mem_block a)
 }
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now want to use the lemma `block_set_rep` to prove our goal that 
`p1.block a = p2.block a`.  This lemma needs five arguments and we
have the first four of them to hand.  The last argument needs to be
a proof that `a ∈ p1.block a`, and this is supplied by the theorem
`mem_block` that we proved earlier.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def of_block_set (blocks : finset (finset α))
 (no_empty_blocks : ∀ b ∈ blocks, b ≠ ∅)
 (unique_block : ∀ a : α, ∃! b, b ∈ blocks ∧ a ∈ b) : 
 { p : partition α // p.block_set = blocks } := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now reconcile our approach to partitions with an obvious alternative
approach.  Suppose that `blocks` is a finite set of finite subsets of
`α`, and we have proofs that none of the sets in `blocks` is empty, 
and that each element `a : α` lies in precisely on of the sets in 
`blocks`.  It is then fairly clear that there is a partition whose
block set is `blocks`.  The present function is a Lean implementation 
of this construction.  In principle we could define a function that
produces the relevant partition, and then separately prove a theorem
showing that the block set of this partition is the family `blocks`
that we started with.  However, if we proceded in that way, then the 
definition and the theorem would share a substantial amount of logic,
which would be inefficient and inelegant.  It is better to do what 
we do here and define a function that returns a term `x` of type 
`{ p : partition α // p.block_set = blocks }`, so that `x.val` is
a partition and `x.property` is a proof that it has the expected 
block set.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 let blocks_for : ∀ (a : α), finset (finset α ) := 
  λ a, blocks.filter (λ b, a ∈ b),
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We define `blocks_for a` to be the set of blocks that contain `a`.  
Of course, our assumptions mean that there is precisely one such block.
Our definition uses the function `finset.filter`, which takes a 
finite set and a decidable predicate, and returns the finite subset 
where that predicate is satisfied.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let block_aux :
  ∀ (a : α), { b : finset α // blocks_for a = finset.singleton b } := 
  λ a , finset.witness blocks (λ b, a ∈ b) (unique_block a),
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now use the function `finset.witness`.  Note that this is not in
the `mathlib` library, but is taken from an auxiliary file 
`unique_element.lean` that was written together with the present file.
Given a finite set `s`, a decidable predicate `p`, and a proof that 
there is a unique element satisfying `p`, the function `finset.witness`
returns that element together with a proof of its key property.  
<br/><br/>
This is a bit more subtle than it appears.  In the absence of
finiteness and decidability, a proof `h` of `∃! x, p x` is not enough 
to compute the relevant value of `x`.  The reason is essentially that 
Lean implements proof irrelevance, so we cannot extract any of the
information that went into the proof of `∃! x, p x`.  If we do not
care about computability then we can write `import classical` and
then use `classical.some h` to produce `x`.  Alternatively, if we
have finiteness and decidability then we can produce `x` in a 
computable way by walking through the finite list of possibilities 
for `x` and checking whether each of them has property `p`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let block : α → finset α := λ a, (block_aux a).val,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
`block_aux a` is a structure consisting of a finite subset of `α` 
together with a proof that it has certain properties.  To define the
block map of the partition that we are trying to construct, we just
use the finite subset and ignore the proof.  However, we will use the
proof later when we verify that we have constructed a partition and 
that it has the expected block set.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let ispart : is_partition block := 
 begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start to construct a proof that our block map has the properties
required for a partition.  This is a complex proof which we will do
mostly in tactic mode, so we start by opening a `begin ... end` block.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove `is_partition blocks`, which is by definition a
conjunction of two clauses.  The `split` tactic makes these two 
clauses into separate goals.
<br/><br/>
Note that `is_partition blocks` is not visibly a conjunction, but the
`split` tactic is clever enough to unwind the definitions until that
form becomes apparent.  One might prefer to start with  
`dsimp[is_partition]`.  That would apply the definition
of `is_partition` to give a an explicit conjunction, to which we 
could apply the `split` tactic.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {intro a,
   let w := block_aux a,
   have h : w.val ∈ finset.singleton w.val := mem_singleton_self _,
   rw[← w.property] at h,
   exact (mem_filter.mp h).right
  },
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In this set of curly brackets, we prove the first clause, that 
`a ∈ block a` for all `a`.  We start by defining `w := block_aux a`,
so that `block a = w.val`, and `w.property` is a proof that the set 
of blocks containing `a` is `{w.val}`.  The theorem 
`mem_singleton_self` says that `w.val ∈ {w.val}`.  We rewrite this 
fact using the equation `w.property`.  We want to replace the right 
hand side of `w.property` by the left hand side, so the appropriate
syntax is `rw[← w.property]` or `rw[w.property.symm]` rather than 
`rw[w.property]`.  (The arrow can be entered as `\left` or just `\l`.)
After this rewrite, we know that `w.val` lies in `blocks_for a`, 
which was defined using `finset.filter`.  The theorem `mem_filter.mp`
tells us that `finset.filter` behaves in the expected way, so we
can use it to deduce that `w.val ∈ blocks ∧ a ∈ w.val`.  We can 
use the notation `(mem_filter.mp h).right` to extract the second
half of this conjunction, and this satisfies our goal.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {intros a1 a2,
   let w1 := block_aux a1,
   let w2 := block_aux a2,
   let b1 := w1.val,
   let b2 := w2.val,
   have b1_in_B1 : b1 ∈ finset.singleton b1 := mem_singleton.mpr rfl,
   have b2_in_B2 : b2 ∈ finset.singleton b2 := mem_singleton.mpr rfl,
   rw[← w1.property] at b1_in_B1,
   rw[← w2.property] at b2_in_B2,
   have b1_in_blocks : b1 ∈ blocks := (mem_filter.mp b1_in_B1).1,
   have b2_in_blocks : b2 ∈ blocks := (mem_filter.mp b2_in_B2).1,
   have a1_in_b1 : a1 ∈ b1 := (mem_filter.mp b1_in_B1).2,
   have a2_in_b2 : a2 ∈ b2 := (mem_filter.mp b2_in_B2).2,
   intro a1_in_b2,
   have b2_in_B1 : b2 ∈ blocks_for a1 := 
    mem_filter.mpr ⟨ b2_in_blocks , a1_in_b2 ⟩,
   rw[w1.property] at b2_in_B1,
   exact (mem_singleton.mp b2_in_B1).symm
  }
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In this set of curly brackets, we prove the second clause, that if 
`a1 ∈ block a2` then `block a1 = block a2`.  A significant part of this
just repeats for `a1` and `a2` the steps that we took for `a` in the
previous set of curly brackets.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 end,
 let p : partition α := ⟨ block , ispart ⟩,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now package together the map `block` and the proof `ispart` to
construct the partition that we wanted to construct.
<br/><br/>
There is a point to notice here about naming.  A partition `p` is
a structure with two members called `p.block` and `p.ispart`.  We
have two local variables called `block` and `ispart`, and we construct
a partition `p` such that the member `p.block` is the local variable
`block` and the member `p.ispart` is the local variable `ispart`.
This correspondence of names is convenient and natural but not
compulsory.  Instead of `let block = ...` and `let ispart = ...` and
let `p = ⟨block,ispart⟩` we could equally well have written 
`let foo = ...` and `let bar = ...` and `let p := ⟨foo,bar⟩`.  The 
definition of `p` could also have been written 
`let p := {block := foo, ispart := bar}`.  (Note that in this form 
we have curly brackets rather than angle brackets.)  Similarly, with
our current names for local variables we could have written 
`let p := { block := block, ispart := ispart}`.  
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 have ok : p.block_set = blocks := 
 begin
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start to prove that the block set of our partiton `p` is the 
same as the block set that we were originally given.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  ext b,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove that two finite sets are equal.  The tactic 
`ext b` converts this to an equivalent goal: a generic element `b`
lies in the first set iff it lies in the second set.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove a bidirectional implication.  The `split` tactic
divides this into two goals, one for each direction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {
    intro b_in_blocks_p,
    rcases mem_image.mp b_in_blocks_p with
      ⟨ a , a_in_univ , p_block_a_eq_b ⟩,
    let w := block_aux a,
    have w_val : w.val = p.block a := rfl,
    rw[p_block_a_eq_b] at w_val,
    have b_in_B : b ∈ finset.singleton w.val := 
     eq.subst (congr_arg finset.singleton w_val.symm)
      (mem_singleton.mpr rfl),
    rw[← w.property] at b_in_B,
    exact (mem_filter.mp b_in_B).1,
  },{
    intro b_in_blocks,
    have b_not_empty : b ≠ ∅ := no_empty_blocks b b_in_blocks,
    rcases exists_mem_of_ne_empty b_not_empty with ⟨ a , a_in_b ⟩ ,
    have b_in_B : b ∈ blocks_for a
     := mem_filter.mpr ⟨ b_in_blocks , a_in_b ⟩ ,
    let w := block_aux a,
    rw[w.property] at b_in_B,
    have b_eq_block_a : b = block a := mem_singleton.mp b_in_B,
    have t : ∃ x, ∃ x_in_univ : x ∈ univ, block x = b := 
     ⟨ a , mem_univ a , b_eq_block_a.symm ⟩, 
    exact (@mem_image α (finset α) _ block univ b).mpr t
  }
 end,
 exact ⟨ p , ok ⟩   
end

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def to_setoid (p : partition α) : setoid α := {
  r := λ a1 a2 : α , p.block a1 = p.block a2,
  iseqv := ⟨λ a : α, rfl,
            λ _ _ e, e.symm,
            λ _ _ _ e1 e2, e1.trans e2 ⟩ 
}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define a function which converts a partition to a setoid 
structure.  A setoid structure is by definition a relation on `α`
(encoded as a map `r : α → α → Prop`) together with a proof that it
is an equivalence relation.  The latter is encoded as a structure
with three members, which are proofs of reflexivity, symmetry and
transitivity.  In our case the relevant relation is just 
`r a1 a2 := (p.block a1 = p.block a2)`, and the equivalence relation 
axioms follow immediately from the reflexivity, symmetry and 
transitivity of the equality relation on `finset α`.  There is a tiny
subtlety about ensuring that we set things up with the right mix
of explicit and implicit arguments.  
<br/><br/>
(In Lean, quotient structures work in much the same way as in 
classical mathematics.  The name "setoid" comes from other proof 
assistant systems in which this is not the case.  In those systems,
one often has to consider a pair consisting of a type and an 
equivalence relation rather than forming the quotient.  Such a
pair is called a "setoid".)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance decidable_to_setoid (p : partition α):
 decidable_rel ((to_setoid p).r) :=
begin
 dsimp[to_setoid],
 apply_instance
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now show that our equivalence relation is decidable.  It seems that
we need to tell Lean explicitly to apply the definition of `to_setoid`,
for which we use the `dsimp` tactic. After that, the `apply_instance` 
tactic succeeds in filling in the required details automatically.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def of_setoid (s : setoid α) [decidable_rel s.r] : partition α := 
begin 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now define the inverse construction, where we start with a 
decidable setoid structure and produce a partition.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let block : α → finset α := λ a , univ.filter (@setoid.r α s a),
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We define the block map.  In ordinary mathematical notation, this 
would be `block a = { x : a ≈ x }`.  Lean's notational conventions
for setoid structures are consistent with the more general conventions
for typeclass instances and are based on the idea that a given type
`α` probably has only one interesting setoid structure that we want
to work with.  Of course this is not consistent with the current
application.  We have therefore preferred to make all arguments 
explicit and write `@setoid.r α s a x` for the proposition that 
`a ≈ x` with respect to `s`.  We can also leave out the final 
argument and write `@setoid.r α s a` for the predicate sending `x` to 
`a ≈ x`.  The set `block a` is obtained by filtering the universal 
set, keeping only the elements that satisfy this predicate.  It 
would also work to write `setoid.r a` in place of `@setoid.r α s a`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 let ispart : is_partition block := 
 begin 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start writing the proof that the above block map satisfies the
partition axioms.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  dsimp[is_partition],split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We apply the definition of the predicate `is_partition`.  The goal is
then to prove a conjunction of two clauses, and the `split` tactic
converts this to a pair of goals, one for each clause.  It is not 
really necessary to do `dsimp[is_partition]` first, but this may make
it slightly easier to follow the proof.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {intro a,apply mem_filter.mpr,split,exact (mem_univ a),exact (setoid.refl a)},
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have written the proof of the first clause in a terse style.  In
VS Code, you can see how the various steps work by placing your cursor
after one of the commas and examining the goal state in the Lean 
Messages window.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {intros a1 a2 a1_in_b2,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For the second clause, we give ourselves `a1` and `a2` with 
`a1 ∈ block a2`, and our goal is to prove that `block a1 = block a2`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  ext x,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal was to prove that the finite sets `block a1` and `block a2`
are the same.  The theorem `finset.ext'` says that two finite sets 
are equal if an arbitrary element lies in the first iff it lies in the
second.  This theorem is marked with the `[extensionality]` attribute,
so the `ext` tactic finds it and uses it.  Our goal is now to prove 
that `x ∈ block a1 ↔ x ∈ block a2`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  simp only [mem_filter,mem_univ x,mem_univ a1,true_and] at a1_in_b2 ⊢,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We apply the definition of the `block` map to convert all statements
like `u ∈ block v` to statements like `u ∈ univ ∧ v ≈ u`.  We do 
this both in the hypothesis `a1_in_b2` and in the goal (denoted here 
by `⊢`).  By including `mem_univ x`, `mem_univ a` and `true_and` in 
the simplification rules, we also get rid of the spurious `u ∈ univ` 
clauses.  The hypothesis `a1_in_b2` has now become `a2 ≈ a1`, 
and the goal is `a1 ≈ x ↔ a2 ≈ x`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  split,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our goal is to prove a bidirectional implication.  The split tactic
converts this to a pair of goals, one for each direction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exact setoid.trans a1_in_b2}, 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our first goal is now to prove `a2 ≈ x → a1 ≈ x`.  We 
could do the proof as follows: write `intro a2_eq_x` to give a 
hypothesis `a2 ≈ x`, then invoke the transitivity rule in the form 
`setoid.trans a1_in_b2 a2_eq_x` to give a proof of `a1 ≈ x`, which 
we can use in the `exact` tactic to satisfy the goal.  However, 
it is in fact equivalent to skip the introduction step and just 
write `exact setoid.trans a1_in_b2`. 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
  {exact setoid.trans (setoid.symm a1_in_b2)}, 
 } 
 end,
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our second goal is to prove `a1 ≈ x → a2 ≈ x`.  Recall that `a1_in_b2` 
is now a proof of `a1 ≈ a2`.  We can write `(setoid.symm a1_in_b2)`
to get a proof of `a2 ≈ a1`, and then proceed as in the first goal.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
 exact ⟨ block , ispart ⟩ 
end 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We finish the definition by combining `block` and `ispart` into a
partition structure.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

def fiber_partition {α β : Type}
 [decidable_eq α] [fintype α] [decidable_eq β] 
  (f : α → β) : partition α := 
{ block := λ a, (@univ α _).filter (λ x, f x = f a),
  ispart := begin
   dsimp[is_partition],split,
   {intro a,apply mem_filter.mpr,simp[mem_univ]},
   {intros a1 a2,
     intro h,
     have e : f a1 = f a2 := (mem_filter.mp h).right,
     congr,ext,simp[e],
   }
  end
}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given a map `f : α → β`, we can partition `α` using the fibers of `f`.
(We need to ignore any fibers that are empty, but with our framework of
definitions we do not need any explicit logic for that.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma fiber_partition_blocks {α β : Type}
 [decidable_eq α] [fintype α] [decidable_eq β] 
  (f : α → β) (a1 a2 : α) :
   (fiber_partition f).block a1 = (fiber_partition f).block a2
    ↔ f a1 = f a2 := 
begin
 have h0 : a1 ∈ (fiber_partition f).block a2 ↔ f a1 = f a2 := 
  by simp[fiber_partition,mem_filter],
 split,
 {intro e,
  exact h0.mp (e.subst ((fiber_partition f).mem_block a1)),
 },{
  intro e,
  have h1 : a1 ∈ ((fiber_partition f).block_alt a2).val := h0.mpr e,
  exact (block_val_eq_of_mem h1).symm
 }
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A basic lemma showing that the block map for the fiber partition 
behaves as expected.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma fiber_partition_blocks_alt {α β : Type}
 [decidable_eq α] [fintype α] [decidable_eq β] 
  (f : α → β) (a1 a2 : α) :
   (fiber_partition f).block_alt a1 = (fiber_partition f).block_alt a2
    ↔ f a1 = f a2 := 
begin
 split; intro e,
 {exact (fiber_partition_blocks f a1 a2).mp (partition.block_alt_eq.mpr e)},
 {exact partition.block_alt_eq.mp ((fiber_partition_blocks f a1 a2).mpr e)}
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This is the same as the previous lemma except that blocks of `p` are
regarded as terms of type `p.block_type` rather than `finset α`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

section fintype
variable (α) 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now start a new section in which we will prove that `partition α` is
finite.  In more detail, we previously assumed that we were given a
term of type `fintype α`, and we use it to construct a term of type
`fintype (partition α)`.  Lean already knows many rules for 
constructing `fintype` instances, and we just need to combine these
in an appropriate way.
<br/><br/>
The `fintype` instance on `partition α` will not depend on any 
auxiliary variables from which we could infer the value of `α`.  We
therefore need to switch to treating `α` as an explicit rather than
implicit variable.  This is the effect of the line `variable (α)`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

private def partition_elems0 : finset (α → (finset α)) := 
  (@univ (α → (finset α)) _).filter(is_partition)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We will build up a definition in several steps.  The individual steps
are not so interesting, so we mark the definitions as "private".  This
means that they will not be visible outside the current section.   
<br/><br/>
In this first 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

private def partition_elems1 :=
 { p : α → (finset α) // p ∈ (partition_elems0 α)}  

private def partition_elems2 : finset (partition_elems1 α) :=
 (partition_elems0 α).attach

private def partition_of_elems1 (p : partition_elems1 α) : (partition α) :=
begin 
 exact 
 { block := p.val,
   ispart := (mem_filter.mp p.property).2
 }
end

lemma partition_of_elems1_block (p : partition_elems1 α) :
 (partition_of_elems1 α p).block = p.val :=
begin
 rcases p with ⟨ p_block , p_in_elems ⟩,
 dsimp[partition_of_elems1],
 exact rfl
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
def partition_elems : finset (partition α) :=
 (partition_elems2 α).image (partition_of_elems1 α)
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We are now ready to give the definition of the finset of all 
partitions.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

lemma partition_elems_complete : 
 ∀ p : partition α, p ∈ partition_elems α := 
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now state the key fact that every partition does indeed appear
in the finset that we have constructed.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/
begin
 intro p,
 rcases p with ⟨ p_block , p_ispart ⟩,
 let p_in_elems0 : p_block ∈ (partition_elems0 α) := 
  mem_filter.mpr ⟨mem_univ p_block,p_ispart⟩,
 let p1 : partition_elems1 α := ⟨p_block, p_in_elems0⟩,
 have p1_in_elems2 : p1 ∈ partition_elems2 α := 
  mem_attach (partition_elems0 α) p1,
 let p2 : partition α := partition_of_elems1 α p1,
 have p2_in_elems : p2 ∈ partition_elems α := 
  mem_image_of_mem (partition_of_elems1 α) p1_in_elems2,
 have p2_eq_p : p2 = ⟨ p_block , p_ispart ⟩  := 
 begin
  apply eq_of_block_eq.mpr,
  by apply partition_of_elems1_block
 end,
 exact eq.subst p2_eq_p p2_in_elems
end
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

instance partition_fintype : fintype (partition α) := {
  elems := partition_elems α,
  complete := partition_elems_complete α 
}
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We can now package what we have done as an instance of 
`fintype (partition α)`, or in other words a proof that the set 
of partitions is finite.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

end fintype
/-~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~-/

section cofunctor 

variables {α} {β : Type*} {γ : Type*} 
 [decidable_eq β] [decidable_eq γ] [fintype β] [fintype γ]
  (f : α → β) (g : β → γ)

def cofunctor (q : partition β) : partition α := {
 block := λ a, univ.filter (λ x, f x ∈ q.block (f a)),
 ispart := begin
  split,
  {intro a,simp[q.ispart.left (f a)]},
  begin
   intros a1 a2 f_in_block,
   have a1_in_b2 : f a1 ∈ (q.block_alt (f a2)).val :=
    (mem_filter.mp f_in_block).right,
   have b1_eq_b2 := block_val_eq_of_mem a1_in_b2,
   dsimp[block_alt] at b1_eq_b2,
   ext,simp[b1_eq_b2]
  end
 end
}

lemma cofunctor_id : cofunctor (@id α) = @id (partition α) := 
begin
 ext p a0 a1,simp[cofunctor],
end

lemma cofunctor_comp : cofunctor (g ∘ f) = (cofunctor f) ∘ (cofunctor g) :=
begin
 ext p a0 a1,simp[cofunctor],
end

end cofunctor

section isofunctor

variables {α} {β : Type*} {γ : Type*} 
 [decidable_eq β] [decidable_eq γ] [fintype β] [fintype γ]
  (f : α ≃ β) (g : β ≃ γ)

def isofunctor : (partition α) ≃ (partition β) := {
  to_fun := cofunctor f.inv_fun,
  inv_fun := cofunctor f.to_fun,
  left_inv := begin
   intro p,
   exact calc
    (cofunctor f.to_fun) ((cofunctor f.inv_fun) p)
      = ((cofunctor f.to_fun) ∘ (cofunctor f.inv_fun)) p : rfl
    ... = (cofunctor (f.inv_fun ∘ f.to_fun)) p : by rw[← cofunctor_comp]
    ... = (cofunctor id) p : by rw[← ((funext f.left_inv) : (f.inv_fun ∘ f.to_fun = id))]
    ... = id p : by rw[cofunctor_id]
    ... = p : rfl
  end,
  right_inv := begin
   intro q,
   exact calc
    (cofunctor f.inv_fun) ((cofunctor f.to_fun) q)
      = ((cofunctor f.inv_fun) ∘ (cofunctor f.to_fun)) q : rfl
    ... = (cofunctor (f.to_fun ∘ f.inv_fun)) q : by rw[← cofunctor_comp]
    ... = (cofunctor id) q : by rw[← ((funext f.right_inv) : (f.to_fun ∘ f.inv_fun = id))]
    ... = id q : by rw[cofunctor_id]
    ... = q : rfl
  end,
}

lemma isofunctor_id : isofunctor (equiv.refl α) = equiv.refl (partition α) :=
begin
 apply equiv.eq_of_to_fun_eq,
 dsimp[isofunctor,equiv.refl,cofunctor],
 exact cofunctor_id
end

lemma isofunctor_comp : isofunctor (f.trans g) = (isofunctor f).trans (isofunctor g) :=
begin
 apply equiv.eq_of_to_fun_eq,
 dsimp[isofunctor,equiv.trans,cofunctor],
 apply cofunctor_comp,
end

end isofunctor

open equiv

variables {α} {β : Type*} [decidable_eq β] [fintype β] (f : α ≃ β) 

theorem card_partitions_eq_card_partitions_fin {n : ℕ} (h : fintype.card α = n) :
  card (partition α) = card (partition (fin n)) :=
begin
  rw ←h,
  refine trunc.induction_on (fintype.equiv_fin α) _,
  intro e,
  exact eq.subst h fintype.card_congr (isofunctor e)
end

instance : has_le (partition α) := 
 ⟨ λ p1 p2 : partition α, ∀ a, p2.block a ⊆ p1.block a ⟩ 

instance decidable_le (p1 p2 : partition α) : decidable (p1 ≤ p2) :=
begin
 dsimp[partition.has_le],
 apply_instance
end

@[simp] theorem le.refl (p : partition α) : p ≤ p :=
by dsimp[partition.has_le]; simp

theorem le.trans {p1 p2 p3 : partition α} : 
 p1 ≤ p2 → p2 ≤ p3 → p1 ≤ p3 := 
begin
 dsimp[partition.has_le],
 intros e1 e2 a,
 exact (subset.trans (e2 a) (e1 a))
end

theorem le.antisymm {p1 p2 : partition α} :
 p1 ≤ p2 → p2 ≤ p1 → p1 = p2 := 
begin
 dsimp[partition.has_le],
 intros e1 e2,
 apply eq_of_block_eq.mpr,
 funext a,
 exact subset.antisymm (e2 a) (e1 a)
end

def bot : partition α := {
 block := λ a, univ,
 ispart := by {split;intros;simp[mem_univ]}
}

def top : partition α := {
 block := @finset.singleton α,
 ispart := begin
  split,
  {apply mem_singleton_self},
  {intros a1 a2 h,rw[mem_singleton.mp h]}
 end
}

def sup (p1 p2 : partition α) : partition α := 
begin 
  let block : α → finset α :=
    λ a, (p1.block a) ∩ (p2.block a), 
  let ispart : is_partition block := 
  begin
   dsimp[is_partition],split,
   {
     intro a,
     exact mem_inter.mpr ⟨p1.ispart.left a,p2.ispart.left a⟩,
   },
   {intros a1 a2,
   let b11 := p1.block a1,
   let b12 := p2.block a1,
   let b21 := p1.block a2,
   let b22 := p2.block a2,
   let b1 := b11 ∩ b12,
   let b2 := b21 ∩ b22,
   intro a1_in_b2,
   have a1_in_b21 : a1 ∈ b21 := 
     (mem_inter.mp (a1_in_b2 : a1 ∈ b2)).1,
   have a1_in_b22 : a1 ∈ b22 := 
     (mem_inter.mp (a1_in_b2 : a1 ∈ b2)).2,
   have b11_eq_b21 : p1.block a1 = p1.block a2 :=
      (p1.ispart.right a1 a2) a1_in_b21,
   have b12_eq_b22 : p2.block a1 = p2.block a2 :=
      (p2.ispart.right a1 a2) a1_in_b22,
   dsimp[block],
   by rw[b11_eq_b21,b12_eq_b22]
   }
  end,
  exact ⟨ block , ispart ⟩ 
end

instance partial_order_of_partitions : partial_order (partition α) :=
{ le := has_le.le,
  le_refl := @partition.le.refl α _ _,
  le_trans := @partition.le.trans α _ _,
  le_antisymm := @partition.le.antisymm _ _ _
}

end partition
end combinatorics