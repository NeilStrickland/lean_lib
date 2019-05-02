import tactic.interactive
import tactic.monotonicity
import data.finset
/-
 To do: also document derive_handlers
-/

#check tactic.interactive.ac_mono
-- Deduce inequalities using known monotonicity properties of functions
#check tactic.interactive.abstract
-- Tactical to record the argument used as a lemma, as well as solving the goal
#check tactic.interactive.ac_reflexivity 
-- Proves an equation using commutativity and associativity
#check tactic.interactive.admit 
-- Sorry
#check tactic.interactive.all_goals 
-- Apply a tactic to all goals
#check tactic.interactive.any_goals 
-- Apply a tactic to any goal where it works
#check tactic.interactive.apply
--
#check tactic.interactive.apply_assumption 
-- Like apply, but looks in the local context for applicable things
#check tactic.interactive.apply_auto_param 
-- Not used directly in mathlib, but used indirectly by the `tidy` tactic.
#check tactic.interactive.apply_field 
--
#check tactic.interactive.apply_instance 
-- Use type class resolution to close the main goal.  For example, if we alread
-- have group structures on G and H, and the goal is to give a group structure
-- on G × (ℕ → H), then `apply_instance` will close the goal.
#check tactic.interactive.apply_opt_param 
-- Not used directly in mathlib
#check tactic.interactive.apply_rules 
-- This is like `apply`, except that you supply a list of rules instead of
-- a single rule, and Lean applies any of the rules that are applicable.
#check tactic.interactive.apply_with 
-- Like apply, but with configurable options
#check tactic.interactive.assume 
-- Like intro, but type can be specified
#check tactic.interactive.assumption 
--
#check tactic.interactive.assumption' 
-- Try to apply `assumption` to all goals
#check tactic.interactive.async 
--
#check tactic.interactive.by_cases 
--
#check tactic.interactive.by_contra 
-- Same as by_contradiction
#check tactic.interactive.by_contradiction 
--
#check tactic.interactive.case 
#check tactic.interactive.cases 
#check tactic.interactive.cases_matching  
#check tactic.interactive.cases_type 
#check tactic.interactive.casesm 
#check tactic.interactive.change 
#check tactic.interactive.choose 
#check tactic.interactive.clarify 
#check tactic.interactive.classical 
#check tactic.interactive.clean 
#check tactic.interactive.clean_ids 
#check tactic.interactive.clear 
#check tactic.interactive.coinduction 
#check tactic.interactive.comp_val 
#check tactic.interactive.congr 
#check tactic.interactive.congr' 
#check tactic.interactive.constructor 
#check tactic.interactive.constructor_matching 
#check tactic.interactive.continue 
#check tactic.interactive.contradiction 
#check tactic.interactive.conv 
#check tactic.interactive.convert 
#check tactic.interactive.decidable_eq 
#check tactic.interactive.delete_expr 
#check tactic.interactive.delta 
#check tactic.interactive.derive_functor 
#check tactic.interactive.derive_lawful_functor 
#check tactic.interactive.derive_lawful_traversable 
#check tactic.interactive.derive_map_equations 
#check tactic.interactive.derive_traverse 
#check tactic.interactive.derive_traverse_equations 
#check tactic.interactive.destruct 
#check tactic.interactive.done 
#check tactic.interactive.dsimp 
#check tactic.interactive.dunfold 
#check tactic.interactive.eapply 
#check tactic.interactive.erewrite 
#check tactic.interactive.exact 
#check tactic.interactive.exactI 
#check tactic.interactive.exacts 
#check tactic.interactive.exfalso 
#check tactic.interactive.existsi 
#check tactic.interactive.ext 
#check tactic.interactive.ext1 
#check tactic.interactive.fail_if_success 
#check tactic.interactive.fapply 
#check tactic.interactive.field 
-- No docstring
#check tactic.interactive.filter_instances 
-- No docstring
#check tactic.interactive.find_lemma 
-- No docstring
#check tactic.interactive.find_one_difference 
-- No docstring
#check tactic.interactive.find_rule 
-- No docstring
#check tactic.interactive.finish 
-- No docstring
#check tactic.interactive.focus 
--
#check tactic.interactive.fold_assoc 
-- No docstring
#check tactic.interactive.fold_assoc1 
-- No docstring
#check tactic.interactive.from 
-- Same as `exact`
#check tactic.interactive.fsplit 
-- No docstring
#check tactic.interactive.functor_derive_handler 
--
#check tactic.interactive.functor_derive_handler' 
--
#check tactic.interactive.funext 
--
#check tactic.interactive.generalize
-- Make goal more general
#check tactic.interactive.generalize_a_aux 
--
#check tactic.interactive.generalize_hyp 
-- Similar to generalize
#check tactic.interactive.generalize_proofs 
-- Similar to generalize?
#check tactic.interactive.get_current_field 
-- No docstring
#check tactic.interactive.get_equations_of 
-- No docstring
#check tactic.interactive.get_monotonicity_lemmas 
-- No docstring
#check tactic.interactive.get_operator 
-- No docstring
#check tactic.interactive.get_rule_eqn_lemmas 
-- No docstring
#check tactic.interactive.guard_class 
-- No docstring
#check tactic.interactive.guard_expr_eq 
-- No docstring
#check tactic.interactive.guard_expr_eq' 
-- No docstring
#check tactic.interactive.guard_hyp 
-- Used for writing tests
#check tactic.interactive.guard_hyp' 
-- Used for writing tests
#check tactic.interactive.guard_hyp_nums 
-- No docstring
#check tactic.interactive.guard_tags 
-- No docstring
#check tactic.interactive.guard_target 
-- Used for writing tests
#check tactic.interactive.guard_target' 
-- Used for writing tests
#check tactic.interactive.h_generalize 
-- For dealing with casts and heterogenous equality
#check tactic.interactive.has_to_format 
-- No docstring
#check tactic.interactive.has_to_tactic_format_mono_ctx 
-- No docstring
#check tactic.interactive.has_to_tactic_format_mono_function 
-- No docstring
#check tactic.interactive.has_to_tactic_format_mono_law 
-- No docstring
#check tactic.interactive.have 
--
#check tactic.interactive.haveI 
--
#check tactic.interactive.have_field 
--
#check tactic.interactive.hide_meta_vars' 
-- No docstring
#check tactic.interactive.iclarify 
-- No docstring
#check tactic.interactive.induction 
--
#check tactic.interactive.injection 
-- Apply the fact that constructors are injective.
#check tactic.interactive.injections 
-- Apply the fact that constructors are injective, repeatedly
#check tactic.interactive.injections_and_clear 
-- No docstring
#check tactic.interactive.intro 
--
#check tactic.interactive.introI 
--
#check tactic.interactive.intros 
--
#check tactic.interactive.introsI 
--
#check tactic.interactive.introv 
-- Like intros, but with slightly different behaviour wrt naming 
-- of introduced variables
#check tactic.interactive.isafe 
-- No docstring
#check tactic.interactive.iterate 
-- Apply a tactic repeatedly
#check tactic.interactive.left 
--
#check tactic.interactive.let 
--
#check tactic.interactive.letI 
#check tactic.interactive.list.minimum_on 
-- No docstring
#check tactic.interactive.list_cast_of 
-- No docstring
#check tactic.interactive.map_constructor 
--
#check tactic.interactive.map_field 
--
#check tactic.interactive.mapply 
--
#check tactic.interactive.match_ac 
-- No docstring
#check tactic.interactive.match_ac' 
-- No docstring
#check tactic.interactive.match_ac'._main 
-- No docstring
#check tactic.interactive.match_assoc 
--
#check tactic.interactive.match_chaining_rules 
-- No docstring
#check tactic.interactive.match_imp 
-- No docstring
#check tactic.interactive.match_prefix 
-- No docstring
#check tactic.interactive.match_rule 
-- No docstring
#check tactic.interactive.match_target 
-- Fail if type of target is not as specified
#check tactic.interactive.min_tac 
-- No docstring
#check tactic.interactive.mk_assumption_set 
-- No docstring
#check tactic.interactive.mk_congr_args 
-- No docstring
#check tactic.interactive.mk_congr_law 
-- No docstring
#check tactic.interactive.mk_fun_app 
-- No docstring
#check tactic.interactive.mk_map 
-- Helps to define functors.  You can just specify the effect on 
-- objects and mk_map will try to work out the effect on maps (?)
#check tactic.interactive.mk_mapp' 
-- No docstring
#check tactic.interactive.mk_one_instance 
-- No docstring
#check tactic.interactive.mk_pattern 
-- No docstring
#check tactic.interactive.mk_rel 
-- No docstring
#check tactic.interactive.mk_traverse 
-- Helps to define traversable functors
#check tactic.interactive.mono 
-- Applies monotonicity rules
#check tactic.interactive.nested_map 
--
#check tactic.interactive.nested_traverse 
--
#check tactic.interactive.one_line 
-- No docstring
#check tactic.interactive.rcases 
--
#check tactic.interactive.refine 
-- Like exact, but allows holes
#check tactic.interactive.refine_struct 
-- When defining a structure, this tactic gives a goal for each required field
-- (Compare with hole commands?)
#check tactic.interactive.refl 
--
#check tactic.interactive.reflexivity 
-- Same as refl
#check tactic.interactive.rename 
--
#check tactic.interactive.repeat 
--
#check tactic.interactive.repeat_or_not 
--
#check tactic.interactive.repeat_until 
--
#check tactic.interactive.repeat_until_or_at_most 
--
#check tactic.interactive.replace 
--
#check tactic.interactive.resetI 
--
#check tactic.interactive.revert 
-- Reverse of intro
#check tactic.interactive.revert_all 
--
#check tactic.interactive.rewrite 
-- same as rw
#check tactic.interactive.right
-- If the goal is P ∨ Q, change it to Q.  Also works with other types with 
-- precisely two constructors 
#check tactic.interactive.rintro 
--
#check tactic.interactive.rintros 
-- Same as rintro
#check tactic.interactive.rsimp 
-- No docstring
#check tactic.interactive.rw  
--
#check tactic.interactive.rwa 
-- rw followed by assumption
#check tactic.interactive.safe 
--
#check tactic.interactive.same_function 
-- No docstring
#check tactic.interactive.same_operator 
-- No docstring
#check tactic.interactive.show 
-- Similar to change, but can alo select a goal other than the first one
#check tactic.interactive.simp 
--
#check tactic.interactive.simp_core 
-- Is this the same as simp only[] ?
#check tactic.interactive.simp_functor 
-- No docstring
#check tactic.interactive.simp_intros 
#check tactic.interactive.simpa 
-- Like intros, but with simplification
#check tactic.interactive.skip 
-- Does nothing; only useful in combinators
#check tactic.interactive.solve1 
-- 
#check tactic.interactive.solve_by_elim 
--
#check tactic.interactive.solve_mvar 
#check tactic.interactive.sorry 
#check tactic.interactive.source_fields 
#check tactic.interactive.specialize 
#check tactic.interactive.split 
#check tactic.interactive.split_ifs 
#check tactic.interactive.squeeze_simpa 
#check tactic.interactive.subst 
#check tactic.interactive.subst_vars 
#check tactic.interactive.substs 
#check tactic.interactive.success_if_fail 
#check tactic.interactive.suffices 
#check tactic.interactive.swap 
#check tactic.interactive.symmetry 
#check tactic.interactive.tauto 
#check tactic.interactive.tautology 
#check tactic.interactive.to_expr' 
#check tactic.interactive.trace 
#check tactic.interactive.trace_simp_set 
#check tactic.interactive.trace_state 
#check tactic.interactive.transitivity 
#check tactic.interactive.traversable_derive_handler 
#check tactic.interactive.traversable_derive_handler' 
#check tactic.interactive.traversable_law_starter 
#check tactic.interactive.traverse_constructor 
#check tactic.interactive.traverse_field 
#check tactic.interactive.triv 
#check tactic.interactive.trivial 
#check tactic.interactive.try 
#check tactic.interactive.try_for 
#check tactic.interactive.type_check 
#check tactic.interactive.unfold 
#check tactic.interactive.unfold1 
#check tactic.interactive.unfold_aux 
#check tactic.interactive.unfold_coes 
#check tactic.interactive.unfold_projs 
#check tactic.interactive.unfreezeI 
#check tactic.interactive.unify_with_instance 
#check tactic.interactive.use 
#check tactic.interactive.with_cases 
#check tactic.interactive.with_prefix 
#check tactic.interactive.wlog 
