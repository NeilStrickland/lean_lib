import tactic.interactive
import tactic.monotonicity

#check traversable

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
--
#check tactic.interactive.apply_field 
--
#check tactic.interactive.apply_instance 
--
#check tactic.interactive.apply_opt_param 
--
#check tactic.interactive.apply_rules 
--
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
#check tactic.interactive.guard_class 
#check tactic.interactive.guard_expr_eq 
#check tactic.interactive.guard_expr_eq' 
#check tactic.interactive.guard_hyp 
#check tactic.interactive.guard_hyp' 
#check tactic.interactive.guard_hyp_nums 
#check tactic.interactive.guard_tags 
#check tactic.interactive.guard_target 
#check tactic.interactive.guard_target' 
#check tactic.interactive.h_generalize 
-- For dealing with casts and heterogenous equality
#check tactic.interactive.has_to_format 
#check tactic.interactive.has_to_tactic_format_mono_ctx 
#check tactic.interactive.has_to_tactic_format_mono_function 
#check tactic.interactive.has_to_tactic_format_mono_law 
#check tactic.interactive.have 
#check tactic.interactive.haveI 
#check tactic.interactive.have_field 
#check tactic.interactive.hide_meta_vars' 
#check tactic.interactive.iclarify 
#check tactic.interactive.induction 
#check tactic.interactive.injection 
#check tactic.interactive.injections 
#check tactic.interactive.injections_and_clear 
#check tactic.interactive.intro 
#check tactic.interactive.introI 
#check tactic.interactive.intros 
#check tactic.interactive.introsI 
#check tactic.interactive.introv 
#check tactic.interactive.isafe 
#check tactic.interactive.itactic 
#check tactic.interactive.iterate 
#check tactic.interactive.last_two 
#check tactic.interactive.lawful_functor_derive_handler 
#check tactic.interactive.lawful_functor_derive_handler' 
#check tactic.interactive.lawful_traversable_derive_handler 
#check tactic.interactive.lawful_traversable_derive_handler' 
#check tactic.interactive.left 
#check tactic.interactive.let 
#check tactic.interactive.letI 
#check tactic.interactive.list.minimum_on 
#check tactic.interactive.list_cast_of 
#check tactic.interactive.map_constructor 
#check tactic.interactive.map_field 
#check tactic.interactive.mapply 
#check tactic.interactive.match_ac 
#check tactic.interactive.match_ac' 
#check tactic.interactive.match_ac'._main 
#check tactic.interactive.match_assoc 
#check tactic.interactive.match_chaining_rules 
#check tactic.interactive.match_imp 
#check tactic.interactive.match_prefix 
#check tactic.interactive.match_prefix._main 
#check tactic.interactive.match_rule 
#check tactic.interactive.match_target 
#check tactic.interactive.min_tac 
#check tactic.interactive.mk_assumption_set 
#check tactic.interactive.mk_congr_args 
#check tactic.interactive.mk_congr_law 
#check tactic.interactive.mk_fun_app 
#check tactic.interactive.mk_map 
#check tactic.interactive.mk_mapp' 
#check tactic.interactive.mk_one_instance 
#check tactic.interactive.mk_pattern 
#check tactic.interactive.mk_rel 
#check tactic.interactive.mk_traverse 
#check tactic.interactive.mono 
#check tactic.interactive.monotoncity.check 
#check tactic.interactive.monotoncity.check_rel 
#check tactic.interactive.nested_map 
#check tactic.interactive.nested_traverse 
#check tactic.interactive.one_line 
#check tactic.interactive.parse_ac_mono_function 
#check tactic.interactive.parse_assoc_chain 
#check tactic.interactive.parse_assoc_chain' 
#check tactic.interactive.parse_config 
#check tactic.interactive.pi_head 
#check tactic.interactive.pi_instance 
#check tactic.interactive.propagate_tags 
#check tactic.interactive.rcases 
#check tactic.interactive.rec.to_tactic_format 
#check tactic.interactive.record_lit 
#check tactic.interactive.recover 
#check tactic.interactive.refine 
#check tactic.interactive.refine_one 
#check tactic.interactive.refine_recursively 
#check tactic.interactive.refine_struct 
#check tactic.interactive.refl 
#check tactic.interactive.reflexivity 
#check tactic.interactive.rename 
#check tactic.interactive.repeat 
#check tactic.interactive.repeat_or_not 
#check tactic.interactive.repeat_until 
#check tactic.interactive.repeat_until_or_at_most 
#check tactic.interactive.repeat_until_or_at_most._main 
#check tactic.interactive.replace 
#check tactic.interactive.resetI 
#check tactic.interactive.revert 
#check tactic.interactive.revert_all 
#check tactic.interactive.rewrite 
#check tactic.interactive.right 
#check tactic.interactive.rintro 
#check tactic.interactive.rintros 
#check tactic.interactive.rsimp 
#check tactic.interactive.rw  
#check tactic.interactive.rwa 
#check tactic.interactive.safe 
#check tactic.interactive.same_function 
#check tactic.interactive.same_operator 
#check tactic.interactive.show 
#check tactic.interactive.side 
#check tactic.interactive.side_conditions 
#check tactic.interactive.simp 
#check tactic.interactive.simp_core 
#check tactic.interactive.simp_core_aux 
#check tactic.interactive.simp_functor 
#check tactic.interactive.simp_intros 
#check tactic.interactive.simpa 
#check tactic.interactive.skip 
#check tactic.interactive.solve1 
#check tactic.interactive.solve_by_elim 
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
