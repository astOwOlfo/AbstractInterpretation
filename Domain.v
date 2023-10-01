From Coq Require Import ZArith Ensembles.

Require Import Arith.

From AbstractInterpretation Require Import Expression ExpressionSemantics Environment
                                           CompleteBoolDomain Ensembles Order.



Module Type Domain.

Parameter abstract_environment : Type.

Parameter to_concrete : abstract_environment -> Ensemble environment.

Parameter empty_environment : abstract_environment.

Parameter empty_environment_correct : Is_empty (to_concrete empty_environment).

Parameter union : abstract_environment -> abstract_environment -> abstract_environment.

Parameter union_correct : forall (ae1 ae2 : abstract_environment),
                            Subset (Union (to_concrete ae1) (to_concrete ae2))
                                   (to_concrete (union ae1 ae2)).

Parameter widen : abstract_environment -> abstract_environment -> abstract_environment.

Parameter widen_correct : forall (ae1 ae2 : abstract_environment),
                            Subset (Union (to_concrete ae1) (to_concrete ae2))
                                   (to_concrete (widen ae1 ae2)).

Definition widens_to (widened env : abstract_environment) : Prop :=
  exists env', widened = widen env env'.

Parameter to_strict_widens_to_well_founded : well_founded (to_strict widens_to).

Parameter assign : var_id -> int_expression -> abstract_environment -> abstract_environment.

Parameter assign_correct :
  forall (var : var_id)
         (abstract_env : abstract_environment)
         (concrete_env : environment)
         (expr : int_expression)
         (result : Z),
      In (to_concrete abstract_env) concrete_env ->
      int_expression_evaluates concrete_env expr result ->
    In (to_concrete (assign var expr abstract_env))
       (Environment.assign var result concrete_env).

Parameter guard : bool_expression -> abstract_environment -> abstract_environment.

Parameter guard_correct :
  forall (abstract_env : abstract_environment)
         (concrete_env : environment)
         (expr : bool_expression),
      bool_expression_evaluates concrete_env expr true ->
      In (to_concrete abstract_env) concrete_env ->
    In (to_concrete (guard expr abstract_env)) concrete_env.

Parameter can_be_false : abstract_environment -> bool_expression -> bool.

Parameter can_be_false_correct :
  forall (abstract_env : abstract_environment)
         (concrete_env : environment)
         (expr : bool_expression),
      bool_expression_evaluates concrete_env expr false ->
      In (to_concrete abstract_env) concrete_env ->
    can_be_false abstract_env expr = true.
    
Parameter eqb : abstract_environment -> abstract_environment -> bool.

Parameter eqb_true_iff : forall (e e' : abstract_environment),
                           eqb e e' = true  <-> e = e'.

Lemma eqb_false_iff :    forall (e e' : abstract_environment),
                           eqb e e' = false <-> e <> e'.
Proof.
  intros e e'. split.
  - intros Hneqb ?. subst.
    assert (H := eq_refl e'). apply eqb_true_iff in H.
    rewrite H in Hneqb. discriminate.
  - intros Hneq.
    destruct (eqb e e') eqn:E; [| reflexivity].
    apply eqb_true_iff in E. destruct (Hneq E).
Qed.

Parameter initial_environment : abstract_environment.

Parameter initial_environment_correct : In (to_concrete initial_environment)
                                           Environment.initial_environment.

Parameter subset : abstract_environment -> abstract_environment -> Prop.

End Domain.
