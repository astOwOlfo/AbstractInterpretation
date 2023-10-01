From AbstractInterpretation Require Import Domain ValueDomain CompleteBoolDomain Environment Maps
                                           Expression ExpressionSemantics Ensembles Order.

From Coq Require Import Ensembles ZArith PeanoNat.

Ltac inv H := inversion H; subst; clear H.

Module NonRelationalDomain (value_domain : ValueDomain) <: Domain.

Inductive abstract_environment : Type :=
  | Empty
  | AE (var_values : total_map var_id_set value_domain.abstract_value)
       (Hnomepty : forall var : var_id, value_domain.nonempty (find var_values var)).

Definition to_concrete (a : abstract_environment) : Ensemble environment :=
  fun concrete_env => match a with
                      | Empty           => False
                      | AE var_values _ => forall var : var_id,
                                             In (value_domain.to_concrete (find var_values var))
                                                (concrete_env var)
                      end.

Definition empty_environment : abstract_environment :=
  Empty.

Lemma empty_environment_correct : Is_empty (to_concrete empty_environment).
Proof.
  intros env contra. destruct contra.
Qed.

Program Definition union (a1 a2 : abstract_environment) : abstract_environment :=
  match a1, a2 with
  | Empty, a | a, Empty =>
      a
  | AE var_values1 _, AE var_values2 _ =>
      AE ( init_map var_id_list
                    var_id_set_iff_var_id_list
                    ( fun var_id => value_domain.union (find var_values1 var_id)
                                                       (find var_values2 var_id) ) ) _
  end.
Next Obligation.
  rewrite find_init_map.
  destruct (wildcard' var).
  eexists. apply value_domain.union_correct. left. eassumption.
Qed.

Lemma union_correct (ae1 ae2 : abstract_environment) :
  Subset (Union (to_concrete ae1) (to_concrete ae2))
         (to_concrete (union ae1 ae2)).
Proof.
  intros env HIn_Union.
  destruct ae1; destruct ae2;
  inv HIn_Union; try destruct H; try assumption;
  intro var; specialize (H var); rewrite find_init_map; apply value_domain.union_correct;
  [left; assumption | right; assumption].
Qed.

Program Definition widen (a1 a2 : abstract_environment) : abstract_environment :=
  match a1, a2 with
  | Empty, a | a, Empty =>
      a
  | AE var_values1 _, AE var_values2 _ =>
      AE ( init_map var_id_list
                    var_id_set_iff_var_id_list
                    ( fun var_id => value_domain.widen (find var_values1 var_id)
                                                       (find var_values2 var_id) ) ) _
  end.
Next Obligation.
  rewrite find_init_map.
  destruct (wildcard' var).
  eexists. apply value_domain.widen_correct. left. eassumption.
Qed.

Lemma widen_correct (ae1 ae2 : abstract_environment) :
  Subset (Union (to_concrete ae1) (to_concrete ae2))
         (to_concrete (widen ae1 ae2)).
Proof.
  intros env HIn_Union.
  destruct ae1; destruct ae2;
  inv HIn_Union; try destruct H; try assumption;
  intro var; specialize (H var); rewrite find_init_map; apply value_domain.widen_correct;
  [left; assumption | right; assumption].
Qed.

Definition widens_to (widened env : abstract_environment) : Prop :=
  exists env', widened = widen env env'.

Lemma to_strict_widens_to_well_founded : well_founded (to_strict widens_to).
Admitted.


Section Evaluate.

Variable vars : total_map var_id_set value_domain.abstract_value.

Fixpoint evaluate_int_expr (expr : int_expression) : value_domain.abstract_value :=
  match expr with
  | IntUnaryOperation  op expr'   => value_domain.unary_operation  op (evaluate_int_expr expr')
  | IntBinaryOperation op lhs rhs => value_domain.binary_operation op (evaluate_int_expr lhs)
                                                                      (evaluate_int_expr rhs)
  | Variable_ var                 => find vars var
  | IntConstant n                 => value_domain.singleton n
  | RandomInt lower upper         => value_domain.range lower upper
  end.


Fixpoint evaluate_bool_expr (expr : bool_expression) : complete_bool_domain :=
  match expr with
  | BoolUnaryOperation  op expr'   => evaluate_bool_unary_operation op (evaluate_bool_expr expr')
  | BoolBinaryOperation op lhs rhs => evaluate_bool_binary_operation op (evaluate_bool_expr lhs)
                                                                        (evaluate_bool_expr rhs)
  | Comparison          op lhs rhs => value_domain.comparison op (evaluate_int_expr lhs)
                                                                 (evaluate_int_expr rhs)
  end.

End Evaluate.

Program Definition assign (var : var_id) (expr : int_expression) (abstr_env : abstract_environment) :
                    abstract_environment :=
  match abstr_env with
  | Empty             => Empty
  | AE vars Hnonempty => let result := evaluate_int_expr vars expr in
                         match value_domain.nonemptyb result with
                         | true  => AE (add vars var result) _
                         | false => Empty
                         end
  end.
Next Obligation.
  destruct (Nat.eqb (proj1_sig var) (proj1_sig var0)) eqn:Evar.
  - apply Nat.eqb_eq in Evar.
    rewrite add_1 by assumption.
    apply value_domain.nonemptyb_correct. symmetry. assumption.
  - rewrite add_2 by (intro E; rewrite E in Evar; rewrite Nat.eqb_refl in Evar; discriminate).
    apply Hnonempty.
Qed.

Lemma assign_correct  (var : var_id)
                      (abstract_env : abstract_environment)
                      (concrete_env : environment)
                      (expr : int_expression)
                      (result : Z) :
      In (to_concrete abstract_env) concrete_env ->
      int_expression_evaluates concrete_env expr result ->
    In (to_concrete (assign var expr abstract_env))
       (Environment.assign var result concrete_env).
Proof.
  intros HIn Heval.
  destruct abstract_env. { inv HIn. }
  unfold assign. destruct (value_domain.nonemptyb (evaluate_int_expr var_values expr)).

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


End NonRelationalDomain.