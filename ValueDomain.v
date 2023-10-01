From AbstractInterpretation Require Import Expression ExpressionSemantics CompleteBoolDomain
                                           Maps Environment Order Ensembles.

From Coq Require Import Ensembles ZArith.

Module Type ValueDomain.

Parameter abstract_value : Type.

Parameter to_concrete : abstract_value -> Ensemble Z.

Parameter singleton : Z -> abstract_value.
Parameter range : Z -> Z -> abstract_value.
Parameter singleton_correct : forall x : Z, In (to_concrete (singleton x)) x.
Parameter range_correct : forall lower upper x : Z, lower <= x <= upper ->
                            In (to_concrete (range lower upper)) x.

Parameter unary_operation : int_unary_operation -> abstract_value -> abstract_value.
Parameter binary_operation : int_binary_operation -> abstract_value -> abstract_value -> abstract_value.
Parameter comparison : comparison_operation -> abstract_value -> abstract_value -> complete_bool_domain.

Parameter unary_operation_correct :
  forall (op : int_unary_operation)
         (abstract_arg : abstract_value)
         (concrete_arg concrete_result : Z),
      int_unary_operation_evaluates op concrete_arg concrete_result ->
      In (to_concrete abstract_arg) concrete_arg ->
    In (to_concrete (unary_operation op abstract_arg)) concrete_result.

Parameter binary_operation_correct :
  forall (op : int_binary_operation)
         (abstract_lhs abstract_rhs : abstract_value)
         (concrete_lhs concrete_rhs concrete_result : Z),
      int_binary_operation_evaluates op concrete_lhs concrete_rhs concrete_result ->
      In (to_concrete abstract_lhs) concrete_lhs ->
      In (to_concrete abstract_rhs) concrete_rhs ->
    In (to_concrete (binary_operation op abstract_lhs abstract_rhs)) concrete_result.

Parameter comparison_correct :
  forall (op : comparison_operation)
         (abstract_lhs abstract_rhs : abstract_value)
         (concrete_lhs concrete_rhs : Z)
         (concrete_result : bool),
      comparison_evaluates op concrete_lhs concrete_rhs concrete_result ->
      In (to_concrete abstract_lhs) concrete_lhs ->
      In (to_concrete abstract_rhs) concrete_rhs ->
    In (bool_to_concrete (comparison op abstract_lhs abstract_rhs)) concrete_result.

Definition nonempty (a : abstract_value) : Prop :=
  exists concrete_value : Z,
    In (to_concrete a) concrete_value.

Parameter nonemptyb : abstract_value -> bool.

Parameter nonemptyb_correct : forall a : abstract_value,
                                nonemptyb a = true <-> nonempty a.

Parameter union : abstract_value -> abstract_value -> abstract_value.

Parameter union_correct : forall (av1 av2 : abstract_value),
                            Subset (Union (to_concrete av1) (to_concrete av2))
                                   (to_concrete (union av1 av2)).

Parameter widen : abstract_value -> abstract_value -> abstract_value.

Parameter widen_correct : forall (av1 av2 : abstract_value),
                            Subset (Union (to_concrete av1) (to_concrete av2))
                                   (to_concrete (widen av1 av2)).

Definition widens_to (widened env : abstract_value) : Prop :=
  exists env', widened = widen env env'.

Parameter to_strict_widens_to_well_founded : well_founded (to_strict widens_to).

End ValueDomain.