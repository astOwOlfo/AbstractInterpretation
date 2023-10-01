From AbstractInterpretation Require Import Expression ExpressionSemantics Ensembles.

From Coq Require Import Ensembles.

Ltac inv H := inversion H; clear H; subst.

Record complete_bool_domain := {
    can_be_true : bool;
    can_be_false : bool
}.

Definition bool_to_concrete (abstract : complete_bool_domain) : Ensemble bool :=
  fun b => if b
           then abstract.(can_be_true) = true
           else abstract.(can_be_false) = true.

Definition evaluate_bool_unary_operation (op : bool_unary_operation)
                                         (arg : complete_bool_domain) :
                                           complete_bool_domain :=
  match op with
  | Not => {| can_be_true  := arg.(can_be_false);
              can_be_false := arg.(can_be_true) |}
  end.

Definition evaluate_bool_binary_operation (op : bool_binary_operation)
                                          (lhs rhs : complete_bool_domain) :
                                            complete_bool_domain :=
  match op with
  | And => {| can_be_true  := lhs.(can_be_true)  && rhs.(can_be_true);
              can_be_false := lhs.(can_be_false) || rhs.(can_be_false) |}
  | Or  => {| can_be_true  := lhs.(can_be_true)  || rhs.(can_be_true);
              can_be_false := lhs.(can_be_false) || rhs.(can_be_false) |}
  end.

Lemma evaluate_bool_unary_operation_correct (op : bool_unary_operation)
                                            (abstr_arg : complete_bool_domain)
                                            (concr_arg concr_result : bool) :
    bool_unary_operation_evaluates op concr_arg concr_result ->
    In (bool_to_concrete abstr_arg) concr_arg ->
  In (bool_to_concrete (evaluate_bool_unary_operation op abstr_arg)) concr_result.
Proof.
  intros Heval HIn.
  inv Heval. destruct abstr_arg. destruct concr_arg;
  unfold In in HIn; simpl in HIn; subst; reflexivity.
Qed.

Lemma evaluate_bool_binary_operation_correct (op : bool_binary_operation)
                                             (abstr_lhs abstr_rhs : complete_bool_domain)
                                             (concr_lhs concr_rhs concr_result : bool) :
    bool_binary_operation_evaluates op concr_lhs concr_rhs concr_result ->
    In (bool_to_concrete abstr_lhs) concr_lhs ->
    In (bool_to_concrete abstr_rhs) concr_rhs ->
  In (bool_to_concrete (evaluate_bool_binary_operation op abstr_lhs abstr_rhs)) concr_result.
Proof.
  intros Heval HlhsIn HrhsIn.
  unfold In in *. destruct abstr_lhs. destruct abstr_rhs.
  destruct concr_lhs; destruct concr_rhs; simpl in *; subst; inv Heval;
  reflexivity || (destruct can_be_true0; reflexivity) || (destruct can_be_false0; reflexivity).
Qed.
