From Coq Require Import Nat ZArith Lists.List.

Import ListNotations.

Axiom var_id_set : nat -> Prop.

Definition var_id : Set := {id : nat | var_id_set id}.

Axiom var_id_list : list nat.

Axiom var_id_set_iff_var_id_list : forall id : nat, var_id_set id <-> In id var_id_list.

Definition environment : Set :=
  var_id -> Z.

Definition assign (var_id : var_id) (value : Z) (env : environment) : environment :=
  fun id => if proj1_sig id =? proj1_sig var_id then value else env id.

Definition initial_environment : environment :=
  fun _ => 0%Z.