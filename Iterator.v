From AbstractInterpretation Require Import CFG CFGSemantics Domain Expression ExpressionSemantics
                                          Environment Order Maps Ensembles.

From Coq Require Import OrderedType Ensembles.

Import Maps.

Ltac inv H := inversion H; subst; clear H.

Module Type Iterator (domain : Domain).

Parameter node_id_set : nat -> Prop.
Parameter cfg : @cfg node_id_set.

Definition node_id : Set :=
  { n : nat | node_id_set n }.

Parameter initial_node_id : node_id.

Parameter overapproximation : total_map node_id_set domain.abstract_environment.

Parameter overapproximation_correct :
  forall (node : node_id) (env : environment),
    star (small_step cfg) (initial_state initial_node_id) (node, env) ->
      In (domain.to_concrete (find overapproximation node)) env.

Definition passes_asserts : bool :=
  let approxes := overapproximation in
  forallb ( fun node : node_id =>
              forallb ( fun arc : arc =>
                          let approx := find approxes arc.(asource) in
                          match arc.(ainstruction) with
                          | Assert expr => negb (domain.can_be_false approx expr)
                          | Skip | Assign _ _ | Guard _ => true
                          end )
                      (find cfg.(coutgoing_arcs) node) )
          (node_list cfg).

Lemma passes_asserts_correct :
  passes_asserts = true ->
    forall (node : node_id) (env : environment) (expr : bool_expression) (arc : arc),
        star (small_step cfg) (initial_state initial_node_id) (node, env) ->
        List.In arc (find cfg.(coutgoing_arcs) node) ->
        arc.(ainstruction) = Assert expr ->
      ~bool_expression_evaluates env expr false.
Proof.
  intro Hpasses_asserts.
  unfold passes_asserts in Hpasses_asserts. rewrite forallb_forall in Hpasses_asserts.
  intros node env expr arc Hstar_small_step Harc_In_outgoing Einstruction Hexpr_false.
  specialize (Hpasses_asserts node (In_node_list _ _)).
  assert (Harc_passes_assert := proj1 (forallb_forall _ _) Hpasses_asserts arc Harc_In_outgoing).
  destruct arc; destruct ainstruction; try discriminate. inv Einstruction. simpl in *.
  eapply domain.can_be_false_correct in Hexpr_false.
  - rewrite Hexpr_false in Harc_passes_assert. discriminate.
  - apply overapproximation_correct.
    apply coutgoing_arcs_iff in Harc_In_outgoing. inv Harc_In_outgoing.
    assumption.
Qed.

End Iterator.
