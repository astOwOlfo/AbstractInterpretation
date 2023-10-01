From AbstractInterpretation Require Import Iterator CFG CFGSemantics Domain Environment
                                           Graph Order Maps Ensembles Sigmas.

From Coq Require Import Structures.OrderedType FSets.FSetAVL Lists.List PeanoNat Bool.Bool
                        Program.Wf.

Import Maps.

Ltac inv H := (inversion H; subst; clear H).

Module Type BasicIterator (domain : Domain) <: Iterator domain.

Parameter node_id_set : nat -> Prop.
Parameter cfg : @cfg node_id_set.

Definition node_id : Set :=
  { n : nat | node_id_set n }.

Parameter initial_node_id : node_id.

Definition widened_node_id_set : nat -> Prop :=
  fun n => NatSet.In n cfg.(cwidened).(dset _).

Definition widened_node_id : Set :=
  { n : nat | widened_node_id_set n }.

Definition cast_node_id_to_widened_node_id
    (node : node_id)
    (H : widened_node_id_set (proj1_sig node)) :
      widened_node_id :=
  exist _ (proj1_sig node) H.

Definition cast_widened_nonde_id_to_node_id (widened_node : widened_node_id) : node_id :=
  exist _ (proj1_sig widened_node) (cfg.(cwidened).(ddomain) _ (proj2_sig widened_node)).
  
Definition do_instruction (abstr_env : domain.abstract_environment)
                          (instr :     instruction) :
                            domain.abstract_environment :=
  match instr with
  | CFG.Skip                                          => abstr_env
  | CFG.Assign var_id expr                            => domain.assign var_id expr abstr_env
  | CFG.Assert condition | CFG.Guard condition => domain.guard  condition   abstr_env
  end.

Lemma do_instruction_correct ( abstr_env_before :    domain.abstract_environment )
                             ( instr :               instruction )
                             ( concrete_env_before
                               concrete_env_after :  environment ) :
  let abstr_env_after := do_instruction abstr_env_before instr in
    instruction_small_step instr concrete_env_before concrete_env_after ->
    Ensembles.In (domain.to_concrete abstr_env_before) concrete_env_before ->
  Ensembles.In (domain.to_concrete abstr_env_after) concrete_env_after.
Proof.
  simpl. intros Hsmall_step HIn_env_before.
  inv Hsmall_step.
  - assumption.
  - apply domain.assign_correct. assumption.
  - apply domain.guard_correct; assumption.
  - apply domain.guard_correct; assumption.
Qed.

Record partial_approximations : Type := {
  papproximations : total_map node_id_set domain.abstract_environment;
  pworklist :       set_with_domain node_id_set
}.

Definition iterate (worked :   node_id)
                   (approxes : partial_approximations) :
                     partial_approximations :=
  let worked_approx := find approxes.(papproximations) worked in

  fold_right
    ( fun '{| CFG.asource      := _;
              CFG.adestination := child;
              CFG.ainstruction := instr |}
           acc_approxes =>
        let child_approx := find acc_approxes.(papproximations) child in
        let added_approx := do_instruction worked_approx instr in
        let widen        := mem cfg.(cwidened) child in
        let new_approx   := if widen
                              then domain.widen child_approx added_approx
                              else domain.union child_approx added_approx in
        let no_change    := domain.eqb child_approx new_approx in
        if no_change
        then acc_approxes
        else {| papproximations := add acc_approxes.(papproximations) child new_approx;
                pworklist       := set_add acc_approxes.(pworklist) child |} )
    {| papproximations := approxes.(papproximations);
       pworklist       := set_remove approxes.(pworklist) worked |}
    (find cfg.(coutgoing_arcs) worked).

(* Record widened_partial_approximations : Type := {
  wwidened_approximations : total_map widened_node_id_set domain.abstract_environment;
  wworklist               : set_with_domain node_id_set
}. *)

Definition widened_partial_approximations : Type :=
      (* approximations of widened nodes only *)
    total_map widened_node_id_set domain.abstract_environment
      (* worklist *)
  * set_with_domain node_id_set.

(* Definition keep_only_widened (approxes : partial_approximations) :
                               widened_partial_approximations := {|
  wwidened_approximations := restrict approxes.(papproximations) cfg.(cwidened);
  wworklist               := approxes.(pworklist)
|}. *)

Definition keep_only_widened (approxes : partial_approximations) :
                               widened_partial_approximations :=
  ( restrict approxes.(papproximations) cfg.(cwidened),
    approxes.(pworklist) ).

(* Definition widened_node_approximations
    (approxes : partial_approximations) :
      total_map (widened_node_id_set cfg) domain.abstract_environment :=
      restrict approxes.(papproximations) cfg.(cwidened). *)

(* Record widened_node_approximations_order
    (approxes1 approxes2 : total_map widened_node_id_set domain.abstract_environment) : Prop
:= mk_widened_node_approximations_order {
  wwidened : widened_node_id;
  wwiden :   domain.widens_to (find approxes1 wwidened) (find approxes2 wwidened);
  wsame :    forall node : widened_node_id,
                 proj1_sig node <> proj1_sig wwidened ->
               find approxes1 node = find approxes2 node
}. *)

Definition widened_node_approximations_order
    (approxes1 approxes2 : total_map widened_node_id_set domain.abstract_environment) : Prop :=
  exists widened : widened_node_id,
       to_strict domain.widens_to (find approxes1 widened) (find approxes2 widened)
    /\ forall node : widened_node_id,    proj1_sig node <> proj1_sig widened ->
                                      find approxes1 node = find approxes2 node.

Definition worklist_order : set_with_domain node_id_set -> set_with_domain node_id_set -> Prop :=
  dag_order (unwidened_arc_graph cfg).

Definition widened_partial_approximations_order :
    widened_partial_approximations -> widened_partial_approximations -> Prop :=
  lexicographical_order (strict_star widened_node_approximations_order)
                        (to_strict worklist_order).

Definition partial_approximations_order (approxes1 approxes2 : partial_approximations) : Prop :=
  widened_partial_approximations_order (keep_only_widened approxes1)
                                       (keep_only_widened approxes2).

Definition strengthened_partial_approximations_order
            (worked              : node_id)
            (approxes1 approxes2 : widened_partial_approximations) : Prop :=
  let '(widened_approxes1, worklist1) := approxes1 in
  let '(widened_approxes2, worklist2) := approxes2 in
     strict_star widened_node_approximations_order widened_approxes1 widened_approxes2
  \/ (    worklist_order worklist1 worklist2
       /\ widened_approxes1 = widened_approxes2
       /\ ~contains worklist1 worked ).
  
Lemma worklist_order_add_destination (worklist1 worklist2 : set_with_domain node_id_set)
                                     (source destination :  node_id)
                                     (instr :               instruction) :
    In {| asource := source; adestination := destination; ainstruction := instr |}
       cfg.(carcs) ->
    ~contains cfg.(cwidened) destination ->
    contains worklist2 source ->
    worklist_order worklist1 worklist2 ->
  worklist_order (set_add worklist1 destination) worklist2.
Proof.
  intros Harc_in_cfg Hdestination_not_widened Hsource_in_worklist2 Hworklist_order.
  intros low Hlow_in.
  destruct (proj1_sig destination =? proj1_sig low) eqn:Edestination_low.
  - apply Nat.eqb_eq in Edestination_low. apply exist_eq_of_porj1_sig_eq in Edestination_low.
    exists source. split.
    + assumption.
    + apply star_of_rel. split.
      * exists {|asource := source; adestination := destination; ainstruction := instr|}.
        repeat split; assumption.
      * rewrite <- Edestination_low. assumption.
  - eapply Hworklist_order.
    apply set_add_3 in Hlow_in.
    + assumption.
    + intro contra. rewrite contra in Edestination_low.
      rewrite Nat.eqb_refl in Edestination_low. discriminate.
Qed.

Lemma worklist_order_remove (worklist : set_with_domain node_id_set)
                            (node :     node_id) :
  worklist_order (set_remove worklist node) worklist.
Proof.
  intros low Hlow_in.
  apply set_remove_3 in Hlow_in.
  exists low. split.
  - assumption.
  - apply StarRefl.
Qed.

Lemma widened_partial_approximations_order_of_strengthened
        (worked              : node_id)
        (approxes1 approxes2 : widened_partial_approximations) :
    contains (snd approxes2) worked ->
    strengthened_partial_approximations_order worked approxes1 approxes2 ->
  widened_partial_approximations_order approxes1 approxes2.
Proof.
  unfold strengthened_partial_approximations_order.
  destruct approxes1 as [widened_approxes1 worklist1].
  destruct approxes2 as [widened_approxes2 worklist2].
  intros Hcontains_worked
         [Hwidened_order | [Hworklist_order [Hwidened_approxes_eq Hnot_contains_worked]]].
  - apply Lex1. assumption.
  - rewrite Hwidened_approxes_eq.
    apply Lex2.
    split.
    + intro contra. subst.
      destruct (Hnot_contains_worked Hcontains_worked).
    + assumption.
Qed.

Lemma strengthened_partial_approximations_order_trans (worked : node_id) :
  transitive _ (strengthened_partial_approximations_order worked).
Proof.
  intros
    [approxes1 worklist1] [approxes2 worklist2] [approxes3 worklist3]
    [Hwidened_node_approxes_ord12 | [Hworklist_order12 [Eapproxes12 Hworked_not_in_worklist1]]]
    [Hwidened_node_approxes_ord23 | [Hworklist_order23 [Eapproxes23 Hworked_not_in_worklist2]]].
  - left. eapply strict_star_trans; eassumption.
  - left. rewrite <- Eapproxes23. assumption.
  - left. rewrite Eapproxes12. assumption.
  - right. repeat split.
    + eapply dag_order_trans; eassumption.
    + etransitivity; eassumption.
    + assumption.
Qed.

  (* How is this called in the standard library? *)
Lemma func_congr {X Y : Type} {f g : X -> Y} (x : X) : f = g -> f x = g x.
Proof. intro E. rewrite E. reflexivity. Qed.

Lemma partial_approximations_order_iterate
    (worked :     node_id)
    (approxes :   partial_approximations)
    (Hworked_In : contains approxes.(pworklist) worked) :
  widened_partial_approximations_order (keep_only_widened (iterate worked approxes))
                                       (keep_only_widened approxes).
Proof.
  apply widened_partial_approximations_order_of_strengthened with (worked := worked);
  [apply Hworked_In |].
  destruct approxes as [approxes worklist].
  unfold iterate.
  remember (find cfg.(coutgoing_arcs) worked) as outgoing_arcs eqn:Eoutgoing_arcs.
  remember (find approxes worked)             as worked_approx eqn:Eworked_approx.
  assert (Houtgoing_arcs_cfg : forall arc,
                                 In arc outgoing_arcs ->
                                   In arc (find cfg.(coutgoing_arcs) worked)).
  { intros. rewrite <- Eoutgoing_arcs. assumption. }
  clear Eoutgoing_arcs.
  induction outgoing_arcs as [| [asource child instr] outgoing_arcs_tail IH];
  simpl.
  - right. repeat split.
    + apply worklist_order_remove.
    + apply set_remove_1.
  - simpl in IH.
    assert (IHpremise : forall arc,
                          In arc outgoing_arcs_tail ->
                            In arc (find cfg.(coutgoing_arcs) worked)).
    { intros. apply Houtgoing_arcs_cfg. right. assumption. }
    specialize (IH IHpremise).
    remember (fold_right _ _ _) as iterate_tail eqn:E. clear E.
    destruct iterate_tail as [acc_approxes acc_worklist]. simpl.
    remember (mem cfg.(cwidened) child) as widen eqn:Ewiden.
    remember (find acc_approxes child) as child_approx eqn:Echild_approx.
    rewrite <- Eworked_approx.
    remember (do_instruction worked_approx instr) as added_approx eqn:Eadded_approx.
    remember ( if widen
              then domain.widen child_approx added_approx
              else domain.union child_approx added_approx ) as new_approx eqn:Enew_approx.
    remember (domain.eqb child_approx new_approx) as no_change eqn:Eno_change.
    destruct no_change; [apply IH |].
    destruct widen; simpl.
    + eapply (fun Horder =>
                strengthened_partial_approximations_order_trans _ (_, _) (_, _) (_, _) Horder IH).
      left. apply StrictStarIntro.
      symmetry in Ewiden. apply mem_2 in Ewiden.
      remember (cast_node_id_to_widened_node_id child Ewiden) as cast_child eqn:Ecast_child.
      exists cast_child.
      * unfold widened_node_id_set. (* This line looks like it doesn't change the goal,
                                      but it does change a thing in the goal that is not
                                   printed because it is an implicit argument. *)
        rewrite find_restrict with (key' := child) by (rewrite Ecast_child; reflexivity).
        rewrite add_1 by reflexivity.
        rewrite find_restrict with (key' := child) by (rewrite Ecast_child; reflexivity).
        split.
        -- split.
           ++ simpl. rewrite <- Echild_approx. intro contra.
              rewrite (proj2 (domain.eqb_true_iff _ _)) in Eno_change by (symmetry; assumption).
              discriminate.
           ++ exists added_approx.
              simpl. rewrite <- Echild_approx. apply Enew_approx.
        -- intros node Hnode_neq.
           remember (cast_widened_nonde_id_to_node_id node) as cast_node eqn:Ecast_node.
           unfold widened_node_id_set.
           repeat rewrite find_restrict with (key' := cast_node)
             by (rewrite Ecast_node; reflexivity).
           apply add_2.
           destruct node. destruct child. rewrite Ecast_child in Hnode_neq. rewrite Ecast_node.
           apply Nat.neq_sym. apply Hnode_neq.
    + rewrite restrict_add_of_not_contains
        by (intro contra; apply mem_1 in contra; rewrite contra in Ewiden; discriminate).
      destruct IH as [IH | [IH1 [IH2 IH3]]]; simpl in *.
      * left. apply IH.
      * right.
        rewrite IH2.
        specialize (Houtgoing_arcs_cfg _ (or_introl (eq_refl _))).
        apply coutgoing_arcs_iff in Houtgoing_arcs_cfg.
        destruct Houtgoing_arcs_cfg as [Harc_In E]. simpl in E. rewrite <- E in *.
        repeat split.
        -- eapply worklist_order_add_destination; try eassumption.
           intro contra. apply mem_1 in contra. rewrite contra in Ewiden. discriminate.
        -- assert (Hchild_neq_worked : proj1_sig child <> proj1_sig worked).
           { intro. subst.
             eapply no_loop_of_acyclic.
             - apply cfg.(cunwidened_arc_graph_acyclic).
             - simpl. split; [eexists |]; repeat split.
               + eassumption.
               + apply exist_eq_of_porj1_sig_eq. simpl. assumption.
               + simpl. rewrite <- (exist_eq_of_porj1_sig_eq _ _ _ H).
                 intro contra. apply mem_1 in contra. rewrite contra in Ewiden. discriminate. }
          intro contra.
          apply set_add_3 in contra; [| assumption].
          destruct (IH3 contra).
Qed.

Lemma widened_node_approximations_order_well_founded :
  well_founded widened_node_approximations_order.
Proof.
  unfold widened_node_approximations_order.
  remember (elements cfg.(cwidened)) as widened_list eqn:Ewidened_list'.
  assert (Ewidened_list : forall id : nat, In id widened_list <-> widened_node_id_set id).
  { intro id. split; rewrite Ewidened_list'; intro H;
    unshelve eremember (exist node_id_set id _) as cast_id eqn:Ecast_id.
    - apply domain_of_In_elements in H. exact H.
    - apply cfg.(cwidened).(ddomain) in H. exact H.
    - assert (H' := H).
      apply (elements_2 _ _ cast_id) in H'.
      + rewrite Ecast_id in H'. apply H'.
      + rewrite Ecast_id. reflexivity.
    - assert (H' := H).
      apply elements_1 with (elt' := cast_id).
      + rewrite Ecast_id. reflexivity.
      + rewrite Ecast_id. apply H'. }
  clear Ewidened_list'.
  unfold widened_node_id.
  generalize dependent widened_node_id_set.
  induction widened_list as [| widened_head widened_tail IH];
  intros  widened_node_id_set Ewidened_list.
  - intros approxes. constructor. intros approxes1 [widened _]. exfalso.
    assert (contra := proj2_sig widened).
    apply Ewidened_list in contra.
    destruct contra.
  - specialize (IH _ (fun _ => iff_refl _)).
    unshelve eapply well_founded_of_implies with
      ( f := fun approxes =>
               ( find approxes (exist _ widened_head _), restrict_to_list approxes widened_tail ) )
      ( strong_ord :=
          lexicographical_order
            ( to_strict domain.widens_to )
            ( fun approxes1 approxes2 : total_map (fun id : nat => In id widened_tail)
                                                  domain.abstract_environment =>
                exists widened,
                     to_strict domain.widens_to (find approxes1 widened)
                                                (find approxes2 widened)
                  /\ forall node,   proj1_sig node <> proj1_sig widened ->
                                  find approxes1 node = find approxes2 node ) ).
    + apply Ewidened_list. left. reflexivity.
    + intros approxes1 approxes2 [widened [Hwiden Hsame]].
      destruct (widened_head =? proj1_sig widened) eqn:Hhead.
      * apply Nat.eqb_eq in Hhead.
        apply Lex1.
        simpl.
        rewrite find_1 with (map := approxes1) (key' := widened) by assumption.
        rewrite find_1 with (map := approxes2) (key' := widened) by assumption.
        assumption.
      * rewrite Hsame by ( simpl; intro contra; rewrite contra in Hhead;
                           rewrite Nat.eqb_refl in Hhead; discriminate ).
        apply Lex2.
        unshelve eremember (exist _ (proj1_sig widened) _ : { id : nat | In id widened_tail })
          as cast_widened eqn:Ecast_widened.
        { simpl.
          assert (HIn := proj2_sig widened).
          apply Ewidened_list in HIn.
          destruct HIn as [Ehead | HIn_tail].
          - rewrite Ehead in Hhead. rewrite Nat.eqb_refl in Hhead. discriminate.
          - assumption. }
        exists cast_widened. split.
        -- repeat rewrite find_restrict_to_list with (key := widened)
             by (rewrite Ecast_widened; reflexivity).
           assumption.
        -- intros node Hnode_neq_widened.
           unshelve eremember (exist _ (proj1_sig node) _ : { id : nat | widened_node_id_set id })
             as cast_node eqn:Ecast_node.
           { apply Ewidened_list. right. apply proj2_sig. }
           repeat rewrite find_restrict_to_list with (key := cast_node)
             by (rewrite Ecast_node; reflexivity).
           apply Hsame.
           intro contra.
           rewrite Ecast_node in contra. simpl in contra.
           rewrite Ecast_widened in Hnode_neq_widened. simpl in Hnode_neq_widened.
           destruct (Hnode_neq_widened contra).
    + apply lexicographical_order_well_founded.
      * apply domain.to_strict_widens_to_well_founded.
      * apply IH.
Qed.

Lemma widened_partial_approximations_order_well_founded :
  well_founded widened_partial_approximations_order.
Proof.
  apply lexicographical_order_well_founded.
  - apply strict_star_well_founded.
    apply widened_node_approximations_order_well_founded.
  - unfold worklist_order.
    apply to_strict_dag_order_well_founded_of_acyclic.
    apply cunwidened_arc_graph_acyclic.
Qed.

Lemma partial_approximations_order_well_founded :
  well_founded partial_approximations_order.
Proof.
  apply proj_well_founded with (f := keep_only_widened).
  apply widened_partial_approximations_order_well_founded.
Qed.

Definition partial_approximations_correct_at_arc
             (approxes : partial_approximations)
             (arc : arc) :
               Prop :=
    ~contains approxes.(pworklist) arc.(asource) ->
  let src_concrete_approx :=
    domain.to_concrete (find approxes.(papproximations) arc.(asource)) in
  let dst_concrete_approx :=
    domain.to_concrete (find approxes.(papproximations) arc.(adestination)) in
  forall src_env dst_env : environment,
      instruction_small_step arc.(ainstruction) src_env dst_env ->
      Ensembles.In src_concrete_approx src_env ->
    Ensembles.In dst_concrete_approx dst_env.

Definition partial_approximations_correct (approxes : partial_approximations) : Prop :=
     ( forall arc : arc,   In arc cfg.(carcs) ->
                         partial_approximations_correct_at_arc approxes arc )
  /\ Ensembles.In (domain.to_concrete (find approxes.(papproximations) initial_node_id))
                  initial_environment.
    
Lemma iterate_preserves_correct (worked :     node_id)
                                (approxes :   partial_approximations)
                                (Hworked_In : contains approxes.(pworklist) worked) :
    partial_approximations_correct approxes ->
  partial_approximations_correct (iterate worked approxes).
Proof.
  intro Hcorrect_before.
  remember (iterate worked approxes) as approxes_after eqn:Eapproxes_after.
  destruct approxes                  as [approxes worklist].
  destruct approxes_after            as [approxes_after worklist_after].
  simpl in *.
  unfold iterate in Eapproxes_after.
  remember (find cfg.(coutgoing_arcs) worked) as outgoing_arcs eqn:Eoutgoing_arcs.
  remember (find approxes worked)             as worked_approx eqn:Eworked_approx.
  enough ( Hgoal :
       ( forall arc : arc,
             In arc outgoing_arcs \/ (In arc cfg.(carcs) /\ arc.(asource) <> worked) ->
           partial_approximations_correct_at_arc
             {| papproximations := approxes_after; pworklist := worklist_after |}
             arc )
    /\ Ensembles.In (domain.to_concrete (find approxes_after initial_node_id))
                    initial_environment
    /\ (    worked_approx = find approxes_after worked
         \/ contains worklist_after worked )
    /\ ( forall node : node_id,
             node <> worked ->
             contains worklist node ->
           contains worklist_after node )
    /\ ( forall node : node_id,
             ( exists arc : arc,    In arc outgoing_arcs
                                 /\ node = arc.(adestination)
                                 /\ domain.eqb (find approxes       node)
                                               (find approxes_after node) = false ) ->
          contains worklist_after node )
    /\ ( forall node : node_id,
             domain.eqb (find approxes       node)
                        (find approxes_after node) = false ->
           exists arc : arc,    In arc outgoing_arcs
                             /\ node = arc.(adestination) ) ).
  { destruct Hgoal as [Gcorrect [Ginitial_env [Gworked_approx
                       [Gworklist_subset [Gworklist_added Goutgoing_arc_of_change]]]]].
    split.
    - intros arc Harc_In_cfg Hsource_not_In_worklist. simpl in *.
      intros src_env dst_env Hinstruction_small_step Hsrc_env_In.
      eapply Gcorrect; try eassumption.
      destruct (proj1_sig (asource arc) =? proj1_sig worked) eqn:Esource_worked.
      + apply Nat.eqb_eq in Esource_worked. apply exist_eq_of_porj1_sig_eq in Esource_worked.
        assert (Harc_In_outgoing : In arc cfg.(carcs) /\ worked = arc.(asource)).
        { split.
          - assumption.
          - symmetry. assumption. }
        apply cfg.(coutgoing_arcs_iff) in Harc_In_outgoing.
        left. rewrite Eoutgoing_arcs. assumption.
      + right. split.
        * assumption.
        * intro contra. rewrite contra in Esource_worked. rewrite Nat.eqb_refl in Esource_worked.
          discriminate.
    - apply Ginitial_env. }
  assert (Houtgoing_arcs_cfg : forall arc,
                                   In arc outgoing_arcs ->
                                In arc (find cfg.(coutgoing_arcs) worked)).
  { intros. rewrite <- Eoutgoing_arcs. assumption. }
  clear Eoutgoing_arcs.
  generalize dependent Houtgoing_arcs_cfg.
  generalize dependent Eapproxes_after.
  revert approxes_after. revert worklist_after.
  induction outgoing_arcs as [| [asource child instr] outgoing_arcs_tail IH];
  simpl; intros.
  - injection Eapproxes_after as E1 E2.
    rewrite E1 in *. rewrite E2 in *. clear E1 E2 approxes_after worklist_after.
    repeat split.
    + intros arc [[] | [Harc_In_cfg Esource_neq_worked]].
      intro Hnot_worklist. simpl in *. eapply Hcorrect_before.
      * assumption.
      * simpl. intro contra. apply Hnot_worklist.
        apply set_remove_2.
        -- intro contra'. apply exist_eq_of_porj1_sig_eq in contra'.
           apply Esource_neq_worked. symmetry. assumption.
        --assumption.
    + apply proj2 in Hcorrect_before. assumption.
    + left. assumption.
    + intros node Enode_neq_worked HIn_worklist.
      apply set_remove_2.
      -- intro contra'. apply exist_eq_of_porj1_sig_eq in contra'.
         apply Enode_neq_worked. symmetry. assumption.
      -- assumption.
    + intros node [arc [[] _]].
    + intros node contra.
      erewrite (proj2 (domain.eqb_true_iff _ _)) in contra by reflexivity. discriminate.
  - simpl in IH.
    remember (fold_right _ _ _) as acc_approxes eqn:E. clear E.
    destruct acc_approxes as [acc_approxes acc_worklist].
    specialize (IH _ _ (eq_refl _)).
    assert (IHpremise : forall arc,
                            In arc outgoing_arcs_tail ->
                          In arc (find cfg.(coutgoing_arcs) worked)).
    { intros. apply Houtgoing_arcs_cfg. right. assumption. }
    specialize (IH IHpremise).
    destruct IH as [IHcorrect [IHinitial_env [IHworked_approx
                    [IHworklist_subset [IHworklist_added IHoutgoing_arc_of_change]]]]].
    simpl in *.
    remember (mem cfg.(cwidened) child) as widen eqn:Ewiden.
    remember (find acc_approxes child) as child_approx eqn:Echild_approx.
    rewrite <- Eworked_approx in Eapproxes_after.
    remember (do_instruction worked_approx instr) as added_approx eqn:Eadded_approx.
    remember ( if widen
               then domain.widen child_approx added_approx
               else domain.union child_approx added_approx ) as new_approx eqn:Enew_approx.
    remember (domain.eqb child_approx new_approx) as no_change eqn:Eno_change.
    specialize (Houtgoing_arcs_cfg
                  {|asource := asource; adestination := child; ainstruction := instr|}
                  (or_introl (eq_refl _))).
    apply cfg.(coutgoing_arcs_iff) in Houtgoing_arcs_cfg.
    destruct Houtgoing_arcs_cfg as [Harc_In_cfg E].
    simpl in E. rewrite <- E in *. clear E. clear asource.
    assert (Efind_child_after : new_approx = find approxes_after child).
    { destruct no_change;
      injection Eapproxes_after as E1 E2; rewrite E1 in *.
      - symmetry in Eno_change. apply domain.eqb_true_iff in Eno_change. rewrite Eno_change in *.
        assumption.
      - symmetry. apply add_1. reflexivity. }
    repeat split.
    + intros arc [[Harc_head | Harc_tail] | [Harc_in_cfg Hsource_neq_worked]];
      intros Hsource_not_In_worklist. simpl in *.
      * rewrite <- Harc_head in *. clear Harc_head. clear arc. simpl in *.
        destruct IHworked_approx as [IHworked_approx | IHworked_worklist].
        2: { destruct no_change;
             injection Eapproxes_after as E1 E2; rewrite E2 in *;
             exfalso; apply Hsource_not_In_worklist; [| apply set_add_2]; assumption. }
        assert (Hadded_approx_new_approx : Subset (domain.to_concrete added_approx)
                                                  (domain.to_concrete new_approx)).
        { destruct widen; rewrite Enew_approx; intros env H;
          [apply domain.widen_correct | apply domain.union_correct ]; right; assumption. }
        intros src_env dst_env Hinstruction_small_step Hsrc_env_In.
        rewrite <- Efind_child_after.
        destruct no_change;
        injection Eapproxes_after as E1 E2; rewrite E1 in *; rewrite E2 in *; clear E1 E2.
        -- symmetry in Eno_change. apply domain.eqb_true_iff in Eno_change.
           rewrite Eno_change in *.
           rewrite <- IHworked_approx in *.
           apply Hadded_approx_new_approx.
           rewrite Eadded_approx. eapply do_instruction_correct; eassumption.
        -- assert (Hchild_neq_worked : proj1_sig child <> proj1_sig worked).
           { intro contra. apply Hsource_not_In_worklist. apply set_add_1. apply contra. }
           rewrite add_2 in Hsrc_env_In by apply Hchild_neq_worked.
           rewrite <- IHworked_approx in Hsrc_env_In.
           apply Hadded_approx_new_approx.
           rewrite Eadded_approx. eapply do_instruction_correct; eassumption.
      * simpl in *.
        intros src_env dst_env Hinstruction_small_step Hsrc_env_In.
        assert (Harc_tail' := Harc_tail).
        apply IHpremise in Harc_tail'. apply cfg.(coutgoing_arcs_iff) in Harc_tail'.
        destruct Harc_tail' as [Harc_In_cfg' Esource_worked]. simpl in Esource_worked.
        rewrite <- Esource_worked in *.
        destruct IHworked_approx as [IHworked_approx | IHworked_worklist].
        2: { destruct no_change;
             injection Eapproxes_after as E1 E2; rewrite E2 in *;
             exfalso; apply Hsource_not_In_worklist; [| apply set_add_2]; assumption. }
        enough (Goal : Ensembles.In (domain.to_concrete (find acc_approxes arc.(adestination))) dst_env).
        { destruct no_change; injection Eapproxes_after as E1 E2;
          rewrite E1 in *; rewrite E2 in *;
          [assumption |].
          destruct (proj1_sig child =? proj1_sig arc.(adestination)) eqn:Echild_destination.
          - apply Nat.eqb_eq in Echild_destination.
            rewrite add_1 by assumption.
            apply exist_eq_of_porj1_sig_eq in Echild_destination.
            rewrite <- Echild_destination in *.
            rewrite <- Echild_approx in Goal.
            destruct widen; rewrite Enew_approx;
            [apply domain.widen_correct | apply domain.union_correct]; left; assumption.
          - rewrite add_2 by ( intro contra; rewrite contra in Echild_destination;
                               rewrite Nat.eqb_refl in Echild_destination; discriminate ).
            assumption. }
        eapply IHcorrect.
        -- left. assumption.
        -- simpl. intro contra. rewrite <- Esource_worked in contra. apply Hsource_not_In_worklist.
           destruct no_change; injection Eapproxes_after as _ E; rewrite E in *;
           [| apply set_add_2]; assumption.
        -- eassumption.
        -- simpl. rewrite <- Esource_worked.
           destruct no_change; injection Eapproxes_after as E1 E2;
           rewrite E1 in *; rewrite E2 in *;
           [assumption |].
           assert (Hchild_neq_worked : proj1_sig child <> proj1_sig worked).
           { intro contra. apply Hsource_not_In_worklist. apply set_add_1. apply contra. }
           rewrite add_2 in Hsrc_env_In by apply Hchild_neq_worked.
           assumption.
      * simpl in *.
        intros src_env dst_env Hinstruction_small_step Hsrc_env_In.
        enough (Goal : Ensembles.In
                        (domain.to_concrete (find acc_approxes arc.(adestination)))
                        dst_env).
        { destruct (proj1_sig arc.(adestination) =? proj1_sig child) eqn:Edestination_child.
          - apply Nat.eqb_eq in Edestination_child.
            apply exist_eq_of_porj1_sig_eq in Edestination_child.
            rewrite Edestination_child in *.
            destruct no_change; injection Eapproxes_after as E1 E2;
            rewrite E1 in *; rewrite E2 in *;
            [assumption |].
            rewrite add_1 by reflexivity.
            rewrite <- Echild_approx in Goal.
            destruct widen; rewrite Enew_approx;
            [eapply domain.widen_correct | eapply domain.union_correct]; left; assumption.
          - destruct no_change; injection Eapproxes_after as E1 E2;
            rewrite E1 in *; rewrite E2 in *;
            [assumption |].
            rewrite add_2 by ( intro contra; rewrite contra in Edestination_child;
                               rewrite Nat.eqb_refl in Edestination_child; discriminate ).
            assumption. }
        eapply IHcorrect.
        -- right. split; assumption.
        -- simpl. intro contra. apply Hsource_not_In_worklist.
           destruct no_change; injection Eapproxes_after as _ E; rewrite E in *;
           [| apply set_add_2]; assumption.
        -- eassumption.
        -- simpl.
           destruct no_change; injection Eapproxes_after as E1 E2;
           rewrite E1 in *; rewrite E2 in *;
           [assumption |].
           destruct (proj1_sig child =? proj1_sig arc.(asource)) eqn:Echild_source.
           ** apply Nat.eqb_eq in Echild_source.
             exfalso. apply Hsource_not_In_worklist.
             apply set_add_1. assumption.
           ** rewrite add_2 in Hsrc_env_In
             by ( intro contra; rewrite contra in Echild_source;
                   rewrite Nat.eqb_refl in Echild_source; discriminate ).
             assumption.
    + destruct no_change; injection Eapproxes_after as E1 _; rewrite E1 in *;
      [assumption |].
      destruct (proj1_sig child =? proj1_sig initial_node_id) eqn:Echild_initial.
      * apply Nat.eqb_eq in Echild_initial. apply exist_eq_of_porj1_sig_eq in Echild_initial.
        rewrite Echild_initial in *. rewrite add_1 by reflexivity.
        destruct widen; rewrite Enew_approx;
        [apply domain.widen_correct | apply domain.union_correct];
        left; rewrite Echild_approx; assumption.
      * rewrite add_2 by ( intro contra; rewrite contra in Echild_initial;
                           rewrite Nat.eqb_refl in Echild_initial; discriminate ).
        assumption.
    + destruct IHworked_approx as [IHworked_approx | IHworked_worklist].
      2: { destruct no_change; injection Eapproxes_after as E1 E2;
           rewrite E1 in *; rewrite E2 in *.
           - right. assumption.
           - right. apply set_add_2. assumption. }
      destruct no_change; injection Eapproxes_after as E1 E2;
      rewrite E1 in *; rewrite E2 in *;
      [left; assumption |].
      destruct (proj1_sig child =? proj1_sig worked) eqn:Echild_worked.
      * apply Nat.eqb_eq in Echild_worked.
        right. apply set_add_1. assumption.
      * left. rewrite add_2 by ( intro contra; rewrite contra in Echild_worked;
                                 rewrite Nat.eqb_refl in Echild_worked; discriminate ).
        assumption.
    + intros node Enode_neq_worked HIn_worklist.
      destruct no_change; injection Eapproxes_after as E1 E2;
      rewrite E1 in *; rewrite E2 in *.
      * apply IHworklist_subset; assumption.
      * apply set_add_2. apply IHworklist_subset; assumption.
    + assert (Hworklist_grows : forall node : node_id,   contains acc_worklist node ->
                                                       contains worklist_after node).
      { intros node HIn_acc_worklist.
        destruct no_change; injection Eapproxes_after as E1 E2;
        rewrite E1 in *; rewrite E2 in *;
        [assumption | apply set_add_2; assumption]. }
      intros node [arc [[Earc | Harc_tail] [Edestination Hchange]]].
      * rewrite Edestination in *. clear node Edestination.
        destruct no_change; injection Eapproxes_after as E1 E2;
        rewrite E1 in *; rewrite E2 in *.
        -- assert (Hchange' := Hchange).
           apply IHoutgoing_arc_of_change in Hchange.
           destruct Hchange as [arc' [Harc'_In Edestination']].
           rewrite Edestination' in *.
           eapply IHworklist_added.
           exists arc'. repeat split; assumption.
        -- rewrite <- Earc. apply set_add_1. reflexivity.
      * destruct no_change; injection Eapproxes_after as E1 E2;
        rewrite E1 in *; rewrite E2 in *.
        -- apply IHworklist_added.
           exists arc. repeat split; assumption.
        -- destruct (proj1_sig child =? proj1_sig node) eqn:Echild_node.
           ++ apply Nat.eqb_eq in Echild_node.
              apply set_add_1. assumption.
           ++ rewrite add_2 in Hchange by ( intro contra; rewrite contra in Echild_node;
                                            rewrite Nat.eqb_refl in Echild_node; discriminate ).
              apply set_add_2.
              apply IHworklist_added.
              exists arc. repeat split; assumption.
    + intros node Hchange.
      destruct (domain.eqb (find approxes node) (find acc_approxes node)) eqn:Eacc_change.
      * destruct no_change; injection Eapproxes_after as E1 _; rewrite E1 in *.
        -- apply domain.eqb_true_iff in Eacc_change. rewrite Eacc_change in Hchange.
           erewrite (proj2 (domain.eqb_true_iff _ _)) in Hchange by reflexivity.
           discriminate.
        -- destruct (proj1_sig node =? proj1_sig child) eqn:Enode_child.
           ++ apply Nat.eqb_eq in Enode_child. apply exist_eq_of_porj1_sig_eq in Enode_child.
              rewrite Enode_child.
              eexists. split.
              ** left. reflexivity.
              ** reflexivity.
           ++ rewrite add_2 in Hchange by ( intro contra; rewrite contra in Enode_child;
                                            rewrite Nat.eqb_refl in Enode_child; discriminate ).
              apply domain.eqb_true_iff in Eacc_change. rewrite Eacc_change in Hchange.
              erewrite (proj2 (domain.eqb_true_iff _ _)) in Hchange by reflexivity.
              discriminate.
      * destruct (IHoutgoing_arc_of_change _ Eacc_change) as [arc [Harc_In_outgoing Edestination]].
        exists arc. split.
        -- right. assumption.
        -- assumption.
Qed.

Program Fixpoint fixpoint_above (approxes : partial_approximations)
                        {wf partial_approximations_order approxes} :
                          partial_approximations :=
  match choose approxes.(pworklist) with
  | Some worked => fixpoint_above (iterate worked approxes)
  | None        => approxes
  end.
Next Obligation.
  apply partial_approximations_order_iterate.
  symmetry in Heq_anonymous. apply choose_1 in Heq_anonymous. assumption.
Qed.
Next Obligation.
  apply partial_approximations_order_well_founded.
Qed.

Lemma fixpoint_above_red (approxes : partial_approximations) :
    fixpoint_above approxes
  = match choose approxes.(pworklist) with
    | Some worked => fixpoint_above (iterate worked approxes)
    | None        => approxes
    end.
Proof. (* What is going on here??? *) Admitted.

Lemma fixpoint_above_preserves_correct (approxes : partial_approximations) :
    partial_approximations_correct approxes ->
  partial_approximations_correct (fixpoint_above approxes).
Proof.
  apply (well_founded_ind
           partial_approximations_order_well_founded
           (fun approxes' =>   partial_approximations_correct approxes' ->
                             partial_approximations_correct (fixpoint_above approxes'))).
  intros approxes' IH Hcorrect_before.
  rewrite fixpoint_above_red.
  destruct (choose approxes'.(pworklist)) as [worked |] eqn:Echoose.
  - apply choose_1 in Echoose.
    apply IH.
    + apply partial_approximations_order_iterate. assumption.
    + apply iterate_preserves_correct; assumption.
  - assumption.
Qed.

Lemma fixpoint_above_empty_worklist (approxes : partial_approximations) :
    Empty (fixpoint_above approxes).(pworklist).
Proof.
  apply (well_founded_ind
           partial_approximations_order_well_founded
           (fun approxes' => Empty (pworklist (fixpoint_above approxes')))).
  intros approxes' IH.
  rewrite fixpoint_above_red.
  destruct (choose approxes'.(pworklist)) eqn:Echoose.
  - apply choose_1 in Echoose.
    apply IH.
    apply partial_approximations_order_iterate.
    assumption.
  - apply choose_2 in Echoose.
    assumption.
Qed.

Definition initial_partial_approximations : partial_approximations := {|
  papproximations := add (constant_total_map cfg.(cnode_id_list)
                                             cfg.(cnode_id_set_iff_node_id_list)
                                             domain.empty_environment)
                         initial_node_id
                         domain.initial_environment;
  pworklist       := set_add empty_set_with_domain initial_node_id
|}.

Lemma initial_partial_approximations_correct :
  partial_approximations_correct initial_partial_approximations.
Proof.
  split.
  - intros arc Harc_in_cfg Hsource_not_In_worklist. simpl in *.
    intros src_env dst_env Hinstruction_small_step Hsrc_env_In.
    destruct (proj1_sig initial_node_id =? proj1_sig arc.(asource)) eqn:Einitial_source.
    + apply Nat.eqb_eq in Einitial_source.
      exfalso. apply Hsource_not_In_worklist. apply set_add_1. assumption.
    + rewrite add_2 in Hsrc_env_In by ( intro contra; rewrite contra in Einitial_source;
                                        rewrite Nat.eqb_refl in Einitial_source; discriminate ).
      rewrite find_const_total_map in Hsrc_env_In.
      apply domain.empty_environment_correct in Hsrc_env_In. destruct Hsrc_env_In.
  - simpl. rewrite add_1 by reflexivity. apply domain.initial_environment_correct.
Qed.

Definition approximations_correct (approxes : total_map node_id_set domain.abstract_environment) :
                                    Prop :=
  forall (node : node_id) (env : environment),
    star (small_step cfg) (initial_state initial_node_id) (node, env) ->
      Ensembles.In (domain.to_concrete (find approxes node)) env.

Lemma papproximations_correct_of_empty_worklist
        (approxes : partial_approximations) :
    partial_approximations_correct approxes ->
    Empty approxes.(pworklist) ->
  approximations_correct approxes.(papproximations).
Proof.
  intros [Happroxes_correct Hinitial_env] Hempty_worklist node env Hstar_small_step.
  rewrite (eq_refl _ : node = fst (node, env)) in *.
  rewrite (eq_refl _ : env  = snd (node, env)) in *.
  eapply (star_ind' _ ( fun _ state => domain.to_concrete
                                         (find approxes.(papproximations) (fst state))
                                         (snd state) )
                    _ _ Hstar_small_step);
  simpl in *.  
  - assumption.
  - intros [src src_env] [dst dst_env] Hsrc_env_In Hsmall_step. simpl in *.
    unfold partial_approximations_correct_at_arc in Happroxes_correct. simpl in Happroxes_correct.
    inv Hsmall_step.
    eapply Happroxes_correct; try eassumption.
    apply Hempty_worklist.
Qed.

Definition overapproximation : total_map node_id_set domain.abstract_environment :=
  (fixpoint_above initial_partial_approximations).(papproximations).

Lemma overapproximation_correct : approximations_correct overapproximation.
Proof.
  apply papproximations_correct_of_empty_worklist.
  - apply fixpoint_above_preserves_correct. apply initial_partial_approximations_correct.
  - apply fixpoint_above_empty_worklist.
Qed.

End BasicIterator.


