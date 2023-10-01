From AbstractInterpretation Require Import Expression Environment Graph Maps Sigmas.

From Coq Require Import Structures.OrderedType Lists.List FSets.FSetAVL.
Import ListNotations.

Import Maps.

Section CFG.

Context {node_id_set : nat -> Prop}.

Definition node_id : Set :=
  { id : nat | node_id_set id }.

Variant instruction : Set :=
  (* Do nothing. *)
| Skip :   instruction
  (* Assign result of expression to variable. *)
| Assign : var_id -> int_expression -> instruction
  (* Expression that must be satisfied to make the transition *)
| Guard :  bool_expression -> instruction
  (* Error if the assertion is not satisfied *)
| Assert : bool_expression -> instruction.

Record arc : Type := {
  asource :      node_id;
  adestination : node_id;
  ainstruction : instruction
}.

Record cfg : Type := {
  carcs :          list arc;
  coutgoing_arcs : total_map node_id_set (list arc);
  cingoing_arcs :  total_map node_id_set (list arc);
  cwidened :       set_with_domain node_id_set;

  cingoing_arcs_iff :  forall (arc : arc) (destination : node_id),
                             In arc (find cingoing_arcs destination)
                         <-> In arc carcs /\ destination = arc.(adestination);

  coutgoing_arcs_iff : forall (arc : arc) (source : node_id),
                             In arc (find coutgoing_arcs source)
                         <-> In arc carcs /\ source = arc.(asource);

  (* [cunwidened_arc_graph_acyclic cfg] is equivalent to [acyclic (unwidened_arc_graph cfg)] *)
  cunwidened_arc_graph_acyclic :
    acyclic ( fun src dst =>    ( exists arc : arc,    In arc carcs
                                                   /\ arc.(asource) = src
                                                   /\ arc.(adestination) = dst )
                             /\ ~contains cwidened dst );

    (* We require there to be finitely many node ids. *)
  cnode_id_list : list nat;
  cnode_id_set_iff_node_id_list : forall node_id : nat,     node_id_set node_id
                                                        <-> In node_id cnode_id_list
}.

Definition unwidened_arc_graph (cfg : cfg) : directed_graph node_id_set :=
  (fun src dst => ( exists arc : arc,    In arc cfg.(carcs)
                                     /\ arc.(asource) = src
                                     /\ arc.(adestination) = dst )
                  /\ ~contains cfg.(cwidened) dst ).

Definition map_hypothesis {X Y : Type} (xs : list X) (f : forall x : X, List.In x xs -> Y) : list Y.
  induction xs as [| head tail IH].
  - exact [].
  - apply cons.
    + apply (f head).
      left. reflexivity.
    + apply IH.
      intros x Htail.
      apply (f x).
      right. assumption.
Qed.

Lemma In_map_hypothesis_iff {X Y : Type} (xs : list X) (y : Y) (f : forall x : X, List.In x xs -> Y) :
  In y (map_hypothesis xs f) <-> exists (x : X) (H : List.In x xs), y = f x H.
Proof. Admitted.

Program Definition node_list (cfg : cfg) : list node_id :=
  map_hypothesis cfg.(cnode_id_list) (fun id H => exist _ id _).
Next Obligation.
  apply cfg0.(cnode_id_set_iff_node_id_list) in H. assumption.
Qed.

Lemma In_node_list (cfg : cfg) (node : node_id) :
  In node (node_list cfg).
Proof.
  destruct node as [node_id Hnode_id_set].
  apply In_map_hypothesis_iff.
  exists node_id. exists (proj1 (cfg.(cnode_id_set_iff_node_id_list) _) Hnode_id_set).
  apply exist_eq_of_porj1_sig_eq. reflexivity.
Qed.

End CFG.
