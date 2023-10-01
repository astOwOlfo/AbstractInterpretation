From AbstractInterpretation Require Import Maps Order.

Section Graph.

Context {vertex_set : nat -> Prop}.

Definition vertex := { v : nat | vertex_set v }.

Definition directed_graph : Type := vertex -> vertex -> Prop.

Definition acyclic (g : directed_graph) := well_founded g.

Definition path (g : directed_graph)
                (source destination : vertex) : Prop :=
  star g source destination.

Definition dag_order (g : directed_graph)
                     (lows highs : set_with_domain vertex_set) : Prop :=
  forall low, contains lows low -> exists high, contains highs high /\ path g high low.

Lemma dag_order_trans (g : directed_graph)
                      (vertices1 vertices2 vertices3 : set_with_domain vertex_set) :
    dag_order g vertices1 vertices2 ->
    dag_order g vertices2 vertices3 ->
  dag_order g vertices1 vertices3.
Proof. Admitted.

Lemma to_strict_dag_order_well_founded_of_acyclic (g : directed_graph)
                                                  (Hacyclic : acyclic g) :
  well_founded (to_strict (dag_order g)).
Proof. Admitted.

Lemma no_loop_of_acyclic (g : directed_graph)
                         (Hacyclic : acyclic g)
                         (vertex : vertex) :
  ~g vertex vertex.
Proof. Admitted.

End Graph.

Arguments directed_graph : clear implicits.
