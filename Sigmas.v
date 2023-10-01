From Coq Require Import Logic.ProofIrrelevance.

Lemma exist_eq_of_porj1_sig_eq {T : Type} (P : T -> Prop) (x y : sig P) :
    proj1_sig x = proj1_sig y ->
  x = y.
Proof.
  intro H. destruct x. destruct y. simpl in H. subst. f_equal. apply proof_irrelevance.
Qed.
