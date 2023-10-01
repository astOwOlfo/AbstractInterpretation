From Coq Require Import Ensembles.
Import Ensembles.

(* Why is it not this way in the standard library? *)
Arguments In           {U}.
Arguments Empty_set    {U}.
Arguments Full_set     {U}.
Arguments Union        {U}.
Arguments Intersection {U}.

(* Why is this not in the standard libarry? *)
Definition Subset {U : Type} (S T : Ensemble U) : Prop :=
  forall x : U, In S x -> In T x.

Definition Is_empty {U : Type} (S : Ensemble U) : Prop :=
  forall x, ~In S x. 

(* Making myself cool by not using functional and propositional extensionality. *)
Definition ensemble_equal {U : Type} (S T : Ensemble U) : Prop :=
  forall x : U, In S x <-> In T x.

Definition extensionally_equal {A B : Type} (f g : A -> B) : Prop :=
  forall a : A, f a = g a.

Lemma ensemble_equal_trans {U :     Type}
                           {R S T : Ensemble U}
                           (HRS :   ensemble_equal R S)
                           (HST :   ensemble_equal S T) :
                             ensemble_equal R T.
Proof. Admitted.

Lemma Subset_trans {U : Type} (R S T : Ensemble U) :
  Subset R S -> Subset S T -> Subset R T.
Proof. Admitted.
