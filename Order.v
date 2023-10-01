From Coq Require Import Lists.List Structures.OrderedType
                        Logic.FunctionalExtensionality Logic.PropExtensionality.
Import ListNotations.

Variant lexicographical_order {T1 T2 : Type}
                              (order1 : T1 -> T1 -> Prop)
                              (order2 : T2 -> T2 -> Prop) :
                                T1 * T2 -> T1 * T2 -> Prop :=
  | Lex1 (x1 y1 : T1) (x2 y2 : T2) :
        order1 x1 y1 ->
      lexicographical_order order1 order2 (x1, x2) (y1, y2)
  | Lex2 (x1 : T1) (x2 y2 : T2) :
        order2 x2 y2 ->
      lexicographical_order order1 order2 (x1, x2) (x1, y2).

Definition to_strict {T : Type} (rel : T -> T -> Prop) (x y : T) : Prop :=
  x <> y /\ rel x y.

Inductive star {T : Type} (rel : T -> T -> Prop) : T -> T -> Prop :=
  | StarRefl (x : T) :                                          star rel x x
  | StarCons {x y z : T} (Hxy : rel x y) (Hyz : star rel y z) : star rel x z.

Arguments StarRefl {T rel}.
Arguments StarCons {T rel x y z}.

Inductive strict_star {T : Type} (rel : T -> T -> Prop) : T -> T -> Prop :=
  | StrictStarIntro {x y : T}   (Hxy : rel x y) :                             strict_star rel x y
  | StrictStarCons  {x y z : T} (Hxy : rel x y) (Hyz : strict_star rel y z) : strict_star rel x z.

Arguments StrictStarIntro {T rel x y}.
Arguments StrictStarCons  {T rel x y z}.

Lemma star_of_rel {T : Type} (rel : T -> T -> Prop) (x y : T) (Hxy : rel x y) : star rel x y.
Proof (StarCons Hxy (StarRefl _)).

Lemma star_trans {T : Type} (rel : T -> T -> Prop) (x y z : T) :
    transitive _ (star rel).
Proof. Admitted.

Lemma star_ind' {T : Type} (rel P : T -> T -> Prop) (x y : T) :
    star rel x y ->
    P x x ->
    (forall y z : T, P x y -> rel y z -> P x z) ->
    P x y.
Proof. Admitted.

Lemma strict_star_trans {T : Type} (rel : T -> T -> Prop) (x y z : T) :
    strict_star rel x y ->
    strict_star rel y z ->
  strict_star rel x z.
Proof. Admitted.

Lemma star_strict_star_trans {T : Type} (rel : T -> T -> Prop) (x y z : T) :
    star        rel x y ->
    strict_star rel y z ->
  strict_star rel x z.
Proof. Admitted.

Lemma strict_star_star_trans {T : Type} (rel : T -> T -> Prop) (x y z : T) :
    strict_star rel x y ->
    star        rel y z ->
  strict_star rel x z.
Proof. Admitted.

Lemma strict_star_well_founded {T : Type} (rel : T -> T -> Prop) :
    well_founded rel ->
  well_founded (strict_star rel).
Proof. Admitted.

Lemma cases_strict_star_lexicographical_order_of_trans
    {T1 T2 : Type}
    (order1 : T1 -> T1 -> Prop)
    (order2 : T2 -> T2 -> Prop)
    (Htrans1 : transitive _ order1)
    (Htrans2 : transitive _ order2)
    (x1 y1 : T1)
    (x2 y2 : T2) :
      strict_star (lexicographical_order order1 order2) (x1, x2) (y1, y2) ->
     order1 x1 y1
  \/ (x1 = y1 /\ order2 x2 y2).
Proof. Admitted.

Lemma lexicographical_order_well_founded
      {T1 T2 : Type}
      (order1 : T1 -> T1 -> Prop)
      (order2 : T2 -> T2 -> Prop) :
    well_founded order1 ->
    well_founded order2 ->
  well_founded (lexicographical_order order1 order2).
Proof. Admitted.

Lemma strict_star_lexicographical_order_of_first {T1 T2 : Type}
                                                 (order1 : T1 -> T1 -> Prop)
                                                 (order2 : T2 -> T2 -> Prop)
                                                 (x1 y1 : T1)
                                                 (x2 y2 : T2) :
    strict_star order1 x1 y1 ->
  strict_star (lexicographical_order order1 order2) (x1, x2) (y1, y2).
Proof. Admitted.

Lemma strict_star_fold_left_apply_of_step
    {X Y Z :        Type}
    (rel :          Z -> Z -> Prop)
    (f :            Y -> X -> Y)
    (g :            Y -> Z)
    (xs :           list X)
    (y0 :           Y)
    (Hstep :        forall x y, In x xs -> star rel (g (f y x)) (g y))
    (Hstrict_step : exists x, In x xs /\ forall y, strict_star rel (g (f y x)) (g y)) :
  strict_star rel (g (fold_left f xs y0)) (g y0).
Proof. Admitted.

Lemma star_fold_left_apply {X Y Z : Type}
                           (rel :   Z -> Z -> Prop)
                           (f :     Y -> X -> Y)
                           (g :     Y -> Z)
                           (xs :    list X)
                           (y0 :    Y)
                           (Hf :    forall x y, In x xs ->
                                        star rel (g y) (g y0) ->
                                      star rel (g (f y x)) (g y0)) :
  star rel (g (fold_left f xs y0)) (g y0).
Proof. Admitted.

Lemma proj_well_founded {X Y : Type} (f : X -> Y) (rel : Y -> Y -> Prop) (Hwf_rel : well_founded rel) :
  well_founded (fun x1 x2 : X => rel (f x1) (f x2)).
Proof.
  unfold well_founded.
  intro a.
  remember (f a) as fa eqn:Heq.
  generalize dependent a.
  induction (Hwf_rel fa) as [y _ IH].
  intros x Hf. constructor. intros y' Hy.
  eapply IH.
  - rewrite Hf. apply Hy.
  - reflexivity.
Qed.

Lemma well_founded_of_implies {X Y : Type}
                              (weak_ord : X -> X -> Prop)
                              (strong_ord : Y -> Y -> Prop)
                              (f : X -> Y) :
    ( forall x y : X, weak_ord x y -> strong_ord (f x) (f y) ) ->
    well_founded strong_ord ->
  well_founded weak_ord.
Proof. Admitted.

(* Lemma well_founded_equiv_congr {X : Type} (rel rel' : X -> X -> Prop)
                               (Hequiv : forall x1 x2, rel x1 x2 <-> rel' x1 x2) :
    well_founded rel ->
  well_founded rel'.
Proof. Admitted.

Lemma to_strict_proj_eq {X Y : Type} (f : X -> Y) (rel : Y -> Y -> Prop)
                        (Hinj : forall x1 x2, f x1 = f x2 -> x1 = x2) :
    to_strict (fun x1 x2 => rel (f x1) (f x2))
  = fun x1 x2 => to_strict rel (f x1) (f x2).
Proof.
  apply functional_extensionality.
  intro x1.
  apply functional_extensionality.
  intro x2.
  unfold to_strict.
  apply propositional_extensionality.
  split; intro H; split; try tauto; intro contra.
  - apply Hinj in contra. tauto.
  - rewrite contra in H. tauto.
Qed. *)