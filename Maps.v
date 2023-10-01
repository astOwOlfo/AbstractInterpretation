From Coq Require Import FSets.FMapAVL FSets.FSetAVL Structures.OrderedTypeEx Lists.SetoidList
                        PeanoNat Lists.List Bool.
Import ListNotations.

Module NatMap := FMapAVL.Make Nat_as_OT.
Module NatSet := FSetAVL.Make Nat_as_OT.

Section TotalMap.

Record total_map (key_set : nat -> Prop) (Value : Type) : Type := {
  tmap :  NatMap.t Value;
  tkeys : forall key : nat, key_set key <-> NatMap.In key tmap
}.

Global Arguments tmap  {key_set Value}.
Global Arguments tkeys {key_set Value}.

Context {key_set : nat -> Prop} {Value : Type}.

Definition keys (map : total_map key_set Value) : Set :=
  { key : nat | key_set key }.

Program Definition find (map : total_map key_set Value) (key : keys map) : Value :=
  match NatMap.find key map.(tmap) with
  | Some value => value
  | None       => False_rect Value _
  end.
Next Obligation.
  destruct key as [k Hkey]. simpl in Heq_anonymous.
  apply map.(tkeys) in Hkey. destruct Hkey as [? Hkey]. apply NatMap.find_1 in Hkey.
  rewrite Hkey in Heq_anonymous. discriminate.
Qed.

Lemma find_1 (map : total_map key_set Value) (key key' : keys map) :
    proj1_sig key = proj1_sig key' ->
  find map key = find map key'.
Admitted.

Definition has_key (map : total_map key_set Value) (key : keys map) : Prop :=
  exists value, find map key = value.

Program Definition add (map : total_map key_set Value) (key : keys map) (value : Value) :
                         total_map key_set Value := {|
  tmap  := NatMap.add key value map.(tmap);
  tkeys := _
|}.
Admit Obligations.

Arguments NatMap.eq_key_elt {elt}.

Definition fold {Acc : Type}
                (map  : total_map key_set Value)
                (f :    keys map -> Value -> Acc -> Acc)
                (init : Acc) : Acc.
                destruct map as [tmap tkeys].
  assert (Hkeys : forall key value, InA NatMap.eq_key_elt (key, value) (NatMap.elements tmap) ->
                                      key_set key).
  { intros key value HIn. apply NatMap.elements_2 in HIn. apply tkeys. exists value. assumption. }
  revert dependent init. revert Hkeys.
  induction (NatMap.elements tmap) as [| [key value] tail IH]; intros.
  - exact init.
  - apply IH; intros.
    + eapply Hkeys. right. eassumption.
    + apply f.
      * exists key. eapply Hkeys. left. reflexivity.
      * exact value.
      * exact init.
Defined.

Lemma add_1 (map : total_map key_set Value) (key key' : keys map) (value : Value) :
    proj1_sig key = proj1_sig key' ->
  find (add map key value) key' = value.
Admitted.

Lemma add_2 (map : total_map key_set Value) (key key' : keys map) (value : Value) :
    proj1_sig key <> proj1_sig key' ->
    find (add map key value) key' = find map key'.
Admitted.

Lemma add_3 (map : total_map key_set Value) (key key' : keys map) (value value' : Value) :
    proj1_sig key <> proj1_sig key ->
    find (add map key value') key' = value ->
  find map key' = value.
Admitted.

Program Definition constant_total_map
    (keys_as_list : list nat)
    (Ekeys :        forall key : nat, key_set key <-> In key keys_as_list)
    (value :        Value) :
      total_map key_set Value :=
{| tmap  := fold_left (fun map key => NatMap.add key value map) keys_as_list (NatMap.empty _) |}.
Admit Obligations.

Lemma find_const_total_map keys_as_list Ekeys key value :
  find (constant_total_map keys_as_list Ekeys value) key = value.
Admitted.

Program Definition init_map (keys_as_list : list nat)
                            (Ekeys :        forall key : nat, key_set key <-> In key keys_as_list)
                            (key_to_value : {key : nat | key_set key} -> Value) :
                              total_map key_set Value :=
{| tmap := fold_left (fun map key => NatMap.add key (key_to_value (exist _ key _)) map)
                     keys_as_list
                     (NatMap.empty _) |}.
Admit Obligations.

Lemma find_init_map (keys_as_list : list nat)
                    (Ekeys :        forall key : nat, key_set key <-> In key keys_as_list)
                    (key_to_value : {key : nat | key_set key} -> Value)
                    (key :          {key : nat | key_set key}) :
  find (init_map keys_as_list Ekeys key_to_value) key = key_to_value key.
Admitted.

End TotalMap.


Section SetWithDomain.

Record set_with_domain (domain_set : nat -> Prop) : Type := {
  dset :    NatSet.t;
  ddomain : forall elt, NatSet.In elt dset -> domain_set elt
}.

Global Arguments dset    {domain_set}.
Global Arguments ddomain {domain_set}.

Context {domain_set : nat -> Prop}.

Definition domain (set : set_with_domain domain_set) : Set :=
  { n : nat | domain_set n }.

Definition contains (set : set_with_domain domain_set) (elt : domain set) : Prop :=
  NatSet.In (proj1_sig elt) set.(dset).

Definition mem (set : set_with_domain domain_set) (elt : domain set) : bool :=
  NatSet.mem (proj1_sig elt) set.(dset).

Lemma mem_1 (set : set_with_domain domain_set) (elt : domain set) :
    contains set elt ->
  mem set elt = true.
Admitted.

Lemma mem_2 (set : set_with_domain domain_set) (elt : domain set) :
    mem set elt = true ->
  contains set elt.
Admitted.

Program Definition set_add (set : set_with_domain domain_set) (elt : domain set) :
                         set_with_domain domain_set := {|
  dset    := NatSet.add elt set.(dset);
  ddomain := _
|}.
Admit Obligations.

Lemma set_add_of_contains (set : set_with_domain domain_set) (elt : domain set) :
    contains set elt ->
  set_add set elt = set.
Admitted.

Lemma set_add_1 (set : set_with_domain domain_set) (elt elt' : domain set) :
    proj1_sig elt = proj1_sig elt' ->
  contains (set_add set elt) elt'.
Admitted.

Lemma set_add_2 (set : set_with_domain domain_set) (elt elt' : domain set) :
    contains set elt' ->
  contains (set_add set elt) elt'.
Admitted.

Lemma set_add_3 (set : set_with_domain domain_set) (elt elt' : domain set) :
    proj1_sig elt <> proj1_sig elt' ->
    contains (set_add set elt) elt' ->
  contains set elt'.
Admitted.

Program Definition set_remove (set : set_with_domain domain_set) (elt : domain set) :
                            set_with_domain domain_set := {|
  dset    := NatSet.remove elt set.(dset);
  ddomain := _
|}.
Admit Obligations.

Lemma set_remove_1 (set : set_with_domain domain_set) (elt : domain set) :
  ~contains (set_remove set elt) elt.
Admitted.

Lemma set_remove_2 (set : set_with_domain domain_set) (elt elt' : domain set) :
    proj1_sig elt <> proj1_sig elt' ->
    contains set elt' ->
  contains (set_remove set elt) elt'.
Admitted.

Lemma set_remove_3 (set : set_with_domain domain_set) (elt elt' : domain set) :
    contains (set_remove set elt) elt' ->
  contains set elt'.
Admitted.

Program Definition choose (set : set_with_domain domain_set) : option (domain set) :=
  match NatSet.choose set.(dset) with
  | Some elt => Some (exist _ elt _)
  | None     => None
  end.
Admit Obligations.

Definition Empty (set : set_with_domain domain_set) : Prop :=
  NatSet.Empty set.(dset).

Lemma choose_1 (set : set_with_domain domain_set) (elt : domain set) :
    choose set = Some elt ->
  contains set elt.
Admitted.

Lemma choose_2 (set : set_with_domain domain_set) :
    choose set = None ->
  Empty set.
Admitted.

Program Definition empty_set_with_domain : set_with_domain domain_set := {|
  dset    := NatSet.empty;
  ddomain := _
|}.
Admit Obligations.

Program Definition elements (set : set_with_domain domain_set) : list nat :=
  NatSet.elements set.(dset).
Admit Obligations.

Lemma domain_of_In_elements (set : set_with_domain domain_set) (elt : nat) :
    In elt (elements set) ->
  domain_set elt.
Admitted.

Lemma elements_1 (set : set_with_domain domain_set) (elt : nat) (elt' : domain set) :
    elt = proj1_sig elt' ->
    contains set elt' ->
  In elt (elements set).
Admitted.

Lemma elements_2 (set : set_with_domain domain_set) (elt : nat) (elt' : domain set) :
    elt = proj1_sig elt' ->
    In elt (elements set) ->
  contains set elt'.
Admitted.

End SetWithDomain.


Section Restrict.

Context {key_set : nat -> Prop} {Value : Type}.

Program Definition restrict (map :  total_map key_set Value)
                            (keys : set_with_domain key_set) :
                              total_map (fun key => NatSet.In key keys.(dset)) Value := {|
  tmap  := fold map
                ( fun key value map_acc => if mem keys key
                                           then NatMap.add (proj1_sig key) value map_acc
                                           else map_acc )
                (NatMap.empty _);
|}.
Admit Obligations.

Lemma find_restrict (map :  total_map key_set Value)
                    (set :  set_with_domain key_set)
                    (key :  keys (restrict map set))
                    (key' : keys map) :
    proj1_sig key = proj1_sig key' ->
  find (restrict map set) key = find map key'.
Admitted.

Lemma restrict_add_of_not_contains (map :   total_map key_set Value)
                                   (set :   set_with_domain key_set)
                                   (key :   keys map)
                                   (value : Value) :
    ~contains set key ->
  restrict (add map key value) set = restrict map set.
Admitted.

(* Lemma find_restrict (map :  total_map key_set Value)
                    (set  : set_with_domain key_set)
                    (key :  keys map)
                    (Hkey : contains set key) :
    find (restrict map set) (exist _ (proj1_sig key) Hkey) = find map key.
Admitted. *)

Fixpoint mem_list_nat (n : nat) (xs : list nat) : bool :=
  match xs with
  | x::xs => (n =? x) || mem_list_nat n xs
  | []    => false
  end.

Program Definition restrict_to_list (map :  total_map key_set Value)
                                    (keys : list nat) :
                                      total_map (fun key : nat => In key keys) Value := {|
  tmap  := fold map
                ( fun key value map_acc => if mem_list_nat key keys
                                           then NatMap.add key value map_acc
                                           else map_acc )
                (NatMap.empty _);
|}.
Admit Obligations.

Lemma find_restrict_to_list (map :   total_map key_set Value)
                            (_keys : list nat)
                            (key :   keys map)
                            (key' :  keys (restrict_to_list map _keys)) :
    proj1_sig key = proj1_sig key' ->
  find (restrict_to_list map _keys) key' = find map key.
Admitted.

End Restrict.