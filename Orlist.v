Require Import List.
(*Import ListNotations.*)
Require Import Infrastructure.

Check fold_right.

Fixpoint foldr_head' {A : Type} (f : A -> A -> A) (df1 df2 : A) (l : list A) : A :=
  match l with
    | nil => f df1 df2
    | cons a l' => f df1 (foldr_head' f df2 a l')
  end.

Definition foldr_head {A : Type} (f : A -> A -> A) (dfl : A) (l : list A) : A :=
  match l with
    | nil => dfl
    | a :: nil => a
    | a :: b :: rest => foldr_head' f a b rest
  end.

Structure tagged_propl := Tag {untag :> list Prop}.
Definition singleton_tag P := Tag P.
Canonical Structure cons_tag P := singleton_tag P.

Definition orl_valid (P : Prop) (Ps : tagged_propl) : Prop :=
  foldr_head or False Ps = P.

Record orl_class (P : Prop) := (* should be Prop? *)
  OrlClass {
      list_of : tagged_propl;
      _ : untag (list_of) <> nil;
      _ : orl_valid P list_of}.

Structure orl_type :=
  OrlPack {obj : Prop; class_of : orl_class obj}.

Definition get_lst (e : orl_type) : tagged_propl :=
  let 'OrlPack _ (OrlClass lstof _ _) := e in lstof.

Require Import Infrastructure.

(*Structure orlist := Orlist { 
         P : Prop;
         list_of : tagged_propl;
         _ : untag (list_of) <> nil;
         _ : orl_valid P list_of }.*)

(*Arguments list_of {o}.*)

Lemma singleton_nemp_proof : forall (P : Prop), (cons P nil) <> nil.
Proof.
  intros. intro. inversion H.
Qed.

Lemma singleton_valid_proof : forall (P : Prop), orl_valid P (singleton_tag (cons P nil)).
Proof.
  intros. compute. reflexivity.
Qed.

Canonical Structure singleton_orl (P : Prop) :=
  [find 

Canonical Structure singleton_orl (P : Prop) :=
  Orlist P (singleton_tag (cons P nil)) (singleton_nemp_proof P) (singleton_valid_proof P).

(* need a dummy object that typechecks to it *)

(*
GIVEN a Prop

- Get me something relating corresponding Props and list Prop
- Project out the list Prop

FINALLY have a list Prop
*)

Definition get_list {orl : orlist}
           {Q : P orl} {Prp : P orl} {gg : P Q} : tagged_propl :=
  list_of orl.

Eval compute in (get_list True).

Lemma cons_nemp_proof :
  forall (P1 P2 : Prop) (orl : orlist P2),
    (cons P1 (untag (list_of orl))) <> nil.
intros. intro. inversion H.
Qed.

Lemma cons_valid_proof : forall (P1 P2 : Prop) (orl : orlist P2),
                          orl_valid (P1 \/ P2) (cons_tag (cons P1 (list_of orl))).
Proof.
dependent inversion orl.
  simpl. unfold orl_valid in *.
  simpl.
  destruct (untag list_of0).
  + elimtype False. auto.
  + simpl in o.
    destruct l.
    * simpl. rewrite o. auto.
    * simpl. rewrite o. auto.
Qed.
 
Canonical Structure cons_orl (P1 P2 : Prop) (orl : orlist P2) :=
  Orlist (P1 \/ P2) (cons_tag (cons P1 (untag (list_of orl))))
         (cons_nemp_proof P1 P2 orl) (cons_valid_proof P1 P2 orl).

Definition get_list (P : Prop) {orl : orlist P} :=
  list_of orl.

Eval compute in (@get_list True).

Eval compute in (@get_list True (singleton_orl True)).

(* 
Lemma derpR : forall (P : Prop) (orl : orlist),
                orl_valid P (list_of orl).
Proof.
dependent inversion orl.
auto.
Qed.

Arguments derpR P {orl}.*)
(*
Lemma hi : exists ls, orl_valid (True \/ False \/ False) ls.
Proof.
eexists.
eapply (derpR (True \/ False \/ False)).
Grab Existential Variables.
apply cons_orl. apply cons_orl. apply singleton_orl.
Qed.
*)

(*
Definition test1 : exists (ps : tagged_propl), orl_valid (True \/ True) ps /\ length ps = 2.
refine (@derpR (True \/ True) _).
apply cons_orl.
apply singleton_orl.
Defined.
*)
