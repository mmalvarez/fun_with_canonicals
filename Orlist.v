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

(*
Record orl_class (P : Prop) := (* should be Prop? *)
  OrlClass {
      list_of : tagged_propl;
      _ : untag (list_of) <> nil;
      _ : orl_valid P list_of}.
*)

(*
Structure orl_type :=
  OrlPack {obj : Prop; class_of : orl_class obj}.

Definition get_lst (e : orl_type) : tagged_propl :=
  let 'OrlPack _ (OrlClass lstof _ _) := e in lstof.
*)

Structure orlist := Orlist { 
         P : Prop;
         list_of : tagged_propl;
         _ : untag (list_of) <> nil;
         _ : orl_valid P list_of }.

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
  Orlist P (singleton_tag (cons P nil)) (singleton_nemp_proof P) (singleton_valid_proof P).

Definition check_list {orl : orlist} (Q : P orl) : tagged_propl :=
  list_of orl.

Inductive phantom {T : Type} (t : T) : Type := Phantom.
Definition unify {T1 T2} (t1 : T1) (t2 : T2) :=
  phantom t1 -> phantom t2.

Definition id {T : Type} {t : T} (x : phantom t) := x.    

Definition get_list {orl : orlist}
           (Q : Prop) (uni : unify Q (P orl)) :=
  list_of orl.

Lemma cons_nemp_proof :
  forall (P1 : Prop) (orl : orlist),
    (cons P1 (untag (list_of orl))) <> nil.
intros. intro. inversion H.
Qed.

Lemma cons_valid_proof : forall (P1 : Prop) (orl : orlist),
                          orl_valid (P1 \/ (P orl)) (cons_tag (cons P1 (list_of orl))).
Proof.
dependent inversion orl.
  simpl. unfold orl_valid in *.
  simpl.
  destruct (untag list_of0).
  + elimtype False. auto.
  + simpl in *.
    destruct l.
    * simpl. rewrite o. reflexivity.
    * simpl. rewrite o. reflexivity.
Qed.
(*intro.
    unfold unify in uni.
    pose (uni (Phantom P1)).
    destruct l.
    * simpl in *. rewrite o. rewrite equ. auto.
    * simpl. rewrite o. rewrite equ. auto.
Qed.*)
 
Canonical Structure cons_orl (P1 : Prop) (orl : orlist) :=
  Orlist (P1 \/ (P orl)) (cons_tag (cons P1 (untag (list_of orl))))
         (cons_nemp_proof P1 orl) (cons_valid_proof P1 orl).

Eval compute in (get_list (True \/ False) id).

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
