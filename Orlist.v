Require Import List.
Import ListNotations.

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

Definition orl_valid (P : Prop) (Pst : tagged_propl) : Prop :=
  foldr_head or False (untag Pst) = P.

Structure orlist (P : Prop) 
  := Orlist { 
         list_of : tagged_propl;
         _ : (untag list_of) <> nil;
         _ : orl_valid P list_of }.

Arguments list_of {P} _.

Lemma singleton_nemp_proof : forall (P : Prop), [P] <> nil.
Proof.
  intros. intro. inversion H.
Qed.

Lemma singleton_valid_proof : forall (P : Prop), orl_valid P (singleton_tag [P]).
Proof.
  intros. compute. reflexivity.
Qed.

Canonical Structure singleton_orl (P : Prop) :=
  Orlist P (singleton_tag [P]) (singleton_nemp_proof P) (singleton_valid_proof P).

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


(* another example - tagging props with something they imply *)
Module Narrow.
  Structure tagged_prop := PTag {puntag :> Prop}.
  Definition andr_tag P := PTag P.
  Definition andl_tag P := andr_tag P.
  Canonical Structure id_tag P := andl_tag P.

  Structure narrowedTo (P : Prop) : Type := NarrowTo { BigP :> tagged_prop;
                                                       _ : (puntag BigP) -> P}.

  Arguments BigP {P} _.

  Lemma id_proof : forall (P : Prop), id_tag P -> P.
  Proof.
    auto.
  Qed.

  Canonical Structure id_narrow (P : Prop) :=
    NarrowTo P (id_tag P) (id_proof P).

  Lemma left_proof : forall (P P1 : Prop) (narr : narrowedTo P),
                       andl_tag (puntag (BigP narr) /\ P1) -> P.
  Proof.
    dependent inversion narr.
    intros. simpl in *.
    inversion H; auto.
  Qed.

  Canonical Structure andl_narrow (P P1 : Prop) (narr : narrowedTo P)  :=
    NarrowTo P (andl_tag (puntag (BigP narr) /\ P1)) (left_proof P P1 narr).

  Lemma right_proof : forall (P P1 : Prop) (narr : narrowedTo P),
                        andr_tag (P1 /\ puntag (BigP narr)) -> P.
  Proof.
    dependent inversion narr.
    intros; simpl in *.
    inversion H; auto.
  Qed.

  Canonical Structure andr_narrow (P P1 : Prop) (narr : narrowedTo P)  :=
    NarrowTo P (andr_tag (P1 /\ puntag (BigP narr))) (right_proof P P1 narr).

  Lemma herpR : forall (P : Prop) (narr : narrowedTo P), 
                  puntag (BigP narr) -> P.
    dependent inversion narr.
    intros.
    simpl in H.
    auto.
  Qed.

  Arguments herpR P {narr} _.

  Lemma test1 : forall (A B : Prop), (A /\ B) -> A.
    intros A B.
    refine (herpR A).
  Qed.

  Lemma test2 : forall (A B C D : Prop), ((D /\ A) /\ (B /\ C)) -> A.
    intros A B C D.
    refine (herpR A).
  Qed.
End Narrow.

Module Addable.

  Record addable (T : Type) := Addable
    { plus : T -> T -> T}.

  Structure adbl_type := Pack {obj : Type; addable_of : addable obj}.

  Definition op (e : adbl_type) : obj e -> obj e -> obj e :=
    let 'Pack _ (Addable the_add) := e in the_add.

  Arguments op {e} _ _.

  Definition addable_nat : addable nat :=
    Addable nat Peano.plus.

  Canonical Structure addable_nat_ty : adbl_type := Pack nat addable_nat.

  Eval compute in (op 1 2).

(*
  Definition plus2 {adT : addable} (t1 t2 : (sort adT)) : (sort adT) :=
    plus adT t1 t2.

  Eval compute in plus2 2 3.
*)
End Addable.

(* another example - reifying types *)
Module Reify.
  Inductive ReiType :=
| RNat
| RBool
| RUnit
| RPair : ReiType -> ReiType -> ReiType.

  Fixpoint denote (R : ReiType) : Type :=
    match R with
      | RNat => nat
      | RBool => bool
      | RUnit => unit
      | RPair i1 i2 => prod (denote i1) (denote i2)
    end.

  (*Structure tagged_ReiType := RTag {runtag :> ReiType}.*)

  Structure reifiable :=
    Reifiable {sort : Type;
               rt_of :> ReiType;
               _ : sort = denote rt_of}.

  (*
Definition nat_tag R := RTag R.
Definition bool_tag R := nat_tag R.
Definition unit_tag R := bool_tag R.
Canonical Structure pair_tag R := unit_tag R.
   *)

  Canonical Structure rei_nat : reifiable :=
    Reifiable nat RNat (eq_refl).

  Canonical Structure rei_bool : reifiable :=
    Reifiable bool RBool (eq_refl).

  Canonical Structure rei_unit : reifiable :=
    Reifiable unit RUnit (eq_refl).

  Lemma rei_pair_proof : forall (r1 r2: reifiable),
                           prod (sort r1) (sort r2) = denote (RPair r1 r2).
    dependent inversion r1. subst. simpl.
    dependent inversion r2. subst. simpl.
    reflexivity.
  Qed.

  Canonical Structure rei_pair (r1 r2 : reifiable) : reifiable :=
    Reifiable (prod (sort r1) (sort r2))
              (RPair (rt_of r1) (rt_of r2))
              (rei_pair_proof r1 r2).

  Definition get_type {reT :reifiable} (t  : (sort reT)) :=
    rt_of reT.

  Eval compute in (get_type (false, (true, false))).
End Reify.


