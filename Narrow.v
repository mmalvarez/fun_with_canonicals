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
