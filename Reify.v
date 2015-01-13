(* another example - reifying types *)
Module Reify.
Require Import Infrastructure.
Import Infrastructure.
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

  Structure tagged_ReiType := RTag {runtag :> ReiType}.
  Structure reifiable :=
    Reifiable {sort : Type;
               rt_of :> ReiType;
               _ : sort = denote rt_of}.
  
  Definition nat_tag R := RTag R.
  Definition bool_tag R := nat_tag R.
  Definition unit_tag R := bool_tag R.
  Canonical Structure pair_tag R := unit_tag R.

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

  (* concept of "matching" *)

Require Import String.
  Inductive phantom {T : Type} (t : T) : Type := Phantom.
  
  (*Structure phantom {T : Type} :=
    Phantom {item : T}.*)

  Check (Phantom 3).

 Structure unify {T1 T2 : Type} (t1 : T1) (t2 : T2) :=
    Unify {unif : phantom t1 -> phantom t2; err : option string}.

  Arguments Unify {_ _} _ _ _ _.
  Check unif.
  Arguments unif {_ _ _ _} _ _.
  Arguments err {_ _} _ _ _.

  Canonical Structure unif_id {T : Type} (t : T) :=
    Unify t t id (Some "hello, world"%string).

  Check unif.

  Definition muney {T : Type} (t : T) {uni : unify t t} :=
    unif uni.
    

  Eval compute in (muney 3).


Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string) :=
  phantom t1 -> phantom t2.

Definition id {T} {t : T} (x : phantom t) := x.



  Definition monay {T : Type} (t : T) {uni : unify t 3} :=
    err _ _ uni.
  
  herp : forall {T : Type} (t : T) {uni : unify t 3},
                      t.
    

  Check Phantom.*)

  (* have some notion of "lifting" a term to a Type
     such that the only thing that typechecks to that type
     is one of it *)

  (* make it store 2 levels of sort? *)

  

  Check (LiftT 3).

  Structure matching {T1 T2} (t1 : T1) :=
    Matching.

  Arguments Matching {T1 T2} _ _.

  Canonical Structure match_id {T : Type} (t : T) : Matching :=
    Matching t t.

  (*Definition matching_of {T : Type} (t : T) {mat : matching t t} :=
    t2 mat.*)

  Definition proof_of {T : Type} (t1 t2 : T) {mat : matching t1 t2} :=
    pf mat.

  (*
  Canonical Structure match_id_3 :=
    Matching 3 3 eq_refl.
   *)

  Lemma ohai : forall {T : Type} (t : T), (t = t).
    Proof.
      intros T t.
      refine (proof_of t t _ _).
      intros.
    apply match_id.*)
Require Import Infrastructure.

  Definition reify_type
             (T : Type)
             {reT : reifiable}
             {mat : matching T (sort reT)} :=
    rt_of reT.

  Eval hnf in (reify_type bool).

(*
  Definition get_type
             {reT :reifiable}
             (t  : (sort reT))
     {mat : matching } :=
    rt_of reT.
*)

  (* something whose type has a *)

  Eval compute in (get_type (false, (true, false))).

End Reify.
n
