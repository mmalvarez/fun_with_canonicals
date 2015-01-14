(* another example - reifying types *)
Module Reify.
Require Import Infrastructure.
Import Infrastructure.

(* Constructs stolen from Infrastructure.v *)
Inductive phantom {T : Type} (t : T) : Type := Phantom.
Definition unify {T1 T2} (t1 : T1) (t2 : T2) :=
  phantom t1 -> phantom t2.

Structure unify2 {T1 T2} (t1 : T1) (t2 : T2) :=
  Unify2 {f : phantom t1 -> phantom t2}.

Definition id {T : Type} {t : T} (x : phantom t) := x.    

Canonical Structure unify2_id {T1 : Type} (t1 : T1) :=
  @Unify2 T1 T1 t1 t1 id.      

(*Canonical Structure unif_id_nat (T : Type) : @unify T T  :=
    @Unify T T (@id T).*)


Inductive ReiType :=
(* primitive set *)
| RNat
| RBool
| RUnit
(* primitive type *)
| RType
| RSet
| RProp
(* combinators *)
| RPair : ReiType -> ReiType -> ReiType
| RFunc : ReiType -> ReiType -> ReiType.

Fixpoint denote (R : ReiType) : Type :=
    match R with
      | RNat => nat
      | RBool => bool
      | RUnit => unit
      | RType => Type
      | RSet => Set
      | RProp => Prop
      | RPair i1 i2 => prod (denote i1) (denote i2)
      | RFunc i1 i2 => ((denote i1) -> (denote i2))
    end.

  (*Structure tagged_ReiType := RTag {runtag :> ReiType}.
*)
(*
  Structure reifiable :=
    Reifiable {sort : Type;
               rt_of :> tagged_ReiType;
               _ : sort = denote rt_of}.
*)

  Structure reifiable :=
    Reifiable {sort : Type;
               rt_of :> ReiType;
               _ : sort = denote rt_of}.

  Structure reified :=
    Reified { T : Type;
              t : T;
              rbl_of :> reifiable;
              _ : T = sort rbl_of}.

  (* no args implicit, will mostly be called from
     notations in any case *)

  

  (*
  Definition reify_term {T : Type} {rei : reifiable} (t : T)
             (uni : unify t ()) : .
   *)

  (*
  Definition Type_tag R := RTag R.
  Definition Set_tag R := Type_tag R.
  Definition Prop_tag R := Set_tag R.
  Definition nat_tag R := Prop_tag R.
  Definition bool_tag R := nat_tag R.
  Definition unit_tag R := bool_tag R.
  Canonical Structure pair_tag R := unit_tag R.
   *)

  Canonical Structure rbl_nat : reifiable :=
    Reifiable nat RNat eq_refl.

  (* bool and instances *)
  Canonical Structure rbl_bool : reifiable :=
    Reifiable bool RBool eq_refl.

  Canonical Structure rbl_type : reifiable :=
    Reifiable Type RType eq_refl.

  Canonical Structure rbl_set : reifiable :=
    Reifiable Set RSet eq_refl.

  Canonical Structure rprop_set : reifiable :=
    Reifiable Prop RProp eq_refl.
  
(*
  Canonical Structure rfd_true : reified :=
    @Reified _ _ true eq_refl.

  Canonical Structure rfd_false : reified :=
    @Reified _ _ false eq_refl.
*)

  (* should this be rbl or _ ?*)
  Definition reify_term {T : Type} (t : T) {rbl : reifiable}
             (eq : T = (sort rbl)) : reified :=
    Reified T t rbl eq.

  
  Eval compute in (reify_term True eq_refl).

  Eval compute in (reify_term Type eq_refl).

  (* do we need one or both levels of search *)
  (* outer eq_refl triggers unification between term at T.
     we want that to be guaranteed immediately, so we fill it in now
     inner eq_refl is the one we care about, it is a commitment
     to a particular reified representation *)

  (* Reify a term, forcing its type *)
  Notation "{| term :~ T |}" :=
    (Reified T term _ eq_refl) (at level 60).

  (* Reify a term, a force its type to whatever
     Coq currently thinks the type is *)
  Notation "{{| term |}}" :=
    (Reified _ term _ eq_refl).

  (*  Reify a term, but do not force its type *)
  Notation "{{ term }}" :=
    (fun equ =>
       (Reified _ term _ equ)) (at level 59).

  (* I need to think about this more
     What I'd really like to have is a more uniform way of
     talking about unification goals - maybe have a monad of
     unification contexts? *)

  (* Notations for displaying ReiTypes *)  

  Canonical Structure rbl_unit : reifiable  :=
    Reifiable unit RUnit eq_refl.

  Lemma rbl_func_proof : forall (dom cod : reifiable),
                           (sort dom -> sort cod) = denote (RFunc dom cod).
    Proof.
      intros.
      dependent inversion dom. subst. simpl.
      dependent inversion cod. subst. simpl.
      reflexivity.
    Qed.

  Canonical Structure rbl_func (dom cod : reifiable) : reifiable :=
    Reifiable (sort dom -> sort cod) (RFunc dom cod) (rbl_func_proof dom cod).    

  Lemma rbl_pair_proof : forall (r1 r2: reifiable),
                           prod (sort r1) (sort r2) = denote (RPair r1 r2).
    dependent inversion r1. subst. simpl.
    dependent inversion r2. subst. simpl.
    reflexivity.
  Qed.

  Canonical Structure rbl_pair (r1 r2 : reifiable) : reifiable :=
    Reifiable (prod (sort r1) (sort r2))
              (RPair (rt_of r1) (rt_of r2))
              (rbl_pair_proof r1 r2).


  Eval compute in (rt_of {{| fun (n : nat) m => m n + 1 |}}).

  (* show RFunc RNat (RFunc (RFunc RNat RNat) RNat
     as <<nat -> nat -> nat>>
     *)

(*
  type is a Type (that we want to display)
  RT is a reified type
*)

  (* concept of "matching" *)
  (* don't think we need this *)
  Definition check_type
             {reT : reifiable} (t : sort reT):=
    rt_of reT.

  Eval compute in (check_type (true, (1, tt))).

  Eval simpl in (rt_of {{| (fun q : nat => q)  |}}).

  Eval compute in (T {{|3|}}).

  Definition get_type {reT : reifiable} (T : Type) (uni : unify T (sort reT)) :=
    reT.

  Check @get_type.

  Print reifiable.

  Definition tylift' (T : Type) {rbl : reifiable}
             (uni : denote (rt_of rbl) = T):= 
    rt_of rbl.


  Check rt_of.

  Eval simpl in (rt_of {{| fun (n : nat) m => m n + 1 |}}).


  Notation "f ! x" := (f x id) (at level 99).

  Eval compute in (get_type! (nat * (bool * unit)%type)%type).

  Canonical Structure rei_Type :

  Canonical Structure rei_Type {T : Type} {reT : reifiable} (uni : unify T (sort re


  Definition get_type {reT : reifiable} (T : Type) : ReiType :=
    get_type' T id.

  Eval compute in (get_type nat id).

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

  Definition get_type
             {reT :reifiable}
             (t  : (sort reT))
     {mat : matching } :=
    rt_of reT.

  (* something whose type has a *)

  Eval compute in (get_type (false, (true, false))).

End Reify.

