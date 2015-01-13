(* Defines "phantom" type for forcing typesystem
   to do unifications on terms *)

Module Infrastructure.
Require Import String.
Inductive phantom {T : Type } (t : T) : Type := Phantom.

Definition unify {T1 T2} (t1 : T1) (t2 : T2) (s : option string) :=
phantom t1 -> phantom t2.

Definition id {T} {t : T} (x : phantom t) := x.

Notation "[find v | t1 ~ t2 ] rest" :=
  (fun v (_ : unify t1 t2 None) => rest) (at level 50).

Notation
"[find v | t1 ~ t2 | msg ] rest" :=
  (fun v (_ : unify t1 t2 (Some msg)) => rest) (at level 49).

Notation "’Error : t msg" := (unify _ t (Some msg)) (at level 48).  
End Infrastructure.
