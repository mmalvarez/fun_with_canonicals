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
