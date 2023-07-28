From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Array Ident Control Std Fresh.

Ltac2 or t0 t1 :=
  match! 'True with
  | True => t0 ()
  | _ => t1 ()
  end.

Ltac2 fail () := Control.zero Match_failure.

Ltac2 tcsearch e :=
  let x := Array.make 1 constr:(tt: unit) in
  or (fun _ =>
        let n := Fresh.in_goal ident:(_TC_) in
        ltac1:(e n|- unshelve evar (n: e);
               [typeclasses eauto|]) (Ltac1.of_constr e) (Ltac1.of_ident n);
        Array.set x 0 (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n));
        fail ())
     (fun _ => Array.get x 0)
.

Ltac tcsearch :=
  ltac2:(e k |-
           let e := Option.get (Ltac1.to_constr e) in
           let v := tcsearch e in
           Ltac1.apply k [Ltac1.of_constr v] Ltac1.run)
.

Set Default Proof Mode "Classic".
