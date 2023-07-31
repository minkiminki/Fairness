From Ltac2 Require Export Ltac2.
From Ltac2 Require Option Array Ident Control Std Fresh Message Constr.
Import Constr.Unsafe.

Ltac2 or t0 t1 :=
  match! 'True with
  | True => t0 ()
  | _ => t1 ()
  end.

Ltac2 fail () := Control.zero Match_failure.

Ltac2 Type exn ::= [ TCSearchSuccess (constr) | TCSearchFail ].

Ltac2 evar t n :=
  let u := open_constr:(_: ltac:(exact_no_check $t)) in
  match Constr.Unsafe.kind u with
  | Constr.Unsafe.Cast v _ _ =>
      Std.pose n t;
      v
  | _ => Control.throw Init.Assertion_failure
  end
.

Ltac2 unshelve_evar e n :=
  let v := evar e (Some n) in
  match Constr.Unsafe.kind v with
  | Constr.Unsafe.Evar e _ =>
      Control.new_goal e
  | _ => Control.throw Init.Assertion_failure
  end
.

Ltac2 unshelve_evar1 e n :=
  (ltac1:(e n|- unshelve evar (n: e))) (Ltac1.of_constr e) (Ltac1.of_ident n)
.

Ltac2 tcsearch e :=
  Control.plus
    (fun _ =>
       let n := Fresh.in_goal ident:(_TC_) in
       unshelve_evar e n > [|typeclasses_eauto];
       Message.print (Message.of_string "xxx");
       Message.print (Message.of_constr (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)));
       Message.print (Message.of_string "yyy");
       Control.zero (TCSearchSuccess (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)))
    )
    (fun e =>
       Message.print (Message.of_string "dddd");
       Message.print (Message.of_exn e);
       Message.print (Message.of_string "nmnn");
       match e with
       | TCSearchSuccess c =>
           Message.print (Message.of_string "aaaa");
           Message.print (Message.of_constr c);
           c
       | _ => Control.zero e
       end
    )
.

Module _TEST.
  Class Foo (n: nat) := mk_Foo {}.
  Global Instance foo: Foo 3 := mk_Foo _.

  Goal True.
    time (do 100 (let _ := tcsearch constr:(Foo 3) in ())).
    exact I.
  Qed.
End _TEST.


Ltac message :=
  ltac2:(e |-
           let e := Option.get (Ltac1.to_constr e) in
           Message.print (Message.of_constr e))
.

Ltac tcsearch :=
  ltac2:(e k |-
           let e := Option.get (Ltac1.to_constr e) in
           let v := tcsearch e in
           Ltac1.apply k [Ltac1.of_constr v] Ltac1.run)
.
