From Fairness Require Import MyLtac2.

Ltac2 Type flag := [ Break | Continue | Fail ].

(* Internals *)
Lemma _equal_f (A B : Type) (f g : A -> B)
      x
      (EQ: f = g)
  :
    f x = g x.
Proof.
  subst. apply (@eq_refl).
Qed.

Lemma _einit (P Q: Prop)
      (EQ: P = Q)
  :
    Q -> P.
Proof.
  subst. apply id.
Qed.

Ltac2 rec _ctx n :=
  if (Int.le n 0)
  then
    (apply f_equal)
  else
    (apply _equal_f; _ctx (Int.sub n 1))
.

(* Ltac2 __prw red_tac success := *)
(*   cbn; *)
(*   tryif (let f := fresh "f" in *)
(*          evar (f:_flag); *)
(*          etransitivity; *)
(*          [red_tac| *)
(*            match goal with *)
(*            | [f0:= ?f1: _flag|- _] => *)
(*                match f1 with *)
(*                | _continue => subst f; __prw red_tac true *)
(*                | _break => subst f; reflexivity *)
(*                | _fail => fail 2 *)
(*                end *)
(*            end]) *)
(*   then *)
(*     idtac *)
(*   else *)
(*     match success with *)
(*     | true => reflexivity *)
(*     | false => fail *)
(*     end. *)

Class Foo (n: nat) := mk_Foo {}.
Instance foo: Foo 3 := mk_Foo _.

Import Constr.Binder Constr.Unsafe.



From Ltac2 Require Export Ltac2.

Goal forall X Y (f: X -> Y) (x: X) (y: Y), f x = y.
Proof.
  intros.
  let d := open_constr:(fun _t => _ _t = _) in
  let c := Std.eval_hnf open_constr:($d _) in
  Std.unify c (Control.goal ());
  Std.pose None d;
  let c := open_constr:(@eq_rect_r X _ $d) in
  eapply $c.


 _ _ _)
  .


  let u := open_constr:(_: ltac:(exact_no_check $t)) in
  match Constr.Unsafe.kind u with
  | Constr.Unsafe.Cast v _ _ =>
      let f := open_constr:(fun _t => _ _t = _) in
      Std.unify open_constr:($f _) (Control.goal ());
      Std.pose None f
      v
  | _ => Control.throw Init.Assertion_failure
  end
  .


  .


  let n := Fresh.in_goal ident:(x) in
  let b := Constr.Binder.make (Some n) open_constr:(X) in
  let x := Constr.Unsafe.make (Constr.Unsafe.Rel 1) in
  let a := Constr.Unsafe.make (Constr.Unsafe.Lambda b open_constr:(_ $x = _)) in
  Std.unify constr:($a x) (Control.goal ());
  Std.pose None a
  .

  end.

 =>
                                 match (Constr.Unsafe.kind c) with
                                 | Rel n
                                   => Message.print (Message.of_int n)


open_constr:(fun _t => _ _t = _) in
  Std.unify constr:($a x) (Control.goal ());
  Std.pose None a
  .


  match (Constr.Unsafe.kind constr:(fun x: nat => x)) with
  | Constr.Unsafe.Lambda b c =>
      match (Constr.Unsafe.kind c) with
      | Rel n
        => Message.print (Message.of_int n)




    (* | Var _ *)
      (*   => Message.print (Message.of_string "1") *)
      (* | Meta _ *)
      (*   => Message.print (Message.of_string "2") *)
      (* | Evar _ _ *)
      (*   => Message.print (Message.of_string "3") *)
      (* | Sort _ *)
      (*   => Message.print (Message.of_string "4") *)
      (* | Cast _ _ _ *)
      (*   => Message.print (Message.of_string "5") *)
      (* | Prod _ _ *)
      (*   => Message.print (Message.of_string "6") *)
      (* | Lambda _ _ *)
      (*   => Message.print (Message.of_string "7") *)
      (* | LetIn _ _ _ *)
      (*   => Message.print (Message.of_string "8") *)
      (* | App _ _ *)
      (*   => Message.print (Message.of_string "9") *)
      (* | Constant _ _ *)
      (*   => Message.print (Message.of_string "10") *)
      (* | Ind _ _ *)
      (*   => Message.print (Message.of_string "11") *)
      (* | Constructor _ _ *)
      (*   => Message.print (Message.of_string "12") *)
      (* | Case _ _ _ _ _ *)
      (*   => Message.print (Message.of_string "13") *)
      (* | Fix _ _ _ _ *)
      (*   => Message.print (Message.of_string "14") *)
      (* | CoFix _ _ _ *)
      (*   => Message.print (Message.of_string "15") *)
      (* | Proj _ _ *)
      (*   => Message.print (Message.of_string "16") *)
      (* | Uint63 _ *)
      (*   => Message.print (Message.of_string "17") *)
      (* | Float _ *)
      (*   => Message.print (Message.of_string "18") *)
      (* | Array _ _ _ _ *)
      (*   => Message.print (Message.of_string "19") *)
      | _ => Control.throw Init.Assertion_failure
      end
  | _ => Control.throw Init.Assertion_failure
  end
  .


Some c =>
      let c := Constr.Unsafe.make (Constr.Unsafe.Var c) in
      let a := Constr.Unsafe.make (Constr.Unsafe.Lambda b open_constr:(_ $c = _)) in
      Std.unify constr:($a x) (Control.goal ());
      Std.pose None a
  | _ => Control.throw Init.Assertion_failure
  end
  .




  let n := Fresh.in_goal ident:(_TC_) in
  let b := Constr.Binder.make (Some n) constr:(X) in
  match (Constr.Binder.name b) with
  | Some c =>
      let c := Constr.Unsafe.make (Constr.Unsafe.Var c) in
      let a := Constr.Unsafe.make (Constr.Unsafe.Lambda b open_constr:(_ $c = _)) in
      Std.unify constr:($a x) (Control.goal ());
      Std.pose None a
  | _ => Control.throw Init.Assertion_failure
  end
  .

  let a := open_constr:(fun _t => _ _t = _) in
  Std.unify constr:($a x) (Control.goal ());
  Std.pose None a
  .


  let n := Fresh.in_goal ident:(_TC_) in
  let b := Constr.Binder.make (Some n) constr:(X) in
  match (Constr.Binder.name b) with
  | Some c =>
      let c := Constr.Unsafe.make (Constr.Unsafe.Var c) in
      let a := Constr.Unsafe.make (Constr.Unsafe.Lambda b open_constr:(_ $b = _)) in
      Std.unify constr:($a x) (Control.goal ());
      Std.pose None a
  | _ => Control.throw Init.Assertion_failure
  end
  .


 ().


  let n := Fresh.in_goal ident:(_TC_) in
  let a := open_constr:(fun $n => _ $n = _) in
  Std.unify constr:($a x) (Control.goal ());
  Std.pose None a
  .
  Show Proof.

  let n := Fresh.in_goal ident:(_TC_) in
  Std.in_context



Goal False.
Proof.
  assert (Foo 3).
  { pose foo.

let n := Fresh.in_goal ident:(_TC_) in
    let m := (Constr.in_context n constr:(unit) (fun _ => typeclasses_eauto)) in
    Message.print (Message.of_constr m).


Message.print (mes.




Ltac2 @ external in_context : ident -> constr -> (unit -> unit) -> constr := "coq-core.plugins.ltac2" "constr_in_context".
(** On a focused goal [Γ ⊢ A], [in_context id c tac] evaluates [tac] in a
    focused goal [Γ, id : c ⊢ ?X] and returns [fun (id : c) => t] where [t] is
    the proof built by the tactic. *)

  intros.
  Std.unify


Ltac2 rec holes pos :=
  match pos with
  | hd::tl =>
      if (Int.le hd 0)
      then
        let k := holes tl in
        open_constr:($k _)
      else
        holes tl
  | [] =>
      open_constr:(4)
  end.




open_constr:(_: ltac:(exact_no_check $t))

                       |


  if (Int.le n 0)
  then
    (apply f_equal)
  else
    (apply _equal_f; _ctx (Int.sub n 1))


  match n with
  |

  match holes with
  | hd::tl =>

Ltac2 rec holes pos :=
  match holes with
  | hd::tl =>


Ltac2 evar t n :=
  let u := open_constr:(_: ltac:(exact_no_check $t)) in
  match Constr.Unsafe.kind u with
  | Constr.Unsafe.Cast v _ _ =>
      Std.pose n t;
      v
  | _ => Control.throw Init.Assertion_failure
  end
.

Ltac2 _prw k0 k1 X :=
  match X with
  | O => eapply _einit > [(k0; k1)|]
  | S ?n => _prw ltac:(k0; _ctx n) k1
  end.

(* Main Tactic *)
Ltac prw red_tac X := _prw ltac:(idtac) ltac:(__prw red_tac false) X.

Module TUTORIAL.
  Section FOO.
    (* Variables *)
    Variable A B C: Type.
    Variable a b c d: A.
    Variable x y z: B.
    Variable p q: C.

    Variable sim: A -> (nat * B) * C -> nat -> Prop.

    (* First Step: Prove Reduction Lemmas *)
    Hypothesis foo_red0: a = b.
    Hypothesis foo_red1: b = c.
    Hypothesis foo_red2: c = d.
    Hypothesis foo_red3: x = y.
    Hypothesis foo_red4: y = z.
    Hypothesis foo_red5: p = q.

    (* Second Step: Define Reduction Strategy (= red_tac) *)
    Ltac red_A f := (* f is a flag indicating continue/break/fail. Must set f before return *)
      ((instantiate (f:=_continue); apply foo_red0; fail) ||
       (instantiate (f:=_break); apply foo_red1; fail) ||
       (instantiate (f:=_fail); apply foo_red2; fail)).

    (* We also give more conenient syntax *)
    Ltac red_A' := (* = red_A *)
      rwal (foo_red0, _continue)
           (foo_red1, _break)
           (foo_red2, _break)
           0.

    Ltac red_B :=
      rwcl foo_red3
           foo_red4
           0.

    Ltac red_B' f := (* = red_B *)
      ((instantiate (f:=_continue); apply foo_red3; fail) ||
       (instantiate (f:=_continue); apply foo_red4; fail)).

    Ltac red_C :=
      rrw foo_red5 _break.

    Ltac red_C' := (* = red_C *)
      rwbl
        foo_red5
        0.

    Ltac red_C'' f := (* = red_C *)
      (instantiate (f:=_break); apply foo_red5; fail).

    (* Done. Let's use it! *)
    Lemma foo: forall (n: nat) (H: sim c ((n, z), q) n),
        sim a ((n, x), p) n.
    Proof.
      intros n H.
      (* goal = sim a (n, x, p) n *)
      prw red_B 2 2 1 0.
      (* prw [red_tac (= red_r)] [l_0 (= 2)] [l_1 (= 2)] [l_2 (= 1)] ... 0 =>
         - find the right l_0th term x0 (= ((n, x), p)) in the goal
         - find the right l_1th term x1 (=  (n, x)    ) in the   x0
         - find the right l_2th term x2 (=      x     ) in the   x1
         ...
         - the last argument must be 0. reduce the x2 following _red_r *)
      (* goal = sim a (n, z, p) n *)
      prw red_A 3 0.
      (* goal = sim c (n, z, p) n *)
      prw red_C 2 1 0.
      (* goal = sim c (n, z, q) n *)
      exact H.
    Qed.
  End FOO.
End TUTORIAL.

? _
