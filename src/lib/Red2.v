From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Array Ident Control Std Fresh Message.

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

Set Default Proof Mode "Classic".

Ltac2 Type flag := [ Break | Continue | Fail ].

(* Internals *)
Lemma _equal_f (A B : Type) (f g : A -> B)
      x
      (EQ: f = g)
  :
    f x = g x.
Proof.
  subst. apply eq_refl.
Qed.

Lemma _einit (P Q: Prop)
      (EQ: P = Q)
  :
    Q -> P.
Proof.
  subst. apply id.
Qed.

Ltac2 rec _ctx n :=
  match! n with
  | O => apply f_equal
  | S ?m => apply _equal_f; _ctx m
  end.

Ltac2 __prw red_tac success :=
  cbn;
  tryif (let f := fresh "f" in
         evar (f:_flag);
         etransitivity;
         [red_tac|
           match goal with
           | [f0:= ?f1: _flag|- _] =>
               match f1 with
               | _continue => subst f; __prw red_tac true
               | _break => subst f; reflexivity
               | _fail => fail 2
               end
           end])
  then
    idtac
  else
    match success with
    | true => reflexivity
    | false => fail
    end.

Ltac _prw k0 k1 X :=
  match X with
  | O => eapply _einit; [(k0; k1)|]
  | S ?n => _prw ltac:(k0; _ctx n) k1
  end.

Ltac _rwb k X :=
  match X with
  | O => k
  | _ => _rwb ltac:(fun f => ltac:(k f || (instantiate (f:=_break); eapply X; fail)))
  end.

Ltac _rwc k X :=
  match X with
  | O => k
  | _ => _rwc ltac:(fun f => ltac:(k f || (instantiate (f:=_continue); eapply X; fail)))
  end.

Ltac _rwa k X :=
  match X with
  | O => k
  | (?H, ?_f) => _rwa ltac:(fun f => ltac:(k f || (instantiate (f:=_f); eapply H; fail)))
  end.

(* Main Tactic *)
Ltac prw red_tac X := _prw ltac:(idtac) ltac:(__prw red_tac false) X.

Ltac rwbl X := _rwb ltac:(fun f => fail) X.
Ltac rwcl X := _rwc ltac:(fun f => fail) X.
Ltac rwal X := _rwa ltac:(fun f => fail) X.
Ltac rrw X _f := ltac:(fun f => instantiate (f:=_f); eapply X; fail).

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
