Require Import String.
From Fairness Require Import MyLtac2.

Ltac2 Type flag := [ Break | Continue | Fail ].

Lemma eq_rw (X: Type) (P: X -> Type) (x: X) (y: X) (EQ: x = y): P y -> P x.
Proof. exact (fun H => @eq_rect_r _ _ P H _ EQ). Qed.

Ltac2 ctx_rw p :=
  let x := open_constr:(_) in
  let c := Std.eval_hnf open_constr:($p $x) in
  Std.unify c (Control.goal ());
  refine (open_constr:(@eq_rw _ $p $x _ _ _)) >
    [Control.shelve ()| |hnf].


Variant red_class: Type := | red_class_cons: string -> red_class.

Class red_db (c: red_class)
      (A: Type)
      (a: A) :=
  mk_red_db {
      red_lemma_type: Type;
      red_lemma: red_lemma_type;
      red_focused_type: Type;
      red_focused: red_focused_type;
      red_next: (unit + red_class)%type;
    }.
Arguments red_db _ [_] _.
Arguments mk_red_db _ [_] _ [_] _ [_] _ _.
Arguments red_lemma [_ _ _] _.
Arguments red_focused [_ _ _] _.
Arguments red_next [_ _ _] _.

Class red_db_incl (c0: red_class) :=
  mk_red_db_incl { red_db_incl_next: red_class; }.
Arguments red_db_incl_next [_] _.

Ltac2 rec _red_tac c term k :=
  match c with
  | Some c =>
      or (fun _ =>
            let tc := tcsearch constr:(@red_db $c _ $term) in
            let lem := (Std.eval_red (Std.eval_red constr:(red_lemma $tc))) in
            let focused := (Std.eval_red (Std.eval_red constr:(red_focused $tc))) in
            let next := (Std.eval_red (Std.eval_red constr:(red_next $tc))) in
            let next := match! next with
                        | inr ?next => Some constr:($next)
                        | inl _ => None
                        end in
            _red_tac next focused (fun _ => k; eapply $lem))
         (fun _ =>
            let tc := tcsearch constr:(@red_db_incl $c) in
            let next := (Std.eval_red (Std.eval_red constr:(red_db_incl_next $tc))) in
            _red_tac (Some next) term k)
  | None =>
      k ()
  end.

Ltac2 red_tac c :=
  match! goal with
  | [ |- ?term = _ ] =>
      (_red_tac (Some c) term (fun _ => ()))
  end
.

Module TUTORIAL.
  Section FOO.
    (* Variables *)
    Variable A B C: Type.
    Variable a b c d: A.
    Variable x y z: B.
    Variable p q: C.
    Variable f: B -> B.

    Variable cl_C: red_class.
    Variable cl_B: red_class.
    Variable cl_B_unfold: red_class.
    Variable cl_A: red_class.

    Variable sim: A -> (nat * B) * C -> nat -> Prop.

    (* First Step: Prove Reduction Lemmas *)
    Hypothesis foo_red0: a = b.
    Hypothesis foo_red1: b = c.
    Hypothesis foo_red2: c = d.
    Hypothesis foo_red3: x = y.
    Hypothesis foo_red4: y = z.
    Hypothesis foo_red5: p = q.


    Instance foo_red1_hint: red_db cl_A a :=
      mk_red_db _ _ foo_red0 b (inl tt).

    Instance foo_red2_hint: red_db cl_A b :=
      mk_red_db _ _ foo_red1 c (inl tt).

    Instance foo_red3_hint: red_db cl_B_unfold x :=
      mk_red_db _ _ foo_red3 y (inl tt).

    Instance foo_red4_hint: red_db cl_B_unfold y :=
      mk_red_db _ _ foo_red4 y (inl tt).

    Instance foo_red5_hint: red_db cl_C p :=
      mk_red_db _ _ foo_red5 q (inl tt).

    Instance cl_B_unfold_cl_B: red_db_incl cl_B := mk_red_db_incl _ cl_B_unfold.

    (* Instance cl_B_unfold_cl_B: red_db_incl cl_B_unfold cl_B := mk_red_db_incl. *)

    Instance foo_red_f_hint a: red_db cl_B (f a) :=
      mk_red_db _ _ (@f_equal _ _ f) a (inr cl_B).


    Class Foo (n: nat) := mk_Foo {}.
    Global Instance foo: Foo 3 := mk_Foo _.


    Ltac2 evar t n :=
      let u := open_constr:(_: ltac:(exact_no_check $t)) in
      match Constr.Unsafe.kind u with
      | Constr.Unsafe.Cast v0 _ v1 =>
          Message.print (Message.of_constr v0);
          Message.print (Message.of_constr v1);
          Std.pose n t;
          v0
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


    Goal True.
    Proof.

      let n := Fresh.in_goal ident:(_TC_) in
      unshelve_evar constr:(nat) n > [|exact 5].

      let e := constr:(red_db cl_A a) in
      Message.print (Message.of_constr e);
      Message.print (Message.of_constr constr:(22));
      let n := Fresh.in_goal ident:(_TC_) in
      Message.print (Message.of_constr constr:(33));
      let u := open_constr:(_) in
      unshelve_evar e n > [|typeclasses_eauto];
      let x := (TCSearchSuccess (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n))) in
      Message.print (Message.of_constr (Control.hyp n));
      Message.print (Message.of_constr (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)))
      .


      let n := Fresh.in_goal ident:(_TC_) in
      Std.pose (Some n) constr:(42);

      Message.print (Message.of_constr (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)));
      Message.print (Message.of_constr ((Control.hyp n)))
      .


      Std.pose None (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n))
      .

                       (Control.hyp n)).


      n.


      let a :=

      let e := constr:(red_db cl_A a) in
      Message.print (Message.of_constr constr:(11));
      Control.plus

        (fun _ =>

           Message.print (Message.of_constr e);
           Message.print (Message.of_constr constr:(22));

           let n := Fresh.in_goal ident:(_TC_) in
           Message.print (Message.of_constr constr:(33));
           let u := open_constr:(_) in
           unshelve_evar e n > [|typeclasses_eauto];
           let x := (TCSearchSuccess (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n))) in
           Message.print (Message.of_constr (Control.hyp n));
           Message.print (Message.of_constr (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)));

           Message.print (Message.of_constr u);
           Message.print (Message.of_constr constr:(55));
           Control.zero (TCSearchSuccess u)
        )

        (fun e =>
           Message.print (Message.of_constr constr:(66));
           Message.print (Message.of_exn e);
           match e with
           | TCSearchSuccess c =>
               Message.print (Message.of_constr constr:(c));
               c
           | _ =>
               constr:(3)
               (* Control.zero e *)
           end
        ).

      or
        (fun _ =>
           let e := constr:(red_db cl_A a) in
           Message.print (Message.of_constr constr:(11));


           Control.plus

             (fun _ =>

                Message.print (Message.of_constr constr:(22));


                let n := Fresh.in_goal ident:(_TC_) in
                unshelve_evar e n > [|typeclasses_eauto];
                Control.zero (TCSearchSuccess (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)))
             )

             (fun e =>
                match e with
                | TCSearchSuccess c =>
                    c
                | _ => Control.zero e
                end
        ))
        (fun _ => ()) ()
      .




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
       Control.zero (TCSearchSuccess (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)))
    )
    (fun e =>
       match e with
       | TCSearchSuccess c =>
           c
       | _ => Control.zero e
       end
    )
.



      time (do 100 (let _ := tcsearch constr:(red_db cl_A a) in ())).

        let x := tcsearch constr:(red_db cl_A a) in ().

      exact I.
    Qed.


    Goal forall (n: nat) (H: sim c ((n, f z), q) n),
        sim a ((n, f x), p) n.
    Proof.

      Set Ltac Profiling.
      intros n H.

      ctx_rw open_constr:(fun t => _ t _ _).
      {

        let c := constr:(cl_A) in
        match! Control.goal () with
        | ?term = _ =>
            Message.print (Message.of_constr constr:((@red_db $c _ $term)));
            let tc := tcsearch constr:(@red_db $c _ $term) in
            let lem := (Std.eval_red (Std.eval_red constr:(red_lemma $tc))) in
            let focused := (Std.eval_red (Std.eval_red constr:(red_focused $tc))) in
            let next := (Std.eval_red (Std.eval_red constr:(red_next $tc))) in
            let next := match! next with
                        | inr ?next => Some constr:($next)
                        | inl _ => None
                        end in
            _red_tac next focused (fun () => eapply $lem)
        | _ =>
            Message.print (Message.of_int 999)
        end.


        let x := tcsearch constr:(red_db cl_A a) in ().




  match c with
  | Some c =>
      or (fun _ =>
            let tc := tcsearch constr:(@red_db $c _ $term) in
            let lem := (Std.eval_red (Std.eval_red constr:(red_lemma $tc))) in
            let focused := (Std.eval_red (Std.eval_red constr:(red_focused $tc))) in
            let next := (Std.eval_red (Std.eval_red constr:(red_next $tc))) in
            let next := match! next with
                        | inr ?next => Some constr:($next)
                        | inl _ => None
                        end in
            _red_tac next focused (fun _ => k; eapply $lem))
         (fun _ =>
            let tc := tcsearch constr:(@red_db_incl $c) in
            let next := (Std.eval_red (Std.eval_red constr:(red_db_incl_next $tc))) in
            _red_tac (Some next) term k)
  | None =>
      k ()
  end.

        let c := constr:(cl_A) in
        match! Control.goal () with
        | ?term = _ =>
            (_red_tac (Some c) term (fun _ => ()))
        | _ =>
            Message.print (Message.of_int 999)
        end.


        red_tac constr:(cl_A).


        match! goal with
        | [ |- ?term = _ ] =>
            (_red_tac (Some c) term (fun _ => ()))
        end.


        red_tac constr:(cl_A).


      try (prw ltac:(red_tac cl_A) 3 0).
      Show Proof.

      ltac2:(open_constr:(_ : ltac:(exact_no_check $type))).

      (prw ltac:(red_tac cl_C) 2 1 0).
      (prw ltac:(red_tac cl_B) 2 2 1 0).
      exact H.
      Show Ltac Profile.
    Qed.

  End FOO.
End TUTORIAL.



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
      ((apply foo_red0; fail) ||
       (apply foo_red1; fail) ||
       (apply foo_red2; fail)).

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


(* Ltac2 ctx_rw p := *)
(*   let x := open_constr:(_) in *)
(*   let c := Std.eval_hnf open_constr:($p $x) in *)
(*   Std.unify c (Control.goal ()); *)
(*   refine (open_constr:(@eq_rect_r _ _ $p _ $x _)) > *)
(*     [Control.shelve ()|hnf|]. *)


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

Goal forall X Y (f: X -> Y) (x: X) (y: Y), f x = y.
Proof.
  intros.

  Show Proof.

  let p := open_constr:(fun t => _ t = _) in
  let x := open_constr:(_) in
  let c := Std.eval_hnf open_constr:($p $x) in
  Std.unify c (Control.goal ());
  refine (open_constr:(@eq_rw _ $p $x _ _ _)) >
    [Control.shelve ()| |hnf].


  ctx_rw open_constr:(fun t => _ t = _).
  Show Proof.

  let p := open_constr:(fun t => _ t = _) in
  let x := open_constr:(_) in
  let c := Std.eval_hnf open_constr:($p $x) in
  Std.unify c (Control.goal ());
  refine (open_constr:(@eq_rect_r _ _ $p _ $x _)) >
    [Control.shelve ()|hnf|].


  (let p := open_constr:(fun t => _ t = _) in
   let x := open_constr:(_) in
   let c := Std.eval_hnf open_constr:($p $x) in
   Std.unify c (Control.goal ());
   (Control.refine (fun _ => open_constr:(@eq_rect_r _ _ $p _ $c _)))).


  >
    [pose 0|pose 1|pose 2|pose 3|pose 4|pose 5|pose 6].

  Control.shelve().
  Control.shelve().
  hnf.


  > [Control.shelve()|..])).


  let p := open_constr:(fun t => _ t = _) in
  let x := open_constr:(_) in
  let c := Std.eval_hnf open_constr:($p $x) in
  Std.unify c (Control.goal ());
  refine (open_constr:(@eq_rect_r _ _ $p _ $x _)) >
    [Control.shelve ()|hnf|].



  (let p := open_constr:(fun t => _ t = _) in
   let x := open_constr:(_) in
   (Control.refine (fun _ => open_constr:(@eq_rect_r _ _ $p _ $x _)) > [Control.shelve()|..])).

  Control.shelve ().
                                                  hnf.

  >
    [Control.shelve ()|hnf|].


  time (let p := open_constr:(fun t => _ t = _) in
        let x := open_constr:(_) in
        let c := Std.eval_hnf open_constr:($p $x) in
        Std.unify c (Control.goal ());
        refine (open_constr:(@eq_rect_r _ _ $p _ $x _)) >
          [Control.shelve ()|hnf|]).

Show Proof.

  let c := open_constr:(@eq_rect_r _ _ $x _ _ _) in
  eapply $c.

  Show Proof.


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
