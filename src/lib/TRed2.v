From Fairness Require Export Red.
Require Import String.

Variant red_class: Type := | red_class_cons: string -> red_class.

Class red_db (c: red_class)
      (A: Type)
      (a: A) :=
  mk_red_db {
      red_lemma_type: Type;
      red_lemma: red_lemma_type;
      red_focused_type: Type;
      red_focused: red_focused_type;
      red_next: (_flag + red_class)%type;
    }.
Arguments red_db _ [_] _.
Arguments mk_red_db _ [_] _ [_] _ [_] _ _.
Arguments red_lemma [_ _ _] _.
Arguments red_focused [_ _ _] _.
Arguments red_next [_ _ _] _.

Class red_db_incl (c0: red_class) :=
  mk_red_db_incl { red_db_incl_next: red_class; }.
Arguments red_db_incl_next [_] _.

(* Class red_db_incl (c0 c1: red_class) := *)
(*   mk_red_db_incl { }. *)
(* Arguments mk_red_db_incl {_ _}. *)

(* #[export] Instance red_db_incl_focus c0 c1 `{red_db_incl c0 c1} *)
(*  A (a: A) *)
(*   : red_db c1 a := *)
(*   mk_red_db _ _ (@id) a (inr c0). *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Array Ident Control Std Fresh Message Constr.

Ltac2 or t0 t1 :=
  match! 'True with
  | True => t0 ()
  | _ => t1 ()
  end.

Ltac2 fail () := Control.zero Match_failure.

Ltac message :=
  ltac2:(e |-
           let e := Option.get (Ltac1.to_constr e) in
           Message.print (Message.of_constr e))
.

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

Class Foo (n: nat) := mk_Foo {}.
Global Instance foo: Foo 3 := mk_Foo _.

From Ltac2 Require Option Array Ident Control Std Fresh Message Constr.

From Ltac2 Require Import Ltac2 Constr.
Import Constr.Unsafe.

Ltac tcsearch :=
  ltac2:(e k |-
           let e := Option.get (Ltac1.to_constr e) in
           let v := tcsearch e in
           Ltac1.apply k [Ltac1.of_constr v] Ltac1.run)
.


Set Default Proof Mode "Classic".

Ltac _red_tac c f term k :=
try(
  match c with
  | inr ?c =>
      first[
          tcsearch
            (@red_db c _ term)
            ltac:(fun tc =>
                    let lem := (eval red in (red_lemma tc)) in
                    let lem := (eval red in lem) in
                    let focused := (eval red in (red_focused tc)) in
                    let focused := (eval red in focused) in
                    let next := (eval red in (red_next tc)) in
                    let next := (eval red in next) in
                    _red_tac next f focused ltac:(k; eapply lem))
        |
          tcsearch
            (@red_db_incl c)
            ltac:(fun tc =>
                    let next := (eval red in (@red_db_incl_next _ tc)) in
                    let next := (eval red in next) in
                    _red_tac (inr next: (_flag + red_class)%type) f term k)
        ]
  | inl ?fl =>
      instantiate (f:=fl);
      k
  end).

Ltac red_tac c f :=
  try(
  match goal with
  | [ |- ?term = _ ] =>
      (_red_tac constr:(inr c: (_flag + red_class)%type) f term ltac:(idtac))
  end)
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
      mk_red_db _ _ foo_red0 b (inl _continue).

    Instance foo_red2_hint: red_db cl_A b :=
      mk_red_db _ _ foo_red1 c (inl _continue).

    Instance foo_red3_hint: red_db cl_B_unfold x :=
      mk_red_db _ _ foo_red3 y (inl _continue).

    Instance foo_red4_hint: red_db cl_B_unfold y :=
      mk_red_db _ _ foo_red4 y (inl _continue).

    Instance foo_red5_hint: red_db cl_C p :=
      mk_red_db _ _ foo_red5 q (inl _break).

    Instance cl_B_unfold_cl_B: red_db_incl cl_B := mk_red_db_incl _ cl_B_unfold.

    (* Instance cl_B_unfold_cl_B: red_db_incl cl_B_unfold cl_B := mk_red_db_incl. *)

    Instance foo_red_f_hint a: red_db cl_B (f a) :=
      mk_red_db _ _ (@f_equal _ _ f) a (inr cl_B).

    Goal forall (n: nat) (H: sim c ((n, f z), q) n),
        sim a ((n, f x), p) n.
    Proof.



      Set Ltac Profiling.
      intros n H.
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
