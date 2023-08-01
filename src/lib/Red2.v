Require Import String.
From Fairness Require Import MyLtac2.

Ltac2 Type flag := [ Break | Continue | Fail ].

Lemma eq_rw (X: Type) (P: X -> Type) (x: X) (y: X) (EQ: x = y): P y -> P x.
Proof. exact (fun H => @eq_rect_r _ _ P H _ EQ). Qed.

Ltac2 ctx_rw p :=
  let x := open_constr:(_) in
  let c := Std.eval_hnf open_constr:($p $x) in
  Std.unify c (Control.goal ());
  Control.refine (fun _ => open_constr:(@eq_rw _ $p $x _ _ _)) >
    [Control.shelve ()| |hnf].

(* Internals *)
Lemma _equal_f (A B : Type) (f g : A -> B)
      x
      (EQ: f = g)
  :
    f x = g x.
Proof.
  subst. apply @eq_refl.
Qed.

Lemma _einit (P Q: Prop)
      (EQ: P = Q)
  :
    Q -> P.
Proof.
  subst. eapply @id.
Qed.

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
      first[let tc := tcsearch constr:(@red_db $c _ $term) in
            let lem := (Std.eval_red (Std.eval_red constr:(red_lemma $tc))) in
            let focused := (Std.eval_red (Std.eval_red constr:(red_focused $tc))) in
            let next := (Std.eval_red (Std.eval_red constr:(red_next $tc))) in
            let next := match! next with
                        | inr ?next => Some constr:($next)
                        | inl _ => None
                        end in
            _red_tac next focused (fun _ => k (); (eapply $lem))
           |let tc := tcsearch constr:(@red_db_incl $c) in
            let next := (Std.eval_red (Std.eval_red constr:(red_db_incl_next $tc))) in
            _red_tac (Some next) term k
        ]
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

    Instance foo_red_f_hint a: red_db cl_B (f a) :=
      mk_red_db _ _ (@f_equal _ _ f) a (inr cl_B_unfold).

    Ltac2 rec __ctx n :=
      if (Int.le n 0)
      then (eapply f_equal)
      else (eapply _equal_f; __ctx (Int.sub n 1)).

    Ltac2 rec _ctx l :=
      match l with
      | hd::tl => __ctx hd; _ctx tl
      | [] => ()
      end.

    Ltac2 ctx l :=
      eapply _einit > [_ctx l|].

    (* much fast *)
    Goal forall (n: nat) (H: sim c ((n, f z), q) n),
        sim a ((n, f x), p) n.
    Proof.
      intros n H.
      do 2 (ctx [2] > [red_tac constr:(cl_A)|]);
      do 1 (ctx [1; 0] > [red_tac constr:(cl_C)|]);
      do 2 (ctx [1; 1; 0] > [red_tac constr:(cl_B)|]);
      exact H.
    Qed.

    (* more flexible and easy to use, but slow *)
    Goal forall (n: nat) (H: sim c ((n, f z), q) n),
        sim a ((n, f x), p) n.
    Proof.
      intros n H.
      do 2 (ctx_rw open_constr:(fun t => _ t _ _) > [red_tac constr:(cl_A)|]);
      do 1 (ctx_rw open_constr:(fun t => sim _ (_, _, t) _) > [red_tac constr:(cl_C)|]);
      do 2 (ctx_rw open_constr:(fun t => sim _ (_, t, _) _) > [red_tac constr:(cl_B)|]); exact H.
    Qed.
  End FOO.
End TUTORIAL.
