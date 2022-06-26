From sflib Require Import sflib.
From ITree Require Export ITree.
From Paco Require Import paco.

Require Export Coq.Strings.String.
Require Import Program.
Require Import Permutation.

From ExtLib Require Import FMapAList.

Export ITreeNotations.

From Fairness Require Import pind5 pind8.
From Fairness Require Export ITreeLib FairBeh FairSim.
From Fairness Require Export Mod ModSimPico Concurrency.

Set Implicit Arguments.



Definition alist_pop (K : Type) (R : K -> K -> Prop) (DEC: RelDec.RelDec R) (V: Type)
  : K -> alist K V -> option (prod V (alist K V)) :=
  fun k l => match alist_find DEC k l with
          | None => None
          | Some v => Some (v, alist_remove DEC k l)
          end.

Definition threads_pop := alist_pop (RelDec.RelDec_from_dec eq tid_dec).



Section AUX.

  Definition alist_proj1 {K} {V} (a: alist K V): list K :=
    List.map fst a.

  Variable E1: Type -> Type.
  Variable E2: Type -> Type.

  Variable _ident_src: ID.
  Variable _ident_tgt: ID.

  Definition wf_ths {R0 R1}
             (ths_src: @threads _ident_src E1 R0)
             (ths_tgt: @threads _ident_tgt E2 R1) :=
    List.NoDup (alist_proj1 ths_src) /\
      (* List.NoDup (alist_proj1 ths_tgt) /\ *)
      Permutation (alist_proj1 ths_src) (alist_proj1 ths_tgt).

  Lemma reldec_correct_tid_dec: RelDec.RelDec_Correct (RelDec.RelDec_from_dec eq tid_dec).
  Proof. eapply RelDec.RelDec_Correct_eq_typ. Qed.

  Lemma ths_find_none_tid_add
        R (ths: @threads _ident_src E1 R) tid
        (NONE: threads_find tid ths = None)
    :
    tid_list_add (alist_proj1 ths) tid (tid :: (alist_proj1 ths)).
  Proof.
    revert_until ths. induction ths; i; ss.
    { econs; ss. }
    des_ifs. ss. destruct (tid_dec tid n) eqn:TID.
    { clarify. eapply RelDec.neg_rel_dec_correct in Heq. ss. }
    eapply IHths in NONE. inv NONE. econs; ss.
    eapply List.not_in_cons. split; auto.
  Qed.

  Lemma ths_pop_find_none
        R (ths ths0: @threads _ident_src E1 R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths0 = None.
  Proof.
    unfold threads_pop, alist_pop in POP. des_ifs.
    unfold threads_find, threads_remove. eapply remove_eq_alist.
    eapply reldec_correct_tid_dec.
  Qed.

  Lemma ths_pop_find_some
        R (ths ths0: @threads _ident_src E1 R) th tid
        (POP: threads_pop tid ths = Some (th, ths0))
    :
    threads_find tid ths = Some th.
  Proof.
    unfold threads_pop, alist_pop in POP. des_ifs.
  Qed.

  Lemma ths_find_some_tid_in
        R (ths: @threads _ident_src E1 R) tid th
        (FIND: threads_find tid ths = Some th)
    :
    tid_list_in tid (alist_proj1 ths).
  Proof.
    revert_until ths. induction ths; i; ss. des_ifs; ss.
    - left. symmetry. eapply RelDec.rel_dec_correct. eauto.
    - right. eapply IHths. eauto.
      Unshelve. eapply reldec_correct_tid_dec.
  Qed.

End AUX.



Section ADEQ.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tids _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tids _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE ident_tgt +' cE) +' sE state_tgt).
  (* Let gsrcE := @eventE ident_src. *)
  (* Let gtgtE := @eventE ident_tgt. *)

  Variable world: Type.
  Variable world_le: world -> world -> Prop.

  Let shared := @shared state_src state_tgt _ident_src _ident_tgt wf_src wf_tgt world.

  Definition threads2 _id ev R := alist tids.(id) (prod bool (@thread _id ev R)).
  Let threads_src R0 := threads2 _ident_src (sE state_src) R0.
  Let threads_tgt R1 := @threads _ident_tgt (sE state_tgt) R1.

  Variant __sim_knot R0 R1 (RR: R0 -> R1 -> Prop)
          (sim_knot: threads_src R0 -> threads_tgt R1 -> tids.(id) -> bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> shared -> Prop)
          (_sim_knot: threads_src R0 -> threads_tgt R1 -> tids.(id) -> bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> shared -> Prop)
          (thsl: threads_src R0) (thsr: threads_tgt R1)
    :
    tids.(id) -> bool -> bool -> (prod bool (itree srcE R0)) -> itree tgtE R1 -> shared -> Prop :=
    | ksim_ret_term
        tid f_src f_tgt
        sf r_src r_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        ths0 tht0 w0
        (THSR: tid_list_remove ths tid ths0)
        (THTR: tid_list_remove tht tid tht0)
        (WORLD: world_le w w0)
        (RET: RR r_src r_tgt)
        (NILS: thsl = [])
        (NILT: thsr = [])
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Ret r_src)
                 (Ret r_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_ret_cont
        tid f_src f_tgt
        sf r_src r_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        ths0 tht0 w0
        (THSR: tid_list_remove ths tid ths0)
        (THTR: tid_list_remove tht tid tht0)
        (WORLD: world_le w w0)
        (RET: RR r_src r_tgt)
        (NNILS: thsl <> [])
        (NNILT: thsr <> [])
        (KSIM: forall tid0,
            ((threads_pop tid0 thsl = None) /\ (threads_pop tid0 thsr = None)) \/
              (exists b th_src thsl0 th_tgt thsr0,
                  (threads_pop tid0 thsl = Some ((b, th_src), thsl0)) /\
                    (threads_pop tid0 thsr = Some (th_tgt, thsr0)) /\
                    ((b = true) ->
                     exists o0 w1,
                       (wf_src.(lt) o0 o) /\ (world_le w0 w1) /\
                         (forall im_tgt0
                            (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (thread_fmap tid0))),
                             sim_knot thsl0 thsr0 tid0 true true
                                      (b, Vis (inl1 (inr1 Yield)) (fun _ => th_src))
                                      (th_tgt)
                                      (ths0, tht0, im_src, im_tgt0, st_src, st_tgt, o0, w1))) /\
                    ((b = false) ->
                     (forall im_tgt0
                        (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (thread_fmap tid0))),
                       exists im_src0,
                         (fair_update im_src im_src0 (sum_fmap_l (thread_fmap tid0))) /\
                           (sim_knot thsl0 thsr0 tid0 true true
                                     (b, th_src)
                                     th_tgt
                                     (ths0, tht0, im_src0, im_tgt0, st_src, st_tgt, o, w0))))))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Ret r_src)
                 (Ret r_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_sync
        tid f_src f_tgt
        sf ktr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        thsl0 thsr0
        (THSL: thsl0 = threads_add tid (true, ktr_src tt) thsl)
        (THSR: thsr0 = threads_add tid (ktr_tgt tt) thsr)
        (KSIM: forall tid0,
            ((threads_pop tid0 thsl0 = None) /\ (threads_pop tid0 thsr0 = None)) \/
              (exists b th_src thsl1 th_tgt thsr1,
                  (threads_pop tid0 thsl0 = Some ((b, th_src), thsl1)) /\
                    (threads_pop tid0 thsr0 = Some (th_tgt, thsr1)) /\
                    ((b = true) ->
                     exists o0 w0,
                       (wf_src.(lt) o0 o) /\ (world_le w w0) /\
                         (forall im_tgt0
                            (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (thread_fmap tid0))),
                             sim_knot thsl1 thsr1 tid0 true true
                                      (b, Vis (inl1 (inr1 Yield)) (fun _ => th_src))
                                      (th_tgt)
                                      (ths, tht, im_src, im_tgt0, st_src, st_tgt, o0, w0))) /\
                    ((b = false) ->
                     (forall im_tgt0
                        (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_l (thread_fmap tid0))),
                       exists im_src0,
                         (fair_update im_src im_src0 (sum_fmap_l (thread_fmap tid0))) /\
                           (sim_knot thsl1 thsr1 tid0 true true
                                     (b, th_src)
                                     th_tgt
                                     (ths, tht, im_src0, im_tgt0, st_src, st_tgt, o, w))))))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inr1 Yield)) ktr_src)
                 (Vis (inl1 (inr1 Yield)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_yieldL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: exists im_src0 o0,
            (fair_update im_src im_src0 (sum_fmap_l (thread_fmap tid))) /\
              (_sim_knot thsl thsr tid true f_tgt
                         (false, ktr_src tt)
                         itr_tgt
                         (ths, tht, im_src0, im_tgt, st_src, st_tgt, o0, w)))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inr1 Yield)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_tauL
        tid f_src f_tgt
        sf itr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, itr_src)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Tau itr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_ChooseL
        tid f_src f_tgt
        sf X ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: exists x, _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src x)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 (Choose X))) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_putL
        tid f_src f_tgt
        sf st_src0 ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src tt)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src0, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inr1 (Mod.Put st_src0)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_getL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src st_src)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inr1 (@Mod.Get _)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_tidL
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src tid)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inr1 GetTid)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_UB
        tid f_src f_tgt
        sf ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 Undefined)) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_fairL
        tid f_src f_tgt
        sf fm ktr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: exists im_src0,
            (<<FAIR: fair_update im_src im_src0 (sum_fmap_r fm)>>) /\
              (_sim_knot thsl thsr tid true f_tgt
                         (sf, ktr_src tt)
                         itr_tgt
                         (ths, tht, im_src0, im_tgt, st_src, st_tgt, o, w)))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 (Fair (sum_fmap_r fm)))) ktr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_tauR
        tid f_src f_tgt
        sf itr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         itr_tgt
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Tau itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_ChooseR
        tid f_src f_tgt
        sf itr_src X ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: forall x, _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt x)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (Choose X))) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_putR
        tid f_src f_tgt
        sf itr_src st_tgt0 ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt tt)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt0, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inr1 (Mod.Put st_tgt0)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_getR
        tid f_src f_tgt
        sf itr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt st_tgt)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inr1 (@Mod.Get _)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_tidR
        tid f_src f_tgt
        sf itr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: _sim_knot thsl thsr tid f_src true
                         (sf, itr_src)
                         (ktr_tgt tid)
                         (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inr1 GetTid)) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
    | ksim_fairR
        tid f_src f_tgt
        sf itr_src fm ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: forall im_tgt0 (FAIR: fair_update im_tgt im_tgt0 (sum_fmap_r fm)),
            (_sim_knot thsl thsr tid f_src true
                       (sf, itr_src)
                       (ktr_tgt tt)
                       (ths, tht, im_src, im_tgt0, st_src, st_tgt, o, w)))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, itr_src)
                 (Vis (inl1 (inl1 (Fair (sum_fmap_r fm)))) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_observe
        tid f_src f_tgt
        sf fn args ktr_src ktr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: forall ret, sim_knot thsl thsr tid true true
                               (sf, ktr_src ret)
                               (ktr_tgt ret)
                               (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid f_src f_tgt
                 (sf, Vis (inl1 (inl1 (Observe fn args))) ktr_src)
                 (Vis (inl1 (inl1 (Observe fn args))) ktr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)

    | ksim_progress
        tid
        sf itr_src itr_tgt
        ths tht im_src im_tgt st_src st_tgt o w
        (KSIM: sim_knot thsl thsr tid false false
                        (sf, itr_src)
                        itr_tgt
                        (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w))
      :
      __sim_knot RR sim_knot _sim_knot thsl thsr tid true true
                 (sf, itr_src)
                 (itr_tgt)
                 (ths, tht, im_src, im_tgt, st_src, st_tgt, o, w)
  .

  Definition sim_knot R0 R1 (RR: R0 -> R1 -> Prop):
    threads_src R0 -> threads_tgt R1 -> tids.(id) ->
    bool -> bool -> (prod bool (itree srcE R0)) -> (itree tgtE R1) -> shared -> Prop :=
    paco8 (fun r => pind8 (__sim_knot RR r) top8) bot8.

  Lemma __ksim_mon R0 R1 (RR: R0 -> R1 -> Prop):
    forall r r' (LE: r <8= r'), (__sim_knot RR r) <9= (__sim_knot RR r').
  Proof.
    ii. inv PR; try (econs; eauto; fail).
    { econs 2; eauto. i. specialize (KSIM tid0). des; eauto. right.
      esplits; eauto.
      i. specialize (KSIM1 H). des. esplits; eauto.
      i. specialize (KSIM2 H _ FAIR). des. esplits; eauto.
    }
    { econs 3; eauto. i. specialize (KSIM tid0). des; eauto. right.
      esplits; eauto.
      i. specialize (KSIM1 H). des. esplits; eauto.
      i. specialize (KSIM2 H _ FAIR). des. esplits; eauto.
    }
  Qed.

  Lemma _ksim_mon R0 R1 (RR: R0 -> R1 -> Prop): forall r, monotone8 (__sim_knot RR r).
  Proof.
    ii. inv IN; try (econs; eauto; fail).
    { des. econs; eauto. }
    { des. econs; eauto. }
    { des. econs; eauto. }
  Qed.

  Lemma ksim_mon R0 R1 (RR: R0 -> R1 -> Prop): forall q, monotone8 (fun r => pind8 (__sim_knot RR r) q).
  Proof.
    ii. eapply pind8_mon_gen; eauto.
    ii. eapply __ksim_mon; eauto.
  Qed.

  Local Hint Constructors __sim_knot: core.
  Local Hint Unfold sim_knot: core.
  Local Hint Resolve __ksim_mon: paco.
  Local Hint Resolve _ksim_mon: paco.
  Local Hint Resolve ksim_mon: paco.



  Ltac gfold := gfinal; right; pfold.

  Ltac pull_tau := rewrite interp_sched_tau; rewrite interp_state_tau.

  Ltac pull_eventE_l :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inl1 (inl1 EV)) >>= ktr)
    end; auto; rewrite interp_sched_eventE_trigger; rewrite interp_state_trigger.

  Ltac pull_eventE_r :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inl1 (inl1 EV)) >>= ktr)
    end; auto; rewrite interp_sched_eventE_trigger; rewrite interp_state_trigger.

  Ltac pull_sE_l :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inr1 EV) >>= ktr)
    end; auto; rewrite interp_sched_trigger.

  Ltac pull_sE_r :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inr1 EV) >>= ktr)
    end; auto; rewrite interp_sched_trigger.

  Ltac rewrite_cE_l :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) _ => replace (trigger EV >>= ktr) with (trigger (inl1 (inr1 EV)) >>= ktr)
    end; auto.

  Ltac rewrite_cE_r :=
    match goal with
    | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, interp_sched (_, inl (_, trigger ?EV >>= ?ktr)))) => replace (trigger EV >>= ktr) with (trigger (inl1 (inr1 EV)) >>= ktr)
    end; auto.



  Lemma sim_perm_l
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        (st_src: state_src) (st_tgt: state_tgt)
        tid ths_tgt tgt
        (ths_src0 ths_src1: @threads _ident_src (sE state_src) R0)
        (PERM: Permutation ths_src0 ths_src1)
        (SIM: sim RR ps ms pt mt
                  (interp_state (st_src, Tau (interp_sched (ths_src1, inr (inl ())))))
                  (interp_state (st_tgt, interp_sched (ths_tgt, inl (tid, tgt)))))
    :
    sim RR ps ms pt mt
        (interp_state (st_src, Tau (interp_sched (ths_src0, inr (inl ())))))
        (interp_state (st_tgt, interp_sched (ths_tgt, inl (tid, tgt)))).
  Proof.
    unfold thread in *. rewrite interp_sched_pick_yield in *. rewrite interp_state_tau in *.
    


  Lemma sim_yieldL_change
        R0 R1 (RR: R0 -> R1 -> Prop)
        ps pt (ms: @imap ident_src wf_src) (mt: @imap ident_tgt wf_tgt)
        (st_src: state_src) (st_tgt: state_tgt)
        tid0 tid1 ths_tgt tgt
        (ths_src0 ths_src1: @threads _ident_src (sE state_src) R0)
        ktr_src0 src
        (POP: threads_pop tid1 (threads_add tid0 (ktr_src0 tt) ths_src0) = Some (src, ths_src1))
        (SIM: sim RR ps ms pt mt
                  (interp_all st_src ths_src1 tid1 (Vis (inl1 (inr1 Yield)) (fun _ => src)))
                  (interp_all st_tgt ths_tgt tid1 tgt))
    :
    sim RR ps ms pt mt
        (interp_all st_src ths_src0 tid0 (Vis (inl1 (inr1 Yield)) ktr_src0))
        (interp_all st_tgt ths_tgt tid1 tgt).
  Proof.
    unfold interp_all in *. unfold thread in *. rewrite interp_sched_yield_vis in *.


  Variable I: shared -> Prop.

  (*invariant for tid_list & threads: tid_list_add threads.proj1 tid tid_list*)
  Theorem local_adequacy
          R0 R1 (RR: R0 -> R1 -> Prop)
          (ths_src: @threads _ident_src (sE state_src) R0)
          (ths_tgt: @threads _ident_tgt (sE state_tgt) R1)
          (* (WFTHS: wf_ths ths_src ths_tgt) *)
          (LOCAL: forall tid (src: itree srcE R0) (tgt: itree tgtE R1)
                    (LSRC: threads_find tid ths_src = Some src)
                    (LTGT: threads_find tid ths_tgt = Some tgt),
              (local_sim world_le I RR src tgt))
          tid
          (THSRC: threads_find tid ths_src = None)
          (THTGT: threads_find tid ths_tgt = None)
          src tgt
          (LSIM: local_sim world_le I RR src tgt)
          (st_src: state_src) (st_tgt: state_tgt)
          (INV: forall im_tgt, exists im_src o w,
              I (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, im_src, im_tgt, st_src, st_tgt, o, w))
          (* (INV: forall im_tgt, exists im_src o w, *)
          (*     I (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, im_src, im_tgt, st_src, st_tgt, o, w)) *)
          (* ths_src0 ths_tgt0 *)
          (* (THSRC: threads_pop tid ths_src = Some (src0, ths_src0)) *)
          (* (THTGT: threads_pop tid ths_tgt = Some (tgt0, ths_tgt0)) *)
          gps gpt
    :
    gsim wf_src wf_tgt RR gps gpt
         (interp_all st_src ths_src tid src)
         (interp_all st_tgt ths_tgt tid tgt).
  Proof.
    ii. specialize (INV mt). des. rename im_src into ms. exists ms.
    unfold local_sim in LSIM.
    hexploit LSIM; clear LSIM. 3: eauto.
    { instantiate (1:=tid). ss. auto. }
    { ss. auto. }
    intro LSIM. clear INV.
    instantiate (1:=gpt) in LSIM. instantiate (1:=gps) in LSIM.
    (* instantiate (1:=true) in LSIM. instantiate (1:=true) in LSIM. *)

    ginit. revert_until RR. gcofix CIH. i.
    move o before CIH. revert_until o. induction (wf_src.(wf) o). clear H. rename x into o, H0 into IHo. i.

    match goal with
    | LSIM: lsim _ _ ?_LRR tid _ _ _ _ ?_shr |- _ => remember _LRR as LRR; remember _shr as shr
    end.
    (* remember true as ps in LSIM at 1. remember true as pt in LSIM at 1. *)
    (* clear Heqps Heqpt. *)
    (* remember tid as tid0 in LSIM. *)
    punfold LSIM.
    2:{ ii. eapply pind5_mon_gen; eauto. i. eapply __lsim_mon; eauto. }
    move LSIM before LOCAL. revert_until LSIM.
    eapply pind5_acc in LSIM.

    { instantiate (1:= (fun gps gpt (src: itree srcE R0) (tgt: itree tgtE R1) shr =>
                          threads_find tid ths_src = None ->
                          threads_find tid ths_tgt = None ->
                          forall (st_src : state_src) (st_tgt : state_tgt) (mt : imap wf_tgt) (ms : imap wf_src) (w : world),
                            LRR = local_RR world_le I RR tid ->
                            shr = (tid :: alist_proj1 ths_src, tid :: alist_proj1 ths_tgt, ms, mt, st_src, st_tgt, o, w) ->
                            gpaco9 (_sim (wft:=wf_tgt)) (cpn9 (_sim (wft:=wf_tgt))) bot9 r R0 R1 RR gps ms gpt mt (interp_all st_src ths_src tid src)
                                   (interp_all st_tgt ths_tgt tid tgt))) in LSIM. auto. }

    ss. clear gps gpt src tgt shr LSIM.
    intros rr DEC IH ps pt src tgt shr LSIM. clear DEC.
    intros THSRC THTGT st_src st_tgt mt ms w ELRR Eshr.
    (* intros THSRC THTGT st_src st_tgt mt ms o w gps gpt ELRR Eshr Eps Ept. clarify. *)
    eapply pind5_unfold in LSIM.
    2:{ eapply _lsim_mon. }
    inv LSIM.

    { clear IH rr. unfold local_RR in LSIM0. des. clarify.
      unfold interp_all. rewrite ! interp_sched_ret. rewrite ! interp_state_tau.
      guclo sim_indC_spec. econs 3. guclo sim_indC_spec. econs 4.
      rewrite ! interp_sched_pick_ret.
      (*TODO: case analysis; all threads done / some other gets the turn -> CIH*)
      admit.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_tau.
      guclo sim_indC_spec. econs 3.
      eapply IH. eauto. all: eauto.
    }

    { des. clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_eventE_l.
      guclo sim_indC_spec. econs 5. exists x.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_sE_l. rewrite interp_state_put.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. pull_sE_l. rewrite interp_state_get.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 1. rewrite_cE_l. rewrite interp_sched_gettid.
      rewrite interp_state_tau. do 1 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all at 1. pull_eventE_l.
      guclo sim_indC_spec. econs 10.
    }

    { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM.
      unfold interp_all at 1. pull_eventE_l.
      guclo sim_indC_spec. econs 7. esplits; eauto.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 3).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. pull_tau.
      guclo sim_indC_spec. econs 4.
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all at 2. pull_eventE_r.
      guclo sim_indC_spec. econs 6. i.
      specialize (LSIM0 x). destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. pull_sE_r. rewrite interp_state_put.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. pull_sE_r. rewrite interp_state_get.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      unfold interp_all at 2. rewrite_cE_r. rewrite interp_sched_gettid.
      rewrite interp_state_tau. do 1 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all at 2. pull_eventE_r.
      guclo sim_indC_spec. econs 8. i.
      specialize (LSIM0 m_tgt0 FAIR). des. destruct LSIM0 as [LSIM0 IND]. clear LSIM0.
      rewrite interp_state_tau. do 2 (guclo sim_indC_spec; econs 4).
      eapply IH. eauto. all: eauto.
    }

    { clarify. unfold interp_all. pull_eventE_l. pull_eventE_r.
      rewrite ! bind_trigger. gfold. econs 2. i; clarify.
      rename r_tgt into retv. specialize (LSIM0 retv). pclearbot.
      clear IH rr.
      rewrite <- ! interp_state_tau. rewrite <- ! interp_sched_tau.
      right. eapply CIH; auto.
      pfold.
      eapply pind5_fold. econs 2. split; ss. eapply pind5_fold. econs 9. split; ss.
      eapply pind5_fold. econs 2. split; ss. eapply pind5_fold. econs 9. split; ss.
      punfold LSIM0. eapply lsim_mon.
    }

    { clarify. clear IH rr.
      unfold interp_all at 2. rewrite_cE_r.
      rewrite interp_sched_yield. rewrite interp_sched_pick_yield2.
      rewrite interp_state_tau. rewrite interp_state_trigger.
      guclo sim_indC_spec. econs 4.
      guclo sim_indC_spec. econs 6. i.
      guclo sim_indC_spec. econs 4.
      (*destruct cases: UB case / 
        x = tid: ind on o1, ind on LSIM0, trivial case: LSIM0, sync: case analysis: IHo1|CIH /
        x <> tid: CIH, LOCAL*)
      des_ifs.
      2:{ admit. }
      destruct (tid_dec x tid) eqn:TID.
      { clarify. eapply IHo. eauto. 1,2,3: admit.
        admit.
      }
      unfold interp_all at 1. rewrite_cE_l.
      rewrite interp_sched_yield. rewrite interp_sched_pick_yield2.
      rewrite interp_state_tau. rewrite interp_state_trigger.
      guclo sim_indC_spec. econs 3.
      guclo sim_indC_spec. econs 5. exists x.
      guclo sim_indC_spec. econs 3.
      (* make lemma for threads_pop *)
      des_ifs.
      2:{ admit. }
      hexploit LOCAL.
      { instantiate (1:=t1). instantiate (1:=x). admit. }
      { instantiate (1:=t). admit. }
      intros LSIM. unfold local_sim in LSIM. hexploit LSIM. 3: eauto.
      { instantiate (1:=x). admit. }
      { admit. }
      clear LSIM; intro LSIM.



      
      gfold. econs 9. right. eapply CIH; ss; auto. all: ss.
      1,2,3: admit.
      


          
        match goal with
        | |- gpaco9 _ _ _ _ _ _ _ _ _ _ _ _ (interp_state (_, trigger ?EV >>= Tau (interp_sched ?a))) =>
            replace (trigger EV >>= Tau (interp_sched a)) with (x <- trigger EV >>= Tau (interp_sched a))
        end; auto; rewrite <- interp_sched_eventE_trigger.

        push_eventE_r.

        
        rewrite interp_state_trigger.
        rewrite bind_trigger. rewrite <- interp_sched_eventE_trigger.
        rewrite interp_sched_tau.

      admit. }

    { des. clarify. destruct LSIM as [LSIM IND]. clear LSIM.
      unfold interp_all at 1. rewrite_cE_l.
      rewrite interp_sched_yield. rewrite interp_sched_pick_yield.
      rewrite interp_state_tau. rewrite interp_state_trigger.
      guclo sim_indC_spec. econs 3.
      guclo sim_indC_spec. econs 5. exists tid.
      guclo sim_indC_spec. econs 3.
      (* lemma for threads_pop, etc., induction *)
      admit.
    }

    { clarify. pclearbot. gfold. econs 9; auto.
      clear IH rr.
      right. eapply CIH; auto. eauto.
    }

  Abort.

  (* Permutation ths_src0 ths_src1 /\ Permutation ths_tgt0 ths_tgt1 /\ I (ths_src0, ths_tgt0, ...) -> I (ths_src1, ths_tgt1, ...). *)


  Lemma ths_find_none_ths_pop_some:
    threads_find tid ths = None /\ threads_pop t ths <> None
    -> t <> tid.
  Abort.

  Lemma ths_find_none_tlist_remove:
    threads_find tid ths = None /\ tid_list_remove (tid :: alist_proj1 ths) tid tl
    -> tl = alist_proj1 ths.
  Abort.

  Lemma perm_ths_pop:
    Permutation (alist_proj1 ths1) (alist_proj1 ths2) /\ threads_pop tid ths1 = Some (th1, ths3)
    -> exists th1 ths4, threads_pop tid ths2 = Some (th1, ths4) /\
                    Permutation (alist_proj1 ths3) (alist_proj1 ths4).
  Abort.

  Lemma ths_pop_cons_perm:
    threads_pop tid ths = Some (th, ths0) /\ List.NoDup (alist_proj1 ths)
    -> Permutation (alist_proj1 ths) (tid :: alist_proj1 ths0).
  Abort.

  Lemma ths_pop_update_ths_eq:
    List.NoDup (alist_proj1 ths) ->
    threads_pop tid (update_threads tid itr ths) = Some (itr, ths).
  Abort.

  Lemma ths_pop_update_ths_perm:
    List.NoDup (alist_proj1 ths) /\
      threads_pop t (update_threads tid itr ths) = Some (th, ths0) ->
    Permutation (tid :: alist_proj1 ths) (t :: alist_proj1 ths0).
  Abort.

  



End ADEQ.
