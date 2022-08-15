From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World WFLib.
From Fairness Require Export Mod ModSimNoSync ModSimStutter.

Set Implicit Arguments.

Section PROOF.

  Context `{M: URA.t}.

  Variable state_src: Type.
  Variable state_tgt: Type.

  Variable _ident_src: ID.
  Definition ident_src := sum_tid _ident_src.
  Variable _ident_tgt: ID.
  Definition ident_tgt := sum_tid _ident_tgt.

  Variable wf_src: WF.
  Variable wf_tgt: WF.

  Let srcE := ((@eventE _ident_src +' cE) +' sE state_src).
  Let tgtE := ((@eventE _ident_tgt +' cE) +' sE state_tgt).

  Let shared :=
    (TIdSet.t *
       (@imap ident_src wf_src) *
       (@imap ident_tgt wf_tgt) *
       state_src *
       state_tgt *
       URA.car)%type.

  Let shared_rel: Type := shared -> Prop.

  Variable I: shared_rel.

  Lemma embed_lrr_iff
        wf_stt
        R0 R1 (RR: R0 -> R1 -> Prop) tid
        r0 r1 r_ctx o
        (shr: shared)
    :
    ModSimStutter.local_RR wf_stt I RR tid r0 r1 r_ctx o shr <->
      embed_lrr wf_stt (ModSimNoSync.local_RR I RR tid) r0 r1 r_ctx o shr.
  Proof.
    unfold embed_lrr, ModSimStutter.local_RR, ModSimNoSync.local_RR. des_ifs. split; i; des.
    - esplits; eauto.
    - esplits; eauto.
  Qed.

  Lemma stutter_lrr_weak
          wf_stt tid
          R0 R1 (LRR1 LRR2: R0 -> R1 -> URA.car -> wf_stt.(T) -> shared_rel)
          (IMPL: forall r0 r1 m o shr, LRR1 r0 r1 m o shr -> LRR2 r0 r1 m o shr)
          ps pt r_ctx src tgt (shr: shared) o
          (LSIM: ModSimStutter.lsim wf_stt I tid LRR1 ps pt r_ctx (o, src) tgt shr)
    :
    ModSimStutter.lsim wf_stt I tid LRR2 ps pt r_ctx (o, src) tgt shr.
  Proof.
    revert_until tid. pcofix CIH; i.
    remember (o, src) as osrc.
    move LSIM before CIH. revert_until LSIM.
    punfold LSIM.
    pattern R0, R1, LRR1, ps, pt, r_ctx, osrc, tgt, shr.
    revert R0 R1 LRR1 ps pt r_ctx osrc tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR1 ps pt r_ctx osrc tgt shr LSIM.
    i; clarify.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimStutter._lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs 1; eauto. }
    { pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 3; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 6; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 7; eauto. }
    { pfold. eapply pind9_fold. econs 8; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 9; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 10; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 12; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 13; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 14; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND; eauto. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 15; eauto.
      i. specialize (LSIM0 ret). pclearbot.
      right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_yieldR; eauto.
      i. hexploit LSIM0; clear LSIM0; eauto; intro LSIM. des. esplits; eauto.
      pclearbot. right. eapply CIH; eauto.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_yieldL; eauto.
      des. esplits; eauto. destruct LSIM as [LSIM IND].
      split; ss. eapply IH in IND; eauto. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimStutter.lsim_progress. right.
      eapply CIH; eauto. pclearbot. auto.
    }

  Qed.


  Let RR_rel R0 R1 := R0 -> R1 -> URA.car -> shared_rel.
  Let A R0 R1 := (bool * bool * URA.car * (itree srcE R0) * (itree tgtE R1) * shared)%type.
  Let wf_stt {R0 R1} := (@ord_tree_WF (A R0 R1)).

  Lemma nosync_implies_stutter
        tid
        R0 R1 (LRR: R0 -> R1 -> URA.car -> shared_rel)
        ps pt r_ctx src tgt
        (shr: shared)
        (LSIM: ModSimNoSync.lsim I tid LRR ps pt r_ctx src tgt shr)
    :
    exists (o: (@wf_stt R0 R1).(T)),
      ModSimStutter.lsim wf_stt I tid (embed_lrr wf_stt LRR) ps pt r_ctx (o, src) tgt shr.
  Proof.
    punfold LSIM.
    pattern R0, R1, LRR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 LRR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 LRR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimNoSync._lsim_mon. }
    inv LSIM.

    { remember (fun _: (A R0 R1) => @ord_tree_base (A R0 R1)) as ao. exists (ord_tree_cons ao).
      pfold. eapply pind9_fold. econs 1; eauto.
      unfold embed_lrr. splits; auto. ss.
      exists (ao (ps, pt, r_ctx, Ret r_src, Ret r_tgt, (ths, im_src, im_tgt, st_src, st_tgt, r_shared))).
      eapply ord_tree_lt_intro.
    }

    { destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. punfold IND.
    }
    { des. destruct LSIM0 as [LSIM IND]. eapply IH in IND. des. exists o.
      pfold. eapply pind9_fold. econs 3; eauto. exists x.
      split; ss. punfold IND.
    }
    all: admit.
  Abort.

  (*   7:{ hexploit ord_tree_join. *)
  (*       { instantiate (2:=A R0 R1). *)
  (*         instantiate (2:= fun '(ps, pt, rs, src, tgt, shr) => @rr R0 R1 LRR ps pt rs src tgt shr). *)
  (*         i. ss. des_ifs. eapply IH in SAT. *)
  (*         instantiate (1:= fun '(ps, pt, rs, src, tgt, shr) o => lsim wf_stt I tid (embed_lrr wf_stt LRR) ps pt rs (o, src) tgt shr). *)
  (*         eauto. *)
  (*       } *)
  (*       intro JOIN. des. exists o1. pfold. eapply pind9_fold. econs 10. i. specialize (LSIM0 x). *)
  (*       destruct LSIM0 as [LSIM IND]. *)
  (*       specialize (JOIN (ps, true, r_ctx, src, (ktr_tgt x), (ths, im_src, im_tgt, st_src, st_tgt, r_shared))). des_ifs. *)
  (*       eapply JOIN in IND; clear JOIN. des. *)
  (*       split; ss. *)
  (*       (*TODO*) *)

  (*       hexploit JOIN. des_ifs. eapply IND. *)

  (*         eapply SAT. *)
  (*                            upind9 (ModSimNoSync.__lsim I tid *)
  (*                                                        (upaco9 (fun r => pind9 (ModSimNoSync.__lsim I tid r) top9) bot9)) rr R0 *)
  (*                                   R1 LRR ps true r_ctx src (ktr_tgt x) (ths, im_src, im_tgt, st_src, st_tgt, r_shared)). ss. *)
  (*         clear LSIM0. i. destruct SAT as [SAT IND]. eapply IH in IND. *)

  (* IND : rr R0 R1 LRR true pt r_ctx (ktr_src x) tgt (ths, im_src, im_tgt, st_src, st_tgt, r_shared) *)


  (*         match goal with *)
  (*         | LSIM0: forall x: X, ?_P x |- _ => instantiate (2:=_P) *)
  (*         end. *)


  (*     exists X.  *)

  (*     pfold. eapply pind9_fold. econs 10; eauto. *)
  (*        i. specialize (LSIM0 x). *)
  (*        split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 4; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 5; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 6; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 7; eauto. } *)
  (*   { pfold. eapply pind9_fold. econs 8; eauto. *)
  (*     des. esplits; eauto. *)
  (*     split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 9; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 10; eauto. *)
  (*     i. specialize (LSIM0 x). *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 11; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 12; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 13; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 14; eauto. *)
  (*     i. specialize (LSIM0 _ FAIR). *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 15; eauto. *)
  (*     i. specialize (LSIM0 ret). pclearbot. *)
  (*     right. eapply CIH; eauto. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL. *)
  (*     des. esplits; eauto. *)
  (*     split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto. *)
  (*     i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto. *)
  (*     i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). *)
  (*     split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL. *)
  (*     des. esplits. eapply FAIR. split; ss. pclearbot. *)
  (*     eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right. *)
  (*     eapply CIH. apply ModSimStid.lsim_set_prog; auto. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right. *)
  (*     eapply CIH. pclearbot. auto. *)
  (*   } *)

  (* Qed. *)


  (* Theorem nosync_implies_stutter *)
  (*         tid *)
  (*         R0 R1 (RR: RR_rel R0 R1) *)
  (*         ps pt r_ctx src tgt *)
  (*         (shr: shared) *)
  (*         (LSIM: ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr) *)
  (*   : *)
  (*   exists o, ModSimStutter.lsim (@ord_tree_WF (A R0 R1)) I tid RR ps pt r_ctx (o, src) tgt shr. *)
  (* Proof. *)
  (*   revert_until tid. pcofix CIH; i. *)
  (*   punfold LSIM. *)
  (*   pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr. *)
  (*   revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc. *)
  (*   intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM. *)
  (*   eapply pind9_unfold in LSIM. *)
  (*   2:{ eapply ModSimNoSync._lsim_mon. } *)
  (*   inv LSIM. *)

  (*   { pfold. eapply pind9_fold. econs 1; eauto. } *)
  (*   { pfold. eapply pind9_fold. econs 2; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 3; eauto. *)
  (*     des. exists x. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 4; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 5; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 6; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 7; eauto. } *)
  (*   { pfold. eapply pind9_fold. econs 8; eauto. *)
  (*     des. esplits; eauto. *)
  (*     split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 9; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 10; eauto. *)
  (*     i. specialize (LSIM0 x). *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 11; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 12; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 13; eauto. *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 14; eauto. *)
  (*     i. specialize (LSIM0 _ FAIR). *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)
  (*   { pfold. eapply pind9_fold. econs 15; eauto. *)
  (*     i. specialize (LSIM0 ret). pclearbot. *)
  (*     right. eapply CIH; eauto. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL. *)
  (*     des. esplits; eauto. *)
  (*     split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto. *)
  (*     i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). *)
  (*     split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto. *)
  (*     i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT). *)
  (*     split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL. *)
  (*     des. esplits. eapply FAIR. split; ss. pclearbot. *)
  (*     eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right. *)
  (*     eapply CIH. apply ModSimStid.lsim_set_prog; auto. *)
  (*   } *)

  (*   { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right. *)
  (*     eapply CIH. pclearbot. auto. *)
  (*   } *)

  (* Qed. *)

End PROOF.
