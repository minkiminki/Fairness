From sflib Require Import sflib.
From Paco Require Import paco.

Require Import Coq.Classes.RelationClasses.
Require Import Program.
Require Import Permutation.

From Fairness Require Import Axioms.
From Fairness Require Export ITreeLib FairBeh FairSim NatStructs.
From Fairness Require Import pind PCM World.
From Fairness Require Import Mod ModSimStid ModSimNoSync.

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

  Theorem stid_implies_nosync
          tid
          R0 R1 (RR: R0 -> R1 -> URA.car -> shared_rel)
          ps pt r_ctx src tgt
          (shr: shared)
          (LSIM: ModSimStid.lsim I tid RR ps pt r_ctx src tgt shr)
    :
    ModSimNoSync.lsim I tid RR ps pt r_ctx src tgt shr.
  Proof.
    revert_until tid. pcofix CIH; i.
    punfold LSIM.
    pattern R0, R1, RR, ps, pt, r_ctx, src, tgt, shr.
    revert R0 R1 RR ps pt r_ctx src tgt shr LSIM. apply pind9_acc.
    intros rr DEC IH. clear DEC. intros R0 R1 RR ps pt r_ctx src tgt shr LSIM.
    eapply pind9_unfold in LSIM.
    2:{ eapply ModSimStid._lsim_mon. }
    inv LSIM.

    { pfold. eapply pind9_fold. econs 1; eauto. }
    { pfold. eapply pind9_fold. econs 2; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 3; eauto.
      des. exists x.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 4; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 5; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 6; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 7; eauto. }
    { pfold. eapply pind9_fold. econs 8; eauto.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 9; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 10; eauto.
      i. specialize (LSIM0 x).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 11; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 12; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 13; eauto.
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }
    { pfold. eapply pind9_fold. econs 14; eauto.
      i. specialize (LSIM0 _ FAIR).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. econs 15; eauto.
      i. specialize (LSIM0 ret). pclearbot.
      split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_progress.
      right. eapply CIH; eauto. eapply ModSimStid.lsim_set_prog. auto.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL.
      des. esplits; eauto.
      split; ss. destruct LSIM as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. destruct LSIM0 as [LSIM IND]. eapply IH in IND. punfold IND.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldR; eauto.
      i. specialize (LSIM0 _ _ _ _ _ _ _ INV0 VALID0 _ TGT).
      split; ss. eapply pind9_fold. eapply ModSimNoSync.lsim_yieldL.
      des. esplits. eapply FAIR. split; ss. pclearbot.
      eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right.
      eapply CIH. apply ModSimStid.lsim_set_prog; auto.
    }

    { pfold. eapply pind9_fold. eapply ModSimNoSync.lsim_progress. right.
      eapply CIH. pclearbot. auto.
    }

  Qed.

End PROOF.
