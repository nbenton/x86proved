Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic basicprog program macros.
Require Import instr instrsyntax instrcodec instrrules reader pointsto cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Example: It is safe to sit forever in a tight loop. *)
Example safe_loop (p q: DWORD) :
  |-- safe @ (EIP ~= p ** p -- q :-> JMP p).
Proof.
  apply: spec_lob.
  have H := @JMP_I_rule p p q.
  rewrite ->spec_reads_entails_at in H; [|apply _].
  autorewrite with push_at in H. apply landAdj in H.
  etransitivity; [|apply H]. apply: landR; [sbazooka | reflexivity].
Qed.

(* We can package up jumpy code in a triple by using labels. *)
Example basic_loop:
  |-- basic empSP (LOCAL l; l:;; JMP l) lfalse.
Proof.
  rewrite /basic. specintros => i j.
  unfold_program. specintros => _ _ <- <-.
  rewrite /spec_reads. specintros => code Hcode.
  autorewrite with push_at.
  apply: limplAdj. apply: landL1.
  etransitivity; [apply safe_loop|]. cancel1. rewrite ->Hcode. by ssimpl.
Qed.

(* Show off the sequencing rule for [basic]. *)
Example basic_inc3 x:
  |-- basic (EAX ~= x)
            (INC EAX;; INC EAX;; INC EAX)
            (EAX ~= x +# 3) @ OSZCP_Any.
Proof.
  autorewrite with push_at. rewrite /OSZCP_Any /flagAny.
  specintros => o s z c p.
  eapply basic_seq; [apply INC_R_rule|].
  eapply basic_seq; [apply INC_R_rule|].
  eapply basic_roc_post; [|apply INC_R_rule].
  rewrite addIsIterInc /OSZCP /iter. by sbazooka.
Qed.

Example incdec_while c a:
  |-- basic
    (ECX ~= c ** EAX ~= a)
    (
      while (TEST ECX, ECX) CC_Z false (
        DEC ECX;;
        INC EAX
      )
    )
    (ECX ~= #0 ** EAX ~= addB c a)
    @ OSZCP_Any.
Proof.
  autorewrite with push_at.
  set (I := fun b => Exists c', Exists a',
    (c' == #0) = b /\\ addB c' a' = addB c a /\\
    ECX ~= c' ** EAX ~= a' **
    flagAny OF ** flagAny SF ** flagAny CF ** flagAny PF).
  eapply basic_basic_context; first apply (while_rule_ro (I:=I));
      first 2 last.
  - reflexivity.
  - subst I. rewrite /OSZCP_Any /flagAny/ConditionIs. sbazooka.
  - subst I; cbv beta. sdestructs => c' a' Hzero Hadd.
    rewrite ->(eqP Hzero) in *. rewrite add0B in Hadd.
    subst a'. rewrite /OSZCP_Any/ConditionIs/flagAny. by sbazooka.
  - specintros => b1 b2. subst I; cbv beta. specintros => c' a' Hzero Hadd.
    eapply basic_basic; first eapply TEST_self_rule.
    + rewrite /OSZCP_Any/ConditionIs/flagAny. by sbazooka.
    rewrite /OSZCP/ConditionIs/flagAny. by sbazooka.
  - subst I; cbv beta. specintros => c' a' Hzero Hadd.
    rewrite /flagAny. specintros => fo fs fc fp. eapply basic_seq.
    + eapply basic_basic; first eapply DEC_R_rule.
      * rewrite /OSZCP /ConditionIs. by ssimpl.
      done.
    eapply basic_basic; first eapply INC_R_rule.
    + by ssimpl.
    ssplits; first last.
    + rewrite /OSZCP/ConditionIs/OSZCP_Any /flagAny. by sbazooka.
    + rewrite <-Hadd. exact: addB_decB_incB.
    + done.
Qed.

