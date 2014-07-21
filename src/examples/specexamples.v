Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.opred x86proved.septac x86proved.spec x86proved.obs x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor.
Require Import x86proved.spectac.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Example: It is safe to sit forever in a tight loop. *)
Example safe_loop (p q: DWORD) (O : PointedOPred) :
  |-- obs O @ (EIP ~= p ** p -- q :-> JMP p).
Proof.
  apply: spec_lob.
  have H := @JMP_I_loopy_rule p p q.
  apply (lforallE_spec O) in H. cbv beta in H.
  rewrite ->spec_reads_entails_at in H; [|apply _].
  autorewrite with push_at in H. apply landAdj in H.
  etransitivity; [|apply H]. apply: landR; [sbazooka | reflexivity].
Qed.

(* We can package up jumpy code in a triple by using labels. *)
Example basic_loop:
  |-- loopy_basic empSP (LOCAL l; l:;; JMP l) empOP lfalse.
Proof.
  rewrite /loopy_basic. specintros => i j O'.
  unfold_program. specintros => _ _ <- <-.
  rewrite /spec_reads. specintros => code Hcode.
  autorewrite with push_at.
  apply: limplAdj. apply: landL1. rewrite -> Hcode.
  etransitivity; [apply safe_loop|]. rewrite ->empOPL. cancel2. reflexivity. eexists _. split; by ssimpl.
Qed.

(* Show off the sequencing rule for [basic]. *)
Example basic_inc3 x:
  |-- basic (EAX ~= x)
            (INC EAX;; INC EAX;; INC EAX) empOP
            (EAX ~= x +# 3) @ OSZCP?.
Proof.
  autorewrite with push_at. rewrite /stateIsAny.
  specintros => o s z c p.
  try_basicapply INC_R_rule. rewrite /OSZCP; sbazooka.
  try_basicapply INC_R_rule. rewrite /OSZCP; sbazooka.
  try_basicapply INC_R_rule. rewrite /OSZCP; sbazooka.
  rewrite /OSZCP addIsIterInc/iter; sbazooka.
Qed.

Example incdec_while c a:
  |-- loopy_basic
    (ECX ~= c ** EAX ~= a)
    (
      while (TEST ECX, ECX) CC_Z false (
        DEC ECX;;
        INC EAX
      )
    ) empOP
    (ECX ~= #0 ** EAX ~= addB c a)
    @ OSZCP?.
Proof.
  autorewrite with push_at.
  set (I := fun b => Exists c', Exists a',
    (c' == #0) = b /\\ addB c' a' = addB c a /\\
    ECX ~= c' ** EAX ~= a' **
    OF? ** SF? ** CF? ** PF?).
  eapply basic_basic_context; first apply (while_rule_ro (I:=I));
      first 2 last.
  - reflexivity.
  - subst I. rewrite /stateIsAny/ConditionIs. sbazooka.
  - reflexivity.
  - subst I; cbv beta. sdestructs => c' a' Hzero Hadd.
    rewrite ->(eqP Hzero) in *. rewrite add0B in Hadd.
    subst a'. rewrite /ConditionIs/stateIsAny. by sbazooka.
  - specintros => b1 b2. subst I; cbv beta. specintros => c' a' Hzero Hadd.
    eapply basic_basic. exact (TEST_self_rule (v:= c')).
    + rewrite /ConditionIs/stateIsAny. by sbazooka.
    rewrite /OSZCP/ConditionIs/stateIsAny. by sbazooka.
  - subst I; cbv beta. specintros => c' a' Hzero Hadd.
    rewrite /stateIsAny. specintros => fo fs fc fp.
    try_basicapply DEC_R_rule. + by rewrite /OSZCP/ConditionIs; ssimpl.
    try_basicapply INC_R_rule. + by rewrite addB_decB_incB.
    rewrite /OSZCP/ConditionIs.
    sbazooka.
Qed.
