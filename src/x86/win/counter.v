Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import x86proved.x86.win.pecoff x86proved.x86.cfunc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

Require Import x86proved.x86.call.
Example counterDLL :=
  GLOBAL Get as "Get";
  GLOBAL Inc as "Inc";
  GLOBAL Counter;
  SECTION CODE
    Inc:;;  mkbody_toyfun (MOV ECX, Counter;; INC [ECX]);;
    Get:;;  mkbody_toyfun (MOV ECX, Counter;; MOV EAX, [ECX]);
  SECTION DATA
    Counter:;; dd #0.

Compute makeDLL #x"00AC0000" "counter.dll" counterDLL.

(*
Require Import SPred septac spectac spec safe pointsto cursor instr.
Require Import basic basicprog program instrsyntax macros instrrules.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

Example counterModuleSpec IAT P Inc Get :=
      (Forall c: DWORD, toyfun Inc (P c ** ECX? ** OSZCP?) (P (c +# 1) ** ECX? ** OSZCP?))
    //\\
      (Forall c: DWORD, toyfun Get (EAX? ** P c ** ECX? ** OSZCP?) (EAX ~= c ** P c ** ECX? ** OSZCP?))
    <@ (IAT :-> (Inc, Get)).

Example counterModuleCode (Inc Get Counter: DWORD) :=
(*  LOCAL Inc; LOCAL Get; LOCAL Counter;*)
    Inc:;;  mkbody_toyfun (MOV ECX, Counter;; INC [ECX]);;
    Get:;;  mkbody_toyfun (MOV ECX, Counter;; MOV EAX, [ECX]).

Example counterModuleData :=
    dd #0.

Example counterModuleIAT Inc Get :=
    dd Inc;; dd Get.

Require Import flags.
Theorem counterModuleCorrect (codeStart codeEnd dataStart:DWORD):
  |-- Forall Inc, Forall Get,
      counterModuleSpec codeStart (fun v => dataStart :-> v) Inc Get <@ (codeStart -- codeEnd :-> counterModuleCode Inc Get dataStart).
Proof.
rewrite /counterModuleSpec.
rewrite /counterModuleCode.
specintros => Inc Get. unfold_program.

specintros => i1 -> -> i2 i3 -> ->.
rewrite !empSPL.
specsplit.
(* Inc *)
specintros => c.
rewrite <- spec_reads_merge.
rewrite <- spec_reads_frame.
  etransitivity; [|apply toyfun_mkbody]. specintro => iret.
  rewrite /flagAny. specintros => O S Z C P. autorewrite with push_at.
  basicapply MOV_RI_rule.
  basicapply INC_M_rule. rewrite addB0.
  rewrite /OSZCP. sbazooka. rewrite addB1 addB0. rewrite /regAny.
  sbazooka.
  rewrite /OSZCP. ssimpl. reflexivity.

(* Get *)
specintros => c.
rewrite spec_reads_swap.
rewrite <- spec_reads_frame.
rewrite <- spec_reads_merge.
rewrite <- spec_reads_swap.
rewrite <- spec_reads_frame.
  etransitivity; [|apply toyfun_mkbody]. specintro => iret.
  rewrite /flagAny. specintros => O S Z C P. autorewrite with push_at.
  basicapply MOV_RI_rule.
  basicapply MOV_RM0_rule. rewrite /regAny. sbazooka.
Qed.

Example useCounterModule IAT : program :=
  MOV EDI, IAT;; call_toyfun [EDI];;
  MOV EDI, IAT;; call_toyfun [EDI];;
  MOV EDI, IAT;; call_toyfun [EDI+4].

Example useCounterModuleCorrect (codeStart codeEnd dataStart Inc Get IAT: DWORD):
  counterModuleSpec codeStart (fun v => dataStart :-> v) Inc Get
  |-- basic (EAX?) (useCounterModule IAT) (EAX ~= #2) @
      (EDI? ** OSZCP? ** retreg?) <@ (IAT :-> (Inc,Get)).
Proof.
  rewrite /useCounterModule. autorewrite with push_at.
  rewrite <- spec_reads_frame.
  eapply basic_seq.
  basicapply MOV_RI_rule.
  rewrite /counterModuleSpec.
  apply landL1.
  - (*apply lforallL with c.*)
    eapply basic_basic_context.
    - have H := toyfun_call. setoid_rewrite spec_at_basic in H. apply H.
    - by apply spec_later_weaken.
    - by ssimpl.
    done.
  apply lforallL with (a +# 2).
  eapply basic_basic_context.
  - have H := toyfun_call. setoid_rewrite spec_at_basic in H. apply H.
  - by apply spec_later_weaken.
  - by ssimpl.
  rewrite -addB_addn. rewrite -[2+2]/4. by ssimpl.
Qed.

Example useCounterSpec IAT :

*)
