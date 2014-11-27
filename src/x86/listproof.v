(*===========================================================================
  Proof that the linked-list implementation meets its spec
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.spectac x86proved.opred x86proved.obs x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.call x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.cursor x86proved.x86.inlinealloc
               x86proved.x86.listspec x86proved.x86.listimp x86proved.triple.
Require Import x86proved.x86.macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Hint Rewrite -> signExtend_fromNat : ssimpl. 
Hint Rewrite -> addB0 : ssimpl. 

Hint Unfold fromSingletonMemSpec : specapply.
Require Import basicspectac.

Lemma inlineHead_correct r1 r2 (i j: ADDR) (p e: QWORD) v vs :
  inlineHead_spec r1 r2 i j p e v vs (inlineHead r1 r2).
Proof.
rewrite /inlineHead_spec/inlineHead/listSeg-/listSeg. unfold_program.
specintro => O. rewrite /stateIsAny.
specintros => q old. 
specapply *. unfold eval.computeEA, ADRtoADDR, eval.computeDisplacement.
sbazooka. 
rewrite <-spec_reads_frame. autorewrite with push_at.
apply limplValid. cancel1. by ssimpl. 
Qed.

Lemma inlineTail_correct (r1 r2: GPReg64) (i j:ADDR) (p e: QWORD) v vs :
  inlineTail_spec r1 r2 i j p e v vs (inlineTail r1 r2).
Proof.
rewrite /inlineTail_spec/inlineTail/listSeg-/listSeg. unfold_program.
specintro => O. rewrite /stateIsAny.
specintros => q old. 
specapply *. unfold eval.computeEA, ADRtoADDR, eval.computeDisplacement. sbazooka.
(* Why doesn't sbazooka clear this? *)
rewrite sepSPC. rewrite sepSPA. reflexivity. 
rewrite <-spec_reads_frame. autorewrite with push_at.
apply limplValid. cancel1. sbazooka. (* Again, what has happened here *) reflexivity. 
Qed.

Lemma inlineCons_correct (r1 r2: GPReg64) failAddr (i j:ADDR) (h t e: QWORD) vs :
  inlineCons_spec r1 r2 failAddr i j h t e vs (inlineCons r1 r2 failAddr).
Proof.
rewrite /inlineCons_spec/inlineCons/updateCons. unfold_program.
specintro => O. specintros => i1 i2 i3.

specapply inlineAlloc_correct. rewrite /allocInv. ssimpl.

(* Failure case *)
specsplit.
  rewrite <-spec_reads_frame. autorewrite with push_at. 
  Require Import chargetac.
  apply limplValid. apply landL1. finish_logic_with sbazooka. 

(* Success case *)
specintros => pb.
have MASA := (memAnySplitAdd pb (m1:=4)).
admit. 
(*(*rewrite -> addB_addn.*)
specintros => d1 d2.
do 1 rewrite -> memAny_entails_pointsToDWORD. 

elim E0:(sbbB false (pb+#8) #8) => [carry0 res0].
assert (H:= subB_equiv_addB_negB (pb+#8) #8).
rewrite E0 addB_negBn /snd in H.
rewrite H in E0. replace (pb +#4 +#4) with (pb +#8) by by rewrite -addB_addn.

specapply SUB_RI_rule. sbazooka.

specapply MOV_M0R_rule. rewrite E0. simpl fst. simpl snd. by sbazooka.

specapply MOV_MR_rule. by ssimpl.

(* Final stuff *)
rewrite <-spec_reads_frame. autorewrite with push_at.
apply limplValid. apply landL2. cancel1.
rewrite /OSZCP/listSeg-/listSeg. rewrite /stateIsAny. sbazooka.
Qed.

Lemma callCons_correct (r1 r2: GPReg32) heapInfo (i j h t e: DWORD) vs :
  |-- callCons_spec r1 r2 heapInfo i j h t e vs (callCons r1 r2 heapInfo).
Proof.

(* First deal with the calling-convention wrapper *)
rewrite /callCons_spec.
autorewrite with push_at.
etransitivity; [|apply toyfun_mkbody]. specintro => iret.

(* Now unfold the control-flow logic *)
rewrite /callCons/basic. specintros => i1 i2 O. unfold_program.
specintros => i3 i4 i5 i6 i7 -> -> i8 -> ->.

specapply inlineCons_correct. by ssimpl.

(* Now we deal with failure and success cases *)
specsplit.

(* failure case *)
autorewrite with push_at.

rewrite /(stateIsAny EDI). specintros => oldedi. 
(* mov EDI, 0 *)
specapply MOV_RI_rule. sbazooka.

rewrite <- spec_reads_frame. apply: limplAdj. apply: landL2.
autorewrite with push_at. simpl OPred_pred. cancel1. ssimpl. apply: lorR1. by rewrite /natAsDWORD.

(* success case *)
autorewrite with push_at.

(* jmp SUCCEED *)
specapply JMP_I_rule. by ssimpl.

(* Final stuff *)
rewrite <-spec_reads_frame.
apply: limplAdj. autorewrite with push_at.
apply: landL2. simpl OPred_pred. rewrite -> empOPL. cancel1.
rewrite /OSZCP/stateIsAny. sbazooka.
apply: lorR2. sbazooka.
*)
Qed.
