(*===========================================================================
  Proof that the linked-list implementation meets its spec
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.safe x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.call x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.inlinealloc
               x86proved.x86.listspec x86proved.x86.listimp x86proved.triple.
Require Import x86proved.x86.macros x86proved.chargetac x86proved.latertac x86proved.basicspectac.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Lemma inlineHead_correct (r1 r2: Reg) (p e: DWORD) v vs :
  inlineHead_spec r1 r2 p e v vs (inlineHead r1 r2).
Proof.
rewrite /inlineHead_spec/inlineHead/listSeg-/listSeg. 
rewrite /stateIsAny.
specintros => q old.
basic apply *. 
Qed.

Lemma inlineTail_correct (r1 r2: Reg) (p e: DWORD) v vs :
  inlineTail_spec r1 r2 p e v vs (inlineTail r1 r2).
Proof.
rewrite /inlineTail_spec/inlineTail/listSeg-/listSeg. 
rewrite /stateIsAny.
specintros => q old. 
basic apply *. 
Qed.

Lemma inlineCons_correct (r1 r2: Reg) heapInfo failAddr (i j h t e: DWORD) vs :
  inlineCons_spec r1 r2 heapInfo failAddr i j h t e vs (inlineCons r1 r2 heapInfo failAddr).
Proof.
rewrite /inlineCons_spec/inlineCons/updateCons. unfold_program.
specintros => i1 i2 i3.

instLem inlineAlloc_correct => H.
rewrite ->spec_at_impl in H. 
rewrite spec_at_impl. 
superspecapply H. clear H.

(* Failure case *)
specsplit.
- finish_logic_with sbazooka. 

(* Success case *)
specintros => pb.
rewrite (memAnySplitAdd pb (m1:=4)) => //.
rewrite -> addB_addn.
do 2 rewrite -> memAny_entails_pointsToDWORD. specintros => d1 d2.

elim E0:(sbbB false (pb+#8) #8) => [carry0 res0].
assert (H:= subB_equiv_addB_negB (pb+#8) #8).
rewrite E0 addB_negBn /snd in H.
rewrite H in E0. replace (pb +#4 +#4) with (pb +#8) by by rewrite -addB_addn.

(* SUB EDI, 8 *)
superspecapply *. 

(* MOV [EDI], r1 *)
rewrite /OSZCP. specapply MOV_M0R_rule. rewrite E0. simpl fst. simpl snd. by ssimpl.
(* MOV [EDI+4], r2 *)
superspecapply MOV_MR_rule.

(* Final stuff *)
rewrite /OSZCP/listSeg-/listSeg /stateIsAny. finish_logic_with sbazooka. 
Qed.

(*
Lemma callCons_correct (r1 r2: Reg) heapInfo (i j h t e: DWORD) vs :
  |-- callCons_spec r1 r2 heapInfo i j h t e vs (callCons r1 r2 heapInfo).
Proof.

(* First deal with the calling-convention wrapper *)
rewrite /callCons_spec.
Check toyfun_mkbody.
autorewrite with push_at.
etransitivity; [|apply toyfun_mkbody]. specintro => iret.

(* Now unfold the control-flow logic *)
rewrite /callCons/basic. specintros => i1 i2. unfold_program.
specintros => i3 i4 i5 i6 i7 -> -> i8 -> ->.

specapply inlineCons_correct. by ssimpl.

(* Now we deal with failure and success cases *)
specsplit.

(* failure case *)
autorewrite with push_at.

unhideReg EDI => olddi.
(* mov EDI, 0 *)
specapply MOV_RI_rule. sbazooka.

rewrite /natAsDWORD. finish_logic_with sbazooka. by apply lorR1. 

(* success case *)
(* jmp SUCCEED *)
specapply JMP_I_rule. by ssimpl.

(* Final stuff *) 
rewrite <- spec_later_weaken.
finish_logic_with sbazooka.
apply: lorR2. sbazooka.
Qed.
*)