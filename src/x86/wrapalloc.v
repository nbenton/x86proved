(*===========================================================================
  Wrapped allocator
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.call x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrrules x86proved.x86.instrcodec x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.inlinealloc
               x86proved.x86.listspec x86proved.x86.listimp x86proved.triple x86proved.x86.macros x86proved.chargetac.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition wrappedAlloc bytes (r1 r2:Reg) heapInfo: program :=
  (LOCAL FAIL;
  LOCAL SUCCEED;
    allocImp heapInfo bytes FAIL;;
    SUB EDI, bytes;;
    JMP SUCCEED;;
  FAIL:;;
    MOV EDI, 0;;
  SUCCEED:;)
  %asm.

Lemma wrappedAlloc_correct bytes (r1 r2: Reg) heapInfo :
  |-- Forall i j: DWORD,
  toyfun i EDI? ((Exists p:DWORD, EDI ~= p ** memAny p (p +# bytes)) \\// EDI ~= #0)

  @  (ESI? ** OSZCP? ** allocInv heapInfo)
  @ (i -- j :-> mkbody_toyfun (wrappedAlloc bytes r1 r2 heapInfo)).
Proof.
specintros => i j.

(* First deal with the calling-convention wrapper *)
rewrite spec_at_toyfun.
etransitivity; [|apply toyfun_mkbody]. specintro => iret.

(* Now unfold the control-flow logic *)
rewrite /wrappedAlloc/basic. specintros => i1 i2. unfold_program.
specintros => i3 i4 i5 i6 i7 i8 -> -> i9 -> ->.

(* Deal with the allocator spec itself *)
have IC := @inlineAlloc_correct bytes.
rewrite /allocSpec in IC. 
eforalls IC. rewrite -> spec_at_impl in IC. rewrite -> spec_at_at in IC. 
safeapply IC; first by ssimpl. 

(* Now we deal with failure and success cases *)
specsplit.

(* failure case *)

(* MOV EDI, 0 *)
safeapply (MOV_RanyI_rule (r:=EDI)); first by ssimpl. 
finish_logic_with sbazooka. apply: lorR2. by rewrite /natAsDWORD.

(* success case *)
(* SUB EDI, bytes *)
specintros => pb.

(* Subtraction arithmetic *)
elim E0:(sbbB false (pb+#bytes) (# bytes)) => [carry0 res0].
assert (H:= subB_equiv_addB_negB (pb+#bytes) # bytes).
rewrite E0 in H. simpl (snd _) in H. rewrite addB_negBn in H.
rewrite H in E0.

safeapply (SUB_RI_rule (r1:=EDI)); first by ssimpl. 

(* JMP SUCCEED *)
safeapply JMP_I_rule; first by ssimpl.
rewrite <- spec_later_weaken. 

(* Final stuff *)
rewrite E0. simpl snd. 
finish_logic_with sbazooka. apply: lorR1. sbazooka. 
Qed.
