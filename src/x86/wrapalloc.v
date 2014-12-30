(*===========================================================================
  Wrapped allocator
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.spectac x86proved.opred x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.call x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrrules x86proved.x86.instrcodec x86proved.reader x86proved.cursor x86proved.x86.inlinealloc
               x86proved.x86.listspec x86proved.x86.listimp x86proved.triple x86proved.x86.macros.
Require Import x86proved.basicspectac x86proved.chargetac. 

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition wrappedAlloc bytes (r1 r2:GPReg64): program :=
  (LOCAL FAIL;
  LOCAL SUCCEED;
    allocImp bytes FAIL;;
    SUB RDI, (# bytes:IMM _);;
    JMP SUCCEED;;
  FAIL:;;
    MOV RDI, (0:QWORD);;
  SUCCEED:;)
  %asm.

Lemma wrappedAlloc_correct bytes (r1 r2: GPReg64) :
  bytes < 2^31 ->
  |-- Forall i j:ADDR,
  toyfun i RDI? empOP ((Exists p:ADDR, RDI ~= p ** memAny p (p +# bytes)) \\// RDI ~= #0)

  @  (RSI? ** OSZCP? ** allocInv)
  <@ (i -- j :-> mkbody_toyfun (wrappedAlloc bytes r1 r2)).
Proof. move => LT.
specintros => i j.

(* First deal with the calling-convention wrapper *)
autorewrite with push_at.
etransitivity; [|apply toyfun_mkbody]. specintro => iret.

(* Now unfold the control-flow logic *)
rewrite /wrappedAlloc/basic. specintros => i1 i2 O. unfold_program.
specintros => i3 i4 i5 i6 i7 i8 -> -> i9 -> ->.

(* Deal with the allocator spec itself *)
specapply inlineAlloc_correct => //; first by ssimpl. 

(* Now we deal with failure and success cases *)
specsplit.
unhideReg RDI => rdi. 

(* MOV RDI, 0 *)
autorewrite with push_at. specapply *; first by ssimpl.

finish_logic_with sbazooka. apply lorR2. cancel1. 

(* success case *)

(* SUB RDI, bytes *)
specintros => pb.

(* Subtraction arithmetic *)
elim E0:(sbbB false (pb+#bytes) (# bytes)) => [carry0 res0].
assert (H:= subB_equiv_addB_negB (pb+#bytes) # bytes).
rewrite E0 in H. simpl (snd _) in H. rewrite addB_negBn in H.
rewrite H in E0.

autorewrite with push_at. specapply *; first by ssimpl. 

(* JMP SUCCEED *)
specapply *; first by ssimpl.

(* Final stuff *)
rewrite /eval.getImm signExtend_fromNat => //.  
rewrite E0. 
finish_logic_with sbazooka. apply: lorR1. simpl snd. sbazooka. 
Qed.
