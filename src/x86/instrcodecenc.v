(*======================================================================================
  Instruction codec: encoding
  ======================================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsopsprops x86proved.bitsops Ssreflect.eqtype Ssreflect.tuple.
Require Import Coq.Strings.String.
Require Import x86proved.cast x86proved.codec x86proved.bitscodec.
Require Import x86proved.x86.instr x86proved.x86.encdechelp x86proved.x86.addr x86proved.x86.reg.
Require Import x86proved.x86.instrcodec.
Require Import x86proved.writer x86proved.monadinst.
Require Import x86proved.bitreader x86proved.monad x86proved.cursor.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Fixpoint writeBytes (s: seq BYTE) : WriterTm unit :=
  if s is b::rest
  then do! writeNext b; writeBytes rest
  else retn tt.

Instance writeBytesI : Writer (seq BYTE) := writeBytes.

(* NOTE: we don't have a Roundtrip instance for Instr because the
   encoding/decoding don't proceed in lock-step, as required by simrw.
  Instead, we use explicit correctness lemma in programassemcorrect.
*)
Instance encodeInstr : Writer Instr := fun instr =>
  let! pc = getWCursor;
  if pc is mkCursor p then
    if enc InstrCodec instr is Some bs
    then writeNext (fromBin bs).2
    else writerFail
  else writerFail.

Lemma writeBytesSkipFree xs : writerTmSkipFree (writeBytes xs).
Proof. induction xs => //. Qed.

Module Examples.

Require Import instrsyntax. Open Scope instr_scope.

Definition exinstr := MOV ECX, [R9D+EAX*4+1234].

(*Definition exinstr2 := ADD RCX, (BOPArgM _ _ (fromSingletonMemSpec None _ (OffsetMemSpec AdSize4 (#x"12345678":DWORD)))).*)
(*Definition exinstr2 := BOP OpSize8 OP_ADD (DstSrcRM _ AdSize8 R12 (RIPrel _ #x"12345678")). *)
Definition exinstr2 := MOVOP OpSize4 (MovDstSrcRM _ _ ECX (mkMemSpec _ (Some GS) (Some (EDX:BaseReg _)) None #0)).
(*Definition exinstr2 := MOV RDX, (#x"0011223344556677":QWORD).*)

Compute (bytesToHex (snd (fromBin (if enc InstrCodec exinstr2 is Some bs then bs else nil)))).
End Examples.

