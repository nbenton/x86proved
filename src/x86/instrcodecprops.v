(*======================================================================================
  Instruction codec correctness
  ======================================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsopsprops x86proved.bitsops Ssreflect.eqtype Ssreflect.tuple.
Require Import Coq.Strings.String.
Require Import x86proved.cast x86proved.codec x86proved.bitscodec.
Require Import x86proved.x86.instr x86proved.x86.encdechelp x86proved.x86.addr x86proved.x86.reg.
Require Import x86proved.x86.instrcodec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import x86proved.codecregex Ssreflect.div.

(* Various facts about the instruction codec that can be determined statically.
   - it's non-ambiguous
   - the maximum number of bits (currently 88)
   - hence, it's finite
   - the number of bits is always divisible by 8
*)



Require Import x86proved.writer x86proved.monadinst.
Require Import x86proved.bitreader x86proved.monad x86proved.cursor.

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

Definition exinstr := LEA ECX, [R9D+EAX*4+1234].

Compute (bytesToHex (snd (fromBin (if enc InstrCodec exinstr is Some bs then bs else nil)))).
End Examples.

(* Qed step takes similar time to actual vm_compute! *)
Lemma InstrCodecIsNonAmbiguous : NonAmbiguous InstrCodec.
Proof. by vm_compute. Qed. 

Lemma InstrCodecMaxBits : maxSize InstrCodec = Some MaxBits.
Proof. by vm_compute. Qed.

Lemma InstrCodecFinite : finiteCodec InstrCodec.
Proof. by rewrite /finiteCodec InstrCodecMaxBits. Qed.

Lemma InstrCodecAlignment : forall l x, interp InstrCodec l x -> 8 %| size l.
Proof. move => l x I.
have byteAligned: all (fun x => 8 %| x) (sizes InstrCodec)
  by vm_compute.
apply: sizesProp I. apply: InstrCodecFinite. apply byteAligned. Qed.

Corollary encInstrAligned : forall l x, enc InstrCodec x = Some l -> 8 %| size l.
Proof. move => l x ENC. apply encSound in ENC. by apply: InstrCodecAlignment ENC. Qed.


Corollary InstrCodecRoundtrip l cursor cursor' e x:
  enc InstrCodec x = Some l ->
  apart (size l) cursor cursor' ->
  runBitReader (codecToBitReader MaxBits InstrCodec) cursor (l++e) = Some(cursor', e, Some x).
Proof. move => ENC AP.
have CC := codecToFiniteBitReaderRoundtrip _ _ InstrCodecMaxBits AP ENC.
have CS := codecToBitReaderSound. apply: CC.
apply nonAmbiguousDet. apply InstrCodecIsNonAmbiguous. Qed.

Require Import x86proved.reader x86proved.x86.addr.
Corollary InstrCodecRoundtripReader (pc:ADDR) (cursor':ADDRCursor) bits x:
  enc InstrCodec x = Some bits ->
  apart ((size bits) %/ 8) (pc:ADDRCursor) cursor' ->
  8 %| size bits /\
  runReader (bitReaderToReader (codecToBitReader MaxBits InstrCodec) nil) pc
    (fromBin bits).2 = Some(cursor',nil,(nil,Some x)).
Proof. move => ENC AP. have CC := InstrCodecRoundtrip nil ENC.
have ALIGN:=encInstrAligned ENC.
case E: (fromBin bits) => [resbits bytes].
have: toBin bytes = bits /\ resbits = nil.
destruct (size_fromBin E) as [E1 E2].
rewrite (eqP ALIGN) in E1.
destruct resbits => //. split => //.
have H := toBinFromBin E. by rewrite cats0 in H. move => [H1 H2]. subst.
have BRR := @bitReaderToReader_correct _ (codecToBitReader MaxBits InstrCodec)
  bytes nil pc (fromByteCursor cursor') (Some x).
case EC: (fromByteCursor pc) => [p |]//. specialize (CC p (fromByteCursor cursor')).
  have AP': apart (size (toBin bytes)) (fromByteCursor pc) (fromByteCursor cursor').
  have AP1 := apart_widen 3 AP. rewrite divnK in AP1. by apply AP1. done.
  rewrite -EC in CC.
specialize (CC AP'). rewrite cats0 in CC. specialize (BRR CC).
  destruct BRR as [resbytes [resbits' [H3 H4]]].
  split => //. simpl snd. destruct resbits' => //. rewrite H3.
  rewrite /bitCursorAndBitsToByteCursor.
  have H: (toBin resbytes) = nil by destruct (toBin resbytes) => //.
  destruct resbytes => //.
  destruct cursor' => //. by rewrite /fromByteCursor/widenCursor high_catB.
  simpl in H. have SR: (size (rev b)) = 8. by rewrite size_rev size_tuple.
  destruct (rev b) => //.
Qed.






