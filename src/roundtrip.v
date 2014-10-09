(*===========================================================================
    Round trip properties for readers and writers
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.choice Ssreflect.fintype Ssreflect.tuple Ssreflect.finfun.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.monad x86proved.reader x86proved.x86.addr x86proved.cursor x86proved.writer Coq.Strings.String x86proved.cstring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* The relation [simrw x p R W] is supposed to mean that reader R simulates
   writer W for the purpose of reading value x from position p.
   Simulating means that they essentially proceed in lock step, except that
   they are allowed to read the cursor position independently of each other.
   If the writer fails, there is no restriction on the reader.
 *)
Inductive simrw {X T} (x: X):
  ADDRCursor -> Reader X -> WriterTm T -> Prop :=
| simrw_retn p t: simrw x p (readerRetn x) (writerRetn t)
| simrw_next p R b W': simrw x (next p) (R b) W' -> simrw x (mkCursor p) (readerNext R) (writerNext b W')
| simrw_skip p R W': simrw x (next p) R W' -> simrw x (mkCursor p) (readerSkip R) (writerSkip W')
| simrw_rcursor p R' W: simrw x p (R' p) W -> simrw x p (readerCursor R') W
| simrw_wcursor p R W': simrw x p R (W' p) -> simrw x p R (writerCursor W')
| simrw_fail p R: simrw x p R writerFail
| simrw_top R b W': simrw x (top _) R (writerNext b W')
| simrw_skiptop R W': simrw x (top _) R (writerSkip W').

(*---------------------------------------------------------------------------
   Put a reader and a writer together with a round-trip property
  ---------------------------------------------------------------------------*)
(*=Roundtrip *)
Class Roundtrip X (R: Reader X) (W: Writer X) :=
  roundtrip: forall x p, simrw x p R (W x).
(*=End *)

(* Generalisation of simrw_next that also handles Cursor *)
Lemma simrw_next' A (x:A) (p:ADDRCursor) R b (W': WriterTm unit):
  (forall p': ADDR, p = mkCursor p' -> simrw x (next p') (R b) W') ->
  simrw x p (readerNext R) (writerNext b W').
Proof.
  intros H. elim Hp: p => [p'|]; last constructor. constructor. exact: H.
Qed.

(* Further generalisation. *)
Lemma simrw_bind A B T (R: Reader T) (W: Writer T) (HRW: Roundtrip R W)
      (x:A) (t:T) (p: ADDRCursor) R' (W': WriterTm B):
  (forall p', simrw x p' (R' t) W') ->
  simrw x p (let! t' = readNext; R' t') (do! writeNext t; W').
Proof.
  intros H. simpl. rewrite /writeNext. specialize (HRW t p).
  induction HRW; try constructor; auto.
Qed.

Lemma simrw_bind_end A T (R: Reader T) (W: Writer T) (HRW: Roundtrip R W)
      (x:A) (t:T) (p: ADDRCursor) R':
  (forall p', simrw x p' (R' t) (retn tt)) ->
  simrw x p (let! t' = readNext; R' t') (writeNext t).
Proof.
  intros H. rewrite <-doRet. exact: simrw_bind.
Qed.

(*---------------------------------------------------------------------------
   BYTE, WORD and DWORD reading and writing
  ---------------------------------------------------------------------------*)
Instance RoundtripBYTE : Roundtrip readBYTE writeBYTE.
Proof. move => x. elim => [p |]; repeat constructor. Qed.

Require Import x86proved.tuplehelp.
Instance RoundtripTupleBYTE m : Roundtrip (readTupleBYTE m) (@writeTupleBYTE m).
Proof.
  induction m => v p.
+ rewrite (tuple0 v)/=. apply simrw_retn.
+ case/tupleP: v => [b bs].
  simpl. apply simrw_next' => p' _.
  rewrite beheadCons theadCons.
  apply simrw_bind_end; first apply IHm.
  move => p''.
  apply simrw_retn.
Qed.

Instance RoundtripSkip : Roundtrip readSkip writeSkipBYTE.
Proof. case. elim => [p |]; repeat constructor. Qed.

Instance RoundtripBITS n : Roundtrip (readBITS n) (writeBITS (n:=n)).
Proof. move => x p. rewrite /readBITS /writeBITS.
  apply simrw_bind. apply RoundtripTupleBYTE. move => p'. 
  rewrite bitsToBytesK. apply simrw_retn. 
Qed. 

Instance RoundtripWORD : Roundtrip readWORD writeWORD := RoundtripBITS (n:=2). 
Instance RoundtripDWORD : Roundtrip readDWORD writeDWORD := RoundtripBITS (n:=4). 
Instance RoundtripQWORD : Roundtrip readQWORD writeQWORD := RoundtripBITS (n:=8).

Instance RoundtripPadWith b m : Roundtrip (readPad m) (writePadWith b m).
Proof.
  induction m => v p; case v.
  apply simrw_retn.
  apply simrw_next' => p' _.
  apply IHm.
Qed.

Instance RoundtripSkipPad m : Roundtrip (readSkipPad m) (writeSkipBy m).
Proof.
  induction m => v p; case v.
  apply simrw_retn.
  simpl.
  destruct p.
  - apply: simrw_skip. apply IHm.
  - constructor.
Qed.

Instance RoundtripPad m : Roundtrip (readPad m) (writePad m).
Proof. apply RoundtripPadWith. Qed.

Instance RoundtripAlignWith b m : Roundtrip (readAlign m) (writeAlignWith b m).
Proof.
rewrite /readAlign/writeAlignWith/Roundtrip.
move => v p. case v.
constructor.
constructor.
destruct p; last exact: simrw_retn.
apply: RoundtripPadWith.
Qed.

Instance RoundtripAlign m : Roundtrip (readAlign m) (writeAlign m).
Proof. apply RoundtripAlignWith. Qed.

Instance RoundtripSkipAlign m : Roundtrip (readSkipAlign m) (writeSkipAlign m).
Proof.
rewrite /readSkipAlign/writeSkipAlign/Roundtrip.
move => v p. case v.
constructor.
constructor.
destruct p; last exact: simrw_retn.
apply: RoundtripSkipPad.
Qed.
