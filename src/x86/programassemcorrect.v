(*===========================================================================
    Assembler for type [program]. Import this and call [assemble_program].
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool seq eqtype tuple.
Require Import tuplehelp bitsrep bitsops mem reg instr instrsyntax cursor update.
Require Import program monad monadinst writer.
Require Import SPred septac pointsto reader roundtrip programassem codec bitreader instrcodec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma runReaderInterp T (R: Reader T) : forall bytes i j (x:T),
  readerTmSkipFree R ->
  runReader R i bytes = Some (j, nil, x) ->
   interpWriterTm (writeBytes bytes) i j tt |-- interpReader R i j x.
Proof. induction R => bytes i j x' SF RR.
- simpl. simpl in RR. injection RR => [-> -> ->]. simpl. sbazooka.
- destruct i => //. destruct bytes => //. simpl. simpl in RR.
  rewrite -> H => //. sbazooka. done.
- done.
- by apply: H.
Qed.

Lemma readerTmSkipFree_bind T U (r: Reader T) (f: T -> Reader U) :
  readerTmSkipFree r ->
  (forall x, readerTmSkipFree (f x)) ->
  readerTmSkipFree (readerBind r f).
Proof. induction r => //=. auto.
auto.
Qed.

Lemma bitReaderToReaderSkipFree t (br: BitReader t) : forall bits,
  readerTmSkipFree (bitReaderToReader br bits).
Proof. induction br => //.
destruct bits => //.
rewrite /bitReaderToReader-/bitReaderToReader. apply readerTmSkipFree_bind.
done. move => x. apply H.
apply H. Qed.

Lemma interpWriter_apart bytes: forall p q,
  interpWriterTm (writeBytes bytes) p q tt -|-
  apart (size bytes) p q /\\ interpWriterTm (writeBytes bytes) p q tt.
Proof. induction bytes => p q.
+ simpl. sbazooka.
+ simpl.
  case Ep: p => [p' |] => //.
  specialize (IHbytes (next p') q).
  rewrite IHbytes. sbazooka. sbazooka.
Qed.

Theorem write_instr_correct (i j: DWORD) (instr: Instr) :
  interpWriter i j instr |-- i -- j :-> instr.
Proof.
  rewrite /interpWriter/encodeInstr.
  rewrite interpWriterTm_bind.
  sdestructs => p p'.
  rewrite interpWriterTm_getWCursor.
  sdestructs => H1 H2. rewrite -H2 -H1 {H1 H2 p p'}. ssimpl.
  case E: (enc InstrCodec instr) => [bs |].
  case E2: (fromBin bs) => [resbits bytes]. simpl snd.
  rewrite /writeNext/writeBytesI.
  rewrite -> interpWriter_apart.  sdestruct => AP.
  have ICRR := InstrCodecRoundtripReader (pc:=i) E.
  specialize (ICRR j).
  destruct (size_fromBin E2) as [SZ1 SZ2].
  rewrite -SZ2 in ICRR.
  have EA:= encInstrAligned E.
  specialize (ICRR AP).
  destruct ICRR as [resbytes H].
  rewrite E2 /snd in H.
  rewrite /memIs/readerMemIs.
  rewrite /reader.readNext.
  rewrite /readInstr.
  rewrite interpReader_bind.
  apply lexistsR with i. apply lexistsR with i.
  simpl (interpReader readCursor). ssimpl. ssplit => //. ssplit => //. ssimpl.
  rewrite interpReader_bind.
  apply lexistsR with j. apply lexistsR with (Some instr).
  rewrite interpReader_retn. ssplit => //. ssplit => //. ssimpl.
  rewrite /readOptionInstr. rewrite interpReader_bind.
  apply lexistsR with j. apply lexistsR with (nil, Some instr).
  rewrite interpReader_retn. ssplit => //. ssplit => //. ssimpl.
  apply: runReaderInterp H. apply bitReaderToReaderSkipFree.
  rewrite  interpWriterTm_writerFail.  sbazooka.
Qed.


Lemma finalpass_correct p st (pos pos': DWORD) arg:
  interpWriterTm (finalpass p st) pos pos' arg |-- pos -- pos' :-> p.
Proof.
  move: st pos pos' arg.
  induction p => st pos pos' arg.
  (* prog_instr *)
    rewrite /finalpass/assemblerLift/SMT_lift.
    rewrite interpWriterTm_bind.
    sdestructs => p' [].
    rewrite interpWriterTm_retn. sdestructs => H1 H2. ssimpl.
    have WIC:= @write_instr_correct pos pos' c. rewrite /interpWriter in WIC.
    rewrite /writeNext. rewrite -{1}H2 in WIC. apply: WIC.
  (* prog_skip *)
    simpl. sdestructs => _ H. sbazooka. congruence.
  (* prog_seq *)
    rewrite /finalpass-/finalpass.
    rewrite interpWriterTm_bind. sdestructs => p' [st' []].
    case: p' => [p'|]; last first.
    - rewrite ->interpWriterTm_top. by ssimpl.
    unfold_program.
    ssplit. by cancel2.
  (* prog_declabel *)
    rewrite /finalpass-/finalpass SMT_bindGet.
    destruct st as [[labels m] errors].
    destruct labels; first exact: lfalseL.
    rewrite SMT_doSet. unfold_program.
    ssplit. by apply H.
  (* prog_label *)
    simpl.
    case Hl: (pos == l); last exact: lfalseL.
    move/eqP: Hl => [<-].
    rewrite /memIs /seqMemIs /interpProgram /=.
    by sbazooka; congruence.
  (* prog_data *)
    rewrite /finalpass. rewrite /assemblerLift /SMT_lift.
    apply interpWriterTm_roundtrip.
    rewrite <-(id_r _ _). rewrite doLet.
    apply: simrw_bind. constructor.
Qed.

(*=write_program_correct *)
Theorem write_program_correct (i j: DWORD) (p: program) :
  interpWriter i j p |-- i -- j :-> p.
(*=End *)
Proof.
  rewrite /interpWriter/write_program.
  rewrite interpWriterTm_bind. sdestructs => i' j'.
  simpl (interpWriterTm getWCursor _ _ _).
  sdestructs => -> ->. ssimpl.
  rewrite /runAssembler.
  case: (runNPasses _ _ _) => [[[npasses labels] bytes] |].
  rewrite interpWriterTm_bind. sdestructs => p' s. simpl.
  sdestructs => _ ->.
  case: i' => [i'' |].
    rewrite -> finalpass_correct. simpl. by ssimpl.
  rewrite interpWriterTm_top.  sbazooka.
  by simpl.
Qed.

(* When applying this lemma, discharge the side condition with [by vm_compute].
 *)
Theorem assemble_correct (offset endpos: DWORD) p:
  assemble_success offset p ->
  offset -- endpos :-> assemble offset p |-- offset -- endpos :-> p.
Proof.
  rewrite /assemble_success /assemble.
  case Hcode: (runWriter true write_program offset p) => [code|]; last done.
  move=> _. setoid_rewrite ->runWriter_interpWriter; last eassumption.
  exact: write_program_correct.
Qed.




