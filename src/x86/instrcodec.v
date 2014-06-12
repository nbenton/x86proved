(*======================================================================================
  Instruction codec
  ======================================================================================*)
Require Import ssreflect ssrfun seq ssrbool ssrnat fintype.
Add LoadPath "..".
Require Import bitsrep bitsprops bitsops eqtype tuple.
Require Import Coq.Strings.String.
Require Import cast codec bitscodec.
Require Import instr encdechelp reg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Casts for datatypes used in instructions
  ---------------------------------------------------------------------------*)
Definition unSrcR : CAST Reg Src.
apply: MakeCast SrcR (fun s => if s is SrcR r then Some r else None) _.
by elim; congruence. Defined.

Definition unSrcI : CAST DWORD Src.
apply: MakeCast SrcI (fun s => if s is SrcI i then Some i else None) _.
by elim; congruence. Defined.

Definition unRegMemR d : CAST (DWORDorBYTEReg d) (RegMem d).
apply: MakeCast (RegMemR d) (fun rm => if rm is RegMemR r then Some r else None) _.
by elim; congruence. Defined.

Definition unShiftCountCL : CAST unit ShiftCount.
apply: MakeCast (fun _=>ShiftCountCL) (fun c => if c is ShiftCountCL then Some tt else None) _.
elim; congruence.
Defined.

Definition unShiftCountI : CAST BYTE ShiftCount.
apply: MakeCast ShiftCountI (fun c => if c is ShiftCountI b then Some b else None) _.
elim; congruence.
Defined.

Definition unJmpTgtI : CAST Tgt JmpTgt.
apply: MakeCast JmpTgtI (fun t => if t is JmpTgtI d then Some d else None) _.
elim; elim; congruence. Defined.

Definition unJmpTgtRM : CAST (RegMem true) JmpTgt.
apply: (MakeCast (fun (rm:RegMem true) => match rm with RegMemR r => JmpTgtR r | RegMemM m => JmpTgtM m end)
  (fun i => match i with JmpTgtR r => Some (RegMemR true r) | JmpTgtM m => Some (RegMemM true m) | _ => None end) _).
elim => //. move => m. elim => // ms. by move => [<-].
by move => r y [<-].
Defined.

Require Import bitsopsprops.
Definition unTgt : CAST DWORD Tgt.
apply: MakeCast mkTgt
                (fun t => let: mkTgt d := t in Some d) _.
by move => [d] y [<-].
Defined.

Definition unSrcRM : CAST (RegMem true) Src.
apply: MakeCast
  (fun (rm: RegMem true) => match rm with RegMemR r => SrcR r | RegMemM m => SrcM m end)
  (fun i => match i with SrcR r => Some (RegMemR true r) | SrcM m => Some (RegMemM _ m)
                       | _ => None
            end) _.
elim => //; by move => ? ? [<-]. Defined.

(*---------------------------------------------------------------------------
    Casts and codecs for bit-encoded types e.g. registers, scales, conditions
  ---------------------------------------------------------------------------*)
Definition regCast : CAST (BITS 3) Reg.
apply: MakeCast (fun x => decReg x) (fun x => Some (encReg x)) _.
move => x y [<-]; by rewrite encRegK. Defined.
Definition regCodec   : Codec Reg   := bitsCodec 3 ~~> regCast.

Definition opCast : CAST (BITS 3) BinOp.
apply: MakeCast (fun x => decBinOp x) (fun x => Some (encBinOp x)) _.
move => x y [<-]; by rewrite encBinOpK. Defined.
Definition opCodec    : Codec BinOp   := bitsCodec 3 ~~> opCast.

Definition shiftOpCast : CAST (BITS 3) ShiftOp.
apply: MakeCast (fun x => decShiftOp x) (fun x => Some (encShiftOp x)) _.
move => x y [<-]; by rewrite encShiftOpK. Defined.
Definition shiftOpCodec : Codec ShiftOp   := bitsCodec 3 ~~> shiftOpCast.

Definition bitOpCast : CAST (BITS 2) BitOp.
apply: MakeCast (fun x => decBitOp x) (fun x => Some (encBitOp x)) _.
move => x y [<-]; by rewrite encBitOpK. Defined.
Definition bitOpCodec : Codec BitOp   := bitsCodec 2 ~~> bitOpCast.

Definition optionalNonSPregCast : CAST (BITS 3) (option NonSPReg).
apply: MakeCast (fun (x: BITS 3) => decNonSPReg x) (fun x =>
  if x is Some r then Some (encNonSPReg r) else Some #b"100") _.
elim => //.
+ move => x y [<-]. by rewrite encNonSPRegK.
+ by move => y [<-]. Defined.
Definition optionalNonSPRegCodec : Codec (option NonSPReg) :=
  bitsCodec 3 ~~> optionalNonSPregCast.

Definition nonSPregCast : CAST (BITS 3) NonSPReg.
apply: MakeCast (fun x => if decNonSPReg x is Some y then y else EAX)
                (fun y => Some (encNonSPReg y)) _.
move => x y [<-]. by rewrite encNonSPRegK. Defined.

Definition nonBPnonSPRegCodec : Codec NonSPReg :=
    #b"000" .$ always EAX
||| #b"001" .$ always ECX
||| #b"010" .$ always EDX
||| #b"011" .$ always EBX
||| #b"110" .$ always ESI
||| #b"111" .$ always EDI.

Definition nonSPRegCodec : Codec NonSPReg :=
    nonBPnonSPRegCodec
||| #b"101" .$ always EBP.

Definition byteRegCast : CAST (BITS 3) BYTEReg.
apply: MakeCast (fun x => decBYTEReg x) (fun x => Some (encBYTEReg x)) _.
move => x y [<-]; by rewrite encBYTERegK. Defined.
Definition byteRegCodec : Codec BYTEReg := bitsCodec 3 ~~> byteRegCast.

Definition dwordorbyteRegCodec dword : Codec (DWORDorBYTEReg dword) :=
  if dword as dword return Codec (DWORDorBYTEReg dword)
  then regCodec
  else byteRegCodec.

Definition scaleCast : CAST (BITS 2) Scale.
apply: MakeCast decScale (fun x => Some (encScale x)) _.
move => x y [<-]; by rewrite encScaleK. Defined.
Definition scaleCodec : Codec Scale := bitsCodec 2 ~~> scaleCast.

Definition conditionCast : CAST (BITS 3) Condition.
apply: MakeCast decCondition (fun x => Some (encCondition x)) _.
move => x y [<-]; by rewrite encConditionK. Defined.
Definition conditionCodec : Codec Condition := bitsCodec 3 ~~> conditionCast.

Hint Rewrite domConstSeq domSeq domCast domAlt domEmp domSym domAny : dom.

Lemma totalScale : total scaleCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalReg : total regCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totaloptionalNonSPReg : total optionalNonSPRegCodec. Proof. apply totalCast => //.
apply totalBITS. case => //. Qed.
Lemma totalOp : total opCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalShiftOp : total shiftOpCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalbyteReg : total byteRegCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totaldwordorbyteReg d : total (dwordorbyteRegCodec d).
Proof. destruct d. apply totalReg. apply totalbyteReg. Qed.

Definition SIB := (Reg * option (NonSPReg * Scale))%type.

Definition SIBCast : CAST (Scale * option NonSPReg * Reg) SIB.
apply: MakeCast (fun p => let: (sc,o,r) := p
                 in (r, if o is Some ix then Some(ix,sc) else None))
                (fun p => let: (base, o) := p
                 in if o is Some(ix,sc) then Some(sc, Some ix, base)
                                        else Some(S1, None, base)) _.
move => [r' o'] [[sc o] r].
case: o' => //.
+ by move => [? ?] [-> <- ->].
+ by move => [<- <- <-].
Defined.

Definition SIBCodec : Codec SIB := scaleCodec $ optionalNonSPRegCodec $ regCodec ~~> SIBCast.

Lemma totalSIB : total SIBCodec.
Proof. rewrite /SIBCodec. apply totalCast. apply totalSeq. apply totalSeq.
apply totalScale. apply totaloptionalNonSPReg. apply totalReg.
rewrite /castIsTotal.  move => [r o]. destruct o => //. by destruct p.
Qed.

Definition dispOffsetSIBCast dword : CAST (SIB * DWORD) (RegMem dword).
apply: MakeCast (fun p => RegMemM dword (mkMemSpec (Some p.1) p.2))
  (fun rm => if rm is RegMemM (mkMemSpec (Some sib) offset) then Some(sib,offset) else None) _.
elim => //. elim => //. elim => //. move => [x y] z [x' y']. by move => [-> ->]. Defined.

Definition dispOffsetCast dword : CAST (NonSPReg * DWORD) (RegMem dword).
apply: (MakeCast (fun p => RegMemM dword (mkMemSpec (Some (nonSPReg p.1,None)) p.2))
  (fun rm => if rm is RegMemM (mkMemSpec (Some (nonSPReg base,None)) offset) then Some(base,offset) else None) _).
elim => //. elim => //. elim => //. move => [x y] z [x' y'].
case: x => // r. case: y => //. by move => [-> ->]. Defined.

Definition dispOffsetNoBaseCast dword : CAST DWORD (RegMem dword).
apply: MakeCast (fun offset => RegMemM dword (mkMemSpec None offset))
                (fun rm => if rm is RegMemM (mkMemSpec None offset)
                           then Some offset else None) _.
elim => //. elim => //. by elim => // ? ? [->]. Defined.

Definition RegMemCodec T (regOrOpcodeCodec : Codec T) dword : Codec (T * RegMem dword) :=
    #b"00" .$ regOrOpcodeCodec $ SIBRM .$ (SIBCodec $ always #0 ~~> dispOffsetSIBCast dword)
||| #b"00" .$ regOrOpcodeCodec $ (nonBPnonSPRegCodec $ always #0 ~~> dispOffsetCast dword)
||| #b"00" .$ regOrOpcodeCodec $ (#b"101" .$ DWORDCodec ~~> dispOffsetNoBaseCast dword)
||| #b"01" .$ regOrOpcodeCodec $ SIBRM .$ (SIBCodec $ shortDWORDCodec ~~> dispOffsetSIBCast dword)
||| #b"01" .$ regOrOpcodeCodec $ (nonSPRegCodec $ shortDWORDCodec ~~> dispOffsetCast dword)
||| #b"10" .$ regOrOpcodeCodec $ (SIBRM .$ SIBCodec $ DWORDCodec ~~> dispOffsetSIBCast dword)
||| #b"10" .$ regOrOpcodeCodec $ (nonSPRegCodec $ DWORDCodec ~~> dispOffsetCast dword)
||| #b"11" .$ regOrOpcodeCodec $ (dwordorbyteRegCodec dword ~~> unRegMemR dword).

(*
Lemma totalRegMemCodec T (c: Codec T) d : total c -> total (RegMemCodec c d).
Proof. move => tc. rewrite /total/RegMemCodec.
autorewrite with dom.
move => [x rm].
destruct rm.
(* Register *)
simpl. by rewrite totaldwordorbyteReg tc.
(* MemSpec *)
destruct ms.
case sib => [[base optix] |].
(* Has a SIB *)
+ case: optix => [[index sc] |].
  - simpl.
    rewrite /SIBCodec.
    case E: (offset == #0). rewrite (eqP E)/=. rewrite tc/=.
    destruct base; autorewrite with dom; simpl;
      by rewrite totalScale totaloptionalNonSPReg totalReg/=.
    destruct base; autorewrite with dom; simpl.
      rewrite totalScale totaloptionalNonSPReg totalDWORD totalReg tc /=.
      by rewrite !orbT !orbF.
    rewrite totalScale totaloptionalNonSPReg totalReg totalDWORD tc/=.
      by rewrite !orbT !orbF.
simpl.
simpl. rewrite totalDWORD/=. rewrite /SIBCodec.
autorewrite with dom. simpl.
case E: (offset == #0). simpl. by rewrite tc totalReg.
rewrite tc totalReg. simpl. by rewrite !orbT !orbF.
case E: (offset == #0). simpl. by rewrite tc totalDWORD.
(* Has no SIB  *)
by rewrite /= tc totalDWORD.
Qed.
*)

Definition RegMemOpCodec (op: BITS 3) dword :=
  RegMemCodec (Const op) dword ~~> sndUnitCast _.

Definition RegMemOpDepCodec (op: BITS 3) :=
  BoolDep (fun d => RegMemCodec (Const op) d ~~> sndUnitCast _).

Definition unDstSrcRMR d : CAST (DWORDorBYTEReg d * RegMem d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR d p.1 y
                              | RegMemM y => DstSrcRM d p.1 y end)
       (fun ds => match ds with DstSrcRR x y => Some (x,RegMemR _ y)
                              | DstSrcRM x y => Some (x,RegMemM _ y)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRR d : CAST (DWORDorBYTEReg d * RegMem d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR d y p.1
                              | RegMemM y => DstSrcMR d y p.1 end)
       (fun ds => match ds with DstSrcRR x y => Some (y, RegMemR _ x)
                              | DstSrcMR x y => Some (y, RegMemM _ x)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRI d : CAST (RegMem d * DWORDorBYTE d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.1 with RegMemR y => (DstSrcRI d y p.2)
                             | RegMemM y => (DstSrcMI d y p.2) end)
       (fun ds => match ds with DstSrcRI x y => Some (RegMemR _ x, y)
                              | DstSrcMI x y => Some (RegMemM _ x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. by move => ? ? [<- ->]. Defined.

(*---------------------------------------------------------------------------
    Casts for instructions
  ---------------------------------------------------------------------------*)
Definition unPUSH : CAST Src Instr.
apply: MakeCast PUSH (fun i => if i is PUSH s then Some s else None) _.
by elim; congruence. Defined.

Definition unINCD : CAST (RegMem true) Instr.
apply: MakeCast (UOP true OP_INC)
                (fun i => if i is UOP true OP_INC rm then Some rm else None) _.
elim => //. elim => //. elim => //. by move => ? ? [->]. Defined.

Definition unDECD : CAST (RegMem true) Instr.
apply: MakeCast (UOP true OP_DEC)
                (fun i => if i is UOP true OP_DEC rm then Some rm else None) _.
elim => //. elim => //. elim => //. by move => ? ? [->]. Defined.

Definition unPOP : CAST (RegMem true) Instr.
apply: MakeCast POP (fun i => if i is POP d then Some d else None) _.
elim => //. by move => d rm [->]. Defined.

Definition unINC : CAST {d:bool & RegMem d} Instr.
apply: (MakeCast (fun (p:{d:bool & RegMem d}) => let: existT d v := p in UOP d OP_INC v)
                 (fun i => if i is UOP d OP_INC v then Some (existT _ d v) else None) _).
elim => //. elim => op src [y z]; destruct op => // [H]; by inversion H. Defined.

Definition unDEC : CAST {d:bool & RegMem d} Instr.
apply: (MakeCast (fun (p:{d:bool & RegMem d}) => let: existT d v := p in UOP d OP_DEC v)
                 (fun i => if i is UOP d OP_DEC v then Some (existT _ d v) else None) _).
elim => //. elim => op src [y z]; destruct op => // [H]; by inversion H. Defined.

Definition unNOT : CAST {d:bool & RegMem d} Instr.
apply: (MakeCast (fun (p:{d:bool & RegMem d}) => let: existT d v := p in UOP d OP_NOT v)
                 (fun i => if i is UOP d OP_NOT v then Some (existT _ d v) else None) _).
elim => //. elim => op src [y z]; destruct op => // [H]; by inversion H. Defined.

Definition unNEG : CAST {d:bool & RegMem d} Instr.
apply: (MakeCast (fun (p:{d:bool & RegMem d}) => let: existT d v := p in UOP d OP_NEG v)
                 (fun i => if i is UOP d OP_NEG v then Some (existT _ d v) else None) _).
elim => //. elim => op src [y z]; destruct op => // [H]; by inversion H. Defined.

Definition unIMUL : CAST (Reg * RegMem true) Instr.
apply: (MakeCast (fun p => IMUL p.1 p.2)
                 (fun i => if i is IMUL dst src then Some (dst,src) else None) _).
elim => //. by move => dst src [dst' src'] [<-] ->.  Defined.

Definition unIN : CAST (bool*BYTE) Instr.
apply: MakeCast (fun p => IN p.1 p.2) (fun i => if i is IN d p then Some(d,p) else None) _.
by elim => // ? ? [? ?] [-> ->]. Defined.

Definition unOUT : CAST (bool*BYTE) Instr.
apply: MakeCast (fun p => OUT p.1 p.2) (fun i => if i is OUT d p then Some(d,p) else None) _.
by elim => // ? ?  [? ?] [-> ->]. Defined.

Definition unLEA : CAST (Reg * RegMem true) Instr.
apply: MakeCast (fun p => LEA p.1 p.2) (fun i => if i is LEA x y then Some(x,y) else None) _.
by elim => // ? ? [? ?] [-> ->]. Defined.

Definition unXCHG : CAST (DWORDorBYTEReg true * RegMem true) Instr.
apply: MakeCast (fun p => XCHG true p.1 p.2) (fun i => if i is XCHG true x y then Some(x,y) else None) _.
elim => //. elim => //. by move => r s [r' s'] [<-] ->. Defined.

Definition unXCHGB : CAST (DWORDorBYTEReg false * RegMem false) Instr.
apply: MakeCast (fun p => XCHG false p.1 p.2) (fun i => if i is XCHG false x y then Some(x,y) else None) _.
elim => //. elim => //. by move => r s [r' s'] [<-] ->. Defined.

Definition unMUL : CAST {d:bool & RegMem d} Instr.
apply: (MakeCast (fun (p:{d:bool & RegMem d}) => let: existT d v := p in MUL v)
                 (fun i => if i is MUL d v then Some (existT _ d v) else None) _).
elim => //. elim => src [y z] [H] H'; by inversion H'.
Defined.

Definition unRET : CAST WORD Instr.
apply: MakeCast RETOP (fun i => if i is RETOP w then Some w else None) _.
elim; congruence. Defined.

Definition unJMP : CAST JmpTgt Instr.
apply: MakeCast JMPrel (fun i => if i is JMPrel t then Some t else None) _.
elim; congruence. Defined.

Definition unCALL : CAST JmpTgt Instr.
apply: MakeCast CALLrel (fun i => if i is CALLrel t then Some t else None) _.
elim; congruence. Defined.

Definition isCMC : CAST unit Instr.
apply: MakeCast (fun _ => CMC) (fun i => if i is CMC then Some tt else None) _; by elim; elim.
Defined.

Definition isCLC : CAST unit Instr.
apply: MakeCast (fun _ => CLC) (fun i => if i is CLC then Some tt else None) _; by elim; elim.
Defined.

Definition isSTC : CAST unit Instr.
apply: MakeCast (fun _ => STC) (fun i => if i is STC then Some tt else None) _; by elim; elim.
Defined.

Definition isHLT : CAST unit Instr.
apply: MakeCast (fun _ => HLT) (fun i => if i is HLT then Some tt else None) _; by elim; elim.
Defined.

Definition unBOP : CAST (BinOp * {d:bool & DstSrc d}) Instr.
apply: (MakeCast (fun (p:BinOp * {d:bool & DstSrc d}) => let: existT d v := p.2 in BOP d p.1 v)
                 (fun i => if i is BOP d op v then Some (op, existT _ d v) else None) _).
elim => //. elim => op src [op' [y z]] [->] H' H; by inversion H. Defined.

Require Import Coq.Program.Equality.
Definition unBOPMRI : CAST ({d:bool & (BinOp * RegMem d * DWORDorBYTE d)%type}) Instr.
apply: (MakeCast (fun (p:{d:bool & (BinOp * RegMem d * DWORDorBYTE d)%type}) =>
  let: existT d (op,rm,c) := p in
    match rm with RegMemR y => BOP d op (DstSrcRI d y c)
                | RegMemM y => BOP d op (DstSrcMI d y c) end)
                 (fun i =>
                  match i with BOP d op (DstSrcRI y c) => Some (existT _ d (op,RegMemR _ y,c))
                             | BOP d op (DstSrcMI y c) => Some (existT _ d (op,RegMemM _ y,c))
                             | _ => None end) _).
elim => //.
move => d.
move => op.
elim => //.
+ move => dst c [d' [[op' rm] c']]. move => [H1 H2 H3 H4]. subst.
by dependent destruction H4.
+ move => dst c [d' [[op' rm] c']]. move => [H1 H2 H3 H4]. subst.
by dependent destruction H4.
Defined.

Definition BOPCodecRMR : Codec {d: bool & DstSrc d} :=
  BoolDep (fun d =>
    RegMemCodec (dwordorbyteRegCodec d) d ~~> unDstSrcRMR d).
Definition BOPCodecMRR : Codec {d: bool & DstSrc d} :=
  BoolDep (fun d =>
    RegMemCodec (dwordorbyteRegCodec d) d ~~> unDstSrcMRR d).

Definition MOVCodecMRI : Codec {d: bool & DstSrc d} :=
  BoolDep (fun d =>
    RegMemOpCodec #0 d $ DWORDorBYTECodec d ~~> unDstSrcMRI d).

Definition BOPCodecMRI : Codec Instr :=
  BoolDep (fun d =>
    RegMemCodec opCodec d $ DWORDorBYTECodec d) ~~> unBOPMRI.

Definition unMOVZX : CAST (Reg * RegMem true) Instr.
apply: MakeCast (fun p => MOVX false true p.1 p.2) (fun i => if i is MOVX false true x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition unMOVZXB : CAST (Reg * RegMem false) Instr.
apply: MakeCast (fun p => MOVX false false p.1 p.2) (fun i => if i is MOVX false false x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition unMOVSX : CAST (Reg * RegMem true) Instr.
apply: MakeCast (fun p => MOVX true true p.1 p.2) (fun i => if i is MOVX true true x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition unMOVSXB : CAST (Reg * RegMem false) Instr.
apply: MakeCast (fun p => MOVX true false p.1 p.2) (fun i => if i is MOVX true false x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition unMOV : CAST ({d:bool & DstSrc d}) Instr.
apply: (MakeCast (fun (p:{d:bool & DstSrc d}) => let: existT d v := p in MOVOP d v)
                 (fun i => if i is MOVOP d v then Some (existT _ d v) else None) _).
elim => // d ds [y z] H. by inversion H. Defined.

Definition unMOVRI : CAST (Reg*DWORD) Instr.
apply: (MakeCast
  (fun p => MOVOP true (DstSrcRI _ p.1 p.2)) (fun i => if i is MOVOP true (DstSrcRI r d) then Some (r,d) else None) _).
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->].
Defined.

Definition unSHIFT : CAST ({d:bool & (ShiftOp * RegMem d)%type} * ShiftCount) Instr.
apply: (MakeCast (fun (p:{d:bool & (ShiftOp * RegMem d)%type} * ShiftCount) =>
                  let: (existT d (op, v), count) := p in SHIFTOP d op v count)
                 (fun i => if i is SHIFTOP d op v count then Some (existT _ d (op,v), count) else None) _).
elim => //. move => d op dst count [c count']. move => [H1 H2]. by subst.
Defined.

Definition unJCC : CAST (Condition*bool*Tgt) Instr.
apply: MakeCast (fun p => let: (c,d,t) := p in JCCrel c (negb d) t)
                (fun i => if i is JCCrel c d t then Some(c,negb d,t) else None) _.
Proof. elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
by rewrite negbK. Defined.

Definition TgtCodec : Codec Tgt := DWORDCodec ~~> unTgt.
Definition ShortTgtCodec : Codec Tgt := shortDWORDCodec ~~> unTgt.

Definition unTESTOP : CAST (Reg * RegMem true) Instr.
apply: (MakeCast (fun p => TESTOP true p.2 (RegImmR true p.1))
                (fun i => if i is TESTOP true y (RegImmR x) then Some(x,y) else None) _).
elim => //. elim => //. move => dst src [dst' src']. case src => // r. by move => [-> ->].
Defined.

Definition unTESTOPB : CAST (BYTEReg * RegMem false) Instr.
apply: (MakeCast (fun p => TESTOP false p.2 (RegImmR false p.1))
                (fun i => if i is TESTOP false y (RegImmR x) then Some(x,y) else None) _).
elim => //. elim => //. move => dst src [dst' src']. case src => // r. by move => [-> ->].
Defined.

Definition unTESTOPI : CAST (RegMem true * DWORD) Instr.
apply: (MakeCast (fun p => TESTOP true p.1 (RegImmI true p.2))
                (fun i => if i is TESTOP true x (RegImmI d) then Some(x,d) else None) _).
elim => //. elim => //. move => dst src [dst' src']. case src => // r. by move => [-> ->].
Defined.

Definition unTESTOPBI : CAST (RegMem false * BYTE) Instr.
apply: (MakeCast (fun p => TESTOP false p.1 (RegImmI false p.2))
                (fun i => if i is TESTOP false x (RegImmI d) then Some(x,d) else None) _).
elim => //. elim => //. move => dst src [dst' src']. case src => // r. by move => [-> ->].
Defined.

Definition unBITOPR : CAST (BitOp * (Reg * RegMem true)) Instr.
apply: (MakeCast (fun p => let: (op,(r,rm)) := p in BITOP op rm (inl r))
                (fun i => if i is BITOP op y (inl r) then Some(op,(r,y)) else None) _).
elim => //. move => op dst src [op' [dst' src']]. case src => // r. by move => [-> -> ->].
Defined.

Definition unBITOPI : CAST (BitOp * RegMem true * BYTE) Instr.
apply: (MakeCast (fun p => let: (op,rm,b) := p in BITOP op rm (inr b))
                (fun i => if i is BITOP op y (inr b) then Some(op,y,b) else None) _).
elim => //. move => op dst src [[op' dst'] src']. case src => // r. by move => [-> -> ->].
Defined.

Definition unEAXimm : CAST (DWORDorBYTE true) (DstSrc true).
apply: (MakeCast
       (fun c => DstSrcRI true EAX c)
       (fun ds => if ds is DstSrcRI EAX y then Some y else None) _).
elim => //. elim => //. elim => //. by move => c y [->]. Defined.

Definition unALimm : CAST (DWORDorBYTE false) (DstSrc false).
apply: (MakeCast
       (fun c => DstSrcRI false AL c)
       (fun ds => if ds is DstSrcRI AL y then Some y else None) _).
elim => //. elim => //. by move => c y [->].
Defined.

Definition EAXimmCodec : Codec {d: bool & DstSrc d} :=
  BoolDep (fun d => DWORDorBYTECodec d ~~> if d then unEAXimm else unALimm).

Definition unBOPMRId : CAST (BinOp * RegMem true * DWORD) Instr.
apply: (MakeCast (fun (p:BinOp * RegMem true * DWORD) =>
  let: (op,rm,c) := p in
    match rm with RegMemR y => BOP true op (DstSrcRI true y c)
                | RegMemM y => BOP true op (DstSrcMI true y c) end)
                 (fun i =>
                  match i with BOP true op (DstSrcRI y c) => Some (op,RegMemR _ y,c)
                             | BOP true op (DstSrcMI y c) => Some (op,RegMemM _ y,c)
                             | _ => None end) _).
elim => //.
elim => //.
move => op.
elim => //.
+ move => dst c [[op' rm] c']. move => [H2 H3 H4]. by subst.
+ move => dst c [[op' rm] c']. move => [H2 H3 H4]. by subst.
Defined.


Definition InstrCodec : Codec Instr :=
(* Unary operations *)
    droplsb #x"FE" .$ RegMemOpDepCodec #0 ~~> unINC
||| droplsb #x"FE" .$ RegMemOpDepCodec #1 ~~> unDEC
||| droplsb #x"F6" .$ RegMemOpDepCodec #2 ~~> unNOT
||| droplsb #x"F6" .$ RegMemOpDepCodec #3 ~~> unNEG
||| INCPREF .$ regCodec ~~> unRegMemR true ~~> unINCD
||| DECPREF .$ regCodec ~~> unRegMemR true ~~> unDECD
(* Binary operations *)
||| #b"00" .$ opCodec $ #b"10" .$ EAXimmCodec ~~> unBOP
||| #b"00" .$ opCodec $ #b"00" .$ BOPCodecMRR ~~> unBOP
||| #b"00" .$ opCodec $ #b"01" .$ BOPCodecRMR ~~> unBOP
||| droplsb #x"80" .$ BOPCodecMRI
||| #x"83" .$ RegMemCodec opCodec true $ shortDWORDCodec ~~> unBOPMRId
(* MOV operationsl *)
||| droplsb #x"8A" .$ BOPCodecRMR ~~> unMOV
||| droplsb #x"88" .$ BOPCodecMRR ~~> unMOV
||| MOVIMMPREF .$ regCodec $ DWORDCodec ~~> unMOVRI
||| droplsb #x"C6" .$ MOVCodecMRI ~~> unMOV
(* IMUL and MUL *)
||| #x"0F" .$ #x"AF" .$ RegMemCodec regCodec _ ~~> unIMUL
||| droplsb #x"F6" .$ RegMemOpDepCodec #4 ~~> unMUL
(* IN and OUT *)
||| droplsb #x"E4" .$ Any $ BYTECodec ~~> unIN
||| droplsb #x"E6" .$ Any $ BYTECodec ~~> unOUT
(* LEA *)
||| #x"8D" .$ RegMemCodec regCodec _ ~~> unLEA
(* XCHG *)
||| #b"10010" .$ always (EAX:Reg) $ (regCodec ~~> unRegMemR true) ~~> unXCHG
||| #x"86" .$ RegMemCodec byteRegCodec _ ~~> unXCHGB
||| #x"87" .$ RegMemCodec regCodec _ ~~> unXCHG
(* PUSH *)
||| #x"68" .$ DWORDCodec ~~> unSrcI ~~> unPUSH
||| #x"6A" .$ shortDWORDCodec ~~> unSrcI ~~> unPUSH
||| #b"01010" .$ regCodec ~~> unSrcR ~~> unPUSH
||| #x"FF" .$ RegMemOpCodec #6 _ ~~> unSrcRM ~~> unPUSH
(* POP *)
||| #x"8F" .$ RegMemOpCodec #0 _ ~~> unPOP
||| #b"01011" .$ regCodec ~~> unRegMemR true ~~> unPOP
(* RET *)
||| #x"C3" .$ always #0 ~~> unRET
||| #x"C2" .$ WORDCodec ~~> unRET
(* Nullary operations *)
||| #x"F4" ~~> isHLT
||| #x"F5" ~~> isCMC
||| #x"F8" ~~> isCLC
||| #x"F9" ~~> isSTC
(* MOVX *)
||| #x"0F" .$ #x"B6" .$ RegMemCodec regCodec false ~~> unMOVZXB
||| #x"0F" .$ #x"B7" .$ RegMemCodec regCodec true ~~> unMOVZX
||| #x"0F" .$ #x"BE" .$ RegMemCodec regCodec false ~~> unMOVSXB
||| #x"0F" .$ #x"BF" .$ RegMemCodec regCodec true ~~> unMOVSX
(* SHIFTOP *)
||| droplsb #x"C0" .$ (BoolDep (RegMemCodec shiftOpCodec)) $ (BYTECodec ~~> unShiftCountI) ~~> unSHIFT
||| droplsb #x"D0" .$ (BoolDep (RegMemCodec shiftOpCodec)) $ (always #1 ~~> unShiftCountI) ~~> unSHIFT
||| droplsb #x"D2" .$ (BoolDep (RegMemCodec shiftOpCodec)) $ (Emp ~~> unShiftCountCL) ~~> unSHIFT
(* BITOP *)
||| #x"0F" .$ BITOPPREF .$ bitOpCodec $ BITOPSUFF .$ (RegMemCodec regCodec true) ~~> unBITOPR
||| #x"0F" .$ #x"BA" .$ RegMemCodec (#b"1" .$ bitOpCodec) true $ BYTECodec ~~> unBITOPI
(* TESTOP *)
||| #x"A8" .$ (always AL ~~> unRegMemR false) $ BYTECodec ~~> unTESTOPBI
||| #x"A9" .$ (always (EAX:Reg) ~~> unRegMemR true) $ DWORDCodec ~~> unTESTOPI
||| #x"F6" .$ RegMemOpCodec #0 false $ BYTECodec ~~> unTESTOPBI
||| #x"F7" .$ RegMemOpCodec #0 true $ DWORDCodec ~~> unTESTOPI
||| #x"84" .$ RegMemCodec byteRegCodec false ~~> unTESTOPB
||| #x"85" .$ RegMemCodec regCodec true ~~> unTESTOP
(* JMP *)
||| #x"E9" .$ DWORDCodec ~~> unTgt ~~> unJmpTgtI ~~> unJMP
||| #x"EB" .$ ShortTgtCodec ~~> unJmpTgtI ~~> unJMP
||| #x"FF" .$ RegMemOpCodec #4 true ~~> unJmpTgtRM ~~> unJMP
(* CALL *)
||| #x"E8" .$ DWORDCodec ~~> unTgt ~~> unJmpTgtI ~~> unCALL
||| #x"FF" .$ RegMemOpCodec #2 true ~~> unJmpTgtRM ~~> unCALL
(* JCC *)
||| #x"0F" .$ JCC32PREF .$ conditionCodec $ Any $ TgtCodec ~~> unJCC
||| JCC8PREF .$ conditionCodec $ Any $ ShortTgtCodec  ~~> unJCC
.

Require Import codecregex div.

(* Various facts about the instruction codec that can be determined statically.
   - it's non-ambiguous
   - the maximum number of bits (currently 88)
   - hence, it's finite
   - the number of bits is always divisible by 8
*)



Lemma InstrCodecIsNonAmbiguous : NonAmbiguous InstrCodec.
Proof. by vm_compute. Qed.

Definition MaxBits := Eval vm_compute in Option.default 0 (maxSize InstrCodec).

Lemma InstrCodecMaxBits : maxSize InstrCodec = Some MaxBits.
Proof. by vm_compute. Qed.

Lemma InstrCodecFinite : finiteCodec InstrCodec.
Proof.  by rewrite /finiteCodec InstrCodecMaxBits. Qed.

Lemma InstrCodecAlignment : forall l x, interp InstrCodec l x -> 8 %| size l.
Proof. move => l x I.
have byteAligned: all (fun x => 8 %| x) (sizes InstrCodec)
  by vm_compute.
apply: sizesProp I. apply: InstrCodecFinite. apply byteAligned. Qed.

Corollary encInstrAligned : forall l x, enc InstrCodec x = Some l -> 8 %| size l.
Proof. move => l x ENC. apply encSound in ENC. by apply: InstrCodecAlignment ENC. Qed.

Require Import bitreader monad cursor.

Corollary InstrCodecRoundtrip l cursor cursor' e x:
  enc InstrCodec x = Some l ->
  apart (size l) cursor cursor' ->
  runBitReader (codecToBitReader MaxBits InstrCodec) cursor (l++e) = Some(cursor', e, Some x).
Proof. move => ENC AP.
have CC := codecToFiniteBitReaderRoundtrip _ _ InstrCodecMaxBits AP ENC.
have CS := codecToBitReaderSound. apply: CC.
apply nonAmbiguousDet. apply InstrCodecIsNonAmbiguous. Qed.

Require Import reader.
Corollary InstrCodecRoundtripReader (pc:DWORD) cursor' bits x:
  enc InstrCodec x = Some bits ->
  apart ((size bits) %/ 8) pc cursor' ->
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

Instance readOptionInstr : Reader (option Instr) :=
  let! (resbits, i) = bitReaderToReader (codecToBitReader MaxBits InstrCodec) nil;
  retn i.

Instance readInstr : Reader Instr :=
  let! pc = readCursor;
  if pc is mkCursor p
  then
    let! r = readOptionInstr;
    if r is Some i then retn i else retn BADINSTR
  else
    retn BADINSTR.


Require Import writer monadinst.
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

(*
Module Examples.

Require Import instrsyntax. Open Scope instr_scope.
Compute bytesToHex (snd (fromBin (if enc InstrCodec
  (BOP _ OP_ADD (DstSrcMI true (mkMemSpec (Some (nonSPReg EBX, Some(EDX,S4))) (#x"12345678")) (#x"87654321":DWORD))) is Some bs then bs else nil))).

End Examples.
*)
