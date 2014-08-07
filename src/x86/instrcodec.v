(*======================================================================================
  Instruction codec
  ======================================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsops Ssreflect.eqtype Ssreflect.tuple.
Require Import Coq.Strings.String.
Require Import x86proved.cast x86proved.codec x86proved.bitscodec.
Require Import x86proved.x86.instr x86proved.x86.encdechelp x86proved.x86.reg.

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

Definition unRegMemR d : CAST (VReg d) (RegMem d).
apply: MakeCast (RegMemR d) (fun rm => if rm is RegMemR r then Some r else None) _.
by elim; congruence. Defined.

Definition unJmpTgtI : CAST Tgt JmpTgt.
apply: MakeCast JmpTgtI (fun t => if t is JmpTgtI d then Some d else None) _.
elim; elim; congruence. Defined.

Definition unJmpTgtRM : CAST (RegMem OpSize4) JmpTgt.
apply: (MakeCast (fun (rm:RegMem OpSize4) => match rm with RegMemR r => JmpTgtR r | RegMemM m => JmpTgtM m end)
  (fun i => match i with JmpTgtR r => Some (RegMemR OpSize4 r) | JmpTgtM m => Some (RegMemM OpSize4 m) | _ => None end) _).
elim => //. move => m. elim => // ms. by move => [<-].
by move => r y [<-].
Defined.

Require Import x86proved.bitsopsprops.
Definition unTgt : CAST DWORD Tgt.
apply: MakeCast mkTgt
                (fun t => let: mkTgt d := t in Some d) _.
by move => [d] y [<-].
Defined.

Definition unSrcRM : CAST (RegMem OpSize4) Src.
apply: MakeCast
  (fun (rm: RegMem OpSize4) => match rm with RegMemR r => SrcR r | RegMemM m => SrcM m end)
  (fun i => match i with SrcR r => Some (RegMemR OpSize4 r) | SrcM m => Some (RegMemM _ m)
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

Definition sreg3Codec : Codec SegReg :=
    #b"000" .$ always ES
||| #b"001" .$ always CS
||| #b"010" .$ always SS
||| #b"011" .$ always DS
||| #b"100" .$ always FS
||| #b"101" .$ always GS.


Definition byteRegCast : CAST (BITS 3) BYTEReg.
apply: MakeCast (fun x => decBYTEReg x) (fun x => Some (encBYTEReg x)) _.
move => x y [<-]; by rewrite encBYTERegK. Defined.
Definition byteRegCodec : Codec BYTEReg := bitsCodec 3 ~~> byteRegCast.

Definition wordRegCast : CAST (BITS 3) WORDReg.
apply: MakeCast (fun x => decWORDReg x) (fun x => Some (encWORDReg x)) _.
move => x y [<-]; by rewrite encWORDRegK. Defined.
Definition wordRegCodec : Codec WORDReg := bitsCodec 3 ~~> wordRegCast.

Definition VRegCodec s : Codec (VReg s) :=
  match s with
  | OpSize1 => byteRegCodec
  | OpSize2 => wordRegCodec
  | OpSize4 => regCodec
  end.

Definition VWORDCodec s : Codec (VWORD s) :=
  match s with
  | OpSize1 => BYTECodec
  | OpSize2 => WORDCodec
  | OpSize4 => DWORDCodec
  end.

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
Lemma totalwordReg : total wordRegCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totaldwordorbyteReg d : total (VRegCodec d).
Proof. destruct d. apply totalbyteReg. apply totalwordReg. apply totalReg. Qed.

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
||| #b"11" .$ regOrOpcodeCodec $ (VRegCodec dword ~~> unRegMemR dword).

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

Definition boolToOpSize b := if b then OpSize4 else OpSize1.
Definition prefAndBoolToOpSize p b := if b then if p then OpSize2 else OpSize4 else OpSize1.

Definition RegMemOpDepCodec (op: BITS 3) :=
  BoolDep (fun d => RegMemCodec (Const op) (boolToOpSize d) ~~> sndUnitCast _).

Definition unDstSrcRMR d : CAST (VReg d * RegMem d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR d p.1 y
                              | RegMemM y => DstSrcRM d p.1 y end)
       (fun ds => match ds with DstSrcRR x y => Some (x,RegMemR _ y)
                              | DstSrcRM x y => Some (x,RegMemM _ y)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRR d : CAST (VReg d * RegMem d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR d y p.1
                              | RegMemM y => DstSrcMR d y p.1 end)
       (fun ds => match ds with DstSrcRR x y => Some (y, RegMemR _ x)
                              | DstSrcMR x y => Some (y, RegMemM _ x)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRI d : CAST (RegMem d * VWORD d) (DstSrc d).
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
Definition prefAndOpSizeToBool (w: bool) (os: OpSize) :=  
  match os, w with
  | OpSize4, false => Some true
  | OpSize2, true => Some true
  | OpSize1, _ => Some false  
  | _, _ => None
  end.

Definition unOpsize : CAST bool OpSize.
apply: MakeCast (fun b => boolToOpSize b) 
 (fun s => match s with OpSize1 => Some false | OpSize4 => Some true | _ => None end) _.
elim => //; elim => //. 
Defined. 

Definition opSizePrefixCodec X (c : bool -> Codec X) : Codec X :=
    #x"66" .$ (c true)
||| c false.

Definition prefAndOpSizeToBool1 pref (os: OpSize)  (r: VReg os) (rm: RegMem os) :=
            match os, pref return VReg os -> RegMem os -> option
                      {d : bool &
                      (VReg (prefAndBoolToOpSize pref d) *
                       RegMem (prefAndBoolToOpSize pref d))%type}
            with
            | OpSize1, _     => fun r rm => Some (existT _ false (r,rm))
            | OpSize2, true  => fun r rm => Some (existT _ true (r, rm))
            | OpSize4, false => fun r rm => Some (existT _ true (r, rm))
            | _,       _     => fun r rm => None
            end r rm.  
   
Definition prefAndOpSizeToBool4 pref (os: OpSize)  (rm: RegMem os) (ri: VWORD os) :=
            match os, pref return RegMem os -> VWORD os -> option
                      {d : bool &
                      (RegMem (prefAndBoolToOpSize pref d) *
                       VWORD (prefAndBoolToOpSize pref d))%type}
            with
            | OpSize1, _     => fun rm ri => Some (existT _ false (rm,ri))
            | OpSize2, true  => fun rm ri => Some (existT _ true (rm, ri))
            | OpSize4, false => fun rm ri => Some (existT _ true (rm, ri))
            | _,       _     => fun rm ri => None
            end rm ri.  
   
Definition prefAndOpSizeToBool2 pref (os: OpSize) (rm: RegMem os) :=
            match os, pref return RegMem os -> option
                      {d : bool & (RegMem (prefAndBoolToOpSize pref d))%type}
            with
            | OpSize1, _     => fun rm => Some (existT _ false rm)
            | OpSize2, true  => fun rm => Some (existT _ true rm)
            | OpSize4, false => fun rm => Some (existT _ true rm)
            | _,       _     => fun rm => None
            end rm.  
   
Definition prefAndOpSizeToBool3 pref (os: OpSize) (x: DstSrc os) :=
            match os, pref return DstSrc os -> option
                      {d : bool & (DstSrc (prefAndBoolToOpSize pref d))%type}
            with
            | OpSize1, _     => fun x => Some (existT _ false x)
            | OpSize2, true  => fun x => Some (existT _ true x)
            | OpSize4, false => fun x => Some (existT _ true x)
            | _,       _     => fun x => None
            end x.  
   

Definition prefAndOpSizeToBool5 pref (os: OpSize) (x: VReg os) (y: VWORD os) :=
            match os, pref return VReg os -> VWORD os -> option
                      {d : bool & (VReg (prefAndBoolToOpSize pref d) * VWORD (prefAndBoolToOpSize pref d))%type}
            with
            | OpSize1, _     => fun x y => Some (existT _ false (x,y))
            | OpSize2, true  => fun x y => Some (existT _ true (x,y))
            | OpSize4, false => fun x y => Some (existT _ true (x,y))
            | _,       _     => fun x y => None
            end x y.  
   
Definition prefAndOpSizeToBool6 pref (os: OpSize) (x: MemSpec) (y: VWORD os) :=
            match os, pref return MemSpec -> VWORD os -> option
                      {d : bool & (MemSpec * VWORD (prefAndBoolToOpSize pref d))%type}
            with
            | OpSize1, _     => fun x y => Some (existT _ false (x,y))
            | OpSize2, true  => fun x y => Some (existT _ true (x,y))
            | OpSize4, false => fun x y => Some (existT _ true (x,y))
            | _,       _     => fun x y => None
            end x y.  
   

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

Require Import Coq.Program.Equality.

(*
Definition unBOPMRId w : CAST (BinOp * RegMem (prefAndBoolToOpSize w true) * VWORD (prefAndBoolToOpSize w true)) Instr.
eapply (MakeCast (fun (p:BinOp * RegMem (prefAndBoolToOpSize w true) * VWORD (prefAndBoolToOpSize w true)) =>
  let: (op,rm,c) := p in
    match rm with RegMemR y => BOP _ op (DstSrcRI _ y c)
                | RegMemM y => BOP _ op (DstSrcMI _ y c) end)
                 (fun i =>
                  match i with BOP _ op (DstSrcRI y c) => Some (op,RegMemR _ y,c)
                             | BOP _ op (DstSrcMI y c) => Some (op,RegMemM _ y,c)
                             | _ => None end) _).
elim => //.
elim => //.
move => op.
elim => //.
+ move => dst c [[op' rm] c']. move => [H2 H3 H4]. by subst.
+ move => dst c [[op' rm] c']. move => [H2 H3 H4]. by subst.
Defined.
*)

Definition BOPCodecRMR w : Codec {d: bool & DstSrc (prefAndBoolToOpSize w d)} :=
  BoolDep (fun d => RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _).
Definition BOPCodecMRR w : Codec {d: bool & DstSrc (prefAndBoolToOpSize w d)} :=
  BoolDep (fun d => RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _).
Definition MOVCodecMRI w : Codec {d: bool & DstSrc (prefAndBoolToOpSize w d)} :=
  BoolDep (fun d => RegMemOpCodec #0 _ $ VWORDCodec _ ~~> unDstSrcMRI _).

(*
Definition BOPCodecMRI : Codec Instr :=
  BoolDep (fun d =>
    RegMemCodec opCodec d $ DWORDorBYTECodec d) ~~> unBOPMRI.

*)

(*
Definition unMOVZX w : CAST ({d:bool & (VReg (prefAndBoolToOpSize w d) * RegMem (prefAndBoolToOpSize w d))%type}) Instr.
  eapply (MakeCast (fun p => let: existT d v := p in MOVX false _ v.1 v.2)). (RegMemR _ v.2))).
  (fun i => if i is TESTOP os x (RegImmR y) then prefAndOpSizeToBool1 w y x else None) _).
  elim:w; elim => //; elim => //; move => r; elim => // s; move => q H; by inversion H. 
apply: MakeCast (fun p => MOVX false OpSize4 p.1 p.2) (fun i => if i is MOVX false OpSize4 x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? ? [<-]. Defined.

Definition unMOVZXB : CAST (Reg * RegMem OpSize4) Instr.
apply: MakeCast (fun p => MOVX false OpSize4 p.1 p.2) (fun i => if i is MOVX false OpSize4 x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition unMOVSX : CAST (Reg * RegMem true) Instr.
apply: MakeCast (fun p => MOVX true true p.1 p.2) (fun i => if i is MOVX true true x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition unMOVSXB : CAST (Reg * RegMem false) Instr.
apply: MakeCast (fun p => MOVX true false p.1 p.2) (fun i => if i is MOVX true false x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.
*)

Definition TgtCodec : Codec Tgt := DWORDCodec ~~> unTgt.
Definition ShortTgtCodec : Codec Tgt := shortDWORDCodec ~~> unTgt.

(*
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

*)

(* RegMemOp codec with lsb [d] of opcode + optional 0x66 prefix [w] determining operand size *)
Definition VRegMemCodec T w (opcode: BYTE) (c: Codec T) :=
  droplsb opcode .$ BoolDep (fun d => RegMemCodec c (prefAndBoolToOpSize w d)).

Definition VRegMemOpCodec w (opcode: BYTE) (op: BITS 3) :=
  droplsb opcode .$ BoolDep (fun d => RegMemOpCodec op (prefAndBoolToOpSize w d)).

Definition VRegMemRegCodec w (opcode: BYTE) :=
  droplsb opcode .$ BoolDep (fun d => RegMemCodec (VRegCodec (prefAndBoolToOpSize w d)) (prefAndBoolToOpSize w d)).

Definition VAXCodec os : Codec (VReg os) :=
match os return Codec (VReg os) with
| OpSize1 => always AL
| OpSize2 => always AX
| OpSize4 => always (EAX:Reg)
end.

Definition opcodeWithSizeCodec X (opcode:BYTE) (c : bool -> Codec X) : Codec X :=
  droplsb opcode .$ (#b"1" .$ (c true) ||| #b"0" .$ (c false)).

(*---------------------------------------------------------------------------
    TEST instruction
  ---------------------------------------------------------------------------*)
Definition unTESTI os : CAST (RegMem os * VWORD os) Instr.
apply: (MakeCast (fun p => TESTOP os p.1 (RegImmI os p.2))
                 (fun i => 
  match i, os with
  | TESTOP OpSize1 x (RegImmI d), OpSize1 => Some(x,d) 
  | TESTOP OpSize2 x (RegImmI d), OpSize2 => Some(x,d)
  | TESTOP OpSize4 x (RegImmI d), OpSize4 => Some(x,d)
  | _, _ => None end) _).
elim:os; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined.

Definition unTESTR w: 
  CAST {d:bool & (VReg (prefAndBoolToOpSize w d) * RegMem (prefAndBoolToOpSize w d))%type} Instr. 
Proof.
  apply: (MakeCast (fun p => let: existT d v := p in TESTOP _ v.2 (RegImmR _ v.1))
  (fun i => if i is TESTOP os x (RegImmR y) then prefAndOpSizeToBool1 w y x else None) _).
  elim:w; elim => //; elim => //; move => r; elim => // s; move => q H; by inversion H. 
Defined.

Definition TESTCodec :=
  opSizePrefixCodec (fun w =>
    (* Short form for TEST AL/AX/EAX, imm8/imm16/imm32 *)
        opcodeWithSizeCodec #x"A8" (fun d => 
        (VAXCodec (prefAndBoolToOpSize w d) ~~> unRegMemR _) $ VWORDCodec _ ~~> unTESTI _)
    (* TEST r/m8, imm8 | TEST r/m16, r16 | TEST r/m32, r32 *)
    ||| opcodeWithSizeCodec #x"F6" (fun d =>
        RegMemOpCodec #0 (prefAndBoolToOpSize w d) $ VWORDCodec _ ~~> unTESTI _)
    (* TEST r/m8, r8 | TEST r/m16, r16 | TEST r/m32, r32 *)
    ||| VRegMemRegCodec _ #x"84" ~~> unTESTR w
    ).

(*---------------------------------------------------------------------------
    RET instruction (near)
  ---------------------------------------------------------------------------*)
Definition unRET : CAST WORD Instr.
apply: MakeCast RETOP (fun i => if i is RETOP w then Some w else None) _.
by elim => // ? ? [->]. 
Defined.

Definition RETCodec :=
    #x"C3" .$ always #0 ~~> unRET
||| #x"C2" .$ WORDCodec ~~> unRET.

(*---------------------------------------------------------------------------
    JMP instruction
    @TODO: 16-bit variants, far jumps
  ---------------------------------------------------------------------------*)
Definition unJMP : CAST JmpTgt Instr.
apply: MakeCast JMPrel (fun i => if i is JMPrel t then Some t else None) _.
by elim => // ? ? [->]. 
Defined.

Definition JMPCodec :=
    #x"EB" .$ ShortTgtCodec ~~> unJmpTgtI ~~> unJMP
||| #x"E9" .$ DWORDCodec ~~> unTgt ~~> unJmpTgtI ~~> unJMP
||| #x"FF" .$ RegMemOpCodec #4 OpSize4 ~~> unJmpTgtRM ~~> unJMP.

(*---------------------------------------------------------------------------
    CALL instruction
    @TODO: 16-bit variants, far calls
  ---------------------------------------------------------------------------*)
Definition unCALL : CAST JmpTgt Instr.
apply: MakeCast CALLrel (fun i => if i is CALLrel t then Some t else None) _.
by elim => // ? ? [->]. 
Defined.

Definition CALLCodec :=
    #x"E8" .$ DWORDCodec ~~> unTgt ~~> unJmpTgtI ~~> unCALL
||| #x"FF" .$ RegMemOpCodec #2 OpSize4 ~~> unJmpTgtRM ~~> unCALL.


(*---------------------------------------------------------------------------
    JCC instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unJCC : CAST (Condition*bool*Tgt) Instr.
apply: MakeCast (fun p => let: (c,d,t) := p in JCCrel c (negb d) t)
                (fun i => if i is JCCrel c d t then Some(c,negb d,t) else None) _.
Proof. elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
by rewrite negbK. Defined.

Definition JCCCodec :=
    #x"0F" .$ JCC32PREF .$ conditionCodec $ Any $ TgtCodec ~~> unJCC
||| JCC8PREF .$ conditionCodec $ Any $ ShortTgtCodec  ~~> unJCC.


(*---------------------------------------------------------------------------
    PUSH instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unPUSH : CAST Src Instr.
apply: MakeCast PUSH (fun i => if i is PUSH s then Some s else None) _.
by elim => // ? ? [->]. Defined.

Definition unPUSHSegR : CAST SegReg Instr.
apply: MakeCast PUSHSegR (fun i => if i is PUSHSegR r then Some r else None) _.
by elim => // ? ? [->]. Defined.

Definition PUSHCodec := 
    #x"68" .$ DWORDCodec ~~> unSrcI ~~> unPUSH
||| #x"6A" .$ shortDWORDCodec ~~> unSrcI ~~> unPUSH
||| #b"01010" .$ regCodec ~~> unSrcR ~~> unPUSH
||| #x"FF" .$ RegMemOpCodec #6 _ ~~> unSrcRM ~~> unPUSH
||| #x"0E" .$ always CS ~~> unPUSHSegR
||| #x"16" .$ always SS ~~> unPUSHSegR
||| #x"1E" .$ always DS ~~> unPUSHSegR
||| #x"06" .$ always ES ~~> unPUSHSegR
||| #x"0F" .$ #x"A0" .$ always FS ~~> unPUSHSegR
||| #x"0F" .$ #x"A8" .$ always GS ~~> unPUSHSegR.

(*---------------------------------------------------------------------------
    POP instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unPOP : CAST (RegMem OpSize4) Instr.
apply: MakeCast POP (fun i => if i is POP d then Some d else None) _.
elim => //. by move => d rm [->]. Defined.

Definition unPOPSegR : CAST SegReg Instr.
apply: MakeCast POPSegR (fun i => if i is POPSegR r then Some r else None) _.
by elim => // ? ? [->]. Defined.

Definition POPCodec :=
    #x"8F" .$ RegMemOpCodec #0 _ ~~> unPOP
||| #b"01011" .$ regCodec ~~> unRegMemR OpSize4 ~~> unPOP
||| #x"17" .$ always SS ~~> unPOPSegR
||| #x"1F" .$ always DS ~~> unPOPSegR
||| #x"07" .$ always ES ~~> unPOPSegR
||| #x"0F" .$ #x"A1" .$ always FS ~~> unPOPSegR
||| #x"0F" .$ #x"A9" .$ always GS ~~> unPOPSegR.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)
Definition unMOV w : CAST ({d:bool & DstSrc (prefAndBoolToOpSize w d)}) Instr.
apply: (MakeCast (fun (p:{d:bool & DstSrc (prefAndBoolToOpSize w d)}) => let: existT d v := p in MOVOP _ v)
                 (fun i => if i is MOVOP os v then prefAndOpSizeToBool3 w v else None) _). 
elim: w; elim => //; elim => // ds y H; by inversion H. Defined.

Definition unMOVRI w : CAST ({d:bool & (VReg (prefAndBoolToOpSize w d) * VWORD (prefAndBoolToOpSize w d))%type}) Instr.
apply: (MakeCast
  (fun (p:{d:bool & (VReg (prefAndBoolToOpSize w d) * VWORD (prefAndBoolToOpSize w d))%type}) => let: existT d (x,y) := p in MOVOP _ (DstSrcRI _ x y))
 (fun i => if i is MOVOP os (DstSrcRI r d) then prefAndOpSizeToBool5 w r d else None) _).
by elim: w; elim => //; elim => //; elim => // => ? ? ? H; inversion H. 
Defined.

Definition unMOVRMSeg : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVRMSeg p.2 p.1) (fun i => if i is MOVRMSeg x y then Some(y,x) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOVSegRM : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVSegRM p.1 p.2) (fun i => if i is MOVSegRM x y then Some(x,y) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.


Definition MOVCodec :=
    opSizePrefixCodec (fun w => droplsb #x"8A" .$ BOPCodecRMR w ~~> unMOV w)
||| opSizePrefixCodec (fun w => droplsb #x"88" .$ BOPCodecMRR w ~~> unMOV w)
||| opSizePrefixCodec (fun w => droplsb #x"C6" .$ MOVCodecMRI w ~~> unMOV w)
||| opSizePrefixCodec (fun w => #x"B" .$ 
              BoolDep (fun d => VRegCodec _ $ VWORDCodec _) ~~> unMOVRI w)
||| #x"8C" .$ RegMemCodec sreg3Codec _ ~~> unMOVRMSeg
||| #x"8E" .$ RegMemCodec sreg3Codec _ ~~> unMOVSegRM.

(*---------------------------------------------------------------------------
    BT, BTC, BTR, BTS instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unBITOPR : CAST (BitOp * (Reg * RegMem OpSize4)) Instr.
apply: (MakeCast (fun p => let: (op,(r,rm)) := p in BITOP op rm (inl r))
                (fun i => if i is BITOP op y (inl r) then Some(op,(r,y)) else None) _).
elim => //. move => op dst src [op' [dst' src']]. case src => // r. by move => [-> -> ->].
Defined.

Definition unBITOPI : CAST (BitOp * RegMem OpSize4 * BYTE) Instr.
apply: (MakeCast (fun p => let: (op,rm,b) := p in BITOP op rm (inr b))
                (fun i => if i is BITOP op y (inr b) then Some(op,y,b) else None) _).
elim => //. move => op dst src [[op' dst'] src']. case src => // r. by move => [-> -> ->].
Defined.

Definition BITCodec :=
    #x"0F" .$ BITOPPREF .$ bitOpCodec $ BITOPSUFF .$ (RegMemCodec regCodec _) ~~> unBITOPR
||| #x"0F" .$ #x"BA" .$ RegMemCodec (#b"1" .$ bitOpCodec) _ $ BYTECodec ~~> unBITOPI.


(*---------------------------------------------------------------------------
    SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unShiftCountCL : CAST unit ShiftCount.
apply: MakeCast (fun _=>ShiftCountCL) (fun c => if c is ShiftCountCL then Some tt else None) _.
elim; congruence.
Defined.

Definition unShiftCountI : CAST BYTE ShiftCount.
apply: MakeCast ShiftCountI (fun c => if c is ShiftCountI b then Some b else None) _.
elim; congruence.
Defined.

Definition unSHIFT pref : CAST ({d:bool & (ShiftOp * RegMem (prefAndBoolToOpSize pref d))%type} * ShiftCount) Instr.
eapply (MakeCast (fun (p:{d:bool & (ShiftOp * RegMem (prefAndBoolToOpSize pref d))%type} * ShiftCount) =>
                  let: (existT _ (op,v), count) := p in SHIFTOP _ op v count)
                 (fun i => if i is SHIFTOP d op v count then
   if prefAndOpSizeToBool2 pref v is Some (existT d x) then Some (existT _ _ (op,x), count) else None else None)). 
elim: pref => //; elim => //; elim => //; move => op dst count q H; by inversion H. 
Defined.

Definition SHIFTCodec :=
  opSizePrefixCodec (fun w => 
    (
      VRegMemCodec _ #x"C0" shiftOpCodec $ (BYTECodec ~~> unShiftCountI) |||
      VRegMemCodec _ #x"D0" shiftOpCodec $ (always #1 ~~> unShiftCountI) |||
      VRegMemCodec _ #x"D2" shiftOpCodec $ (Emp ~~> unShiftCountCL)
    ) ~~> unSHIFT w
  ).

(*---------------------------------------------------------------------------
    ADC/ADD/SUB/SBB/OR/AND/XOR/CMP instructions
  ---------------------------------------------------------------------------*)
Definition unBOP w : CAST (BinOp * {d:bool & DstSrc (prefAndBoolToOpSize w d)}) Instr.
apply: (MakeCast (fun p:BinOp * {d:bool & DstSrc (prefAndBoolToOpSize w d)} => 
                  let: existT d v := p.2 in BOP _ p.1 v)
                 (fun i => if i is BOP d op v 
                  then if prefAndOpSizeToBool3 w v is Some x then Some (op,x) else None else None) _).
elim:w; elim => //; elim => //; move => op ds [op' p] H; by inversion H. 
Defined.

Definition unBOPMRI w : CAST ({d:bool & (BinOp * RegMem (prefAndBoolToOpSize w d) * VWORD (prefAndBoolToOpSize w d))%type}) Instr.
apply: (MakeCast (fun (p:{d:bool & (BinOp * RegMem (prefAndBoolToOpSize w d) * VWORD (prefAndBoolToOpSize w d))%type}) =>
  let: existT d (op,rm,c) := p in
    match rm with RegMemR y => BOP _ op (DstSrcRI _ y c)
                | RegMemM y => BOP _ op (DstSrcMI _ y c) end)
                 (fun i =>
                  match i with BOP os op (DstSrcRI y c) =>
                    if prefAndOpSizeToBool5 w y c is Some (existT _ (y,c))
                    then Some (existT _ _ (op,RegMemR _ y,c)) else None           
                             | BOP os op (DstSrcMI y c) => 
                    if prefAndOpSizeToBool6 w y c is Some (existT _ (y,c))
                    then Some (existT _ _ (op,RegMemM _ y,c)) else None
                             | _ => None end) _).
elim: w; elim => //; elim => // ?; elim => // ? ? ? H; by inversion H. 
Defined.

Definition BINOPCodec :=
(* Binary operations *)
(*
||| #b"00" .$ opCodec $ #b"10" .$ EAXimmCodec ~~> unBOPMRI
*)
    opSizePrefixCodec (fun w => #b"00" .$ opCodec $ #b"00" .$ BOPCodecMRR w ~~> unBOP w)
||| opSizePrefixCodec (fun w => #b"00" .$ opCodec $ #b"01" .$ BOPCodecRMR w ~~> unBOP w)
||| opSizePrefixCodec (fun w => droplsb #x"80" .$ 
              BoolDep (fun d => RegMemCodec opCodec _ $ VWORDCodec _) ~~> unBOPMRI w)
(*||| opSizePrefixCodec (fun w => #x"83" .$ RegMemCodec opCodec _ $ shortDWORDCodec ~~> unBOPMRId w)*)
.

(*---------------------------------------------------------------------------
    INC/DEC/NOT/NEG instructions
  ---------------------------------------------------------------------------*)
Definition unINCR w : CAST (VReg (if w then OpSize2 else OpSize4)) Instr.
apply: (MakeCast (fun r => UOP _ OP_INC (RegMemR _ r))
                (fun i => if i is UOP os OP_INC (RegMemR r) then
                          (match os, w return VReg os -> option (VReg (if w then OpSize2 else OpSize4)) with 
                            OpSize4, false => fun r => Some r
                          | OpSize2, true => fun r => Some r
                          | _, _ => fun _ => None end) r else None) _).
by elim: w; elim => //; elim => //; elim => //; elim => // => ? ? [->]. Defined.

Definition unDECR w : CAST (VReg (if w then OpSize2 else OpSize4)) Instr.
apply: (MakeCast (fun r => UOP _ OP_DEC (RegMemR _ r))
                (fun i => if i is UOP os OP_DEC (RegMemR r) then
                          (match os, w return VReg os -> option (VReg (if w then OpSize2 else OpSize4)) with 
                            OpSize4, false => fun r => Some r
                          | OpSize2, true => fun r => Some r
                          | _, _ => fun _ => None end) r else None) _).
by elim: w; elim => //; elim => //; elim => //; elim => // => ? ? [->]. Defined.

Definition unINC pref : CAST {d:bool & RegMem (prefAndBoolToOpSize pref d)} Instr.
apply: MakeCast (fun p => let: existT d v := p in UOP _ OP_INC v)
                (fun i => if i is UOP s OP_INC v then prefAndOpSizeToBool2 pref v else None) _.
elim: pref; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unDEC pref : CAST {d:bool & RegMem (prefAndBoolToOpSize pref d)} Instr.
apply: MakeCast (fun p => let: existT d v := p in UOP _ OP_DEC v)
                (fun i => if i is UOP s OP_DEC v then prefAndOpSizeToBool2 pref v else None) _.
elim: pref; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNOT pref : CAST {d:bool & RegMem (prefAndBoolToOpSize pref d)} Instr.
apply: MakeCast (fun p => let: existT d v := p in UOP _ OP_NOT v)
                (fun i => if i is UOP s OP_NOT v then prefAndOpSizeToBool2 pref v else None) _.
elim: pref; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNEG pref : CAST {d:bool & RegMem (prefAndBoolToOpSize pref d)} Instr.
apply: MakeCast (fun p => let: existT d v := p in UOP _ OP_NEG v)
                (fun i => if i is UOP s OP_NEG v then prefAndOpSizeToBool2 pref v else None) _.
elim: pref; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition UOPCodec :=
    opSizePrefixCodec (fun w => VRegMemOpCodec _ #x"FE" #0 ~~> unINC w)
||| opSizePrefixCodec (fun w => VRegMemOpCodec _ #x"FE" #1 ~~> unDEC w)
||| opSizePrefixCodec (fun w => VRegMemOpCodec _ #x"F6" #2 ~~> unNOT w)
||| opSizePrefixCodec (fun w => VRegMemOpCodec _ #x"F6" #3 ~~> unNEG w)
||| opSizePrefixCodec (fun w => INCPREF .$ VRegCodec _ ~~> unINCR w)
||| opSizePrefixCodec (fun w => DECPREF .$ VRegCodec _ ~~> unDECR w).


(*---------------------------------------------------------------------------
    IN/OUT instructions
  ---------------------------------------------------------------------------*)
Definition unINI (w:bool) : CAST (bool*BYTE) Instr.
apply: (MakeCast (fun p => INOP (prefAndBoolToOpSize w p.1) (PortI p.2)) (fun i => if i is INOP os (PortI p) then if prefAndOpSizeToBool w os is Some d then Some(d,p) else None else None) _).
elim: w; elim => //; elim => //; elim => // => ? [? ?] H; by inversion H. Defined.

Definition unOUTI (w:bool) : CAST (bool*BYTE) Instr.
apply: (MakeCast (fun p => OUTOP (prefAndBoolToOpSize w p.1) (PortI p.2)) (fun i => if i is OUTOP os (PortI p) then if prefAndOpSizeToBool w os is Some d then Some(d,p) else None else None) _).
elim: w; elim => //; elim => //; elim => // => ? [? ?] H; by inversion H. Defined.

Definition unINR (w:bool) : CAST bool Instr.
apply: MakeCast (fun p => INOP (prefAndBoolToOpSize w p) PortDX) 
  (fun i => if i is INOP os PortDX then prefAndOpSizeToBool w os else None) _.
elim: w; elim => //; elim => //; elim => // => ? H; by inversion H. 
Defined. 

Definition unOUTR (w:bool) : CAST bool Instr.
apply: MakeCast (fun p => OUTOP (prefAndBoolToOpSize w p) PortDX) 
  (fun i => if i is OUTOP os PortDX then prefAndOpSizeToBool w os else None) _.
elim: w; elim => //; elim => //; elim => // => ? H; by inversion H. 
Defined. 

Definition INOUTCodec :=
    opSizePrefixCodec (fun w => droplsb #x"E4" .$ Any $ BYTECodec ~~> unINI w)
||| opSizePrefixCodec (fun w => droplsb #x"E6" .$ Any $ BYTECodec ~~> unOUTI w)
||| opSizePrefixCodec (fun w => droplsb #x"EC" .$ Any ~~> unINR w)
||| opSizePrefixCodec (fun w => droplsb #x"EE" .$ Any ~~> unOUTR w).

(*---------------------------------------------------------------------------
    MUL and IMUL instructions
  ---------------------------------------------------------------------------*)
Definition unIMUL : CAST (Reg * RegMem OpSize4) Instr.
apply: (MakeCast (fun p => IMUL p.1 p.2)
                 (fun i => if i is IMUL dst src then Some (dst,src) else None) _).
elim => //. by move => dst src [dst' src'] [<-] ->.  Defined.

Definition unMUL w : CAST {d:bool & RegMem (prefAndBoolToOpSize w d)} Instr.
apply: (MakeCast (fun p => let: existT d v := p in MUL v)
                 (fun i => if i is MUL os v then prefAndOpSizeToBool2 w v else None) _).
elim: w; elim => //; elim => //; move => r q H; by inversion H.  
Defined.

Definition MULCodec :=
(*||| #x"0F" .$ #x"AF" .$ RegMemCodec regCodec _ ~~> unIMUL*)
   opSizePrefixCodec (fun w => VRegMemOpCodec _ #x"F6" #5 ~~> unMUL w).

(*---------------------------------------------------------------------------
    LEA instruction 
  ---------------------------------------------------------------------------*)
Definition unLEA : CAST (Reg * RegMem OpSize4) Instr.
apply: MakeCast (fun p => LEA p.1 p.2) (fun i => if i is LEA x y then Some(x,y) else None) _.
by elim => // ? ? [? ?] [-> ->]. Defined.

Definition LEACodec :=
  #x"8D" .$ RegMemCodec regCodec _ ~~> unLEA.

(*---------------------------------------------------------------------------
    XCHG instruction 
  ---------------------------------------------------------------------------*)
Definition unXCHG pref : 
  CAST {d:bool & (VReg (prefAndBoolToOpSize pref d) * RegMem (prefAndBoolToOpSize pref d))%type} Instr. 
Proof. 
  apply: MakeCast (fun p => let: existT d v := p in XCHG _ v.1 v.2)
  (fun i => if i is XCHG os x y then prefAndOpSizeToBool1 pref x y else None) _. 
  elim: pref; elim => //; elim => //; move => r s q H; by inversion H.
Defined. 

Definition XCHGCodec :=
(*||| opSizePrefixCodec (fun w => #b"10010" .$ always (if w then AX else (EAX:Reg)) $ (VRegCodec _ ~~> unRegMemR _) ~~> unXCHG w)
*)
    opSizePrefixCodec (fun w => VRegMemRegCodec _ #x"86" ~~> unXCHG w).

(*---------------------------------------------------------------------------
    All instructions
  ---------------------------------------------------------------------------*)
Definition InstrCodec : Codec Instr :=
(* Nullary operations *)
    #x"F4" ~~> isHLT
||| #x"F5" ~~> isCMC
||| #x"F8" ~~> isCLC
||| #x"F9" ~~> isSTC
(* Everything else *)
(* MOVX *)
(*
||| opSizePrefixCodec (fun w => #x"0F" .$ VRegMemRegCodec _ #x"B6" ~~> unMOVZX w)
||| #x"0F" .$ #x"B7" .$ RegMemCodec regCodec true ~~> unMOVZX
||| #x"0F" .$ #x"BE" .$ RegMemCodec regCodec false ~~> unMOVSXB
||| #x"0F" .$ #x"BF" .$ RegMemCodec regCodec true ~~> unMOVSX
*)
||| JMPCodec ||| CALLCodec ||| TESTCodec ||| PUSHCodec ||| POPCodec ||| RETCodec
||| MOVCodec ||| BITCodec ||| SHIFTCodec ||| JCCCodec ||| BINOPCodec ||| UOPCodec
||| INOUTCodec ||| LEACodec ||| XCHGCodec ||| MULCodec
.


Require Import x86proved.codecregex Ssreflect.div.

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
Proof. by rewrite /finiteCodec InstrCodecMaxBits. Qed.

Lemma InstrCodecAlignment : forall l x, interp InstrCodec l x -> 8 %| size l.
Proof. move => l x I.
have byteAligned: all (fun x => 8 %| x) (sizes InstrCodec)
  by vm_compute.
apply: sizesProp I. apply: InstrCodecFinite. apply byteAligned. Qed.

Corollary encInstrAligned : forall l x, enc InstrCodec x = Some l -> 8 %| size l.
Proof. move => l x ENC. apply encSound in ENC. by apply: InstrCodecAlignment ENC. Qed.

Require Import x86proved.bitreader x86proved.monad x86proved.cursor.

Corollary InstrCodecRoundtrip l cursor cursor' e x:
  enc InstrCodec x = Some l ->
  apart (size l) cursor cursor' ->
  runBitReader (codecToBitReader MaxBits InstrCodec) cursor (l++e) = Some(cursor', e, Some x).
Proof. move => ENC AP.
have CC := codecToFiniteBitReaderRoundtrip _ _ InstrCodecMaxBits AP ENC.
have CS := codecToBitReaderSound. apply: CC.
apply nonAmbiguousDet. apply InstrCodecIsNonAmbiguous. Qed.

Require Import x86proved.reader.
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


Require Import x86proved.writer x86proved.monadinst.
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
Definition exinstr := (TESTOP OpSize2 (RegMemM OpSize2 (mkMemSpec (Some (nonSPReg EBX, Some(EDX, S4))) (#x"12345678"))) (RegImmR OpSize2 BP)).

Compute bytesToHex (snd (fromBin (if enc InstrCodec exinstr is Some bs then bs else nil))).

End Examples.
*)
