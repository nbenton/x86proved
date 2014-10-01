(*======================================================================================
  Instruction codec
  ======================================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsopsprops x86proved.bitsops Ssreflect.eqtype Ssreflect.tuple.
Require Import Coq.Strings.String.
Require Import x86proved.cast x86proved.codec x86proved.bitscodec.
Require Import x86proved.x86.instr x86proved.x86.encdechelp x86proved.x86.reg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Casts for datatypes used in instructions
  ---------------------------------------------------------------------------*)
Definition unSrcR : CAST GPReg32 Src.
apply: MakeCast SrcR (fun s => if s is SrcR r then Some r else None) _.
by elim; congruence. Defined.

Definition unSrcI : CAST DWORD Src.
apply: MakeCast SrcI (fun s => if s is SrcI i then Some i else None) _.
by elim; congruence. Defined.

Definition unRegMemR d : CAST (GPReg d) (RegMem d).
apply: MakeCast (RegMemR d) (fun rm => if rm is RegMemR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmR d : CAST (GPReg d) (RegImm d).
apply: MakeCast (RegImmR d) (fun rm => if rm is RegImmR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmI d : CAST (VWORD d) (RegImm d).
apply: MakeCast (RegImmI d) (fun rm => if rm is RegImmI v then Some v else None) _.
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

Definition unTgt : CAST DWORD Tgt.
apply: MakeCast mkTgt (fun t => let: mkTgt d := t in Some d) _.
by move => [d] y [<-].
Defined.

Definition unSrcRM : CAST (RegMem OpSize4) Src.
apply: MakeCast
  (fun (rm: RegMem OpSize4) => match rm with RegMemR r => SrcR r | RegMemM m => SrcM m end)
  (fun i => match i with SrcR r => Some (RegMemR OpSize4 r) | SrcM m => Some (RegMemM _ m)
                       | _ => None
            end) _.
elim => //; by move => ? ? [<-]. Defined.

Definition unGPReg64 : CAST NonSPReg64 GPReg64.
apply: MakeCast mkGPReg64 (fun r => if r is mkGPReg64 r then Some r else None) _.
by elim => // ? ? [->]. 
Defined.

(*---------------------------------------------------------------------------
    Casts and codecs for bit-encoded types e.g. registers, scales, conditions
  ---------------------------------------------------------------------------*)

(* Non-ESP, 32-bit register encoding *)
Definition NonSPReg32Codec (rexBit:bool) : Codec NonSPReg32 :=
if rexBit then
    #b"000" .$ always R8D
||| #b"001" .$ always R9D
||| #b"010" .$ always R10D
||| #b"011" .$ always R11D
||| #b"100" .$ always R12D
||| #b"101" .$ always R13D
||| #b"110" .$ always R14D
||| #b"111" .$ always R15D
else
    #b"000" .$ always EAX
||| #b"001" .$ always ECX
||| #b"010" .$ always EDX
||| #b"011" .$ always EBX
||| #b"110" .$ always ESI
||| #b"111" .$ always EDI
||| #b"101" .$ always EBP.

(* 32-bit register encoding, including ESP *)
Definition GPReg32Codec (rexBit:bool) : Codec GPReg32 :=
if rexBit then
    #b"000" .$ always (R8D:GPReg32)
||| #b"001" .$ always (R9D:GPReg32)
||| #b"010" .$ always (R10D:GPReg32)
||| #b"011" .$ always (R11D:GPReg32)
||| #b"100" .$ always (R12D:GPReg32)
||| #b"101" .$ always (R13D:GPReg32)
||| #b"110" .$ always (R14D:GPReg32)
||| #b"111" .$ always (R15D:GPReg32)
else
    #b"000" .$ always (EAX:GPReg32)
||| #b"001" .$ always (ECX:GPReg32)
||| #b"010" .$ always (EDX:GPReg32)
||| #b"011" .$ always (EBX:GPReg32)
||| #b"100" .$ always ESP
||| #b"110" .$ always (ESI:GPReg32)
||| #b"111" .$ always (EDI:GPReg32)
||| #b"101" .$ always (EBP:GPReg32).

(* Non-RSP, 64-bit register encoding *)
Definition NonSPReg64Codec (rexBit:bool) : Codec NonSPReg64 :=
if rexBit then 
    #b"000" .$ always R8
||| #b"001" .$ always R9
||| #b"010" .$ always R10
||| #b"011" .$ always R11
||| #b"100" .$ always R12
||| #b"101" .$ always R13
||| #b"110" .$ always R14
||| #b"111" .$ always R15
else
    #b"000" .$ always RAX
||| #b"001" .$ always RCX
||| #b"010" .$ always RDX
||| #b"011" .$ always RBX
||| #b"110" .$ always RSI
||| #b"111" .$ always RDI
||| #b"101" .$ always RBP.
  
(* 64-bit register encoding, including RSP *)
Definition GPReg64Codec (rexBit:bool) : Codec GPReg64 :=
if rexBit then 
    #b"000" .$ always (R8:GPReg64)
||| #b"001" .$ always (R9:GPReg64)
||| #b"010" .$ always (R10:GPReg64)
||| #b"011" .$ always (R11:GPReg64)
||| #b"100" .$ always (R12:GPReg64)
||| #b"101" .$ always (R13:GPReg64)
||| #b"110" .$ always (R14:GPReg64)
||| #b"111" .$ always (R15:GPReg64)
else
    #b"000" .$ always (RAX:GPReg64)
||| #b"001" .$ always (RCX:GPReg64)
||| #b"010" .$ always (RDX:GPReg64)
||| #b"011" .$ always (RBX:GPReg64)
||| #b"100" .$ always RSP
||| #b"110" .$ always (RSI:GPReg64)
||| #b"111" .$ always (RDI:GPReg64)
||| #b"101" .$ always (RBP:GPReg64).
  
(* Non-SP, 16-bit register encoding *)
Definition NonSPReg16Codec (rexBit:bool) : Codec NonSPReg16 :=
if rexBit then
    #b"000" .$ always R8W
||| #b"001" .$ always R9W
||| #b"010" .$ always R10W
||| #b"011" .$ always R11W
||| #b"100" .$ always R12W
||| #b"101" .$ always R13W
||| #b"110" .$ always R14W
||| #b"111" .$ always R15W
else
    #b"000" .$ always AX
||| #b"001" .$ always CX
||| #b"010" .$ always DX
||| #b"011" .$ always BX
||| #b"110" .$ always SI
||| #b"111" .$ always DI
||| #b"101" .$ always BP.

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

(*
Definition optionalNonSPregCast : CAST (BITS 3) (option NonSPReg32).
apply: MakeCast (fun (x: BITS 3) => decNonSPReg x) (fun x =>
  if x is Some r then Some (encNonSPReg r) else Some #b"100") _.
elim => //.
+ move => x y [<-]. by rewrite encNonSPRegK.
+ by move => y [<-]. Defined.
Definition optionalNonSPRegCodec : Codec (option NonSPReg) :=
  bitsCodec 3 ~~> optionalNonSPregCast.
*)

Definition optionalNonSPReg32Codec : Codec (option NonSPReg32) :=
    #b"000" .$ always (Some EAX)
||| #b"001" .$ always (Some ECX)
||| #b"010" .$ always (Some EDX)
||| #b"011" .$ always (Some EBX)
||| #b"100" .$ always None
||| #b"110" .$ always (Some ESI)
||| #b"111" .$ always (Some EDI)
||| #b"101" .$ always (Some EBP).
  
Definition NonBPNonSPReg32Codec : Codec NonSPReg32 :=
    #b"000" .$ always EAX
||| #b"001" .$ always ECX
||| #b"010" .$ always EDX
||| #b"011" .$ always EBX
||| #b"110" .$ always ESI
||| #b"111" .$ always EDI.

Definition sreg3Codec : Codec SegReg :=
    #b"000" .$ always ES
||| #b"001" .$ always CS
||| #b"010" .$ always SS
||| #b"011" .$ always DS
||| #b"100" .$ always FS
||| #b"101" .$ always GS.


Definition Reg8Codec : Codec Reg8 := 
    #b"000" .$ always (AL:Reg8)
||| #b"001" .$ always (CL:Reg8)
||| #b"010" .$ always (DL:Reg8)
||| #b"011" .$ always (BL:Reg8).
(*
||| #b"100" .$ always AH
||| #b"101" .$ always CH
||| #b"110" .$ always DH
||| #b"111" .$ always BH.*)

Definition GPReg16Codec : Codec GPReg16 := 
    #b"000" .$ always (AX:GPReg16)
||| #b"001" .$ always (CX:GPReg16)
||| #b"010" .$ always (DX:GPReg16)
||| #b"011" .$ always (BX:GPReg16)
||| #b"100" .$ always SP
||| #b"101" .$ always (BP:GPReg16)
||| #b"110" .$ always (SI:GPReg16)
||| #b"111" .$ always (DI:GPReg16).

Definition VRegCodec s : Codec (GPReg s) :=
  match s return Codec (GPReg s) with
  | OpSize1 => Reg8Codec
  | OpSize2 => GPReg16Codec
  | OpSize4 => GPReg32Codec false
  | OpSize8 => GPReg64Codec false
  end.

Definition VWORDCodec s : Codec (VWORD s) :=
  match s with
  | OpSize1 => BYTECodec
  | OpSize2 => WORDCodec
  | OpSize4 => DWORDCodec
  | OpSize8 => QWORDCodec
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
(*Lemma totalReg : total regCodec. Proof. apply totalCast => //. apply totalBITS. Qed.*)
(*Lemma totaloptionalNonSPReg : total optionalNonSPRegCodec. Proof. apply totalCast => //.*)
Lemma totalOp : total opCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalShiftOp : total shiftOpCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
(*Lemma totalbyteReg : total byteRegCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalwordReg : total wordRegCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
(*Lemma totaldwordorbyteReg d : total (VRegCodec d).
Proof. destruct d. apply totalbyteReg. apply totalwordReg. apply totalReg. Qed.*)*)

Definition SIB := (GPReg32 * option (NonSPReg32 * Scale))%type.

Definition SIBCast : CAST (Scale * option NonSPReg32 * GPReg32) SIB.
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

Definition SIBCodec : Codec SIB := scaleCodec $ optionalNonSPReg32Codec $ GPReg32Codec false ~~> SIBCast.

(*
Lemma totalSIB : total SIBCodec.
Proof. rewrite /SIBCodec. apply totalCast. apply totalSeq. apply totalSeq.
apply totalScale. apply totaloptionalNonSPReg. apply totalReg.
rewrite /castIsTotal.  move => [r o]. destruct o => //. by destruct p.
Qed.
*)

Definition dispOffsetSIBCast s : CAST (SIB * DWORD) (RegMem s).
apply: MakeCast (fun p => RegMemM s (mkMemSpec (Some p.1) p.2))
  (fun rm => if rm is RegMemM (mkMemSpec (Some sib) offset) then Some(sib,offset) else None) _.
elim => //. elim => //. elim => //. move => [x y] z [x' y']. by move => [-> ->]. Defined.

Definition dispOffsetCast s : CAST (NonSPReg32 * DWORD) (RegMem s). 
eapply (MakeCast (fun p => RegMemM s (mkMemSpec (Some (mkGPReg32 (NonSPReg32_base p.1),None)) p.2))
  (fun rm => if rm is RegMemM (mkMemSpec (Some (mkGPReg32 (mkGPReg64 base),None)) offset) then Some(mkNonSPReg32 base,offset) else None)).
elim => //. elim => //. elim => //. move => [x y] z [x' y'].
case: x => // r. case: r => //. move => r'. case: y => //. by move => [<- ->]. Defined.

Definition dispOffsetNoBaseCast s : CAST DWORD (RegMem s).
apply: MakeCast (fun offset => RegMemM s (mkMemSpec None offset))
                (fun rm => if rm is RegMemM (mkMemSpec None offset)
                           then Some offset else None) _.
elim => //. elim => //. by elim => // ? ? [->]. Defined.

Definition RegMemCodec T (regOrOpcodeCodec : Codec T) dword : Codec (T * RegMem dword) :=
    #b"00" .$ regOrOpcodeCodec $ SIBRM .$ (SIBCodec $ always #0 ~~> dispOffsetSIBCast dword)
||| #b"00" .$ regOrOpcodeCodec $ (NonBPNonSPReg32Codec $ always #0 ~~> dispOffsetCast dword)
||| #b"00" .$ regOrOpcodeCodec $ (#b"101" .$ DWORDCodec ~~> dispOffsetNoBaseCast dword)
||| #b"01" .$ regOrOpcodeCodec $ SIBRM .$ (SIBCodec $ shortDWORDCodec ~~> dispOffsetSIBCast dword)
||| #b"01" .$ regOrOpcodeCodec $ (NonSPReg32Codec false $ shortDWORDCodec ~~> dispOffsetCast dword)
||| #b"10" .$ regOrOpcodeCodec $ (SIBRM .$ SIBCodec $ DWORDCodec ~~> dispOffsetSIBCast dword)
||| #b"10" .$ regOrOpcodeCodec $ (NonSPReg32Codec false $ DWORDCodec ~~> dispOffsetCast dword)
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

Definition mkOpSize p b := if b then if p then OpSize2 else OpSize4 else OpSize1.

Definition unDstSrcRMR s : CAST (GPReg s * RegMem s) (DstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR s p.1 y
                              | RegMemM y => DstSrcRM s p.1 y end)
       (fun ds => match ds with DstSrcRR x y => Some (x,RegMemR _ y)
                              | DstSrcRM x y => Some (x,RegMemM _ y)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRR s : CAST (GPReg s * RegMem s) (DstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR s y p.1
                              | RegMemM y => DstSrcMR s y p.1 end)
       (fun ds => match ds with DstSrcRR x y => Some (y, RegMemR _ x)
                              | DstSrcMR x y => Some (y, RegMemM _ x)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRI s : CAST (RegMem s * VWORD s) (DstSrc s).
apply: (MakeCast
       (fun p => match p.1 with RegMemR y => (DstSrcRI s y p.2)
                             | RegMemM y => (DstSrcMI s y p.2) end)
       (fun ds => match ds with DstSrcRI x y => Some (RegMemR _ x, y)
                              | DstSrcMI x y => Some (RegMemM _ x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. by move => ? ? [<- ->]. Defined.

Definition unDstSrcRI s : CAST (GPReg s * VWORD s) (DstSrc s).
apply: (MakeCast (fun p => DstSrcRI _ p.1 p.2)
       (fun ds => match ds with DstSrcRI x y => Some (x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. Defined.

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

Definition opSizePrefixCodec X (c : bool -> Codec X) : Codec X :=
    #x"66" .$ (c true)
||| c false.

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

Definition isENCLU : CAST unit Instr.
apply: MakeCast (fun _ => ENCLU) (fun i => if i is ENCLU then Some tt else None) _; by elim; elim.
Defined.

Definition isENCLS : CAST unit Instr.
apply: MakeCast (fun _ => ENCLS) (fun i => if i is ENCLS then Some tt else None) _; by elim; elim.
Defined.

Definition TgtCodec : Codec Tgt := DWORDCodec ~~> unTgt.
Definition ShortTgtCodec : Codec Tgt := shortDWORDCodec ~~> unTgt.

Definition VAXCodec s : Codec (GPReg s) :=
match s return Codec (GPReg s) with
| OpSize1 => always (AL:Reg8)
| OpSize2 => always (AX:GPReg16)
| OpSize4 => always (EAX:GPReg32)
| OpSize8 => always (RAX:GPReg64)
end.

Definition opcodeWithSizeCodec X (opcode:BYTE) (c : bool -> Codec X) : Codec X :=
  droplsb opcode .$ Cond c.

(*---------------------------------------------------------------------------
    TEST instruction
  ---------------------------------------------------------------------------*)
Definition tryEqOpSize F (s1 s2: OpSize): F s1 -> option (F s2) :=
  match s1, s2 with
  | OpSize1, OpSize1 => fun x => Some x
  | OpSize2, OpSize2 => fun x => Some x
  | OpSize4, OpSize4 => fun x => Some x
  | _, _ => fun x => None
  end. 

Definition unTEST s : CAST (RegMem s * RegImm s) Instr.
apply (MakeCast (fun p => TESTOP s p.1 p.2)
                (fun i => if i is TESTOP s1 x d
  then tryEqOpSize (F:= fun s=> (RegMem s * RegImm s)%type) s (x,d) else None)). 
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined.

Definition TESTCodec :=
  opSizePrefixCodec (fun w =>
    (* Short form for TEST AL/AX/EAX, imm8/imm16/imm32 *)
        opcodeWithSizeCodec #x"A8" (fun d => 
        (VAXCodec (mkOpSize w d) ~~> unRegMemR _) $ (VWORDCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, imm8 | TEST r/m16, r16 | TEST r/m32, r32 *)
    ||| opcodeWithSizeCodec #x"F6" (fun d =>
        RegMemOpCodec #0 (mkOpSize w d) $ (VWORDCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, r8 | TEST r/m16, r16 | TEST r/m32, r32 *)
    ||| opcodeWithSizeCodec #x"84" (fun d =>
        RegMemCodec (VRegCodec _ ~~> unRegImmR _) _ ~~> swapPairCast _ _ ~~> unTEST (mkOpSize w d))
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
||| #b"01010" .$ GPReg32Codec false ~~> unSrcR ~~> unPUSH
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
||| #b"01011" .$ GPReg32Codec false ~~> unRegMemR OpSize4 ~~> unPOP
||| #x"17" .$ always SS ~~> unPOPSegR
||| #x"1F" .$ always DS ~~> unPOPSegR
||| #x"07" .$ always ES ~~> unPOPSegR
||| #x"0F" .$ #x"A1" .$ always FS ~~> unPOPSegR
||| #x"0F" .$ #x"A9" .$ always GS ~~> unPOPSegR.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)
Definition unMOVRMSeg : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVRMSeg p.2 p.1) (fun i => if i is MOVRMSeg x y then Some(y,x) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOVSegRM : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVSegRM p.1 p.2) (fun i => if i is MOVSegRM x y then Some(x,y) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOV w d : CAST (DstSrc (mkOpSize w d)) Instr.
apply (MakeCast (MOVOP _) (fun i => if i is MOVOP _ d then tryEqOpSize _ d else None)). 
by elim:w; elim:d; elim => //; elim => //; move => ? src [->]. 
Defined. 

Definition MOVCodec :=
  opSizePrefixCodec (fun w =>
      (* MOV r/m8, r8 | MOV r/m16, r16 | MOV r/m32, r32 *)
      opcodeWithSizeCodec #x"88" (fun d =>
        RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _ ~~> unMOV w d)
      (* MOV r8, r/m8 | MOV r16, r/m16 | MOV r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"8A" (fun d =>   
        RegMemCodec (VRegCodec _) _  ~~> unDstSrcRMR _ ~~> unMOV w d)
      (* MOV r/m8, imm8 | MOV r/m16, imm16 | MOV r/m32, imm32 *)
  ||| opcodeWithSizeCodec #x"C6" (fun d =>
        RegMemOpCodec #0 _ $ VWORDCodec _ ~~> unDstSrcMRI _ ~~> unMOV w d)
      (* MOV r8, imm8 | MOV r16, imm16 | MOV r32, imm32 *)
  ||| #x"B" .$ Cond (fun d => 
        VRegCodec _ $ VWORDCodec _ ~~> unDstSrcRI _ ~~> unMOV w d)
  )
  (* MOV r/m16, Sreg *)
||| #x"8C" .$ RegMemCodec sreg3Codec _ ~~> unMOVRMSeg

  (* MOV Sreg, r/m16 *)
||| #x"8E" .$ RegMemCodec sreg3Codec _ ~~> unMOVSegRM.

(*---------------------------------------------------------------------------
    MOVX instruction
  ---------------------------------------------------------------------------*)
(*
Definition unMOVZX s : CAST (Reg * RegMem s) Instr.
  apply (MakeCast (fun v => MOVX false _ v.1 v.2)) (RegMemR _ v.2))).
  (fun i => if i is TESTOP os x (RegImmR y) then prefAndOpSizeToBool1 w y x else None) _).
  elim:w; elim => //; elim => //; move => r; elim => // s; move => q H; by inversion H. 
apply: MakeCast (fun p => MOVX false OpSize4 p.1 p.2) (fun i => if i is MOVX false OpSize4 x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? ? [<-]. Defined.

Definition unMOVSX : CAST (Reg * RegMem true) Instr.
apply: MakeCast (fun p => MOVX true true p.1 p.2) (fun i => if i is MOVX true true x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition MOVXCodec :=
    opSizePrefixCodec (fun w => #x"0F" .$ VRegMemRegCodec _ #x"B6" ~~> unMOVZX w)
||| #x"0F" .$ #x"B7" .$ RegMemCodec regCodec true ~~> unMOVZX
||| #x"0F" .$ #x"BE" .$ RegMemCodec regCodec false ~~> unMOVSXB
||| #x"0F" .$ #x"BF" .$ RegMemCodec regCodec true ~~> unMOVSX.
*)

(*---------------------------------------------------------------------------
    BT, BTC, BTR, BTS instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unBITOPR : CAST (BitOp * (GPReg32 * RegMem OpSize4)) Instr.
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
    #x"0F" .$ BITOPPREF .$ bitOpCodec $ BITOPSUFF .$ (RegMemCodec (GPReg32Codec false) _) ~~> unBITOPR
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

Definition unSHIFT s : CAST (ShiftOp * RegMem s * ShiftCount) Instr.
eapply (MakeCast (fun p => let: (op,v,count) := p in SHIFTOP _ op v count)
                 (fun i => if i is SHIFTOP s1 op v count 
  then tryEqOpSize (F:= fun s=> (ShiftOp*RegMem s*ShiftCount)%type) s (op,v,count) else None)).
elim:s; elim => //; elim => //; move => ? ? src [[? ?] ?]; by move => [-> -> ->]. 
Defined.

Definition SHIFTCodec :=
  opSizePrefixCodec (fun w => 
    (
      opcodeWithSizeCodec #x"C0" (fun d => 
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (BYTECodec ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D0" (fun d =>
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (always #1 ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D2" (fun d =>
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (Emp ~~> unShiftCountCL) ~~> unSHIFT _)
    )
  ).

(*---------------------------------------------------------------------------
    ADC/ADD/SUB/SBB/OR/AND/XOR/CMP instructions
  ---------------------------------------------------------------------------*)
Definition unBOP s : CAST (BinOp * DstSrc s) Instr.
apply: (MakeCast (fun p => BOP _ p.1 p.2))
                 (fun i => if i is BOP s1 op v 
                  then tryEqOpSize (F:=fun s => (BinOp*DstSrc s)%type) s (op,v) else None) _.  elim:s; elim => //; elim => //; move => ? src [? ?]; by move => [-> ->]. 
Defined.

Definition shortVWORDEmb w : CAST BYTE (VWORD (if w then OpSize2 else OpSize4)).
destruct w. 
apply: MakeCast (@signExtend 8 7) (@signTruncate 8 7) _.
- move => d b/= H. by apply signTruncateK. 
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
- move => d b/= H. by apply signTruncateK. 
Defined.

Definition shortVWORDCodec w: Codec _ :=
  BYTECodec ~~> shortVWORDEmb w.

Definition BINOPCodec :=
    opSizePrefixCodec (fun w => 
      (* OP AL, imm8 | OP AX, imm16 | OP EAX, imm32 *)
    #b"00" .$ opCodec $ #b"100" .$ 
      (VAXCodec _ $ VWORDCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"101" .$ 
      (VAXCodec _ $ VWORDCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w true)

    (* OP r/m8, r8 | OP r/m16, r16 | OP r/m32, r32 *)
||| #b"00" .$ opCodec $ #b"000" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"001" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w true)

    (* OP r8, r/m8 | OP r16, r/m16 | OP r32, r/m32 *)
||| #b"00" .$ opCodec $ #b"010" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"011" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w true)

    (* OP r/m8, imm8 | OP r/m16, imm16 | OP r/m32, imm32 *)
||| opcodeWithSizeCodec #x"80" (fun d => RegMemCodec opCodec _ $ VWORDCodec _
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP (mkOpSize w d))

    (* OP r/m16, imm8 | OP r/m32, imm8 (sign-extended) *)
||| #x"83" .$ (RegMemCodec opCodec _ $ shortVWORDCodec w) 
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP _ 

    )
.

(*---------------------------------------------------------------------------
    INC/DEC/NOT/NEG instructions
  ---------------------------------------------------------------------------*)
Definition unINC s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_INC v)
                (fun i => if i is UOP s1 OP_INC v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unDEC s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_DEC v)
                (fun i => if i is UOP s1 OP_DEC v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNEG s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_NEG v)
                (fun i => if i is UOP s1 OP_NEG v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNOT s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_NOT v)
                (fun i => if i is UOP s1 OP_NOT v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition UOPCodec :=
  opSizePrefixCodec (fun w => 
    opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec #0 _ ~~> unINC (mkOpSize w d))

||| opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec #1 _ ~~> unDEC (mkOpSize w d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec #2 _ ~~> unNOT (mkOpSize w d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec #3 _ ~~> unNEG (mkOpSize w d))

||| INCPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unINC (mkOpSize w false)
||| DECPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unDEC (mkOpSize w false)
  ).


(*---------------------------------------------------------------------------
    IN/OUT instructions
  ---------------------------------------------------------------------------*)
Definition unINI (w:bool) : CAST (bool*BYTE) Instr.
apply: (MakeCast (fun p => INOP (mkOpSize w p.1) (PortI p.2)) 
       (fun i => if i is INOP os (PortI p) then if prefAndOpSizeToBool w os is Some d then Some(d,p) else None else None) _).
elim: w; elim => //; elim => //; elim => // => ? [? ?] H; by inversion H. Defined.

Definition unOUTI (w:bool) : CAST (bool*BYTE) Instr.
apply: (MakeCast (fun p => OUTOP (mkOpSize w p.1) (PortI p.2)) (fun i => if i is OUTOP os (PortI p) then if prefAndOpSizeToBool w os is Some d then Some(d,p) else None else None) _).
elim: w; elim => //; elim => //; elim => // => ? [? ?] H; by inversion H. Defined.

Definition unINR (w:bool) : CAST bool Instr.
apply: MakeCast (fun p => INOP (mkOpSize w p) PortDX) 
  (fun i => if i is INOP os PortDX then prefAndOpSizeToBool w os else None) _.
elim: w; elim => //; elim => //; elim => // => ? H; by inversion H. 
Defined. 

Definition unOUTR (w:bool) : CAST bool Instr.
apply: MakeCast (fun p => OUTOP (mkOpSize w p) PortDX) 
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
Definition unIMUL : CAST (GPReg32 * RegMem OpSize4) Instr.
apply: (MakeCast (fun p => IMUL p.1 p.2)
                 (fun i => if i is IMUL dst src then Some (dst,src) else None) _).
elim => //. by move => dst src [dst' src'] [<-] ->.  Defined.

Definition unMUL s : CAST (RegMem s) Instr.
apply: (MakeCast (@MUL s)
                 (fun i => if i is MUL s1 v 
                  then tryEqOpSize s v else None) _).  
elim: s; elim => //; elim => //; move => r q H; by inversion H.  
Defined.

Definition MULCodec :=
    (* IMUL r32, r/m32 *)
    #x"0F" .$ #x"AF" .$ RegMemCodec (GPReg32Codec false) _ ~~> unIMUL

    (* MUL r/m8 | MUL r/m16 | MUL r/m32 *)
||| opSizePrefixCodec (fun w => 
    opcodeWithSizeCodec #x"F6" (fun d =>  
    RegMemOpCodec #4 _ ~~> unMUL (mkOpSize w d))).

(*---------------------------------------------------------------------------
    LEA instruction 
  ---------------------------------------------------------------------------*)
Definition unLEA : CAST (GPReg32 * RegMem OpSize4) Instr.
apply: MakeCast (fun p => LEA p.1 p.2) (fun i => if i is LEA x y then Some(x,y) else None) _.
by elim => // ? ? [? ?] [-> ->]. Defined.

Definition LEACodec :=
  #x"8D" .$ RegMemCodec (GPReg32Codec false) _ ~~> unLEA.

(*---------------------------------------------------------------------------
    XCHG instruction 
  ---------------------------------------------------------------------------*)
Definition unXCHG s : CAST (GPReg s * RegMem s) Instr. 
Proof. 
  apply: MakeCast (fun p => XCHG s p.1 p.2) 
  (fun i => if i is XCHG s1 x y 
            then tryEqOpSize (F:=fun s => (GPReg s * RegMem s)%type) s (x,y) else None) _.  
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined. 

Definition XCHGCodec :=
    opSizePrefixCodec (fun w => 
      (* XCHG AX, r16 | XCHG EAX, r32 *)
      #b"10010" .$ VAXCodec _ $ (VRegCodec _ ~~> unRegMemR _) ~~> unXCHG (mkOpSize w true)
      (* XCHG r8, r/m8 | XCHG r16, r/m16 | XCHG r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"86" (fun d =>
        RegMemCodec (VRegCodec _) _ ~~> unXCHG (mkOpSize w d))
  ).

(*---------------------------------------------------------------------------
    All instructions
  ---------------------------------------------------------------------------*)
Definition InstrCodec : Codec Instr :=
(* Nullary operations *)
    #x"F4" ~~> isHLT
||| #x"F5" ~~> isCMC
||| #x"F8" ~~> isCLC
||| #x"F9" ~~> isSTC
||| #x"0F" .$ #x"01" .$ #x "D7" ~~> isENCLU
||| #x"0F" .$ #x"01" .$ #x "CF" ~~> isENCLS
(* Everything else *)
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

Require Import x86proved.reader x86proved.x86.addr.
Corollary InstrCodecRoundtripReader (pc:ADDR) cursor' bits x:
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

Module Examples.
Require Import instrsyntax. Open Scope instr_scope.
(* Doesn't work: need 64-bit REX extensions *)
Definition exinstr := (BOP OpSize8 OP_ADD (DstSrcMR OpSize8 (mkMemSpec (Some (EBX:GPReg32, Some(EDX, S4))) (#x"12345678")) RBP)).
(*
Definition exinstr := (BOP OpSize2 OP_ADD (DstSrcMR OpSize2 (mkMemSpec (Some (EBX:GPReg32, Some(EDX, S4))) (#x"12345678")) BP)).
*)

Compute (bytesToHex (snd (fromBin (if enc InstrCodec exinstr is Some bs then bs else nil)))).

End Examples.
