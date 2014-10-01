(*===========================================================================
    Instruction evaluator
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.tuple.
Require Import x86proved.bitsops x86proved.x86.instr x86proved.monad x86proved.reader x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.x86.exn.
Require Import x86proved.common_definitions.

Definition updateZPS {n} (result: BITS n) :=
  do! updateFlagInProcState ZF (result == #0);
  do! updateFlagInProcState PF (lsb result);
  updateFlagInProcState SF (msb result).


Definition evalArithOp {n}
  (f : bool -> BITS n -> BITS n -> bool * BITS n) (arg1 arg2: BITS n)  :=
  let! c = getFlagFromProcState CF;
  let (c, result) := eta_expand (f c arg1 arg2) in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (computeOverflow arg1 arg2 result);
  do! updateZPS result;
  retn result.

Definition evalArithOpNoCarry {n}
  (f : bool -> BITS n -> BITS n -> bool * BITS n) (arg1 arg2: BITS n)  :=
  let (c,result) := eta_expand (f false arg1 arg2) in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (computeOverflow arg1 arg2 result);
  do! updateZPS result;
  retn result.

Definition evalArithUnaryOp {n} (f : BITS n -> bool*BITS n) arg  :=
  let (c,result) := eta_expand (f arg) in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (msb arg != msb result);
  do! updateZPS result;
  retn result.

Definition evalArithUnaryOpNoCarry {n} (f : BITS n -> BITS n) arg  :=
  let result := f arg in
  do! updateFlagInProcState OF (msb arg != msb result);
  do! updateZPS result;
  retn result.

Definition evalLogicalOp {n} (f : BITS n -> BITS n -> BITS n) arg1 arg2 :=
  let result := f arg1 arg2 in
  do! updateFlagInProcState CF false;
  do! updateFlagInProcState OF false;
  do! updateZPS result;
  retn result.

Definition evalBinOp {n} op : BITS n -> BITS n -> ST (BITS n) :=
  match op with
  | OP_ADC => evalArithOp adcB
  | OP_ADD => evalArithOpNoCarry adcB
  | OP_AND => evalLogicalOp andB
  | OP_OR  => evalLogicalOp orB
  | OP_SBB => evalArithOp sbbB
  | OP_SUB => evalArithOpNoCarry sbbB
  | OP_CMP => evalArithOpNoCarry sbbB
  | OP_XOR => evalLogicalOp xorB
  end.

(* Assume that count has been masked already *)
Definition evalShiftOp {n} (op: ShiftOp)(arg: BITS n.+1) (count:BYTE) : ST (BITS n.+1) :=
  let count := toNat count in
  (* If the count is zero then no flags are changed, argument is left alone *)
  if count is 0 then retn arg
  else

  (* Otherwise we mess with the carry flag *)
  let! (o, c, res) =
    match op with
    | OP_ROL => let res:= iter count rolB arg
                in retn (xorb (lsb res) (msb res), lsb res, res)

    | OP_ROR => let res:= iter count rorB arg
                in retn (xorb (msb res) (msb (dropmsb res)), msb res, res)

    | OP_RCL => let! carry = getFlagFromProcState CF;
                let res:= iter count rolB (joinmsb(carry, arg))
                in retn (xorb (lsb res) (msb res), msb res, dropmsb res)

    | OP_RCR => let! carry = getFlagFromProcState CF;
                let res := iter count rorB (joinlsb(arg, carry))
                in retn (xorb (msb res) (msb (dropmsb res)), lsb res, droplsb res)

    | OP_SHL | OP_SAL => let res:= iter count shlB (joinmsb(false,arg))
                in retn (xorb (msb arg) (msb (dropmsb arg)), msb res, dropmsb res)

    | OP_SHR => let res := iter count shrB (joinlsb(arg,false))
                in retn (msb arg, lsb res, droplsb res)

    | OP_SAR => let res := iter count sarB (joinlsb(arg,false))
                in retn (false, lsb res, droplsb res)
    end;
  do! updateFlagInProcState CF c;
  do! (if count is 1 then updateFlagInProcState CF o else forgetFlagInProcState OF);
  retn res.

Definition evalUnaryOp {n} op : BITS n -> ST (BITS n) :=
  match op with
  | OP_INC => evalArithUnaryOpNoCarry incB
  | OP_DEC => evalArithUnaryOpNoCarry decB
  | OP_NOT => fun arg => retn (invB arg)
  | OP_NEG => evalArithUnaryOp (fun arg => (arg != #0, negB arg))
  end.

Definition evalCondition cc : ST bool :=
  match cc with
  | CC_O => getFlagFromProcState OF
  | CC_B => getFlagFromProcState CF
  | CC_Z => getFlagFromProcState ZF
  | CC_BE => let! cf = getFlagFromProcState CF; let! zf = getFlagFromProcState ZF; retn (cf || zf)
  | CC_S => getFlagFromProcState SF
  | CC_P => getFlagFromProcState PF
  | CC_L => let! sf = getFlagFromProcState SF; let! f = getFlagFromProcState OF; retn (xorb sf f)
  | CC_LE =>
    let! sf = getFlagFromProcState SF; let! f = getFlagFromProcState OF; let! zf = getFlagFromProcState ZF;
    retn ((xorb sf f) || zf)
  end.


Definition scaleBy {n} s (d: BITS n) :=
  match s with
  | S1 => d
  | S2 => shlB d
  | S4 => shlB (shlB d)
  | S8 => shlB (shlB (shlB d))
  end.

(* Evaluation functions for various syntactic entities *)
(*Definition evalRegPiece rp :=
  let: AnyRegPiece r b := rp in
  let! d = getRegFromProcState r;
  retn (getRegPiece d b).
*)

Definition evalReg32 (r: Reg32) := 
  let! q = getReg32FromProcState r;
  retn q. 

Require Import fintype.
Definition evalReg64 (r:Reg64) := getReg64FromProcState r. 
Definition evalReg16 := getReg16FromProcState.
Definition evalReg8 := getReg8FromProcState.
Definition evalReg {s:OpSize} : Reg s -> ST (VWORD s) :=
  match s return Reg s -> ST (VWORD s) with
  | OpSize1 => evalReg8
  | OpSize2 => evalReg16
  | OpSize4 => evalReg32
  | OpSize8 => evalReg64
  end.

Definition evalMemSpec m : ST ADDR :=
  match m with
    mkMemSpec optSIB offset =>
    if optSIB is Some(base,ixopt)
    then
      let! baseval = evalReg32 base;
      let p := addB baseval offset in
      if ixopt is Some(index,sc)
      then
        let! indexval = evalReg32 index;
        retn (addB p (scaleBy sc indexval))
      else retn p
    else retn offset
  end.

Definition evalSrc src :=
  match src with
  | SrcI c => retn c
  | SrcR r => evalReg32 r
  | SrcM m =>
    let! p = evalMemSpec m;
    getDWORDFromProcState p
  end.

Definition evalJmpTgt tgt : ST ADDR :=
  match tgt with
  | JmpTgtI (mkTgt r) =>
    let! nextIP = getReg32FromProcState EIP;
    retn (addB nextIP r)
  | JmpTgtR r => let! p = evalReg32 r; retn p
  | JmpTgtM m => evalMemSpec m
  end.

Definition setVRegInProcState {s:OpSize} : Reg s -> VWORD s -> _ :=
  match s with
  | OpSize1 => setReg8InProcState
  | OpSize2 => setReg16InProcState
  | OpSize4 => setReg32InProcState
  | OpSize8 => setReg64InProcState
  end.

Definition evalDstR {s:OpSize} (drop: bool) (r:Reg s) :=
    fun (op : VWORD s -> ST (VWORD s)) =>
    let! rval = evalReg r;
    let! result = op rval;
    if drop then retn tt else setVRegInProcState r result.

Definition evalDstM {s:OpSize} (drop: bool) m
  (op: VWORD s -> ST (VWORD s)) := 
    let! a = evalMemSpec m; 
    let! v = getVWORDFromProcState a;
    let! result = op v; 
    if drop then retn tt
    else setVWORDInProcState a result. 

Definition evalDst {s:OpSize} drop (dst: RegMem s)
  (op: VWORD s -> ST (VWORD s)) :=
  match dst with
  | RegMemR r => evalDstR drop r op
  | RegMemM m => evalDstM drop m op
  end.

Definition evalRegMem {s:OpSize} (rm: RegMem s) :=
  match rm with
  | RegMemR r => evalReg r
  | RegMemM m => let! a = evalMemSpec m; getVWORDFromProcState a
  end.

Definition evalRegMemBYTE (rm: RegMem OpSize1) :=
  match rm with
  | RegMemR r => evalReg8 r
  | RegMemM m => let! a = evalMemSpec m; getBYTEFromProcState a
  end.

Definition evalRegMemWORD (rm: RegMem OpSize2) :=
  match rm with
  | RegMemR r => let! d = evalReg16 r; retn (low 16 d)
  | RegMemM m => let! a = evalMemSpec m; getWORDFromProcState a
  end.


Definition evalRegImm {s} (ri: RegImm s)  :=
  match ri with
  | RegImmR r => evalReg r
  | RegImmI c => retn c
  end.

Definition evalPort (p: Port) :=
  match p with
  | PortI b => retn (zeroExtend 8 b)
  | PortDX => let! d = evalReg32 EDX; retn (low 16 d)
  end.

Definition evalShiftCount (c: ShiftCount) :=
  match c with
  | ShiftCountCL => evalReg8 CL
  | ShiftCountI c => retn c
  end.

Definition evalDstSrc {s} (drop: bool) (ds: DstSrc s)
  (op: VWORD s -> VWORD s -> ST (VWORD s)) :=
  match ds with
  | DstSrcRR dst src =>
    evalDstR drop dst (fun a => let! rval = evalReg src; op a rval)

  | DstSrcRM dst src =>
    evalDstR drop dst (fun v1 => let! a = evalMemSpec src;
                                 let! v2 = getVWORDFromProcState a; op v1 v2)

  | DstSrcMR dst src =>
    evalDstM drop dst (fun a => let! rval = evalReg src; op a rval)

  | DstSrcRI dst c   =>
    evalDstR drop dst (fun a => op a c)

  | DstSrcMI dst c   =>
    evalDstM drop dst (fun a => op a c)
  end.


Definition evalMOV {s} (ds: DstSrc s) :=
  match ds with
  | DstSrcRR dst src =>
    let! v = evalReg src;
    setVRegInProcState dst v

  | DstSrcRM dst src =>
    let! a = evalMemSpec src;
    let! v = getVWORDFromProcState a;
    setVRegInProcState dst v

  | DstSrcMR dst src =>
    let! v = evalReg src;
    let! a = evalMemSpec dst;
    setVWORDInProcState a v

  | DstSrcRI dst v   =>
    setVRegInProcState dst v

  | DstSrcMI dst v   =>
    let! a = evalMemSpec dst;
    setVWORDInProcState a v
  end.



Definition evalPush (v: DWORD) : ST unit :=
  let! oldSP = getReg32FromProcState ESP;
  do! setReg32InProcState ESP (oldSP-#4);
  setDWORDInProcState (oldSP-#4) v.

Definition evalInstr instr : ST unit :=
  match instr with
  | POP dst =>
    let! oldSP = evalReg32 ESP;
    do! evalDst false dst (fun d => getDWORDFromProcState oldSP);
    setReg32InProcState ESP (oldSP+#4)

  | UOP s op dst =>
    evalDst false dst (evalUnaryOp op)

  | MOVOP dword ds =>
    evalMOV ds

  | MOVX signextend OpSize1 dst src =>
    let! v = evalRegMemBYTE src;
    setReg32InProcState dst (if signextend then signExtend n24 v else zeroExtend n24 v)

  | MOVX signextend OpSize2 dst src =>
    let! v = evalRegMemWORD src;
    setReg32InProcState dst (if signextend then signExtend n16 v else zeroExtend n16 v)

    (* @todo akenn: implement bit operations *)
  | BITOP op dst b =>
    raiseExn ExnUD

  | BOP dword op ds =>
    evalDstSrc (match op with OP_CMP => true | _ => false end) ds
    (fun d s => evalBinOp op d s)

  | TESTOP s dst src =>
    evalDst true dst
    (fun d => let! s = evalRegImm src; evalBinOp OP_AND d s)

  | SHIFTOP OpSize8 op dst count =>
    evalDst false dst
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=n63) op d (andB #x"3f" c))

  | SHIFTOP OpSize4 op dst count =>
    evalDst false dst
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=n31) op d (andB #x"1f" c))

  | SHIFTOP OpSize2 op dst count =>
    evalDst false dst
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=n15) op d (andB #x"1f" c))

  | SHIFTOP OpSize1 op dst count =>
    evalDst false dst
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=n7) op d (andB #x"1f" c))

  | IMUL dst src =>
    raiseExn ExnUD

  | MUL OpSize4 src =>
    let! v1 = evalReg32 EAX;
    let! v2 = evalRegMem src;
    let res := fullmulB v1 v2 in
    let cfof := high n32 res == #0 in
    do! setReg32InProcState EAX (low n32 res);
    do! setReg32InProcState EDX (high n32 res);
    do! updateFlagInProcState CF cfof;
    do! updateFlagInProcState OF cfof;
    do! forgetFlagInProcState SF;
    do! forgetFlagInProcState PF;
    forgetFlagInProcState ZF

  | LEA r (RegMemM m) =>
    let! a = evalMemSpec m;
    setReg32InProcState r a

  | LEA r (RegMemR _) =>
    raiseExn ExnUD

  | XCHG s r1 (RegMemR r2) =>
    let! v1 = evalReg r1;
    let! v2 = evalReg r2;
    do! setVRegInProcState r1 v2;
    setVRegInProcState r2 v1

  | XCHG d r (RegMemM ms) =>
    let! v1 = evalReg r;
    let! addr = evalMemSpec ms;
    let! v2 = getVWORDFromProcState addr;
    do! setVRegInProcState r v2;
    setVWORDInProcState addr v1

  | JMPrel src =>
    let! newIP = evalJmpTgt src;
    setReg32InProcState EIP newIP

  | JCCrel cc cv (mkTgt tgt) =>
    let! b = evalCondition cc;
    if b == cv then
      let! oldIP = getReg32FromProcState EIP;
      setReg32InProcState EIP (addB oldIP tgt)
    else
      retn tt

  | CLC =>
    updateFlagInProcState CF false


  | STC =>
    updateFlagInProcState CF true

  | CMC =>
    let! c = getFlagFromProcState CF;
    updateFlagInProcState CF (negb c)

    (* Actually, this should loop *)
  | HLT =>
    retn tt

  | BADINSTR =>
    raiseExn ExnUD

  | PUSH src =>
    let! v = evalSrc src;
    evalPush v

  | CALLrel src =>
    let! oldIP = getReg32FromProcState EIP;
    let! newIP = evalJmpTgt src;
    do! setReg32InProcState EIP newIP;
    evalPush oldIP
(*=evalRET *)
  | RETOP offset =>
    let! oldSP = getReg32FromProcState ESP;
    let! IP' = getDWORDFromProcState oldSP;
    do! setReg32InProcState ESP
      (addB (oldSP+#n4) (zeroExtend 16 offset));
    setReg32InProcState EIP IP'
(*=End *)

  | INOP OpSize1 port =>
    let! p = evalPort port;
    let! d = inputOnChannel p;
    setReg8InProcState AL d

  | OUTOP OpSize1 port =>
    let! p = evalPort port;
    let! data = evalReg8 AL;
    outputOnChannel p data

  | _ =>
    raiseUnspecified

  end.

