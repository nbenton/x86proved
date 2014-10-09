(*===========================================================================
    Instruction evaluator

    It is currently assumed that the processor is operating in IA-32e mode,
    and that the code segment descriptor has the following settings:

    - CS.L=1 and CS.D=0
      i.e. we are in 64-bit mode with default operand size of 32 bits and
      default address size of 64 bits

    See Section 5.2.1 of Intel spec for more details.
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

(* Base register for effective address calculation *)
Definition evalBaseReg {a} : BaseReg a -> ST (ADR a) :=
  match a return BaseReg a -> ST (ADR a) with
  | AdSize4 => getRegFromProcState
  | AdSize8 => getRegFromProcState
  end.

(* Index register for effective address calculation *)
Definition evalIxReg {a} : IxReg a -> ST (ADR a) :=
  match a return IxReg a -> ST (ADR a) with
  | AdSize4 => getRegFromProcState
  | AdSize8 => getRegFromProcState
  end.

(* Displacement for effective address calculation. Note that this is sign-extended to 64-bits *)
Definition computeDisplacement a : DWORD -> ADR a :=
  match a return DWORD -> ADR a with 
  | AdSize4 => fun x => x
  | AdSize8 => fun x => signExtend _ x
  end.

(* Compute the effective address, given a base and signed 32-bit displacement *)
Definition computeAdr {a} (base: ADR a) (displacement:DWORD) : ADR a :=
  addB base (computeDisplacement a displacement).

(* Compute the effective address, given a base, index and signed 32-bit displacement *)
Definition computeIxAdr {a} (base: ADR a) (displacement:DWORD) (ix: ADR a) : ADR a :=
  addB (computeAdr base displacement) ix.

Definition computeAddr {a} (base: ADR a) (displacement:DWORD) : ADDR :=
  ADRtoADDR (computeAdr base displacement). 

Definition computeIxAddr {a} (base: ADR a) (displacement:DWORD) (ix: ADR a) : ADDR :=
  ADRtoADDR (computeIxAdr base displacement ix).

Definition getUIP a := 
  match a return ST (ADR a) with
  | AdSize4 => getRegFromProcState EIP
  | AdSize8 => getRegFromProcState RIP
  end.

Definition evalMemSpec {a} (m:MemSpec a) : ST ADDR :=
  match m with
    mkMemSpec optSIB displacement =>
    if optSIB is Some SIB
    then
      match SIB with
      | mkSIB base ixopt =>
        let! baseval = evalBaseReg base;
        if ixopt is Some(index,sc)
        then
          let! indexval = evalIxReg index;
          retn (computeIxAddr baseval displacement (scaleBy sc indexval))
        else 
          retn (computeAddr baseval displacement)
      | RIPrel =>
        let! baseval = getUIP a;
        retn (computeAddr baseval displacement)
      end
    else retn (ADRtoADDR (computeDisplacement a displacement))
  end.

Definition evalSrc src :=
  match src with
  | SrcI c => retn (signExtend _ c)
  | SrcR r => getRegFromProcState r
  | SrcM a m =>
    let! p = evalMemSpec m;
    getFromProcState p
  end.

Definition setARegInProcState {a} : BaseReg a -> ADR a -> ST unit :=
  match a with
  | AdSize4 => setRegInProcState
  | AdSize8 => setRegInProcState
  end.


Definition evalDstR {s} (drop: bool) (r:Reg s) :=
    fun (op : VWORD s -> ST (VWORD s)) =>
    let! rval = getRegFromProcState r;
    let! result = op rval;
    if drop then retn tt else setRegInProcState r result.

Definition evalDstM {s a} (drop: bool) (m: MemSpec a)
  (op: VWORD s -> ST (VWORD s)) := 
    let! addr = evalMemSpec m; 
    let! v = getFromProcState addr;
    let! result = op v; 
    if drop then retn tt
    else setInProcState addr result. 

Definition evalDst {s} drop (dst: RegMem s)
  (op: VWORD s -> ST (VWORD s)) :=
  match dst with
  | RegMemR r => evalDstR drop r op
  | RegMemM a m => evalDstM drop m op
  end.

Definition evalRegMem {s} (rm: RegMem s) :=
  match rm with
  | RegMemR r => getRegFromProcState r
  | RegMemM a m => let! addr = evalMemSpec m; getFromProcState addr
  end.

Definition evalRegMemBYTE (rm: RegMem OpSize1) :=
  match rm with
  | RegMemR r => getRegFromProcState r
  | RegMemM a m => let! addr = evalMemSpec m; getFromProcState addr
  end.

Definition evalRegMemWORD (rm: RegMem OpSize2) :=
  match rm with
  | RegMemR r => let! d = getRegFromProcState r; retn (low 16 d)
  | RegMemM a m => let! addr = evalMemSpec m; getFromProcState addr
  end.

Definition evalJmpTgt tgt : ST ADDR :=
  match tgt with
  | JmpTgtI (mkTgt r) =>
    let! nextIP = getRegFromProcState UIP;
    retn (addB nextIP (signExtend _ r))
  | JmpTgtRegMem rm => evalRegMem rm
  end.

Definition getImm {s} : IMM s -> VWORD s :=
  match s with
  | OpSize8 => fun c => signExtend _ c
  | _ => fun c => c
  end.

Definition evalRegImm {s} (ri: RegImm s) : ST (VWORD s)  :=
  match ri with
  | RegImmR r => getRegFromProcState r
  | RegImmI c => retn (getImm c)
  end.

Definition evalPort (p: Port) :=
  match p with
  | PortI b => retn (zeroExtend _ b)
  | PortDX => let! d = getRegFromProcState EDX; retn (low 16 d)
  end.

Definition evalShiftCount (c: ShiftCount) :=
  match c with
  | ShiftCountCL => getRegFromProcState CL
  | ShiftCountI c => retn c
  end.

Definition evalDstSrc {s} (drop: bool) (ds: DstSrc s)
  (op: VWORD s -> VWORD s -> ST (VWORD s)) :=
  match ds with
  | DstSrcRR dst src =>
    evalDstR drop dst (fun a => let! rval = getRegFromProcState src; op a rval)

  | DstSrcRM a dst src =>
    evalDstR drop dst (fun v1 => let! addr = evalMemSpec src;
                                 let! v2 = getFromProcState addr; op v1 v2)

  | DstSrcMR a dst src =>
    evalDstM drop dst (fun v => let! rval = getRegFromProcState src; op v rval)

  | DstSrcRI dst c   =>
    evalDstR drop dst (fun v => op v (getImm c))

  | DstSrcMI a dst c   =>
    evalDstM drop dst (fun v => op v (getImm c))
  end.


Definition evalMOV {s} (ds: DstSrc s) :=
  match ds with
  | DstSrcRR dst src =>
    let! v = getRegFromProcState src;
    setRegInProcState dst v

  | DstSrcRM a dst src =>
    let! addr = evalMemSpec src;
    let! v = getFromProcState addr;
    setRegInProcState dst v

  | DstSrcMR a dst src =>
    let! v = getRegFromProcState src;
    let! addr = evalMemSpec dst;
    setInProcState addr v

  | DstSrcRI dst c   =>
    setRegInProcState dst (getImm c)

  | DstSrcMI a dst c   =>
    let! addr = evalMemSpec dst;
    setInProcState addr (getImm c)
  end.



(* Push a value on the stack *)
Definition evalPush {s} (v: VWORD s) : ST unit :=
  let! oldSP = getRegFromProcState USP;
  let newSP := oldSP -#(opSizeToNat s) in
  do! setRegInProcState USP newSP;
  setInProcState newSP v.

Definition evalPop {s} (f: VWORD s -> ST unit) : ST unit :=
  let! oldSP = getRegFromProcState USP;
  let newSP := oldSP +#(opSizeToNat s) in
  let! v = getFromProcState oldSP;
  do! f v;
  setRegInProcState USP newSP.

Definition evalInstr instr : ST unit :=
  match instr with
  | POP dst =>
    evalPop (fun v => evalDst false dst (fun _ => retn v))

  | UOP s op dst =>
    evalDst false dst (evalUnaryOp op)

  | MOVOP dword ds =>
    evalMOV ds

  | MOVX signextend OpSize1 dst src =>
    let! v = evalRegMemBYTE src;
    setRegInProcState dst (if signextend then signExtend _ v else zeroExtend _ v)

  | MOVX signextend OpSize2 dst src =>
    let! v = evalRegMemWORD src;
    setRegInProcState dst (if signextend then signExtend _ v else zeroExtend _ v)

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
    let! v1 = getRegFromProcState EAX;
    let! v2 = evalRegMem src;
    let res := fullmulB v1 v2 in
    let cfof := high n32 res == #0 in
    do! setRegInProcState EAX (low n32 res);
    do! setRegInProcState EDX (high n32 res);
    do! updateFlagInProcState CF cfof;
    do! updateFlagInProcState OF cfof;
    do! forgetFlagInProcState SF;
    do! forgetFlagInProcState PF;
    forgetFlagInProcState ZF

(*
  @TODO: restore this; operand/address size stuff is hairy
  | LEA s a r m =>
    let! addr = evalMemSpec m;
    setVRegInProcState r addr
*)

  | XCHG s r1 (RegMemR r2) =>
    let! v1 = getRegFromProcState r1;
    let! v2 = getRegFromProcState r2;
    do! setRegInProcState r1 v2;
    setRegInProcState r2 v1

  | XCHG d r (RegMemM a ms) =>
    let! v1 = getRegFromProcState r;
    let! addr = evalMemSpec ms;
    let! v2 = getFromProcState addr;
    do! setRegInProcState r v2;
    setInProcState addr v1

  | JMPrel src =>
    let! newIP = evalJmpTgt src;
    setRegInProcState UIP newIP

  | JCCrel cc cv (mkTgt tgt) =>
    let! b = evalCondition cc;
    if b == cv then
      let! oldIP = getRegFromProcState UIP;
      setRegInProcState UIP (addB oldIP (signExtend _ tgt))
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
    evalPush (s:=OpSize8) v

  | CALLrel src =>
    let! oldIP = getRegFromProcState UIP;
    let! newIP = evalJmpTgt src;
    do! setRegInProcState UIP newIP;
    evalPush oldIP
(*=evalRET *)
  | RETOP offset =>
    let! oldSP = getRegFromProcState USP;
    let! IP' = getFromProcState oldSP;
    do! setRegInProcState USP
      (addB (oldSP+#8) (zeroExtend _ offset));
    setRegInProcState UIP IP'
(*=End *)

  | INOP OpSize1 port =>
    let! p = evalPort port;
    let! d = inputOnChannel p;
    setRegInProcState AL d

  | OUTOP OpSize1 port =>
    let! p = evalPort port;
    let! data = getRegFromProcState AL;
    outputOnChannel p data

  | _ =>
    raiseUnspecified

  end.


