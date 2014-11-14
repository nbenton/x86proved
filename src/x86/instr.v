(*===========================================================================
    Instruction type and helpers

    Notation to support Intel-style syntax is defined in instrsyntax.v.

    Instructions are *not* in one-to-one correspondence with binary formats,
    as there may be more than one way of encoding the same instruction e.g.
    - short and long forms for constants (e.g. PUSH constant)
    - special casing (e.g. special forms for EAX/AL register, special form for RET 0)
    - symmetry in direction (e.g. MOV r1, r2 has two encodings)

    It is currently assumed that the processor is operating in IA-32e mode,
    and that the code segment descriptor has the following settings:

    - CS.L=1 and CS.D=0
      i.e. we are in 64-bit mode with default operand size of 32 bits and
      default address size of 64 bits

    See Section 5.2.1 of Intel spec for more details.
  ===========================================================================*)
(* We need ssreflect for the [if ... then ... else ...] syntax in an inlineable way. *)
Require Import Ssreflect.ssreflect.
Require Import x86proved.bitsrep x86proved.x86.addr x86proved.x86.reg.


(* Memory addressing. Note: using ESP for the index register is illegal *)
Definition BaseReg a := GPReg (adSizeToOpSize a).
Coercion GPReg32_to_BaseReg32 (r:GPReg32) : BaseReg AdSize4 := r.
Coercion NonSPReg32_to_BaseReg32 (r:NonSPReg32) : BaseReg AdSize4 := r.
Coercion GPReg64_to_BaseReg64 (r:GPReg64) : BaseReg AdSize8 := r.
Coercion NonSPReg64_to_BaseReg64 (r:NonSPReg64) : BaseReg AdSize8 := r.

Definition IxReg a := NonSPReg (adSizeToOpSize a).
Coercion NonSPReg32_to_IxReg32 (r:NonSPReg32) : IxReg AdSize4 := r.
Coercion NonSPReg64_to_IxReg64 (r:NonSPReg64) : IxReg AdSize8 := r.

(*=MemSpec *)
Inductive Scale := S1 | S2 | S4 | S8.
Inductive SIB a := 
| mkSIB (base: BaseReg a) (ixdisp: option (IxReg a * Scale))
| RIPrel.
Inductive MemSpec (a: AdSize) :=
| mkMemSpec (seg: option SegReg) (sib: option (SIB a)) (displacement: DWORD).
(*=End *)

(* Immediates are maximum 32-bits, sign-extended to 64-bit if necessary *)
Definition IMM s := 
  BITS (match s with OpSize1 => n8 | OpSize2 => n16 | OpSize4 => n32 | OpSize8 => n32 end).

(* Register or memory *)
(*=RegMem *)
Inductive RegMem s :=
| RegMemR (r: GPReg s) :> RegMem s 
| RegMemM a (ms: MemSpec a).
Inductive RegImm s :=
| RegImmI (c: IMM s)
| RegImmR (r: GPReg s) :> RegImm s.
(*=End *)

Coercion DWORDRegMemM a (ms: MemSpec a) := RegMemM OpSize4 a ms.
Coercion DWORDRegImmI (d: DWORD)    := RegImmI OpSize4 d.

(* Unary ops: immediate, register, or memory source *)
(* Binary ops: five combinations of source and destination *)
(*=Src *)
Inductive Src :=
| SrcI (c: DWORD) :> Src
| SrcM a (ms: MemSpec a) :> Src 
| SrcR (r: GPReg64) :> Src.
Inductive DstSrc (s: OpSize):=
| DstSrcRR (dst src: GPReg s)
| DstSrcRM a (dst: GPReg s) (src: MemSpec a)
| DstSrcMR a (dst: MemSpec a) (src: GPReg s)
| DstSrcRI (dst: GPReg s) (c: IMM s)
| DstSrcMI a (dst: MemSpec a) (c: IMM s).
(*=End *)

Inductive MovDstSrc (s: OpSize):=
| MovDstSrcRR (dst src: GPReg s)
| MovDstSrcRM a (dst: GPReg s) (src: MemSpec a)
| MovDstSrcMR a (dst: MemSpec a) (src: GPReg s)
| MovDstSrcRI (dst: GPReg s) (c: VWORD s)
| MovDstSrcMI a (dst: MemSpec a) (c: IMM s).

(* Jump target: PC-relative offset *)
(* We make this a separate type constructor to pick up type class instances later *)
(* Jump ops: immediate, register, or memory source *)
(*=Tgt *)
Inductive Tgt a :=
| mkTgt :> VWORD (adSizeToOpSize a) -> Tgt a.
Inductive JmpTgt a :=
| JmpTgtI (t:Tgt a) :> JmpTgt a
| JmpTgtRegMem (rm: RegMem (adSizeToOpSize a)) :> JmpTgt a.
Inductive ShiftCount :=
| ShiftCountCL | ShiftCountI (c: BYTE).
Inductive Port :=
| PortI :> BYTE -> Port
| PortDX : Port.
(*=End *)


(* All binary operations come in byte and dword flavours, specified in the instruction *)
(* Unary operations come in byte and dword flavours, except for POP *)
(*=BinOp *)
Inductive BinOp :=
| OP_ADC | OP_ADD | OP_AND | OP_CMP | OP_OR | OP_SBB | OP_SUB | OP_XOR.
Inductive UnaryOp :=
| OP_INC | OP_DEC | OP_NOT | OP_NEG.
Inductive BitOp :=
| OP_BT | OP_BTC | OP_BTR | OP_BTS.
Inductive ShiftOp :=
| OP_ROL | OP_ROR | OP_RCL | OP_RCR | OP_SHL | OP_SHR | OP_SAL | OP_SAR.
(*=End *)

(*=Condition *)
Inductive Condition :=
| CC_O | CC_B | CC_Z | CC_BE | CC_S | CC_P | CC_L | CC_LE.
(*=End *)

(* dword=true if 32-bits, dword=false if 8-bits *)
(*=Instr *)
Inductive Instr :=
| UOP s (op: UnaryOp) (dst: RegMem s)
| BOP s (op: BinOp) (ds: DstSrc s)
| BITOP (op: BitOp) (dst: RegMem OpSize4) (bit: GPReg32 + BYTE)
| TESTOP s (dst: RegMem s) (src: RegImm s)
| MOVOP s (ds: MovDstSrc s)
| MOVSegRM (dst: SegReg) (src: RegMem OpSize2)
| MOVRMSeg (dst: RegMem OpSize2) (dst: SegReg)
| MOVX (signextend:bool) s (dst: GPReg32) (src: RegMem s)
| SHIFTOP s (op: ShiftOp) (dst: RegMem s) (count: ShiftCount)
| MUL {s} (src: RegMem s)
| IMUL (dst: GPReg32) (src: RegMem OpSize4)
| LEA s (reg: GPReg s) (src: RegMem s)
| XCHG s (reg: GPReg s) (src: RegMem s)
| JCCrel (cc: Condition) (cv: bool) (tgt: Tgt AdSize8)
| PUSH (src: Src)
| PUSHSegR (r: SegReg)
| POP (dst: RegMem OpSize8)
| POPSegR (r: SegReg)
| CALLrel a (tgt: JmpTgt a) | JMPrel a (tgt: JmpTgt a)
| CLC | STC | CMC
| RETOP (size: WORD)
| OUTOP (s: OpSize) (port: Port)
| INOP (s: OpSize) (port: Port)
| HLT | ENCLU | ENCLS | BADINSTR.
(*=End *)
