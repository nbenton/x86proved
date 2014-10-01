(*===========================================================================
    Instruction type and helpers

    Notation to support Intel-style syntax is defined in instrsyntax.v.

    Instructions are *not* in one-to-one correspondence with binary formats,
    as there may be more than one way of encoding the same instruction e.g.
    - short and long forms for constants (e.g. PUSH constant)
    - special casing (e.g. special forms for EAX/AL register, special form for RET 0)
    - symmetry in direction (e.g. MOV r1, r2 has two encodings)
  ===========================================================================*)
(* We need ssreflect for the [if ... then ... else ...] syntax in an inlineable way. *)
Require Import Ssreflect.ssreflect.
Require Import x86proved.bitsrep x86proved.x86.reg.


(* Memory addressing. Note: using ESP for the index register is illegal *)
(*=MemSpec *)
Inductive Scale := S1 | S2 | S4 | S8.
Inductive MemSpec :=
  mkMemSpec (sib: option (GPReg32 * option (NonSPReg32*Scale)))
            (offset: DWORD).
(*=End *)

(* Register or memory *)
(*=RegMem *)
Inductive RegMem s :=
| RegMemR (r: GPReg s) :> RegMem s
| RegMemM (ms: MemSpec).
Inductive RegImm s :=
| RegImmI (c: VWORD s)
| RegImmR (r: GPReg s).
(*=End *)

Coercion DWORDRegMemM (ms: MemSpec) := RegMemM OpSize4 ms.
Coercion DWORDRegImmI (d: DWORD)    := RegImmI OpSize4 d.

(* Unary ops: immediate, register, or memory source *)
(* Binary ops: five combinations of source and destination *)
(*=Src *)
Inductive Src :=
| SrcI (c: DWORD) :> Src
| SrcM (ms: MemSpec) :> Src
| SrcR (r: GPReg32) :> Src.
Inductive DstSrc (s: OpSize) :=
| DstSrcRR (dst src: GPReg s)
| DstSrcRM (dst: GPReg s) (src: MemSpec)
| DstSrcMR (dst: MemSpec) (src: GPReg s)
| DstSrcRI (dst: GPReg s) (c: VWORD s)
| DstSrcMI (dst: MemSpec) (c: VWORD s).
(*=End *)

(* Jump target: PC-relative offset *)
(* We make this a separate type constructor to pick up type class instances later *)
(* Jump ops: immediate, register, or memory source *)
(*=Tgt *)
Inductive Tgt :=
| mkTgt :> DWORD -> Tgt.
Inductive JmpTgt :=
| JmpTgtI :> Tgt -> JmpTgt
| JmpTgtM :> MemSpec -> JmpTgt
| JmpTgtR :> GPReg32 -> JmpTgt.
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
| MOVOP s (ds: DstSrc s)
| MOVSegRM (dst: SegReg) (src: RegMem OpSize2)
| MOVRMSeg (dst: RegMem OpSize2) (dst: SegReg)
| MOVX (signextend:bool) s (dst: GPReg32) (src: RegMem s)
| SHIFTOP s (op: ShiftOp) (dst: RegMem s) (count: ShiftCount)
| MUL {s} (src: RegMem s)
| IMUL (dst: GPReg32) (src: RegMem OpSize4)
| LEA (reg: GPReg32) (src: RegMem OpSize4)
| XCHG s (reg: GPReg s) (src: RegMem s)
| JCCrel (cc: Condition) (cv: bool) (tgt: Tgt)
| PUSH (src: Src)
| PUSHSegR (r: SegReg)
| POP (dst: RegMem OpSize4)
| POPSegR (r: SegReg)
| CALLrel (tgt: JmpTgt) | JMPrel (tgt: JmpTgt)
| CLC | STC | CMC
| RETOP (size: WORD)
| OUTOP (s: OpSize) (port: Port)
| INOP (s: OpSize) (port: Port)
| HLT | ENCLU | ENCLS | BADINSTR.
(*=End *)
