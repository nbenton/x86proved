(*===========================================================================
    Instruction type and helpers
    Instructions abstract the actual machine-code encoding in a number of ways:
    (a) There may be more than one way of encoding the same instruction
        e.g. short forms and long forms
    (b) Jump and call targets are recorded as absolute addresses but might be
        encoded as relative offsets.
    Instructions therefore are *not* position-independent.
  ===========================================================================*)
Require Import bitsrep reg.


(* Memory addressing. Note: using ESP for the index register is illegal *)
(*=MemSpec *)
Inductive Scale := S1 | S2 | S4 | S8.
Inductive MemSpec :=
  mkMemSpec (sib: option (Reg * option (NonSPReg*Scale))) 
            (offset: DWORD).
(*=End *)

(* 8-bit register *)
(*=BYTEReg *)
Inductive BYTEReg := AL|BL|CL|DL|AH|BH|CH|DH.
Definition DWORDorBYTEReg (d: bool) := if d then Reg else BYTEReg.
(*=End *)

(* Register or memory *)
(*=RegMem *)
Inductive RegMem d := 
| RegMemR (r: DWORDorBYTEReg d)
| RegMemM (ms: MemSpec).
Inductive RegImm d :=
| RegImmI (c: DWORDorBYTE d)
| RegImmR (r: DWORDorBYTEReg d).
(*=End *)

Coercion mkRegMemR (r:Reg) := RegMemR true r.

(* Unary ops: immediate, register, or memory source *)
(* Binary ops: five combinations of source and destination *)
(*=Src *)
Inductive Src :=
| SrcI (c: DWORD)
| SrcM (ms: MemSpec)
| SrcR (r: Reg).
Inductive DstSrc (d: bool) :=
| DstSrcRR (dst src: DWORDorBYTEReg d)
| DstSrcRM (dst: DWORDorBYTEReg d) (src: MemSpec)
| DstSrcMR (dst: MemSpec) (src: DWORDorBYTEReg d)
| DstSrcRI (dst: DWORDorBYTEReg d) (c: DWORDorBYTE d)
| DstSrcMI (dst: MemSpec) (c: DWORDorBYTE d).
(*=End *)
Coercion SrcI : DWORD >-> Src.
Coercion SrcR : Reg >-> Src.
Coercion SrcM : MemSpec >-> Src.
(* Jump target: PC-relative offset *)
(* We make this a separate type constructor to pick up type class instances later *)
(* Jump ops: immediate, register, or memory source *)
(*=Tgt *)
Inductive Tgt := 
| mkTgt :> DWORD -> Tgt.
Inductive JmpTgt :=
| JmpTgtI :> Tgt -> JmpTgt
| JmpTgtM :> MemSpec -> JmpTgt
| JmpTgtR :> Reg -> JmpTgt.
Inductive ShiftCount :=
| ShiftCountCL | ShiftCountI (c: BYTE).
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
| UOP d (op: UnaryOp) (dst: RegMem d)
| BOP d (op: BinOp ) (ds: DstSrc d)
| BITOP (op: BitOp) (dst: RegMem true) (bit: Reg + BYTE)
| TESTOP d (dst: RegMem d) (src: RegImm d)
| MOVOP d (ds: DstSrc d)
| MOVX (signextend w:bool) (dst: Reg) (src: RegMem w)
| SHIFTOP d (op: ShiftOp) (dst: RegMem d) (count: ShiftCount)
| MUL {d} (src: RegMem d)
| IMUL (dst: Reg) (src: RegMem true) 
| LEA (reg: Reg) (src: RegMem true) 
| XCHG d (reg: DWORDorBYTEReg d) (src: RegMem d)
| JCCrel (cc: Condition) (cv: bool) (tgt: Tgt)
| PUSH (src: Src)
| POP (dst: RegMem true)
| CALLrel (tgt: JmpTgt) | JMPrel (tgt: JmpTgt)
| CLC | STC | CMC 
| RETOP (size: WORD)
| OUT (d: bool) (port: BYTE)
| IN (d: bool) (port: BYTE)
| HLT | BADINSTR.
(*=End *)


