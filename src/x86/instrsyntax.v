(*===========================================================================
    Notation to simulate Intel x86 instruction syntax
    You can cut-and-paste this notation into inline assembler in VS!
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.seq.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.x86.reg x86proved.x86.addr x86proved.x86.instr.
Require Export Coq.Strings.String.

Delimit Scope instr_scope with asm.
Delimit Scope memspec_scope with ms.

(*---------------------------------------------------------------------------
    MemSpec notation
  ---------------------------------------------------------------------------*)
Inductive SingletonMemSpec :=
| OffsetMemSpec :> DWORD -> SingletonMemSpec
| RegMemSpec :> GPReg32 -> SingletonMemSpec.

Definition fromSingletonMemSpec seg (msa: SingletonMemSpec) :=
  match msa with
  | OffsetMemSpec d => mkMemSpec AdSize4 seg None d
  | RegMemSpec r => mkMemSpec AdSize4 seg (Some (mkSIB _ r None)) (natAsDWORD 0)
  end.

Inductive InstrArg s :=
| InstrArgR (r: GPReg s) :> InstrArg s 
| InstrArgM a (m:MemSpec a) : InstrArg s
| InstrArgI (v: VWORD s) :> InstrArg s.

Definition VWORDasIMM s : VWORD s -> option (IMM s) :=
  match s with
  | OpSize1 => fun x => Some x
  | OpSize2 => fun x => Some x
  | OpSize4 => fun x => Some x
  | OpSize8 => fun x => None
  end.

Notation "'[' m ']'" :=
  (InstrArgM _ _ (fromSingletonMemSpec None m))
  (at level 0, m at level 0) : memspec_scope.

Notation "s ':[' m ']'" :=
  (InstrArgM _ _ (fromSingletonMemSpec (Some s) m))
  (at level 1, m at level 0) : memspec_scope.

Notation "'[' r '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) None)) n))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "s ':[' r '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ (Some s) (Some(mkSIB _ (r:BaseReg _) None)) n))
  (at level 1, r at level 0, n at level 0, format "s :[ r + n ] ") : memspec_scope.

Notation "'[' r '-' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) None)) (negB n)))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "s ':[' r '-' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ (Some s) (Some(mkSIB _ (r:BaseReg _) None)) (negB n)))
  (at level 1, r at level 0, n at level 0, format "s :[ r - n ] ") : memspec_scope.

Notation "'[' r '+' i '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some (i,S1)))) n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "s ':[' r '+' i '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ (Some s) (Some(mkSIB _ (r:BaseReg _) (Some (i,S1)))) n))
  (at level 1, r at level 0, i at level 0, n at level 0, format "s :[ r + i + n ]") : memspec_scope.

Notation "'[' r '+' i '*' '2' ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S2)))) #0))
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S2)))) n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '4' ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S4)))) 0))
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S4)))) n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '8' ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S8)))) 0))
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' '+' n ']'" :=
  (InstrArgM _ _ (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S8)))) n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

(*---------------------------------------------------------------------------
    Binary operations
  ---------------------------------------------------------------------------*)
Definition makeBOP s op dst (src: InstrArg s) :=
  match dst, src with
  | InstrArgR dst, InstrArgR src => BOP s op (DstSrcRR s dst src)
  | InstrArgR dst, InstrArgM a src => BOP s op (DstSrcRM s a dst src)

  | InstrArgR dst, InstrArgI n => 
    if VWORDasIMM s n is Some v then BOP s op (DstSrcRI s dst v) 
    else BADINSTR

  | InstrArgM a dst, InstrArgR src => BOP s op (DstSrcMR s a dst src)
  | InstrArgM a dst, InstrArgI n => 
    if VWORDasIMM s n is Some v then BOP s op (DstSrcMI s a dst v) 
    else BADINSTR
    
  | _, _=> BADINSTR
  end.

Definition makeUOP s op (arg: InstrArg s) :=
  match arg with
  | InstrArgR r => UOP _ op (RegMemR s r)
  | InstrArgM a m => UOP _ op (RegMemM s a m)
  | _ => BADINSTR
  end.

Definition makeLEA s r (arg: InstrArg s) :=
  match arg with
  | InstrArgM a m => LEA s r (RegMemM s a m)
  | _ => BADINSTR
  end.

Open Scope instr_scope.

Bind Scope memspec_scope with MemSpec.

(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)
Notation "'NOT' x"
  := (makeUOP _ OP_NOT x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NOT' 'BYTE' 'PTR' m"
  := (makeUOP OpSize1 OP_NOT m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'NOT' 'WORD' 'PTR' m"
  := (makeUOP OpSize2 OP_NOT m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'NOT' 'DWORD' 'PTR' m"
  := (makeUOP OpSize4 OP_NOT m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'NOT' 'QWORD' 'PTR' m"
  := (makeUOP OpSize8 OP_NOT m%ms) (m at level 55, at level 60) : instr_scope.

Notation "'NEG' x"
  := (makeUOP _ OP_NEG x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NEG' 'BYTE' 'PTR' m"
  := (makeUOP OpSize1 OP_NEG m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' 'WORD' 'PTR' m"
  := (makeUOP OpSize2 OP_NEG m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' 'DWORD' 'PTR' m"
  := (makeUOP OpSize4 OP_NEG m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' 'QWORD' 'PTR' m"
  := (makeUOP OpSize8 OP_NEG m%ms) (m at level 55, at level 60) : instr_scope.

Notation "'INC' x"
  := (makeUOP _ OP_INC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'INC' 'BYTE' 'PTR' m"
  := (makeUOP OpSize1 OP_INC m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'INC' 'WORD' 'PTR' m"
  := (makeUOP OpSize2 OP_INC m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'INC' 'DWORD' 'PTR' m"
  := (makeUOP OpSize4 OP_INC m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'INC' 'QWORD' 'PTR' m"
  := (makeUOP OpSize8 OP_INC m%ms) (m at level 55, at level 60) : instr_scope.

Notation "'DEC' x"
  := (makeUOP _ OP_DEC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'DEC' 'BYTE' 'PTR' m"
  := (makeUOP OpSize1 OP_DEC m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' 'WORD' 'PTR' m"
  := (makeUOP OpSize2 OP_DEC m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' 'DWORD' 'PTR' m"
  := (makeUOP OpSize4 OP_DEC m%ms) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' 'QWORD' 'PTR' m"
  := (makeUOP OpSize8 OP_DEC m%ms) (m at level 55, at level 60) : instr_scope.

Notation "'ADC' x , y" := (makeBOP _ OP_ADC x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_ADC x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , y" := (makeBOP _ OP_ADD x%ms y%ms) (x,y at level 56, at level 60) : instr_scope.
Notation "'ADD' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_ADD x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , y" := (makeBOP _ OP_SUB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_SUB x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , y" := (makeBOP _ OP_SBB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_SBB x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , y" := (makeBOP _ OP_AND x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_AND x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , y" := (makeBOP _ OP_OR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_OR x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , y" := (makeBOP _ OP_XOR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_XOR x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , y" := (makeBOP _ OP_CMP x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_CMP x%ms y) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)
Definition makeMOV s dst (src: InstrArg s) :=
  match dst, src with
  | InstrArgR dst, InstrArgR src => MOVOP s (MovDstSrcRR s dst src)
  | InstrArgR dst, InstrArgM a src => MOVOP s (MovDstSrcRM s a dst src)
  | InstrArgR dst, InstrArgI n => MOVOP s (MovDstSrcRI s dst n)
  | InstrArgM a dst, InstrArgR src => MOVOP s (MovDstSrcMR s a dst src)
  | InstrArgM a dst, InstrArgI n => 
    if VWORDasIMM s n is Some v then MOVOP s (MovDstSrcMI s a dst v) 
    else BADINSTR
  | _, _=> BADINSTR
  end.

Notation "'MOV' x , y" := (makeMOV _ x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'BYTE' 'PTR' x , y" :=
  (makeMOV OpSize1 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'WORD' 'PTR' x , y" :=
  (makeMOV OpSize2 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'DWORD' 'PTR' x , y" :=
  (makeMOV OpSize4 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'QWORD' 'PTR' x , y" :=
  (makeMOV OpSize8 x%ms y) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)

Notation "'TEST' x , y"       := (TESTOP _  x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'BYTE' 'PTR' x , y":= (TESTOP OpSize1 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'WORD' 'PTR' x , y":= (TESTOP OpSize2 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'DWORD 'PTR' x , y":= (TESTOP OpSize4 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'QWORD' 'PTR' x , y":= (TESTOP OpSize8 x%ms y) (x,y at level 55, at level 60) : instr_scope.

Notation "'MOVZX' x , y" := (MOVX OpSize1 OpSize4 x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOVSX' x , y" := (MOVX OpSize4 OpSize4 x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    Shift and rotate
  ---------------------------------------------------------------------------*)

Notation "'SAL' x , c" := (SHIFTOP _ OP_SAL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SAR' x , c" := (SHIFTOP _ OP_SAR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SHL' x , c" := (SHIFTOP _ OP_SHL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SHR' x , c" := (SHIFTOP _ OP_SHR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'RCL' x , c" := (SHIFTOP _ OP_RCL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'RCR' x , c" := (SHIFTOP _ OP_RCR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'ROL' x , c" := (SHIFTOP _ OP_ROL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'ROR' x , c" := (SHIFTOP _ OP_ROR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.

Notation "'IMUL' x , y" := (IMUL x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

Notation "'LEA' x , y" := (makeLEA _ x y%ms) (x,y at level 55, at level 60) : instr_scope.

Notation "'RET' x" := (RETOP x) (at level 60, x at level 55, format "'RET' x") : instr_scope.

Notation "'OUT' 'DX' ',' 'AL'" := (OUTOP OpSize1 PortDX) : instr_scope.
Notation "'OUT' 'DX' ',' 'EAX'" := (OUTOP OpSize4 PortDX) : instr_scope.
Notation "'IN'  'DX' ',' 'AL'" := (INOP OpSize1 PortDX) : instr_scope.
Notation "'IN' 'DX' ',' 'EAX'" := (INOP OpSize4 PortDX) : instr_scope.

Notation "'OUT' x ',' 'AL'" := (OUTOP OpSize1 (PortI x)) : instr_scope.
Notation "'OUT' x ',' 'EAX'" := (OUTOP OpSize4 (PortI x)) : instr_scope.
Notation "'IN'  x ',' 'AL'" := (INOP OpSize1 (PortI x)) : instr_scope.
Notation "'IN' x ',' 'EAX'" := (INOP OpSize4 (PortI x)) : instr_scope.

Definition NOP := XCHG OpSize4 EAX (RegMemR OpSize4 EAX).

Arguments PUSH (src)%ms.
Arguments POP (dst)%ms.

(* Typical use: in "Eval showinstr in linearize p" *)
Declare Reduction showinstr := cbv beta delta -[fromNat makeMOV makeBOP] zeta iota.

Module Examples.
Open Scope instr_scope.

Example ex1 := ADD EAX, [EBX + 3].
Example ex2 := INC BYTE PTR [ECX + EDI*4 + 78].
Example ex2' := INC DWORD PTR [ECX + EDI*4 + 78].
Example ex3 (r:NonSPReg32) := MOV EDI, [r].
Example ex4 (a:DWORD) := MOV EDI, [ESI]. 
Example ex4' (a:DWORD) := MOV BYTE PTR [EBX], natAsBYTE 3.
Example ex5 (a:DWORD) := MOV EDI, a.
Example ex5' (a:QWORD) := MOV RDI, a. 
Example ex11 := CMP BYTE PTR [EDI + ECX*2], #c"*".
Example ex13 := LEA EBP, FS:[RBP + 23].
Example ex6 r := MOV AL, r.
Example ex12 := INC BX.
(*Example ex7 (r:NonSPReg64) := POP [r + #x"0000001C"].*)
Example ex8 := CMP AL, #c"!".
Example ex9 := MOV DX, BP. 
Example ex10 := NOT DWORD PTR [EBX + EDI*4 + 3]. 

Close Scope instr_scope.
End Examples.
