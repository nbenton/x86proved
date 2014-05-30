(*===========================================================================
    Notation to simulate Intel x86 instruction syntax
    You can cut-and-paste this notation into inline assembler in VS!
  ===========================================================================*)
Require Import ssreflect ssrbool seq.
Require Import bitsrep bitsops reg instr.
Require Export String.

Delimit Scope instr_scope with asm. 
Delimit Scope memspec_scope with ms.

(*---------------------------------------------------------------------------
    MemSpec notation
  ---------------------------------------------------------------------------*)
Inductive SingletonMemSpec :=
| OffsetMemSpec :> DWORD -> SingletonMemSpec
| RegMemSpec :> Reg -> SingletonMemSpec.

Definition fromSingletonMemSpec (msa: SingletonMemSpec) :=
  match msa with
  | OffsetMemSpec d => mkMemSpec None d
  | RegMemSpec r => mkMemSpec (Some(r,None)) 0
  end.

Notation "'[' m ']'" := 
  (fromSingletonMemSpec m)
  (at level 0, m at level 0) : memspec_scope.

Notation "'[' r '+' n ']'" := 
  (mkMemSpec (Some(r:Reg, None)) n)
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "'[' r '-' n ']'" := 
  (mkMemSpec (Some(r:Reg, None)) (negB n)) 
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '+' n ']'" := 
  (mkMemSpec (Some(r:Reg, Some (i,S1))) n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '2' ']'" := 
  (mkMemSpec (Some(r:Reg, Some(i,S2))) #0) 
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' '+' n ']'" := 
  (mkMemSpec (Some(r:Reg, Some(i,S2))) n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '4' ']'" := 
  (mkMemSpec (Some(r:Reg, Some(i,S4))) 0) 
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' '+' n ']'" := 
  (mkMemSpec (Some(r:Reg, Some(i,S4))) n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '8' ']'" := 
  (mkMemSpec (Some(r:Reg, Some(i,S8))) 0) 
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' '+' n ']'" := 
  (mkMemSpec (Some(r:Reg, Some(i,S8))) n) 
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Definition DWORDtoDWORDorBYTE dword : DWORD -> DWORDorBYTE dword :=
  match dword return DWORD -> DWORDorBYTE dword 
  with true => fun d => d | false =>fun d => low 8 d end. 

Inductive InstrArg :=
| BYTERegArg :> BYTEReg -> InstrArg
| RegArg :> Reg -> InstrArg
| MemSpecArg :> MemSpec -> InstrArg.

Inductive InstrSrc :=
| ArgSrc :> InstrArg -> InstrSrc
| ConstSrc :> DWORD -> InstrSrc.

Definition SrcToRegImm src :=
  match src with
  | SrcI c => RegImmI true c
  | SrcR r => RegImmR true r
  (* Don't do it! *)
  | SrcM m => RegImmI _ (#0: DWORDorBYTE true)
  end.

Bind Scope memspec_scope with MemSpec.  

(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)
Definition makeUOP op (i: InstrArg) :=
  match i with
  | BYTERegArg r => UOP false op (RegMemR false r)
  | RegArg r => UOP true op (RegMemR true r)
  | MemSpecArg ms => UOP true op (RegMemM true ms)
  end.

Notation "'NOT' x"          
  := (makeUOP OP_NOT x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NOT' 'BYTE' m"   
  := (UOP false OP_NOT (RegMemM false m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' x"          
  := (makeUOP OP_NEG x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NEG' 'BYTE' m"   
  := (UOP false OP_NEG (RegMemM false m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'INC' x"          
  := (makeUOP OP_INC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'INC' 'BYTE' m"   
  := (UOP false OP_INC (RegMemM false m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' x"          
  := (makeUOP OP_DEC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'DEC' 'BYTE' m"   
  := (UOP false OP_DEC (RegMemM false m%ms)) (m at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    Binary operations
  ---------------------------------------------------------------------------*)
Definition makeBOP op dst (src: InstrSrc) := 
  match dst, src with
  | BYTERegArg dst, BYTERegArg src => BOP false op (DstSrcRR false dst src)
  | BYTERegArg dst, MemSpecArg src => BOP false op (DstSrcRM false dst src)
  | RegArg dst, RegArg src => BOP true op (DstSrcRR true dst src)
  | BYTERegArg dst, ConstSrc n => BOP false op (DstSrcRI false dst (low 8 n))
  | RegArg dst, ConstSrc n => BOP true op (DstSrcRI true dst n)
  | MemSpecArg dst, RegArg src => BOP true op (DstSrcMR true dst src)
  | MemSpecArg dst, BYTERegArg src => BOP false op (DstSrcMR false dst src)
  | RegArg dst, MemSpecArg src => BOP true op (DstSrcRM true dst src)
  | MemSpecArg dst, ConstSrc n => BOP true op (DstSrcMI true dst n)
  | _, _=> BADINSTR
  end.

Notation "'ADC' x , y" := (makeBOP OP_ADC x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , y" := (makeBOP OP_ADD x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , y" := (makeBOP OP_SUB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , y" := (makeBOP OP_SBB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , y" := (makeBOP OP_AND x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , y" := (makeBOP OP_OR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , y" := (makeBOP OP_XOR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , y" := (makeBOP OP_CMP x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

(* Only need byte modifier for constant source, memspec destination *) 
Notation "'ADC' 'BYTE' x , y" := 
  (BOP false OP_ADC (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' 'BYTE' x , y" := 
  (BOP false OP_ADD (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'BYTE' x , y" := 
  (BOP false OP_SUB (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'BYTE' x , y" := 
  (BOP false OP_SBB (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'BYTE' x , y" := 
  (BOP false OP_AND (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'BYTE' x , y" := 
  (BOP false OP_OR (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'BYTE' x , y" := 
  (BOP false OP_XOR (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'BYTE' x , y" := 
  (BOP false OP_CMP (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)
Definition makeMOV dst (src: InstrSrc) := 
  match dst, src with
  | BYTERegArg dst, BYTERegArg src => MOVOP false (DstSrcRR false dst src)
  | BYTERegArg dst, MemSpecArg src => MOVOP false (DstSrcRM false dst src)
  | RegArg dst, RegArg src => MOVOP true (DstSrcRR true dst src)
  | BYTERegArg dst, ConstSrc n => MOVOP false (DstSrcRI false dst (low 8 n))
  | RegArg dst, ConstSrc n => MOVOP true (DstSrcRI true dst n)
  | MemSpecArg dst, RegArg src => MOVOP true (DstSrcMR true dst src)
  | MemSpecArg dst, BYTERegArg src => MOVOP false (DstSrcMR false dst src)
  | RegArg dst, MemSpecArg src => MOVOP true (DstSrcRM true dst src)
  | MemSpecArg dst, ConstSrc n => MOVOP true (DstSrcMI true dst n)
  | _, _=> BADINSTR
  end.

Notation "'MOV' x , y" := (makeMOV x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'BYTE' x , y" := 
  (MOVOP false (DstSrcMI false x%ms y)) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)

Notation "'TEST' x , y"       := (TESTOP true  x%ms (SrcToRegImm y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'BYTE' x , y":= (TESTOP false x%ms (SrcToRegImm y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOVZX' x , y" := (MOVX false true x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOVSX' x , y" := (MOVX true true x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

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

Notation "'LEA' x , y" := (LEA x (RegMemM true y%ms)) (x,y at level 55, at level 60) : instr_scope.

Notation "'RET' x" := (RETOP x) (at level 60, x at level 55, format "'RET' x") : instr_scope. 

Definition NOP := XCHG true EAX (RegMemR true EAX).

Arguments PUSH (src)%ms.
Arguments POP (dst)%ms.

(* Typical use: in "Eval showinstr in linearize p" *)
Declare Reduction showinstr := cbv beta delta -[fromNat makeMOV makeUOP makeBOP] zeta iota.

Module Examples.
Open Scope instr_scope.

Example ex1 := ADD EAX, [EBX + 3]. 
Example ex2 := INC BYTE [ECX + EDI*4 + 78].
Example ex3 (r:Reg) := MOV EDI, [r]. 
Example ex4 (a:DWORD) := MOV EDI, [a]. 
Example ex5 (a:DWORD) := MOV EDI, a.
Example ex6 (r:BYTEReg) := MOV AL, r. 
Example ex7 (r:Reg) := POP [r + #x"0000001C"].
Example ex8 := CMP AL, (#c"!":BYTE).

Close Scope instr_scope.
End Examples.

