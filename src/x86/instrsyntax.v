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

Definition VWORDasIMM s : VWORD s -> option (IMM s) :=
  match s with
  | OpSize1 => fun x => Some x
  | OpSize2 => fun x => Some x
  | OpSize4 => fun x => Some x
  | OpSize8 => fun x => None
  end.

Notation "'[' m ']'" :=
  (fromSingletonMemSpec None m)
  (at level 0, m at level 0) : memspec_scope.

Notation "s ':[' m ']'" :=
  (fromSingletonMemSpec (Some s) m)
  (at level 1, m at level 0) : memspec_scope.

Notation "'[' r '+' n ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) None)) n)
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "s ':[' r '+' n ']'" :=
  (mkMemSpec _ (Some s) (Some(mkSIB _ (r:BaseReg _) None)) n)
  (at level 1, r at level 0, n at level 0, format "s :[ r + n ] ") : memspec_scope.

Notation "'[' r '-' n ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) None)) (negB n))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "s ':[' r '-' n ']'" :=
  (mkMemSpec _ (Some s) (Some(mkSIB _ (r:BaseReg _) None)) (negB n))
  (at level 1, r at level 0, n at level 0, format "s :[ r - n ] ") : memspec_scope.

Notation "'[' r '+' i '+' n ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some (i,S1)))) n)
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "s ':[' r '+' i '+' n ']'" :=
  (mkMemSpec _ (Some s) (Some(mkSIB _ (r:BaseReg _) (Some (i,S1)))) n)
  (at level 1, r at level 0, i at level 0, n at level 0, format "s :[ r + i + n ]") : memspec_scope.

Notation "'[' r '+' i '*' '2' ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S2)))) #0)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' '+' n ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S2)))) n)
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '4' ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S4)))) 0)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' '+' n ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S4)))) n)
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '8' ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S8)))) 0)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' '+' n ']'" :=
  (mkMemSpec _ None (Some(mkSIB _ (r:BaseReg _) (Some(i,S8)))) n)
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Open Scope instr_scope.

Bind Scope memspec_scope with MemSpec.

(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)
Inductive UOPArg s :=
| UOPArgR (r: GPReg s) :> UOPArg s 
| UOPArgM a (m:MemSpec a) : UOPArg s.

Coercion UOPArgM4 a (m: MemSpec a) : UOPArg OpSize4 := UOPArgM OpSize4 a m.

Definition makeUOP s op (arg: UOPArg s) :=
  match arg with
  | UOPArgR r => UOP _ op (RegMemR s r)
  | UOPArgM a m => UOP _ op (RegMemM s a m)
  end.

Notation "'NOT' x"
  := (makeUOP _ OP_NOT x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NOT' 'BYTE' 'PTR' m"
  := (UOP OpSize1 OP_NOT (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NOT' 'WORD' 'PTR' m"
  := (UOP OpSize2 OP_NOT (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NOT' 'DWORD' 'PTR' m"
  := (UOP OpSize4 OP_NOT (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NOT' 'QWORD' 'PTR' m"
  := (UOP OpSize8 OP_NOT (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.

Example exNOT1 := NOT WORD PTR [EBX+4].
Example exNOT2 := NOT [EBX+ECX*4+9].
Example exNOT3 := NOT CL. 

Notation "'NEG' x"
  := (makeUOP _ OP_NEG x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NEG' 'BYTE' 'PTR' m"
  := (UOP OpSize1 OP_NEG (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' 'WORD' 'PTR' m"
  := (UOP OpSize2 OP_NEG (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' 'DWORD' 'PTR' m"
  := (UOP OpSize4 OP_NEG (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'NEG' 'QWORD' 'PTR' m"
  := (UOP OpSize8 OP_NEG (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.

Example exNEG1 := NEG [EDI].

Notation "'INC' x"
  := (makeUOP _ OP_INC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'INC' 'BYTE' 'PTR' m"
  := (UOP OpSize1 OP_INC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'INC' 'WORD' 'PTR' m"
  := (UOP OpSize2 OP_INC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'INC' 'DWORD' 'PTR' m"
  := (UOP OpSize4 OP_INC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'INC' 'QWORD' 'PTR' m"
  := (UOP OpSize8 OP_INC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.

Example exINC1 := INC [EAX+ESI*4].
Example exINC2 := INC R12.
Example exINC3 := INC BYTE PTR [ECX + EDI*4 + 78].

Notation "'DEC' x"
  := (makeUOP _ OP_DEC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'DEC' 'BYTE' 'PTR' m"
  := (UOP OpSize1 OP_DEC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' 'WORD' 'PTR' m"
  := (UOP OpSize2 OP_DEC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' 'DWORD' 'PTR' m"
  := (UOP OpSize4 OP_DEC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' 'QWORD' 'PTR' m"
  := (UOP OpSize8 OP_DEC (RegMemM _ _ m%ms)) (m at level 55, at level 60) : instr_scope.

Example exDEC1 := INC DWORD PTR [ECX + EDI*4 + 78].

(*---------------------------------------------------------------------------
    Binary operations
  ---------------------------------------------------------------------------*)
Inductive BOPArg s :=
| BOPArgR (r: GPReg s) :> BOPArg s 
| BOPArgM a (m:MemSpec a) : BOPArg s
| BOPArgI (x: IMM s) :> BOPArg s. 

Coercion BOPArgM4 a (m: MemSpec a) : BOPArg OpSize4 := BOPArgM OpSize4 a m.
Coercion BOPArgI1 (x: BYTE) : BOPArg OpSize1 := BOPArgI OpSize1 x.
Coercion BOPArgI2 (x: WORD) : BOPArg OpSize2 := BOPArgI OpSize2 x.
Coercion BOPArgI4 (x: DWORD) : BOPArg OpSize4 := BOPArgI OpSize4 x.

Definition makeBOP s op dst (src: BOPArg s) :=
  match dst, src with
  | UOPArgR dst, BOPArgR src => BOP s op (DstSrcRR s dst src)
  | UOPArgR dst, BOPArgM a src => BOP s op (DstSrcRM s a dst src)

  | UOPArgR dst, BOPArgI v => BOP s op (DstSrcRI s dst v) 

  | UOPArgM a dst, BOPArgR src => BOP s op (DstSrcMR s a dst src)
  | UOPArgM a dst, BOPArgI v =>  BOP s op (DstSrcMI s a dst v) 
    
  | _, _=> BADINSTR
  end.

Notation "'ADC' x , y" := (makeBOP _ OP_ADC x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_ADC (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_ADC (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_ADC (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_ADC (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_ADC x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_ADC x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_ADC x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADC' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_ADC x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Example exADC1 (x:DWORD) := ADC [EDI], x.
Example exADC2 (x:WORD) := ADC WORD PTR [EDI], x.
Example exADC3 := ADC R10, QWORD PTR [R12 + 4].
Example exADC4 := ADC EAX, [EDI + 4].
Example exADC5 := ADC BL, 10.
Example exADC6 := ADC EAX, (10:DWORD).

Notation "'ADD' x , y" := (makeBOP _ OP_ADD x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_ADD (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_ADD (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_ADD (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_ADD (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_ADD x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_ADD x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_ADD x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_ADD x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.

Example exADD1 := ADD EAX, [EBX + 3].
Example exADD2 := ADD EBX, (12:DWORD).
Example exADD3 := ADD WORD PTR [EBX], CX.
Example exADD4 := ADD R10, QWORD PTR [R13 + 6].
Example exADD5 := ADD R10, ((12:DWORD):IMM OpSize8).

Notation "'SUB' x , y" := (makeBOP _ OP_SUB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_SUB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_SUB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_SUB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_SUB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_SUB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_SUB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_SUB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_SUB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.

Notation "'SBB' x , y" := (makeBOP _ OP_SBB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_SBB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_SBB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_SBB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_SBB (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_SBB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_SBB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_SBB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_SBB x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.


Notation "'AND' x , y" := (makeBOP _ OP_AND x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_AND (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_AND (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_AND (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_AND (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_AND x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_AND x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_AND x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_AND x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.

Notation "'OR' x , y" := (makeBOP _ OP_OR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_OR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_OR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_OR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_OR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_OR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_OR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_OR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_OR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.


Notation "'XOR' x , y" := (makeBOP _ OP_XOR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_XOR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_XOR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_XOR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_XOR (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_XOR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_XOR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_XOR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_XOR x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.


Notation "'CMP' x , y" := (makeBOP _ OP_CMP x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'BYTE' 'PTR' x , y" :=
  (makeBOP OpSize1 OP_CMP (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'WORD' 'PTR' x , y" :=
  (makeBOP OpSize2 OP_CMP (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'DWORD' 'PTR' x , y" :=
  (makeBOP OpSize4 OP_CMP (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'QWORD' 'PTR' x , y" :=
  (makeBOP OpSize8 OP_CMP (UOPArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , 'BYTE' 'PTR' y" :=
  (makeBOP OpSize1 OP_CMP x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , 'WORD' 'PTR' y" :=
  (makeBOP OpSize2 OP_CMP x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , 'DWORD' 'PTR' y" :=
  (makeBOP OpSize4 OP_CMP x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , 'QWORD' 'PTR' y" :=
  (makeBOP OpSize8 OP_CMP x (BOPArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.


Example exCMP1 := CMP BYTE PTR [EDI + ECX*2], (#c"*":IMM OpSize1).

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)
Inductive MOVArg s :=
| MOVArgR (r: GPReg s) :> MOVArg s 
| MOVArgM a (m:MemSpec a) : MOVArg s
| MOVArgI (v: VWORD s) :> MOVArg s.

Coercion MOVArgM4 a (m: MemSpec a) : MOVArg OpSize4 := MOVArgM OpSize4 a m.

Definition makeMOV s dst (src: MOVArg s) :=
  match dst, src with
  | MOVArgR dst, MOVArgR src => MOVOP s (MovDstSrcRR s dst src)
  | MOVArgR dst, MOVArgM a src => MOVOP s (MovDstSrcRM s a dst src)
  | MOVArgR dst, MOVArgI n => MOVOP s (MovDstSrcRI s dst n)
  | MOVArgM a dst, MOVArgR src => MOVOP s (MovDstSrcMR s a dst src)
  | MOVArgM a dst, MOVArgI n => 
    if VWORDasIMM s n is Some v then MOVOP s (MovDstSrcMI s a dst v) 
    else BADINSTR
  | _, _=> BADINSTR
  end.

Notation "'MOV' x , y" := (makeMOV _ x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'BYTE' 'PTR' x , y" :=
  (makeMOV OpSize1 (MOVArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'WORD' 'PTR' x , y" :=
  (makeMOV OpSize2 (MOVArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'DWORD' 'PTR' x , y" :=
  (makeMOV OpSize4 (MOVArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'QWORD' 'PTR' x , y" :=
  (makeMOV OpSize8 (MOVArgM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.

Notation "'MOV' x , 'BYTE' 'PTR' y" :=
  (makeMOV OpSize1 x (MOVArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' x , 'WORD' 'PTR' y" :=
  (makeMOV OpSize2 x (MOVArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' x , 'DWORD' 'PTR' y" :=
  (makeMOV OpSize4 x (MOVArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' x , 'QWORD' 'PTR' y" :=
  (makeMOV OpSize8 x (MOVArgM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.

Notation "'MOVZX' x , y" := (MOVX OpSize1 OpSize4 x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOVSX' x , y" := (MOVX OpSize4 OpSize4 x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

Example exMOV1 := MOV EDI, [ESI].
Example exMOV2 := MOV BYTE PTR [EBX], (3:BYTE).
Example exMOV3 (a:DWORD) := MOV EDI, a.
Example exMOV4 (a:QWORD) := MOV RDI, a. 
Example exMOV5 r := MOV AL, r.
Example exMOV6 := MOV DX, BP. 

(*---------------------------------------------------------------------------
    TEST operations
  ---------------------------------------------------------------------------*)

Notation "'TEST' x , y"       := (TESTOP _  x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'BYTE' 'PTR' x , y":= (TESTOP OpSize1 (RegMemM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'WORD' 'PTR' x , y":= (TESTOP OpSize2 (RegMemM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'DWORD 'PTR' x , y":= (TESTOP OpSize4 (RegMemM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'QWORD' 'PTR' x , y":= (TESTOP OpSize8 (RegMemM _ _ x%ms) y) (x,y at level 55, at level 60) : instr_scope.

Example exTEST1 := TEST AX, BX.
Example exTEST2 := TEST BYTE PTR [EBX+4], AL.
Example exTEST3 := TEST AL, (#2:IMM OpSize1).

(*---------------------------------------------------------------------------
    Shift and rotate
  ---------------------------------------------------------------------------*)

Notation "'SAL' x , c" := (SHIFTOP _ OP_SAL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SAL' x , 'CL'" := (SHIFTOP _ OP_SAL x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'SAR' x , c" := (SHIFTOP _ OP_SAR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SAR' x , 'CL'" := (SHIFTOP _ OP_SAR x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'SHL' x , c" := (SHIFTOP _ OP_SHL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SHL' x , 'CL'" := (SHIFTOP _ OP_SHL x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'SHR' x , c" := (SHIFTOP _ OP_SHR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SHR' x , 'CL'" := (SHIFTOP _ OP_SHR x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'RCL' x , c" := (SHIFTOP _ OP_RCL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'RCL' x , 'CL'" := (SHIFTOP _ OP_RCL x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'RCR' x , c" := (SHIFTOP _ OP_RCR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'RCR' x , 'CL'" := (SHIFTOP _ OP_RCR x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'ROL' x , c" := (SHIFTOP _ OP_ROL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'ROL' x , 'CL'" := (SHIFTOP _ OP_ROL x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.
Notation "'ROR' x , c" := (SHIFTOP _ OP_ROR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'ROR' x , 'CL'" := (SHIFTOP _ OP_ROR x%ms (ShiftCountCL)) (x at level 55, at level 60) : instr_scope.

Example exSAL1 := SAL EAX, CL.
Example exRCL1 := RCL [ESI + 4], 5.

Notation "'IMUL' x , y" := (IMUL x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    LEA
  ---------------------------------------------------------------------------*)
Notation "'LEA' x , y" := (instr.LEA _ x (RegMemM _ _ y%ms)) (x,y at level 55, at level 60) : instr_scope.
Example exLEA1 := LEA EAX, [EBX + ESI*8 + 24].
Example exLEA2 := LEA R12, [R14 + RSI*4].

(*---------------------------------------------------------------------------
    RET
  ---------------------------------------------------------------------------*)
Notation "'RET' x" := (RETOP x) (at level 60, x at level 55) : instr_scope.
Example exRET1 := RET 12.
Example exRET2 := RET 0.

(*---------------------------------------------------------------------------
    IN/OUT
  ---------------------------------------------------------------------------*)
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

