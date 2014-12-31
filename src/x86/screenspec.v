(*===========================================================================
  Specification of CGA screen functions
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrcodec x86proved.reader x86proved.cursor x86proved.x86.instrrules.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This should be hidden behind an abstraction *)
Definition screenBase: ADR AdSize4 := #x"000b8000".
Definition numCols := 80.
Definition numRows := 50.
Definition screenLimit : ADR AdSize4 := screenBase +# numCols*numRows*2.
Definition screenMapped := memAny (ADRtoADDR screenBase) (ADRtoADDR screenLimit).

Definition charPos col row := screenBase +# col*2 +# row*160.

Definition charIs (p: ADR AdSize4) (b: BYTE) := ADRtoADDR p :-> b.
Definition colourIs (p: ADR AdSize4) (c: BYTE) := ADRtoADDR (a:=AdSize4) (p+#1) :-> c.

Definition inlineComputeLinePos_spec (row:nat) (base:ADR AdSize4) (instrs: program) :=
  basic (EDX ~= # row ** EDI ~= base) instrs 
        (EDX ~= # row ** EDI ~= base +# row*160) @ OSZCP?.


Definition inlineComputeCharPos_spec (col row:nat) (instrs: program) :=
  basic (ECX ~= # col ** EDX ~= # row ** EDI?) instrs 
        (ECX?         ** EDX? **         EDI ~= charPos col row) @ OSZCP?.

Definition inlineOutputChar_spec (col row: nat) (char: BYTE) (instrs: program) :=
  basic
    (ECX ~= # col ** EDX ~= # row ** AL ~= char ** (Exists old, charIs (charPos col row) old))
    instrs 
    (ECX?        ** EDX?        ** AL ~= char ** charIs (charPos col row) char)
  @ (OSZCP? ** EDI?).

Definition inlineReadChar_spec (col row: nat) (char:BYTE) (instrs: program) :=
  basic
    (ECX ~= # col ** EDX ~= # row ** AL? ** charIs (charPos col row) char)
    instrs 
    (ECX?        ** EDX?        ** AL ~= char ** charIs (charPos col row) char)
  @ (OSZCP? ** EDI?).
