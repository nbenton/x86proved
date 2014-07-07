(*===========================================================================
  Specification of CGA screen functions
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.program.
Require Import x86proved.x86.instr x86proved.x86.instrcodec x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.instrrules.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* This should be hidden behind an abstraction *)
Definition screenBase: DWORD := #x"000b8000".
Definition numCols := 80.
Definition numRows := 50.
Definition screenLimit : DWORD := screenBase +# numCols*numRows*2.
Definition screenMapped := memAny screenBase screenLimit.

Definition charPos col row := screenBase +# col*2 +# row*160.

Definition charIs (p: DWORD) (b: BYTE) := p :-> b.
Definition colourIs (p: DWORD) (c: BYTE) := p+#1 :-> c.

Definition inlineComputeLinePos_spec (row:nat) (base:DWORD) (instrs: program) :=
  basic (EDX ~= # row ** EDI ~= base) instrs empOP
        (EDX ~= # row ** EDI ~= base +# row*160) @ OSZCP?.


Definition inlineComputeCharPos_spec (col row:nat) (instrs: program) :=
  basic (ECX ~= # col ** EDX ~= # row ** EDI?) instrs empOP
        (ECX?         ** EDX? **         EDI ~= charPos col row) @ OSZCP?.

Definition inlineOutputChar_spec (col row: nat) (char: BYTE) (instrs: program) :=
  basic
    (ECX ~= # col ** EDX ~= # row ** BYTEregIs AL char ** (Exists old, charIs (charPos col row) old))
    instrs empOP
    (ECX?        ** EDX?        ** BYTEregIs AL char ** charIs (charPos col row) char)
  @ (OSZCP? ** EDI?).

Definition inlineReadChar_spec (col row: nat) (char:BYTE) (instrs: program) :=
  basic
    (ECX ~= # col ** EDX ~= # row ** EAX? ** charIs (charPos col row) char)
    instrs empOP
    (ECX?        ** EDX?        ** BYTEregIs AL char ** charIs (charPos col row) char)
  @ (OSZCP? ** EDI?).
