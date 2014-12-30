(*===========================================================================
  Implementation of linked lists
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.spec x86proved.x86.basic x86proved.x86.program x86proved.x86.macros.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.reader x86proved.cursor x86proved.x86.inlinealloc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Definition inlineHead (r1 r2:GPReg64) :program :=
  MOV r1, QWORD PTR [r2].

Definition inlineTail (r1 r2:GPReg64) :program :=
  MOV r1, QWORD PTR [r2+8].

(* Head is in r1, tail is in r2, result in EDI, ESI trashed *)
Definition updateCons (r1 r2:GPReg64) :program :=
    SUB RDI, (#16 : IMM _);;
    MOV QWORD PTR [RDI], r1;;
    MOV QWORD PTR [RDI+8], r2.

Definition inlineCons (r1 r2:GPReg64) failAddr: program :=
  allocImp 16 failAddr;;
  updateCons r1 r2.

Definition callCons (r1 r2:GPReg64): program :=
  LOCAL FAIL;
  LOCAL SUCCEED;
    inlineCons r1 r2 FAIL;;
    JMP SUCCEED;;
  FAIL:;;
    MOV RDI, (0:QWORD);;
  SUCCEED:;.
