(*===========================================================================
  Factorial example, from Section 1.1 of the PPDP 2013 submission
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.program x86proved.x86.macros x86proved.x86.call.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.programassem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Definition defproc (p: program) :=
  p;; JMP EDI.

Notation "'letproc' f ':=' p 'in' q" :=
  (LOCAL skip; JMP skip;; LOCAL f; f:;; defproc p;; skip:;; q)
  (at level 65, f ident, right associativity).

Definition callproc f :=
  LOCAL iret; MOV EDI, iret;; JMP f;;
  iret:;.

(*=main *)
Definition call_cdecl3 f arg1 arg2 arg3 :=
  PUSH arg3;; PUSH arg2;; PUSH arg1;;
  CALL f;; ADD ESP, 12.

Definition main (printfSlot: DWORD) :=
  (* Argument in EBX *)
  letproc fact :=
    MOV EAX, 1;;
    MOV ECX, 1;;
      (* while ECX <= EBX *)
      while (CMP ECX, EBX) CC_LE true (
        MUL ECX;; (* Multiply EAX by ECX *)
        INC ECX
      )
  in
    LOCAL format;
      MOV EBX, 10;; callproc fact;;
      MOV EDI, printfSlot;;
      call_cdecl3 [EDI]%ms format EBX EAX;;
      MOV EBX, 12;; callproc fact;;
      MOV EDI, printfSlot;;
      call_cdecl3 [EDI]%ms format EBX EAX;;
      RET 0;;
    format:;;
      ds "Factorial of %d is %d";; db 10;; db 0.

Compute assembleToString #x"C0000004" (main #x"C0000000").
(*=End *)
