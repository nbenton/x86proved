Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import x86proved.x86.win.pecoff x86proved.x86.cfunc x86proved.x86.macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

Require Import x86proved.x86.call.
Example useCounterCode :=
  IMPORTDLL "msvcrt.dll";
  IMPORT "printf" as printfSlot;
  IMPORTDLL "counter.dll";
  IMPORT "Inc" as incSlot; IMPORT "Get" as getSlot;
  SECTION CODE
    LOCAL formatString;
    MOV EDI, incSlot;;    call_toyfun [EDI]%ms;;
    MOV EDI, getSlot;;    call_toyfun [EDI]%ms;;
    PUSH EAX;;
    MOV EBX, formatString;; PUSH EBX;;
    MOV EDI, printfSlot;; CALL [EDI];;
    ADD ESP, 8;; RET 0;;
  formatString:;;
    ds "Got %d";; db #10;; db #0.

Compute makeEXE #x"12E30000" "usecounter.exe" useCounterCode.
