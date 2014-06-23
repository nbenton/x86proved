Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

Require Import call.
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
