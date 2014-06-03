Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

(*=tellProg *)
Example tellProg :=
  IMPORTDLL "msvcrt.dll"; IMPORT "printf" as printfSlot;
  IMPORTDLL "ask.dll";    IMPORT "AskForNum" as AskForNumSlot;
  GLOBAL greeting;
  SECTION CODE
    CALL [AskForNumSlot];;
    MOV EBX, EAX;; ADD EAX, EAX;;
    call_cdecl_with 3 [printfSlot]%ms greeting EBX EAX;;
    RET 0;
  SECTION DATA
    greeting:;; ds "Twice %d is %d";; db 10;; db 0.
Compute makeEXE #x"00AB0000" "tell.exe" tellProg.
(*=End *)

