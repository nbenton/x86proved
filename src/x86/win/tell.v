Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import x86proved.x86.win.pecoff x86proved.x86.cfunc x86proved.x86.macros.

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

