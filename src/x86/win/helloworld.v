(*===========================================================================
  Hello world for Windows
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops x86proved.monad writer reg instr instrsyntax program.
Require Import pecoff programassem macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

Example helloWorldCode :=
  IMPORTDLL "MSVCRT.DLL";
  IMPORT "printf" as printfSlot;
  SECTION CODE
  LOCAL formatString;
    PUSH formatString;;
    CALL [printfSlot];;
    ADD ESP, 4;;    (* cdecl calling convention for printf *)
    RET 0;;
  formatString:;;
    ds "Hello, world";; db 10;; db 0.

Compute makeEXE #x"10E30000" "helloworld.exe" helloWorldCode.
