(*===========================================================================
  Hello world for Windows
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program.
Require Import x86proved.x86.win.pecoff x86proved.x86.programassem x86proved.x86.macros.

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
