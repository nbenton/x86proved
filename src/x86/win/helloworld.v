(*===========================================================================
  Hello world for Windows
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program.
Require Import pecoff programassem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

Example helloWorldCode :=
  IMPORTDLL "MSVCRT.DLL";
  IMPORT "printf" as printf;
  SECTION CODE
    LOCAL formatString;
    MOV EDI, formatString;;
    PUSH EDI;;
    MOV EDI, printf;;
    CALL [EDI];;
    ADD ESP, 4;;    (* cdecl calling convention for printf *)
    RET 0;;
  formatString:;;
    ds "Hello, world";; db #10;; db #0.

Compute makeEXE #x"10E30000" "helloworld.exe" helloWorldCode.
