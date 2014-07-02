Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import x86proved.x86.win.pecoff x86proved.x86.cfunc x86proved.x86.fact.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=bytes *)
Definition winfact :=
  IMPORTDLL "msvcrt.dll";
  IMPORT "printf" as printfSlot;
  SECTION CODE
    main printfSlot.

Compute makeEXE #x"00760000" "winfact.exe" winfact.
(*=End *)
