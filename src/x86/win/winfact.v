Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc fact.

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
