Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import x86proved.x86.win.pecoff x86proved.x86.cfunc x86proved.x86.macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

(*=askProg *)
Example askDLL :=
  IMPORTDLL "MSVCRT.DLL";
    IMPORT "printf" as printfSlot; IMPORT "scanf" as scanfSlot;
  GLOBAL AskForNum as "AskForNum";
  GLOBAL greeting; GLOBAL pat; GLOBAL res;
  SECTION CODE
    AskForNum:;;
    call_cdecl_with 1 [printfSlot]%ms greeting;;
    call_cdecl_with 2 [scanfSlot]%ms pat res;;
    MOV ESI, res;; MOV EAX, [ESI];; RET 0;
  SECTION DATA
    greeting:;; ds "Please enter a number";; db 10;; db 0;;
    pat:;; dsz "%d";;  res:;; dd 0.
Compute makeDLL #x"00AC0000" "ask.dll" askDLL.
(*=End *)
