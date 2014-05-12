Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc macros.

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
    MOV EDI, printfSlot;; call_cdecl_with 1 [EDI] greeting;;
    MOV EDI, scanfSlot;;  call_cdecl_with 2 [EDI] pat res;;
    MOV ESI, res;; MOV EAX, [ESI];; RET 0; 
  SECTION DATA
    greeting:;; ds "Please enter a number";; db #10;; db #0;; 
    pat:;; dsz "%d";;  res:;; dd #0.
Compute makeDLL #x"00AC0000" "ask.dll" askDLL.
(*=End *)

