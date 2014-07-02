Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops x86proved.monad writer reg instr instrsyntax program programassem cursor.
Require Import pecoff cfunc macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope instr_scope.
Open Scope string_scope.

Definition call_cdecl2 f arg1 arg2 :=
  PUSH arg2;; PUSH arg1;; CALL f;; ADD ESP, 8.

(*=main *)
Example main :=
  IMPORTDLL "MSVCRT.DLL";
  IMPORT "printf" as printf;
  IMPORTDLL "exporter.dll";
  IMPORT "add" as add;
  SECTION CODE
LOCAL greeting;
LOCAL answer;
  MOV EDI, printf;; PUSH greeting;; CALL [EDI];; ADD ESP, 4;;
  MOV EDI, add;;
  MOV EAX, 19;;
  MOV EBX, 23;;
  CALL [EDI];;
  MOV EDI, printf;;
  call_cdecl2 ([EDI]%ms) answer EAX;;
  RET 0;;
greeting:;;
  ds "Hello!";; db #10;; db #0;;
answer:;;
  ds "The answer is %d.";; db #10;; db #0.
(*=End *)

(*=mainBytes *)
Compute makeEXE #x"00AB0000" "importer.exe" main.
(*=End *)

