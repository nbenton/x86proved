Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program x86proved.x86.programassem x86proved.cursor.
Require Import x86proved.x86.win.pecoff x86proved.x86.cfunc x86proved.x86.macros.

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

