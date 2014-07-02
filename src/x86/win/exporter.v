Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program.
Require Import x86proved.x86.win.pecoff x86proved.x86.programassem.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

(*=add *)
Example add :=
  GLOBAL add as "add";
  SECTION CODE
    add:;; ADD EAX, EBX;; RET 0.
(*=End *)

(*=addBytes *)
Compute makeDLL #x"22770000" "exporter.dll" add.
(*=End *)
