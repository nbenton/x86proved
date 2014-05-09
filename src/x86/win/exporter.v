Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops monad writer reg instr instrsyntax program.
Require Import pecoff programassem.

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
