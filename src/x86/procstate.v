(*===========================================================================
    Processor state: registers, flags and memory
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.finfun Ssreflect.fintype Ssreflect.eqtype Ssreflect.tuple.
Require Export x86proved.update x86proved.x86.reg x86proved.x86.regstate x86proved.x86.flags x86proved.x86.mem x86proved.bitsrep.
Require Import x86proved.bitsops x86proved.x86.addr.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope update_scope.

(* Processor state consists of a register file, flags and memory *)
(*=ProcState *)
Record ProcState := mkProcState
{ segregisters:> SegRegState; registers:> RegState; flags:> FlagState; memory:> Mem }.
(*=End *)
Require Import Coq.Strings.String.
Definition procStateToString s :=
  (let: mkProcState sr rs fs ms := s in
  regStateToString rs ++ " EFL=" ++ flagsToString fs ++ " " ++ memToString ms)%string.

(* Functional update notation, for registers and memory *)
Global Instance ProcStateUpdateOps : UpdateOps ProcState Reg64 QWORD :=
  fun s r v => mkProcState (segregisters s) (registers s !r:=v) (flags s) (memory s).

Global Instance ProcStateUpdateSegOps : UpdateOps ProcState SegReg WORD :=
  fun s r v => mkProcState (segregisters s !r:=v) (registers s) (flags s) (memory s).

Global Instance ProcStateUpdateFlagOpsBool : UpdateOps ProcState Flag bool :=
  fun s f v => mkProcState (segregisters s) (registers s) (flags s!f:=mkFlag v) (memory s).

Global Instance ProcStateUpdateFlagOps : UpdateOps ProcState Flag FlagVal :=
  fun s f v => mkProcState (segregisters s) (registers s) (flags s!f:=v) (memory s).

Global Instance ProcStateUpdate : Update ProcState Reg64 QWORD.
apply Build_Update.
move => m k v w. rewrite /update /ProcStateUpdateOps. by rewrite update_same.
move => m k l v w kl. rewrite /update /ProcStateUpdateOps. by rewrite update_diff.
Qed.

Global Instance ProcStateSegUpdate : Update ProcState SegReg WORD.
apply Build_Update.
move => m k v w. rewrite /update /ProcStateUpdateSegOps. by rewrite update_same.
move => m k l v w kl. rewrite /update /ProcStateUpdateSegOps. by rewrite update_diff.
Qed.

Global Instance ProcStateUpdateOpsBYTE : UpdateOps ProcState ADDR BYTE :=
  fun s p v => mkProcState (segregisters s) (registers s) (flags s) ((memory s) !p:=v).

(*
Global Instance ProcStateUpdateOpsDWORD : UpdateOps ProcState ADDR DWORD :=
  fun s p v =>
  let '(b3,b2,b1,b0) := DWORDToBytes v in
  let ms := memory s in
  mkProcState (registers s) (flags s)
    (ms !p:=b0 !incB p:=b1 !incB(incB p):=b2 !incB(incB(incB p)):=b3).
*)

(* @TODO: update lemmas *)
