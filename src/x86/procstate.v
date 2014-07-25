(*===========================================================================
    Processor state: registers, flags and memory
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.finfun Ssreflect.fintype Ssreflect.eqtype Ssreflect.tuple.
Require Export x86proved.update x86proved.x86.reg x86proved.x86.regstate x86proved.x86.flags x86proved.x86.mem x86proved.bitsrep.
Require Import x86proved.bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope update_scope.

(* Processor state consists of a register file, flags and memory *)
(*=ProcState *)
Record ProcState := mkProcState
{ registers:> RegState; flags:> FlagState; memory:> Mem }.
(*=End *)
Require Import Coq.Strings.String.
Definition procStateToString s :=
  (let: mkProcState rs fs ms := s in
  regStateToString rs ++ " EFL=" ++ flagsToString fs ++ " " ++ memToString ms)%string.

(* Functional update notation, for registers and memory *)
Global Instance ProcStateUpdateOps : UpdateOps ProcState AnyReg DWORD :=
  fun s r v => mkProcState (registers s !r:=v) (flags s) (memory s).

Global Instance ProcStateUpdateFlagOpsBool : UpdateOps ProcState Flag bool :=
  fun s f v => mkProcState (registers s) (flags s!f:=mkFlag v) (memory s).

Global Instance ProcStateUpdateFlagOps : UpdateOps ProcState Flag FlagVal :=
  fun s f v => mkProcState (registers s) (flags s!f:=v) (memory s).

Global Instance ProcStateUpdate : Update ProcState AnyReg DWORD.
apply Build_Update.
move => m k v w. rewrite /update /ProcStateUpdateOps. by rewrite update_same.
move => m k l v w kl. rewrite /update /ProcStateUpdateOps. by rewrite update_diff.
Qed.

Global Instance ProcStateUpdateOpsBYTE : UpdateOps ProcState PTR BYTE :=
  fun s p v => mkProcState (registers s) (flags s) ((memory s) !p:=v).

Global Instance ProcStateUpdateOpsDWORD : UpdateOps ProcState PTR DWORD :=
  fun s p v =>
  let '(b3,b2,b1,b0) := DWORDToBytes v in
  let ms := memory s in
  mkProcState (registers s) (flags s)
    (ms !p:=b0 !incB p:=b1 !incB(incB p):=b2 !incB(incB(incB p)):=b3).

Definition toSlice (b: BITS 2) := toNat b * 8. 

Definition getRegPiece (v: DWORD) (ix: BITS 2)  := 
  if ix == #0 then slice 0 8 _ v else
  if ix == #1 then slice 8 8 _ v else
  if ix == #2 then slice 16 8 _ v else
  slice 24 8 _ v.

Definition putRegPiece (v: DWORD) (ix: BITS 2) (b: BYTE) : DWORD :=
  if ix == #0 then updateSlice 0 8 _ v b else
  if ix == #1 then updateSlice 8 8 _ v b else
  if ix == #2 then updateSlice 16 8 _ v b else
  updateSlice 24 8 _ v b.
  
  
(* @TODO: update lemmas *)
