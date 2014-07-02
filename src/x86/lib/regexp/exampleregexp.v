Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.finfun Ssreflect.fintype Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.SPred x86proved.septac x86proved.spec x86proved.safe x86proved.x86.basic x86proved.x86.program x86proved.x86.macros x86proved.x86.call.
Require Import x86proved.x86.instr x86proved.monad x86proved.reader x86proved.writer x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.x86.mem x86proved.x86.exn x86proved.x86.eval
               x86proved.monadinst x86proved.x86.ioaction x86proved.bitsrep x86proved.bitsops x86proved.x86.eval x86proved.x86.step x86proved.x86.instrcodec x86proved.pointsto x86proved.cursor.
Require Import x86proved.x86.program x86proved.x86.programassem x86proved.x86.reg x86proved.x86.instrsyntax x86proved.x86.instrrules.
Require Import x86proved.spectac x86proved.charge.iltac x86proved.triple.


(* ATBR *)
Require Import ATBR.DecideKleeneAlgebra.
Require Import ATBR.DKA_Definitions.

Require Import interfaceATBR.
Require Import regexpsyntax.

Local Open Scope regex_scope.
Open Scope char_scope.

(**********************************)
(* Floating point regexp          *)
(**********************************)

Definition alphabet: seq DWORD :=
cat [seq (# c) | c <- iota (Ascii.nat_of_ascii "0") 10 ]
    [:: #(Ascii.nat_of_ascii "-")
      ; #(Ascii.nat_of_ascii "+")
      ; #(Ascii.nat_of_ascii "e")
      ; #(Ascii.nat_of_ascii ".")].


(* ^[-+]?[0-9]*\.?[0-9]+([e][-+]?[0-9]+)?$ *)
(*=FP *)
Definition FP: regex :=
  [[ "-" , "+"]]? '
  [{ "0" , "9" }]* ' $"." ? '
  [{ "0" , "9" }]+ '
  ($"e" ' [[ "-" , "+"]]? ' [{ "0" , "9" }]+)?.
(*=End *)

(**********************************)
(* Examples:                      *)
(**********************************)

(*=FP_code*)
Definition FP_x86 (acc rej: DWORD): program :=
    X_to_x86 FP alphabet acc rej.
(*=End*)

(*
Definition code_zero: program := code rO [:: #1 ; #2 ; #3 ] #42 #24.
Definition bytes_zero := assemble #x"C0000000" code_zero.
(* Compute (bytesToHex bytes_zero). *)

Definition code_var1: program := code $"1" [:: #1 ; #2 ; #3 ] #42 #24.
Definition bytes_var1 := assemble #x"C0000000" code_var1.
(* Compute (bytesToHex bytes_var1). *)
*)

Local Close Scope regex_scope.