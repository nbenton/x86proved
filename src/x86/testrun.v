(*===========================================================================
    Actually run the transition function on some code
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq.
Require Import x86proved.x86.instr x86proved.monad x86proved.reader x86proved.writer x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.x86.mem x86proved.x86.exn x86proved.x86.eval x86proved.x86.instrcodec
               x86proved.monadinst x86proved.x86.ioaction x86proved.bitsrep x86proved.bitsops x86proved.x86.eval x86proved.x86.step x86proved.cursor x86proved.examples.fact.

Require Import x86proved.x86.program x86proved.x86.programassem x86proved.x86.reg x86proved.x86.instrsyntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition codeAddr := #x"C0000004".
Definition codeSpace := 256.
Definition stackAddr := #x"D0000000".
Definition stackSpace := 256.

Definition reservedMemory :=
  reserveMemory
  (reserveMemory initialMemory codeAddr # codeSpace)
  (stackAddr -# stackSpace) # stackSpace.

(* We expect this to succeed *)
Definition initializedMemory :=
  if writeMem write_program reservedMemory (mkCursor codeAddr) (main #x"C0000000") is Some (_,m) then m else reservedMemory.

Definition initialState :=
  mkProcState ((initialReg ! RIP:=(zeroExtend 32 codeAddr) ! (RSP:Reg64):=(zeroExtend 32 stackAddr))) initialFlagState initializedMemory.

(*
Definition runFor n s :=
  let: (output,r) := doMany n step s
  in (output, fst r).

Fixpoint outputToString (s: seq (Chan*Data)) :=
  (if s is (c,d)::s
  then toHex c ++ ":" ++ toHex d ++ " " ++ outputToString s
  else "")%string.

Definition resultToString r := (outputToString (fst r) ++ procStateToString (snd r))%string.
*)

(* We need some better pretty-printing! *)
(*
Compute resultToString (runFor 0 initialState).
Compute resultToString (runFor 1 initialState).
Compute resultToString (runFor 2 initialState).
*)
