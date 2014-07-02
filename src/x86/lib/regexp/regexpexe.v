Require Import ssreflect ssrfun ssrbool finfun fintype ssrnat eqtype seq tuple.
Require Import path fingraph  finset.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec safe basic program macros call.
Require Import instr x86proved.monad reader writer procstate procstatemonad mem exn eval
               monadinst ioaction bitsrep bitsops eval step instrcodec pointsto cursor.
Require Import program programassem reg instrsyntax instrrules.
Require Import spectac iltac triple.
Require Import pecoff.

Require Import stringbuff.
Require Import interfaceATBR.
Require Import exampleregexp.
Require Import compiler.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(*****************************************************************)
(* Pe/Coff                                                       *)
(*****************************************************************)


Fixpoint compileString (s: string): program :=
  match s with
    | EmptyString => dd #0
    | String c s =>
        dd #(Ascii.nat_of_ascii c);;
        compileString s
  end.

Definition buffSize := 32.

Definition exampleCode :=
  IMPORTDLL "MSVCRT.DLL";
  IMPORT "puts" as puts;
  IMPORT "gets" as gets;
  GLOBAL data; GLOBAL buffer;
SECTION CODE
  LOCAL succMsg; LOCAL failMsg; LOCAL errMsg;
  LOCAL print;
  LOCAL succ; LOCAL fail; LOCAL err;
  LOCAL loop; LOCAL run_dfa;
  LOCAL load_any; LOCAL load_minus; LOCAL load_plus; LOCAL load_dot; LOCAL load_exp;
  LOCAL cap; LOCAL num; LOCAL symb;
  LOCAL next;
  (* Load input in [buffer] *)
  MOV EDI, gets;;
  PUSH buffer;;
  CALL [EDI];;
  ADD ESP, 4;;

  (* Reformat input in [data] *)
  (* Got: BYTE with ascii characters *)
  (* Want: DWORD containing these ascii characters *)
  (* Output in [buffer] *)
  MOV EAX, buffer;;
  MOV EBX, data;;
(*  MOV ECX, (#0: DWORD);; *)
 loop:;;
  CMP BYTE [EAX], #0;;
  JE run_dfa;;
  (* Copy Byte in [EAX] to DWORD [EBX] *)
  MOV CL, [EAX];;
  MOV [EBX], CL;;

  (* Next char *)
  INC EAX;;
  ADD EBX, (#4: DWORD);;
  JMP loop;;

  (* Run DFA on [data] *)
 run_dfa:;;
  MOV [EBX], (#0: DWORD);;
  MOV EAX, data;;
  FP_x86 succ fail;;
 succ:;;
  MOV EAX, succMsg;;
  JMP print;;
fail:;;
  MOV EAX, failMsg;;
  JMP print;;
err:;;
  MOV EAX, errMsg;;
print:;;
  MOV EDI, puts;;
  PUSH EAX;;
  CALL [EDI];;
  ADD ESP, 4;;
  RET 0;;
succMsg:;;
  dd #c"Acc.";; db #0;;
failMsg:;;
  dd #c"Rej.";; db #0;;
errMsg:;;
  dd #c"Err.";; db #0;
SECTION DATA
  data:;;
    pad ((buffSize + 1) * 8);;
  buffer:;;
    pad (buffSize + 1).

Compute
  makeEXE #x"10E30000" "compiler.exe" exampleCode.

