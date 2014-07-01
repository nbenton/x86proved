(*===========================================================================
  GUI version of hello world for Windows
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import bitsrep bitsops bitsopsprops x86proved.monad writer reg instr instrsyntax program.
Require Import pecoff programassem cfunc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope string_scope.
Open Scope instr_scope.

(*=messageBoxProg *)
Definition mbProg: topprog :=
  IMPORTDLL "user32.dll";
  IMPORT "MessageBoxA" as MessageBoxA;
  GLOBAL message; GLOBAL title;
SECTION CODE
  call_with stdcall 4 [MessageBoxA]%ms 0 title message 0;;
  RET 0;
SECTION DATA
  message:;; dsz "Hello, world";;
  title:;;   dsz "My first app".
(*=End *)

(*=makeEXE *)
Compute makeEXE #x"10E30000" "messagebox.exe" mbProg.
(*=End *)
