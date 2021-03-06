(*===========================================================================
  GUI version of hello world for Windows
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsopsprops x86proved.monad x86proved.writer x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.program.
Require Import x86proved.x86.win.pecoff x86proved.x86.programassem x86proved.x86.cfunc.

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
