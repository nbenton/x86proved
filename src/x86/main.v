Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.finfun Ssreflect.tuple Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.charge.ilogic.
Require Import x86proved.x86.program x86proved.x86.programassem x86proved.x86.imp x86proved.x86.call.
Require Import x86proved.cursor x86proved.safe x86proved.x86.instrrules.
Require Import x86proved.x86.reg x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.macros Coq.Strings.Ascii x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.x86.screenspec x86proved.x86.screenimp x86proved.x86.lifeimp.

Open Scope instr_scope.
Local Transparent ILFun_Ops.

Definition codeAddr: DWORD := #x"00300000".
Definition bufAddr : DWORD := #x"00400000".
Definition vesaAddr: DWORD := #x"f0000000".
Definition white   : DWORD := #x"ffffffff".

Definition prog : program :=
  (LOCAL buf;
  clsProg;;
  copyBuf screenBase buf;;
  MOV ECX, 20;;  MOV EDX, 40;;  makeGlider buf;;
  MOV ECX, 50;;  MOV EDX, 15;;  makeGlider buf;;
  MOV ECX, 5;;   MOV EDX, 5;;  makePulsar buf;;
  copyBuf buf screenBase;;

  LOCAL busy;
    busy:;;
      delay;;
      oneStepScreen screenBase buf;;
      copyBuf buf screenBase;;
      JMP busy;;
  buf:;
  ) (* ++ nseq (numCols*numRows*2) #0 *).


Compute assembleToString codeAddr prog.

