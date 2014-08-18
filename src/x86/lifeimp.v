(*===========================================================================
  Implementation of "Game of Life"
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.opred x86proved.x86.basic x86proved.x86.program x86proved.x86.basicprog x86proved.x86.macros x86proved.x86.call.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.x86.instrrules x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.screenspec.
Require Import x86proved.common_tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

(* Compute line position EDX in screen buffer starting at EDI *)
(* EDI contains the position; EDX is preserved if it is in range *)
Definition inlineComputeLinePos: program :=
     SHL EDX, 5;;
     ADD EDI, EDX;;
     SHL EDX, 2;;
     ADD EDI, EDX;;
     SHR EDX, 7.

Definition inlineComputeLine_spec (row:nat) (base:DWORD) (instrs: program) :=
  basic (EDX ~= #row ** EDI ~= base) instrs empOP
        (EDX ~= #row ** EDI ~= base +# row*160) @ OSZCP?.

Lemma inlineComputeLinePos_correct row base :
  row < numRows ->
  |-- inlineComputeLine_spec row base inlineComputeLinePos.
Proof.
  move => NR.
  rewrite /inlineComputeLine_spec/inlineComputeLinePos.
  autorewrite with push_at.
  rewrite /stateIsAny.
  specintros => *.

  do !basic apply * => //.

  rewrite /iter. autorewrite with bitsHints. (*rewrite -addB_addn. rewrite !shlB_asMul. *)
  do 6 rewrite -[in X in (regIs EDI X)]mulB_muln.
  rewrite !fromNat_mulBn.
  replace (2 * _) with 32 => //.
  replace (32 * (2*2)) with 128 => //.
  rewrite -addB_addn.
  (* Can't use ring 'cos it's inside bits *)
  rewrite -mulnDr addnC. replace (128 + 32) with 160 => //.
  ssimpl.

  rewrite -6!mulnA.
  replace (2 * _) with (2^7) => //.
  have SH := @shrB_mul2exp 7 25 #row.
  rewrite /iter fromNat_mulBn in SH. rewrite SH {SH}.
  reflexivity.
  rewrite toNat_fromNatBounded. apply (ltn_trans NR) => //.
  apply (ltn_trans NR) => //.
Qed.

(* Increment ESI if location buf[ECX, EDX] contains a dot *)
Definition incIfDot buf: program :=
  LOCAL skip;
  MOV EDI, buf;;
  inlineComputeLinePos;;
  CMP BYTE [EDI + ECX*2], #c"*";;
  JNE skip;;
  INC ESI;;
skip:;.

Definition decModN (r:Reg) n : program :=
  CMP r, 0;;
  ifthenelse CC_Z true (MOV r, (n.-1)) (DEC r).

Definition incModN (r: Reg) n : program :=
  CMP r, (n.-1);;
  ifthenelse CC_Z true (MOV r, 0) (INC r).

Require Import Ssreflect.div.
Lemma decModN_correct (r:Reg) n m : n < 2^32 -> m < n ->
  |-- basic (r ~= #m) (decModN r n) empOP (r ~= #((m + n.-1) %% n)) @ OSZCP?.
Proof.
  move => LT1 LT2.

  autorewrite with push_at.
  rewrite /decModN.

  (* CMP r, 0 *)
  basic apply *.

  basic apply (if_rule_const_io
    (P:= fun b =>
    (m == 0) = b /\\ r ~= #m ** OF? ** SF? ** CF? ** PF?));
    (rewrite /stateIsAny; try specintros => *; idtac);
    do ?basic apply *.

  { rewrite subB0.
    apply fromNatBounded_eq => //.
      by apply (ltn_trans LT2). }

  { destruct m, n => //.
    rewrite decB_fromSuccNat.
    rewrite succnK addSnnS modnDr.
    rewrite modn_small => //.
    apply (leq_ltn_trans (leq_pred _) LT2). }

  { destruct m, n => //.
    rewrite add0n modn_small => //. }
Qed.

Definition incModN_correct (r:Reg) n m : n < 2^32 -> m < n ->
  |-- basic (r ~= #m) (incModN r n) empOP (r ~= #((m.+1) %% n)) @ OSZCP?.
Proof.
move => LT1 LT2.

  autorewrite with push_at.
  rewrite /incModN.

  (* CMP r, 0 *)
  basic apply *.

  basic apply (if_rule_const_io
    (P:= fun b =>
    (m == n.-1) = b /\\ r ~= #m ** OF? ** SF? ** CF? ** PF?));
    (rewrite /stateIsAny; try specintros => *; idtac);
    do ?basic apply *;
    try match goal with
          | [ H : (_ == _) = true |- _ ] => move/eqP in H; progress subst
          | [ H : (_ == _.-1) = ~~true |- _ ] => rewrite -eqSS prednK in H
        end.


  { have B2: m < 2^32.
    { by apply (ltn_trans LT2). }

    rewrite subB_eq add0B.
    apply fromNatBounded_eq; try eassumption; by apply (leq_ltn_trans (leq_pred _)). }

  { rewrite incB_fromNat. rewrite modn_small => //.
    rewrite ltn_neqAle. rewrite LT2 andbT.
    by hyp_rewrite *. }

  { by destruct n. }

  { destruct n => //.
      by rewrite modnn. }
Qed.

(* Move ECX one column left, wrapping around if necessary *)
Definition goLeft: program := decModN ECX numCols.

Lemma goLeftCorrect col : col < numCols ->
  |-- basic (ECX ~= # col) goLeft empOP (ECX ~= #((col + numCols.-1) %% numCols))@ OSZCP?.
Proof. apply decModN_correct => //. Qed.

(* Move ECX one column right, wrapping around if necessary *)
Definition goRight: program := incModN ECX numCols.

Lemma goRightCorrect col : col < numCols ->
  |-- basic (ECX ~= # col) goRight empOP (ECX ~= #((col.+1) %% numCols)) @ OSZCP?.
Proof. apply incModN_correct => //. Qed.

(* Move EDX one row up, wrapping around if necessary *)
Definition goUp: program := decModN EDX numRows.

Lemma goUpCorrect row : row < numRows ->
  |-- basic (EDX ~= # row) goUp empOP (EDX ~= #((row + numRows.-1) %% numRows)) @ OSZCP?.
Proof. apply decModN_correct => //. Qed.

(* Move EDX one row down, wrapping around if necessary *)
Definition goDown: program := incModN EDX numRows.

Lemma goDownCorrect row : row < numRows ->
  |-- basic (EDX ~= # row) goDown empOP (EDX ~= #((row.+1) %% numRows)) @ OSZCP?.
Proof. apply incModN_correct => //. Qed.

(* Given a character at buf[ECX, EDX], return its neighbour count in ESI *)
(* Preserve ECX, EDX *)
Definition countNeighbours (buf:DWORD) : program :=
  let_toyfun f := incIfDot buf
  in
  MOV ESI, 0;;
  goLeft;; call_toyfun f;;
  goUp;; call_toyfun f;;
  goRight;; call_toyfun f;;
  goRight;; call_toyfun f;;
  goDown;; call_toyfun f;;
  goDown;; call_toyfun f;;
  goLeft;; call_toyfun f;;
  goLeft;; call_toyfun f;;
  goUp;; goRight.

Definition bufDefined (buf:DWORD) := memAny buf (buf +# numRows*numCols*2).

Definition writeChar buf ch: program :=
  MOV EDI, buf;;
  inlineComputeLinePos;;
  MOV BYTE [EDI+ECX*2], charToBYTE ch.

(* Using the screen buffer as input, produce new chracter in buf *)
Open Scope char_scope.
Definition oneStep screen buf: program :=
  LOCAL ALIVE;
  LOCAL SKIP;
  LOCAL KILL;
  countNeighbours screen;;
  MOV EDI, screen;;
  inlineComputeLinePos;;
  CMP BYTE [EDI+ECX*2], #c"*";;
  JE ALIVE;;
  CMP ESI, 3;;
  JNE SKIP;;
  writeChar buf ("*":Ascii.ascii);;
  JMP SKIP;;
ALIVE:;;
  CMP ESI, 3;;
  JG KILL;;
  CMP ESI, 2;;
  JL KILL;;
  JMP SKIP;;
KILL:;;
  writeChar buf " ";;
SKIP:;.

(* Code for clear screen. *)
Definition clearColour := toNat (n:=8) (#x"4F").

Definition clsProg :program :=
      MOV EBX, screenBase;;
      while (CMP EBX, screenLimit) CC_B true ( (* while EBX < screenLimit *)
        MOV BYTE [EBX], #c" ";;
        MOV BYTE [EBX+1], # clearColour;;
        INC EBX;; INC EBX (* move one character right on the screen *)
      ).

Definition oneStepScreen screen buf :program :=
      MOV EDX, 0;;
      while (CMP EDX, numRows) CC_B true ( (* while EDX < numRows *)
        MOV ECX, 0;;
        while (CMP ECX, numCols) CC_B true ( (* while ECX < numCols *)
          oneStep screen buf;;
          INC ECX
        );;
        INC EDX
      ).

(* Copy the screen to a buffer, or vice versa.
   Only copy the text, not the colours *)
Definition copyBuf (src dst:DWORD) : program:=
      MOV ESI, src;;
      MOV EDI, dst;;
      while (CMP ESI, (src +# numCols*numRows.*2:DWORD)) CC_B true ( (* while ESI < screenLimit *)
        MOV EAX, [ESI];;
        MOV [EDI], EAX;;
        ADD ESI, 4;; ADD EDI, 4
      ).

Definition delay:program :=
      MOV EBX, (#x"08000001":DWORD);;
      while (CMP EBX, 0) CC_Z false (DEC EBX).


Definition copyBlock (src dst:DWORD) : program:=
      MOV ESI, src;;
      MOV EDI, dst;;
      while (CMP ESI, (src +# numCols*numRows.*2:DWORD)) CC_B true ( (* while ESI < screenLimit *)
        MOV EAX, [ESI];;
        MOV [EDI], EAX;;
        ADD ESI, 4;; ADD EDI, 4
      ).


Fixpoint makeLine s (screen:DWORD) :=
  if s is String c s'
  then writeChar screen c;; goRight;; makeLine s' screen
  else prog_skip.

Fixpoint makeFigure ss screen :=
  if ss is s::ss'
  then MOV EAX, ECX;; makeLine s screen;; MOV ECX, EAX;; goDown;; makeFigure ss' screen
  else prog_skip.

(*
Definition makeFigureAlt (ss: seq string) screen render :=
LOCAL shape;
  MOV EDX, (fromNat (List.length ss):DWORD);;
  MOV ECX, (fromNat (String.length (List.hd ""%string ss)):DWORD);;
  MOV EDI, screen;;
  CALL render;;
shape:
  ds (flatten ss).
*)

Open Scope string.
Definition makeGlider := makeFigure
  [:: " * ";
      "  *";
      "***"].

Definition makeBlock := makeFigure
  [:: "**";
      "**"].

Definition makeBeehive := makeFigure
  [:: " ** ";
      "*  *";
      " ** "].

Definition makeBeacon := makeFigure
  [:: "**  ";
      "**  ";
      "  **";
      "  **"].

Definition makePulsar := makeFigure
  [:: "  ***   ***  ";
      "             ";
      "*    * *    *";
      "*    * *    *";
      "*    * *    *";
      "  ***   ***  ";
      "             ";
      "  ***   ***  ";
      "*    * *    *";
      "*    * *    *";
      "*    * *    *";
      "             ";
      "  ***   ***  "].
