(*===========================================================================
  Specification of CGA screen functions
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.spred x86proved.septac x86proved.spec x86proved.spectac x86proved.safe x86proved.x86.basic x86proved.x86.basicprog x86proved.x86.program x86proved.x86.basic.
Require Import x86proved.x86.instr x86proved.x86.instrsyntax x86proved.x86.instrcodec x86proved.reader x86proved.pointsto x86proved.cursor x86proved.x86.instrrules x86proved.x86.macros.
Require Import x86proved.x86.screenspec x86proved.x86.screenimp.
Reset Profile.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma inlineComputeCharPos_correct col row :
  col < numCols ->
  row < numRows ->
  |-- inlineComputeCharPos_spec col row inlineComputeCharPos.
Proof.
  move => NC NR.
  rewrite /inlineComputeCharPos_spec/inlineComputeCharPos/stateIsAny.
  rewrite <- spec_at_basic_directionalized1.
  specintros => *.

  start profiling.
  do !basic apply * => //.
  stop profiling.

  rewrite /charPos/iter !shlB_asMul.

  rewrite -5!mulB_muln.
  rewrite -mulB_muln.
  rewrite !fromNat_mulBn.
  do 2 rewrite <- addB_addn.
  rewrite addnA -mulnDr addnC.
  rewrite addB_addn.
  reflexivity.
Qed.

(* Correct placement of unfolding of stateIsAny is tricky. *)
Lemma inlineOutputChar_correct col row char :
  col < numCols ->
  row < numRows ->
  |-- inlineOutputChar_spec col row char inlineOutputChar.
Proof.
  move => NC NR.
  rewrite /inlineOutputChar_spec/inlineOutputChar/charIs.

  autorewrite with push_at. rewrite {1}/stateIsAny.
  specintros => olddi oldchar.

  have ICCP := (inlineComputeCharPos_correct NC NR : instrrule inlineComputeCharPos).
  start profiling.
  do 2 basic apply *.
  Stop Profiling.
Qed.

Lemma inlineReadChar_correct col row char :
  col < numCols ->
  row < numRows ->
  |-- inlineReadChar_spec col row char inlineReadChar.
Proof.
  move => NC NR.
  rewrite /inlineReadChar_spec/inlineReadChar/memIs/interpProgram/charIs{1}/stateIsAny.

  autorewrite with push_at.
  specintros => oldal.

  have ICCP := (inlineComputeCharPos_correct NC NR : instrrule inlineComputeCharPos).
  start profiling.
  do 2 basic apply *.
  Stop Profiling.
Qed.
Show Profile.
