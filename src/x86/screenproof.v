(*===========================================================================
  Specification of CGA screen functions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic basicprog program basic.
Require Import instr instrsyntax instrcodec reader pointsto cursor instrrules macros.
Require Import screenspec screenimp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma inlineComputeCharPos_correct col row :
  col < numCols ->
  row < numRows ->
  |-- inlineComputeCharPos_spec col row inlineComputeCharPos.
Proof.
  move => NC NR.
  rewrite /inlineComputeCharPos_spec/inlineComputeCharPos.
  autorewrite with push_at.

  (* We don't unfold OSZCP? anywhere because no rules talk about flags *)

  (* MOV EDI, screenBase *)
  rewrite {1}/stateIsAny. specintros => olddi.
  basicapply MOV_RI_rule.

  (* SHL EDX, 5 *)
  basicapply SHL_RI_rule => //.

  (* ADD EDI, EDX *)
  basicapply ADD_RR_ruleNoFlags.

  (* SHL EDX, 2 *)
  basicapply SHL_RI_rule => //.

  (* ADD EDI, EDX *)
  basicapply ADD_RR_ruleNoFlags.

  (* SHL ECX, 1 *)
  basicapply SHL_RI_rule => //.

  (* ADD EDI, ECX *)
  basicapply ADD_RR_ruleNoFlags; rewrite /stateIsAny; sbazooka.

  rewrite /charPos/iter !shlB_asMul.

  rewrite -5!mulB_muln.
  rewrite -mulB_muln.
  rewrite !fromNat_mulBn.
  rewrite -2!addB_addn.
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

  have ICCP := inlineComputeCharPos_correct NC NR.
  rewrite /inlineComputeCharPos_spec in ICCP.
  try_basicapply ICCP.

  rewrite /stateIsAny.
  sbazooka.

  (* MOV BYTE [EDI + 0], EAX *)
  try_basicapply MOV_MbR_rule.
  rewrite -> addB0.
  sbazooka.

  rewrite /stateIsAny.
  rewrite -> addB0.
  sbazooka.
Qed.

Lemma inlineReadChar_correct col row char :
  col < numCols ->
  row < numRows ->
  |-- inlineReadChar_spec col row char inlineReadChar.
Proof.
  move => NC NR.
  rewrite /inlineReadChar_spec/inlineReadChar/memIs/interpProgram/charIs.

  autorewrite with push_at. rewrite {1}/stateIsAny.
  specintros => oldeax.

  have ICCP := inlineComputeCharPos_correct NC NR.
  rewrite /inlineComputeCharPos_spec in ICCP.
  basicapply ICCP.

  (* MOV EAX, BYTE [EDI + 0] *)
  try_basicapply MOV_RMb_rule.
  rewrite -> addB0. rewrite /BYTEregIs/BYTEregIsAux. sbazooka.

  rewrite /stateIsAny addB0.
  sbazooka.
Qed.
