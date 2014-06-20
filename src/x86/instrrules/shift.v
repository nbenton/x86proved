(** * SHL and SHR instructions *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(** Lazy man's proof *)
Lemma SmallCount : forall count, count < 32 -> toNat (n:=8) (andB #x"1f" (fromNat count)) = count.
Proof. do 32 case => //.
Qed.

Lemma SHL_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 ->
  |-- basic (r~=v ** OSZCP?) (SHL r, count)
            (r~=iter count shlB v ** OSZCP?).
Proof.
  move => BOUND.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDst/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalShiftCount/evalShiftOp. rewrite id_l.
  rewrite (SmallCount BOUND).
  case E: count => [| count'].
  + replace (iter _ _ v) with v by done.
    triple_apply triple_setRegSep.


  triple_apply triple_pre_introFlags => o s z c p.
  rewrite /OSZCP/stateIsAny.
  triple_apply triple_doSetFlagSep.
  case E': count' => [| count''].
  + triple_apply triple_doSetFlagSep.
    try_triple_apply triple_setRegSep. rewrite dropmsb_iter_shlB.
    sbazooka.
  + triple_apply triple_doForgetFlagSep.
    try_triple_apply triple_setRegSep.
    rewrite dropmsb_iter_shlB.
    rewrite /stateIsAny. sbazooka.
Qed.

Lemma SHR_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 ->
  |-- basic (r~=v ** OSZCP?) (SHR r, count)
            (r~=iter count shrB v ** OSZCP?).
Proof.
  move => BOUND.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalShiftCount/evalShiftOp id_l.
  rewrite (SmallCount BOUND).
  case E: count => [| count'].
  + replace (iter _ _ v) with v by done.
    triple_apply triple_setRegSep.


  triple_apply triple_pre_introFlags => o s z c p.
  rewrite /OSZCP/stateIsAny.
  triple_apply triple_doSetFlagSep.
  case E': count' => [| count''].
  + triple_apply triple_doSetFlagSep.
    try_triple_apply triple_setRegSep. rewrite droplsb_iter_shrB.
    sbazooka.
  + triple_apply triple_doForgetFlagSep.
    try_triple_apply triple_setRegSep.
    rewrite droplsb_iter_shrB.
    rewrite /stateIsAny. sbazooka.
Qed.
