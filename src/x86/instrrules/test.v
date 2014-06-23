(** * TEST instruction *)
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

(* We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

Hint Unfold
  evalInstr
  evalArithOp evalArithOpNoCarry evalArithUnaryOp evalArithUnaryOpNoCarry
  evalLogicalOp evalBinOp evalShiftOp evalUnaryOp evalCondition
  evalMOV evalDst evalDstR evalDstM evalSrc evalMemSpec evalBYTEReg : eval.

Hint Unfold interpJmpTgt : specapply.

Lemma TEST_self_rule (r:Reg) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP?) (TEST r, r)
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDst/evalDstR/evalRegImm.
  triple_apply evalReg_rule.
  triple_apply evalReg_rule. rewrite andBB.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_skip.
Qed.
End InstrRules.
