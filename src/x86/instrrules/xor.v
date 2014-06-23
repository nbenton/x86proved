(** * XOR instruction *)
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

Lemma XOR_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (XOR r1, r2)
            (r1~=xorB v1 v2 ** r2~=v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalReg_rule.
  triple_apply evalReg_rule.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP/evalLogicalOp.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
Qed.

Lemma XOR_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (XOR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  (* Copy-paste of OR_RM_rule proof *)
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule.
  triple_apply evalMemSpecNone_rule.
  unfold natAsDWORD.
  triple_apply triple_letGetDWORDSep.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep. rewrite E.
  triple_apply triple_doUpdateZPS.
  triple_apply triple_setRegSep.
Qed.

Corollary XOR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) (r1~=xorB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
basicapply (@XOR_RM_rule pd r1 r2 v1 v2 offset (xorB v1 v2) (refl_equal _)).
rewrite /OSZCP/stateIsAny/snd. sbazooka.
Qed.
End InstrRules.
