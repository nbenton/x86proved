(** * NOT instruction *)
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

Lemma NOT_rule d (src:RegMem d) v:
  |-- specAtRegMemDst src (fun V => basic (V v) (UOP d OP_NOT src) (V (invB v))).
Proof.
rewrite /specAtRegMemDst.
destruct src.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_setDWORDorBYTERegSep.

rewrite /specAtMemSpecDst.
destruct ms.
case sib => [[r indexAndScale] |].
destruct indexAndScale.
destruct p as [rix sc].
specintros => pbase ixval.
autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalInstr/evalUnaryOp.
  triple_apply evalMemSpec_rule.
  triple_apply triple_letGetDWORDorBYTESep.
  triple_apply triple_setDWORDorBYTESep.

specintros => pbase.
autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalSrc/evalUnaryOp.
  triple_apply evalMemSpecNone_rule.
  triple_apply triple_letGetDWORDorBYTESep.
  triple_apply triple_setDWORDorBYTESep.

autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalSrc/evalUnaryOp. rewrite /evalMemSpec.
  triple_apply triple_letGetDWORDorBYTESep.
  triple_apply triple_setDWORDorBYTESep.
Qed.

Ltac basicNOT :=
  try unfold makeUOP;
  match goal with
  | |- |-- basic ?p (@UOP ?d OP_NOT ?a) ?q => try_basicapply (@NOT_rule d a)
  end.


(* Special case for not *)
Lemma NOT_R_rule (r:Reg) (v:DWORD):
  |-- basic (r~=v) (NOT r) (r~=invB v).
Proof. basicNOT. Qed.

Corollary NOT_M_rule (r:Reg) (offset:nat) (v pbase:DWORD):
  |-- basic (r~=pbase ** pbase +# offset :-> v) (NOT [r + offset])
            (r~=pbase ** pbase +# offset :-> invB v).
Proof. basicNOT. Qed.
End InstrRules.
