(** * POP instruction *)
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

(** ** Generic POP *)
Lemma POP_rule (rm:RegMem true) (sp:DWORD) (oldv v:DWORD):
  |-- specAtRegMemDst rm (fun V =>
      basic (V oldv ** ESP ~= sp    ** sp:->v) (POP rm)
            (V v    ** ESP ~= sp+#4 ** sp:->v)).
Proof.
  rewrite /specAtRegMemDst. destruct rm.
  + apply TRIPLE_basic => R.
    repeat autounfold with eval. rewrite /DWORDorBYTEregIs.
    triple_apply evalReg_rule.
    triple_apply evalReg_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    triple_apply triple_setRegSep.
  + rewrite /specAtMemSpecDst.
    elim: ms => [optSIB offset].
    elim: optSIB => [[base indexAndScale] |].
    case: indexAndScale => [[rix sc] |].
    - specintros => pbase indexval.
      autorewrite with push_at. apply TRIPLE_basic => R.
      rewrite /evalInstr.
      triple_apply evalReg_rule.
      rewrite /evalDst/evalDstM.
      triple_apply evalMemSpec_rule.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep.
      triple_apply triple_setRegSep.
    - specintros => pbase.
      autorewrite with push_at. apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.
      triple_apply evalReg_rule.
      triple_apply evalMemSpecNone_rule.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep.
      triple_apply triple_setRegSep.
    - autorewrite with push_at.
      apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.
      triple_apply evalReg_rule.
      rewrite /evalMemSpec.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep.
      triple_apply triple_setRegSep.
Qed.

Ltac basicPOP :=
  match goal with
  | |- |-- basic ?p (POP ?a) ?q => try_basicapply (POP_rule a)
  end.


(** ** POP r *)
Corollary POP_R_rule (r:Reg) (sp oldv v:DWORD) :
  |-- basic (r ~= oldv ** ESP ~= sp    ** sp:->v) (POP (RegMemR true r))
            (r ~= v    ** ESP ~= sp+#4 ** sp:->v).
Proof. basicPOP. Qed.

(** ** POP [r + offset] *)
Corollary POP_M_rule (r:Reg) (offset:nat) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> oldv ** ESP ~= sp ** sp :-> v)
            (POP [r + offset])
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp+#4 ** sp :-> v).
Proof. basicPOP. Qed.

(** ** POP [r] *)
Corollary POP_M0_rule (r: Reg) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> oldv ** ESP ~= sp    ** sp :-> v)
            (POP [r])
            (r ~= pbase ** pbase :-> v    ** ESP ~= sp+#4 ** sp :-> v).
Proof. basicPOP. Qed.
End InstrRules.
