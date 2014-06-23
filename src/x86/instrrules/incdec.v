(** * INC and DEC instructions *)
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

(** ** Generic increment/decrement rule *)
Lemma INCDEC_rule d (dir: bool) (src:RegMem d) oldv o s z c pf:
  |-- specAtRegMemDst src (fun V =>
      basic (V oldv ** OSZCP o s z c pf) (if dir then UOP d OP_INC src else UOP d OP_DEC src)
      (let w := if dir then incB oldv else decB oldv in
      V w ** OSZCP (msb oldv!=msb w) (msb w) (w == #0) c (lsb w))).
Proof.
rewrite /specAtRegMemDst.
destruct src.
  apply TRIPLE_basic => R.
  autounfold with eval. rewrite /evalDst/evalDstR.
  destruct dir;
    triple_apply evalDWORDorBYTEReg_rule; rewrite /evalUnaryOp/OSZCP/evalArithUnaryOpNoCarry;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep.

destruct ms.
+ elim sib => [[r indexAndScale] |].
  destruct indexAndScale. destruct p as [rix sc]. rewrite /specAtMemSpecDst.
  specintros => pbase ixval.
  autorewrite with push_at.
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM.
  destruct dir.
  - triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp.
    rewrite /evalArithUnaryOpNoCarry/OSZCP.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
  - triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.

rewrite /specAtMemSpecDst.
specintros => pbase.
autorewrite with push_at.  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM/evalSrc.
  destruct dir.
  - triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
  - triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.

rewrite /specAtMemSpecDst.
autorewrite with push_at.  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM/evalMemSpec.
    rewrite /evalSrc.
  destruct dir.
  - triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
  - triple_apply triple_letGetDWORDorBYTESep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep.
    triple_apply triple_setDWORDorBYTESep.
Qed.

Definition INC_rule := Eval hnf in @INCDEC_rule true true.
Definition DEC_rule := Eval hnf in @INCDEC_rule true false.

Ltac basicINCDEC :=
  try unfold makeUOP;
  match goal with
  | |- |-- basic ?p (@UOP ?d OP_INC ?a) ?q => try_basicapply (@INCDEC_rule d true a)
  | |- |-- basic ?p (@UOP ?d OP_DEC ?a) ?q => try_basicapply (@INCDEC_rule d false a)
  end.

(* Special case for increment register *)
Corollary INC_R_rule (r:Reg) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (INC r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Corollary INC_M_rule (r:Reg) (offset:nat) (v pbase:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** OSZCP o s z c pf) (INC [r + offset])
            (r ~= pbase ** pbase +# offset :-> w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma INC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (INC r) (r~=incB v) @ OSZCP?.
Proof.
autorewrite with push_at. rewrite /stateIsAny. specintros => o s z c p.
basicINCDEC; rewrite /OSZCP/stateIsAny; sbazooka.
Qed.

(* Special case for decrement *)
Lemma DEC_R_rule (r:Reg) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (DEC r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicINCDEC. Qed.

Lemma DEC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (DEC r) (r~=decB v) @ OSZCP?.
Proof.
autorewrite with push_at. rewrite /stateIsAny. specintros => o s z c p.
basicINCDEC; rewrite /OSZCP/stateIsAny; sbazooka.
Qed.
End InstrRules.
