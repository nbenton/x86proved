(** * JMP (rel) instruction *)
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

Lemma JMPrel_rule (tgt: JmpTgt) (p q: DWORD) :
  |-- interpJmpTgt tgt q (fun P addr =>
     (|> safe @ (EIP ~= addr ** P) -->> safe @ (EIP ~= p ** P)) <@ (p -- q :-> JMPrel tgt)).
Proof.
  rewrite /interpJmpTgt. destruct tgt.
  (* JmpTgtI *)
  destruct t. apply TRIPLE_safe => R.
  rewrite /evalInstr/evalSrc/evalJmpTgt.
  triple_apply triple_letGetRegSep.
  triple_apply triple_setRegSep.

  (* JmpTgtM *)
  destruct m.
  case: sib => [[base indexAndScale] |].
  - destruct indexAndScale.
    destruct p0 as [rix sc].
    rewrite /interpMemSpecSrc.
    specintros => pase ixval addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    by triple_apply triple_setRegSep.
    rewrite /interpMemSpecSrc.
    specintros => pbase addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    by triple_apply triple_setRegSep.
    rewrite /interpMemSpecSrc.
    specintros => addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg.
    triple_apply triple_letGetDWORDSep.
    by triple_apply triple_setRegSep.

  (* JmpTgtR *)
  specintros => addr.
  apply TRIPLE_safe => R.
  rewrite /evalInstr/evalJmpTgt /evalRegMem /evalReg /evalPush.
  triple_apply triple_letGetRegSep.
  by triple_apply triple_setRegSep.
Qed.

(** ** unconditional jump *)
Lemma JMPrel_I_rule rel (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addB q rel) -->> safe @ (EIP ~= p)) <@
        (p -- q :-> JMPrel (mkTgt rel)).
Proof.
  specapply (JMPrel_rule (JmpTgtI (mkTgt rel))). by ssimpl.

  autorewrite with push_at. rewrite <-spec_reads_frame. apply limplValid.
  cancel1. cancel1. sbazooka.
Qed.

Lemma JMPrel_R_rule (r:Reg) addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr ** r ~= addr) -->> safe @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMPrel (JmpTgtR r)).
Proof.
  specapply (JMPrel_rule (JmpTgtR r)). by ssimpl.

  rewrite <-spec_reads_frame. autorewrite with push_at. rewrite limplValid.
  cancel1. cancel1. sbazooka.
Qed.
End InstrRules.
