(** * CALL (rel) instruction *)
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

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> safe @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt.
  destruct tgt.

  (* JmpTgtI *)
  destruct t.
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg.
  triple_apply triple_letGetRegSep.
  rewrite /evalJmpTgt.
  triple_apply triple_letGetRegSep.
  triple_apply triple_doSetRegSep.
  by triple_apply evalPush_rule.

  (* JmpTgtM *)
  destruct m.
  - case: sib => [[base indexAndScale] |].
    destruct indexAndScale.
    destruct p0 as [rix sc].
    rewrite /interpMemSpecSrc. specintros => pbase indexval addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.
    rewrite /interpMemSpecSrc. specintros => pbase addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.
    rewrite /interpMemSpecSrc. specintros => addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg.
    triple_apply triple_letGetRegSep.
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.

  (* JmpTgtR *)
  specintros => addr.
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg.
  triple_apply triple_letGetRegSep.
  triple_apply triple_letGetRegSep.
  triple_apply triple_doSetRegSep.
  by triple_apply evalPush_rule.
Qed.

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, Forall p', (
      |> safe @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof.
  specintros => w sp p'.
  specapply (CALLrel_rule p q (JmpTgtR r)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, (
      |> safe @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof.
  specintros => w sp.
  specapply (CALLrel_rule p q (JmpTgtI rel)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at.
  cancel1. cancel1. sbazooka.
Qed.
End InstrRules.
