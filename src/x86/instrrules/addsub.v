(** * ADD and SUB instructions *)
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

(** ** Generic ADD/SUB rule *)
Lemma ADDSUB_rule isSUB d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d (if isSUB then OP_SUB else OP_ADD) ds)
             (let: (carry,v) := (if isSUB then sbbB else adcB) false v1 v2 in
              D v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof.
  rewrite /specAtDstSrc.
  destruct ds.
  (* RR *)
  specintros => v2.
  autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply evalDWORDorBYTEReg_rule.
  rewrite /evalBinOp/evalArithOpNoCarry.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).
  (* RM *)
  rewrite /specAtMemSpec.
  elim:src => [optSIB offset].
  elim: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => v2 pbase ixval.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).
(* Non-indexed *)
  + specintros => v2 pbase.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).
(* offset only *)
  + specintro => v2.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.  rewrite /evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).

  (* MR *)
  specintros => v2. rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  case: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].
(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 v2) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
  (* RI *)
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false _ _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTERegSep).

  (* MI *)
  rewrite /specAtMemSpecDst.
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |].

(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
  destruct isSUB;
    (elim: (_ false v1 _) => [carry v];
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setDWORDorBYTESep).
Qed.

Ltac basicADDSUB :=
  try unfold makeBOP;
  match goal with
  | |- |-- basic ?p (@BOP ?d OP_ADD ?a) ?q => try_basicapply (@ADDSUB_rule false d a)
  | |- |-- basic ?p (@BOP ?d OP_SUB ?a) ?q => try_basicapply (@ADDSUB_rule true d a)
  | _ => idtac
  end.

(* Special cases *)
(* ADD r, v2 *)
Corollary ADD_RI_rule (r:Reg) v1 (v2:DWORD):
  |-- basic (r~=v1 ** OSZCP?) (ADD r, v2)
            (let: (carry,v) := adcB false v1 v2 in
             r~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Corollary ADD_RI_ruleNoFlags (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1) (ADD r1, v2) (r1~=addB v1 v2) @ OSZCP?.
Proof. apply: basicForgetFlags; apply ADD_RI_rule. Qed.

(** ** ADD r1, r2 *)
Corollary ADD_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2)
            (let: (carry,v) := adcB false v1 v2 in
             r1~=v ** r2~=v2 ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicADDSUB. sbazooka. elim: (adcB _) => [carry v]. by ssimpl. Qed.

Corollary ADD_RR_ruleNoFlags (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2)
            (r1~=addB v1 v2 ** r2~=v2 ** OSZCP?).
Proof.
rewrite /dropmsb.
basicADDSUB.
elim: (adcB _) => [carry v].
rewrite /OSZCP/stateIsAny. simpl snd. sbazooka.
Qed.

Corollary ADD_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (ADD r1, [r2 + offset])
            (let: (carry,v) := adcB false v1 v2 in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. elim: (adcB _) => [carry v]. by ssimpl. Qed.

Corollary ADD_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (ADD r1, [r2 + offset]) (r1~=addB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
basicADDSUB.
rewrite /OSZCP/stateIsAny/dropmsb/snd.
elim: (adcB _) => [carry v].
sbazooka.
Qed.

Lemma SUB_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (SUB r1, [r2 + offset])
            (let: (carry,v) := sbbB false v1 v2 in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. elim (sbbB _) => [carry v]. by ssimpl. Qed.

Corollary SUB_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (SUB r1, [r2 + offset]) (r1~=subB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof.
autorewrite with push_at.
elim E: (sbbB _ _ _) => [carry v].
basicADDSUB.
rewrite /OSZCP/stateIsAny/snd E. sbazooka.
Qed.

Lemma SUB_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (SUB r1, r2)
            (let: (carry,v) := sbbB false v1 v2 in r1~=v  ** r2~=v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. elim (sbbB _ _ _) => [carry v]. by ssimpl. Qed.

Lemma SUB_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** OSZCP?) (SUB r1, v2)
            (let: (carry,v) := sbbB false v1 v2 in
             r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.
End InstrRules.
