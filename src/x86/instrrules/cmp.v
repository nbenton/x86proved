(** * CMP instruction *)
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

(** ** Generic rule *)
Lemma CMP_rule d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds)
             (let: (carry,v) := sbbB false v1 v2 in
              D v1 ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
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
  elim: (_ false v1 v2) => [carry v]. simpl fst. simpl snd.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doUpdateZPS. triple_apply triple_skip.
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
    (elim: (_ false v1 v2) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Non-indexed *)
  + specintros => v2 pbase.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDorBYTESep.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* offset only *)
  + specintro => v2.
    autorewrite with push_at. apply TRIPLE_basic => R. rewrite /evalInstr/evalDstSrc/evalDstR.
    triple_apply evalDWORDorBYTEReg_rule.  rewrite /evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).

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
    (elim: (_ false v1 v2) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply evalDWORDorBYTEReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 v2) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
  (* RI *)
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDstSrc/evalDstR.
  triple_apply evalDWORDorBYTEReg_rule.
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 _) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).

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
    (elim: (_ false v1 _) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 _) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R.
    rewrite /evalInstr/evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDorBYTESep.
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    rewrite /evalBinOp/evalArithOpNoCarry.
    (elim: (_ false v1 _) => [carry v]; simpl fst; simpl snd;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_skip).
Qed.

(* Generic rule with C and Z flags determining ltB and equality respectively *)
Lemma CMP_ruleZC d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds)
             (D v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2))).
Proof.
have C := (CMP_rule ds) v1. rewrite /specAtDstSrc in C. rewrite /specAtDstSrc.
destruct ds.
+ specintros => v. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
+ destruct src as [optSIB offset].
  destruct optSIB as [[base ixopt] |].
  destruct ixopt as [[ixr sc] |].
  rewrite /specAtMemSpec. rewrite /specAtMemSpec in C.
  specintros => v pbase ixval. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  rewrite /specAtMemSpec. rewrite /specAtMemSpec in C.
  specintros => v pbase. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  rewrite /specAtMemSpec. rewrite /specAtMemSpec in C.
  specintros => v. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  specintros => v. rewrite /specAtMemSpecDst. rewrite /specAtMemSpecDst in C.
  destruct dst as [optSIB offset].
  destruct optSIB as [[base ixopt] |].
  destruct ixopt as [[ixr sc] |].
  specintros => pbase ixval. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  specintros => pbase. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 v) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.

  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.

rewrite /specAtMemSpecDst. rewrite /specAtMemSpecDst in C.
  destruct dst as [optSIB offset].
  destruct optSIB as [[base ixopt] |].
  destruct ixopt as [[ixr sc] |].
  specintros => pbase ixval. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
  specintros => pbase. autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
autorewrite with push_at.
  eapply basic_basic. eforalls C. autorewrite with push_at in C.
  apply C. sbazooka. elim E:(sbbB false v1 c) => [carry r].
  rewrite /OSZCP/stateIsAny. sbazooka.
  by apply sbbB_ZC.
Qed.

Ltac basicCMP :=
  try unfold makeBOP;
  match goal with
  | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => try_basicapply (@CMP_rule d a)
  | _ => idtac
  end.

Ltac basicCMP_ZC :=
  try unfold makeBOP;
  match goal with
  | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => try_basicapply (@CMP_ruleZC d a)
  | _ => idtac
  end.


(** ** Special cases *)
Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2)
            (let: (carry,res) := sbbB false v1 v2 in
             r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_RbI_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (CMP r1, v2)
            (let: (carry,res) := sbbB false v1 v2 in
  BYTEregIs r1 v1 ** OSZCP (computeOverflow v1 v2 res) (msb res) (res == #0) carry (lsb res)).
Proof. rewrite /BYTEtoDWORD/makeBOP low_catB. basicCMP. Qed.

Lemma CMP_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP r1, [r2+offset])
            (let (carry,res) := sbbB false v1 v2 in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP.
case E: (sbbB false v1 v2) => [carry res].
sbazooka.
Qed.

Lemma CMP_MR_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP [r2+offset], r1)
            (let (carry,res) := sbbB false v2 v1 in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP.
case E: (sbbB false v2 v1) => [carry res].
sbazooka.
Qed.

Lemma CMP_MR_ZC_rule (pd: DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OSZCP?) (CMP [r1+offset], r2)
            (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (CMP r1, r2)
            (let: (carry,res) := sbbB false v1 v2 in
             r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof. basicCMP. destruct (sbbB false v1 v2); by ssimpl. Qed.


Lemma CMP_RI_ZC_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2)
            (r1 ~= v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbR_ZC_rule (r1:Reg) (r2: BYTEReg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OSZCP?) (CMP [r1], r2)
            (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbI_ZC_rule (r1:Reg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** p :-> v1 ** OSZCP?) (CMP BYTE [r1], v2)
            (r1 ~= p ** p :-> v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbxI_ZC_rule (r1:Reg) (r2:NonSPReg) (p ix:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OSZCP?) (CMP BYTE [r1 + r2 + 0], v2)
            (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC; rewrite /scaleBy; by ssimpl. Qed.


Lemma CMP_RbI_ZC_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (BOP false OP_CMP (DstSrcRI false r1 v2))
            (BYTEregIs r1 v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.
End InstrRules.
