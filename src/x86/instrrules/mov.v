(** * MOV instruction *)
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

(** ** Generic rule *)
Lemma MOV_rule d ds oldv:
  |-- specAtDstSrc ds (fun V v =>
      basic (V oldv) (MOVOP d ds) (V v)).
Proof. do_instrrule_triple. Qed.

Ltac basicMOV :=
  rewrite /makeMOV;
  let R := lazymatch goal with
             | |- |-- basic ?p (@MOVOP ?d ?a) ?q => constr:(@MOV_rule d a)
           end in
  basicapply R.


(** We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

(** ** Register to register *)
Lemma MOV_RR_rule (r1 r2:Reg) v1 v2:
  |-- basic (r1 ~= v1 ** r2 ~= v2) (MOV r1, r2) (r1 ~= v2 ** r2 ~= v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyR_rule (r1 r2:Reg) v2:
  |-- basic (r1? ** r2 ~= v2) (MOV r1, r2) (r1 ~= v2 ** r2 ~= v2).
Proof. unhideReg r1 => old. basicMOV. Qed.

(** ** Immediate to register *)
Lemma MOV_RI_rule (r:Reg) (v1 v2:DWORD) :
  |-- basic (r ~= v1) (MOV r, v2) (r ~= v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyI_rule (r:Reg) (v2:DWORD) :
  |-- basic r? (MOV r, v2) (r ~= v2).
Proof. unhideReg r => old. basicMOV. Qed.

(** ** Memory to register *)
Lemma MOV_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset])
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyM_rule (pd:DWORD) (r1 r2:Reg) offset (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd +# offset :-> v2)
            (MOV r1, [r2 + offset])
            (r1 ~= v2 ** r2 ~= pd ** pd +# offset :-> v2).
Proof. unhideReg r1 => old. basicMOV. Qed.

Lemma MOV_RM0_rule (pd:DWORD) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2])
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. basicMOV. Qed.

Lemma MOV_RanyM0_rule (pd:DWORD) (r1 r2:Reg) (v2: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd :-> v2)
            (MOV r1, [r2])
            (r1 ~= v2 ** r2 ~= pd ** pd :-> v2).
Proof. unhideReg r1 => old. basicMOV. Qed.

(** ** Register to memory *)
Lemma MOV_MR_rule (p: DWORD) (r1 r2: Reg) offset (v1 v2:DWORD) :
  |-- basic (r1~=p ** p +# offset :-> v1 ** r2~=v2)
            (MOV [r1 + offset], r2)
            (r1~=p ** p +# offset :-> v2 ** r2~=v2).
Proof. basicMOV. Qed.

(** ** Immediate to memory *)
Lemma MOV_MI_rule dword (pd:DWORD) (r:Reg) offset (v w:DWORDorBYTE dword) :
  |-- basic (r ~= pd ** pd +# offset :-> v)
            (MOVOP _ (DstSrcMI dword (mkMemSpec (Some(r, None)) #offset) w))
            (r ~= pd ** pd +# offset :-> w).
Proof. basicMOV. Qed.

Lemma MOV_M0R_rule (pd:DWORD) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= pd ** pd :-> v1 ** r2 ~= v2)
            (MOV [r1], r2)
            (r1 ~= pd ** pd :-> v2 ** r2 ~= v2).
Proof. basicMOV. Qed.


Lemma MOV_MbR_rule (p: DWORD) (r1:Reg) (r2: BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v2)
            (MOV [r1 + offset], r2)
            (r1 ~= p ** p +# offset :-> v2 ** BYTEregIs r2 v2).
Proof. basicMOV. Qed.

Lemma MOV_MbR_ruleGen d (p: DWORD) (r1:Reg) (r2: DWORDorBYTEReg d) offset (v1 v2:DWORDorBYTE d):
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** DWORDorBYTEregIs r2 v2)
            (MOVOP d (DstSrcMR d (mkMemSpec (Some(r1,None)) #offset) r2))
            (r1 ~= p ** p +# offset :-> v2 ** DWORDorBYTEregIs r2 v2).
Proof.
  destruct d.
  { apply MOV_MR_rule. }
  { apply MOV_MbR_rule. }
Qed.

Lemma MOV_RMb_rule (p: DWORD) (r1:Reg) (r2:BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v2)
            (MOV r2, [r1 + offset])
            (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v1).
Proof. basicMOV. Qed.

Lemma MOV_MbI_rule (pd:DWORD) (r1:Reg) offset (v1 v2:BYTE) :
  |-- basic (r1 ~= pd ** pd +# offset :-> v1)
            (MOV BYTE [r1 + offset], v2)
            (r1 ~= pd ** pd +# offset :-> v2).
Proof. basicMOV. Qed.
End InstrRules.
