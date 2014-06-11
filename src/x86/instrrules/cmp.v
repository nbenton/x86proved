(** * CMP instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import common_definitions.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(** ** Generic rule *)
Lemma CMP_rule d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds)
             (let: (carry,v) := eta_expand (sbbB false v1 v2) in
              D v1 ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof. do_instrrule_triple. Qed.

Lemma sbbB_ZC n (r : BITS n) carry (v1 v: BITS n) :
  sbbB false v1 v = (carry, r) ->
   ZF~=(r == #(0)) ** CF~=carry |-- CF~=ltB v1 v ** ZF~=(v1 == v).
Proof. move => E.
  have S0 := subB_eq0 v1 v. rewrite E/snd in S0. rewrite S0.
  have HH := (sbbB_ltB_leB v1 v). rewrite E/fst in HH.
  destruct carry. + rewrite HH. by ssimpl. + rewrite ltBNle HH /negb. by ssimpl.
Qed.


(** TODO(t-jagro): Figure out a more systematic way to do this. *)
Local Ltac CMP_ruleZC_t v1 :=
  (move => *; try specintros => *; autorewrite with push_at);
  let C := match goal with | [ C : |-- _ |- _ ] => constr:(C) end in
  eapply basic_basic;
  [ by (eforalls C; autorewrite with push_at in C; apply C)
  | by sbazooka
  | ];
  (elim E:(sbbB false v1 _) => [? ?]);
  rewrite /OSZCP/stateIsAny; sbazooka;
    by apply sbbB_ZC.

(* Generic rule with C and Z flags determining ltB and equality respectively *)
Lemma CMP_ruleZC d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds)
             (D v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2))).
Proof.
  generalize (CMP_rule ds v1).
  do_instrrule (CMP_ruleZC_t v1).
Qed.

Ltac basicCMP :=
  rewrite /makeBOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => constr:(@CMP_rule d a)
           end in
  basicapply R.

Ltac basicCMP_ZC :=
  rewrite /makeBOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => constr:(@CMP_ruleZC d a)
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

(** TODO(t-jagro): Find a better place to put this *)
Hint Unfold scaleBy : spred.

(** ** Special cases *)
Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2)
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_RbI_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (CMP r1, v2)
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
  BYTEregIs r1 v1 ** OSZCP (computeOverflow v1 v2 res) (msb res) (res == #0) carry (lsb res)).
Proof. rewrite /BYTEtoDWORD/makeBOP low_catB. basicCMP. Qed.

Lemma CMP_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP r1, [r2+offset])
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_MR_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP [r2+offset], r1)
            (let: (carry,res) := eta_expand (sbbB false v2 v1) in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_MR_ZC_rule (pd: DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OSZCP?) (CMP [r1+offset], r2)
            (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (CMP r1, r2)
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.


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
Proof. basicCMP_ZC. Qed.


Lemma CMP_RbI_ZC_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (BOP false OP_CMP (DstSrcRI false r1 v2))
            (BYTEregIs r1 v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.
End InstrRules.
