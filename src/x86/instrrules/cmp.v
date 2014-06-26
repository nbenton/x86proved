(** * CMP instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import spectac (* for [eforalls] *) bitsprops (* for [low_catB] *).

(** ** Generic rule *)
Lemma CMP_rule d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds) empOP
             (let: (carry,v) := eta_expand (sbbB false v1 v2) in
              D v1 ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof. do_instrrule_triple. Qed.

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

(** ** Generic rule with C and Z flags determining ltB and equality respectively *)
(** TODO(t-jagro): speed this up by proving that entailment of the result from basic plays well with [specAtDstSrc] *)
Lemma CMP_ruleZC d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds) empOP
             (D v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2))).
Proof.
  generalize (CMP_rule ds v1).
  do_instrrule (CMP_ruleZC_t v1).
Qed.

Ltac basicCMP :=
  rewrite /makeBOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?O ?q => constr:(@CMP_rule d a)
           end in
  instrrules_basicapply R.

Ltac basicCMP_ZC :=
  rewrite /makeBOP;
  let R := lazymatch goal with
             | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?O ?q => constr:(@CMP_ruleZC d a)
           end in
  instrrules_basicapply R.


(** ** Special cases *)
Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2) empOP
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_RbI_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (CMP r1, v2) empOP
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
  BYTEregIs r1 v1 ** OSZCP (computeOverflow v1 v2 res) (msb res) (res == #0) carry (lsb res)).
Proof. rewrite /BYTEtoDWORD/makeBOP low_catB. basicCMP. Qed.

Lemma CMP_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP r1, [r2+offset]) empOP
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_MR_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP [r2+offset], r1) empOP
            (let: (carry,res) := eta_expand (sbbB false v2 v1) in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.

Lemma CMP_MR_ZC_rule (pd: DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OSZCP?) (CMP [r1+offset], r2) empOP
            (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (CMP r1, r2) empOP
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof. basicCMP. Qed.


Lemma CMP_RI_ZC_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2) empOP
            (r1 ~= v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbR_ZC_rule (r1:Reg) (r2: BYTEReg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OSZCP?) (CMP [r1], r2) empOP
            (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbI_ZC_rule (r1:Reg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** p :-> v1 ** OSZCP?) (CMP BYTE [r1], v2) empOP
            (r1 ~= p ** p :-> v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbxI_ZC_rule (r1:Reg) (r2:NonSPReg) (p ix:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OSZCP?) (CMP BYTE [r1 + r2 + 0], v2) empOP
            (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.


Lemma CMP_RbI_ZC_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP?) (BOP false OP_CMP (DstSrcRI false r1 v2)) empOP
            (BYTEregIs r1 v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.
