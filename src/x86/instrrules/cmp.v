(** * CMP instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import Coq.Classes.Morphisms.
Require Import x86proved.spectac (* for [eforalls] *) x86proved.bitsprops (* for [low_catB] *) x86proved.septac (* for [ssplits] *).

(** ** Generic rule *)
Lemma CMP_rule sz (ds:DstSrc sz) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP _ OP_CMP ds) 
             (let: (carry,v) := eta_expand (sbbB false v1 v2) in
              D v1 ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (ds : DstSrc d), instrrule (BOP d OP_CMP ds) := @CMP_rule.

(** ** Generic rule with C and Z flags determining ltB and equality respectively *)
Section setoid_rewrite_opacity.
(** TODO(t-jagro): Figure out a way to [setoid_rewrite] without making [sepSP] opaque here *)
Local Opaque sepSP.
(** TODO(t-jagro): Figure out a way to not need to do so much setoid_rewriting manually *)
Lemma CMP_ruleZC d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d OP_CMP ds) 
             (D v1 ** OF? ** SF? ** ZF ~= (v1==v2) ** CF ~= ltB v1 v2 ** PF?)).
Proof.
  etransitivity; first by apply CMP_rule.
  eapply specAtDstSrc_entails_m.
  move => ? ?.
  setoid_rewrite <- sbbB_ZC'; [ | by apply prod_eta ].
  eapply basic_entails_m; try reflexivity.
  rewrite /OSZCP/stateIsAny; try ssplits => *; reflexivity.
Qed.
End setoid_rewrite_opacity.

Ltac basicCMP_ZC :=
  rewrite /makeBOP; 
  let R := lazymatch goal with
             | |- |-- basic ?p (@BOP ?d OP_CMP ?a) ?q => constr:(@CMP_ruleZC d a)
           end in
  basic apply R.


(** ** Special cases *)
Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2) 
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof. basic apply *. Qed.

(** Too bad there are no hint databases for ssr [rewrite] *)
(*Lemma CMP_RbI_rule (r1:VReg OpSize1) (v1 v2:BYTE):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2) 
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
  r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res) (res == #0) carry (lsb res)).
Proof. attempt basic apply (@CMP_rule OpSize1 _ v1). by rewrite low_catB. Qed.
*)

Lemma CMP_RM_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD) :
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP r1, [r2+offset]) 
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basic apply *. Qed.

Lemma CMP_MR_rule (pd:DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (CMP [r2+offset], r1) 
            (let: (carry,res) := eta_expand (sbbB false v2 v1) in
             r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof. basic apply *. Qed.

Lemma CMP_MR_ZC_rule (pd: DWORD) (r1 r2:Reg) offset (v1 v2:DWORD):
  |-- basic (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OSZCP?) (CMP [r1+offset], r2) 
            (r1 ~= pd ** r2 ~= v2 ** pd +# offset :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_IndR_ZC_rule (pd: DWORD) (r:Reg) (v1 v2:DWORD):
  |-- basic (r ~= v2 ** pd :-> v1 ** OSZCP?) (CMP [pd], r) 
            (r ~= v2 ** pd :-> v1 ** OF? ** SF? ** PF? **
                        CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (CMP r1, r2) 
            (let: (carry,res) := eta_expand (sbbB false v1 v2) in
             r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof. basic apply *. Qed.


Lemma CMP_RI_ZC_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP?) (CMP r1, v2) 
            (r1 ~= v1 ** OF? ** SF? ** PF? ** CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.

Lemma CMP_MbR_ZC_rule (r1:Reg) (r2: BYTEReg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** r2 ~= v2 ** p :-> v1 ** OSZCP?) (CMP [r1], r2) 
            (r1 ~= p ** r2 ~= v2 ** p :-> v1 ** OF? ** SF? ** PF? **
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
  |-- basic (r1 ~= v1 ** OSZCP?) (BOP _ OP_CMP (DstSrcRI OpSize1 r1 v2)) 
            (r1 ~= v1 ** OF? ** SF? ** PF? **
                         CF ~= ltB v1 v2 ** ZF ~= (v1==v2)).
Proof. basicCMP_ZC. Qed.
