(** * ADD and SUB instructions *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic ADD/SUB rule *)
Lemma ADDSUB_rule isSUB d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d (if isSUB then OP_SUB else OP_ADD) ds)
             (let v := (if isSUB then subB v1 v2 else addB v1 v2) in
              let carry := (if isSUB then carry_subB v1 v2 else carry_addB v1 v2) in
              D v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof. do_instrrule_triple. Qed.

(** Only succeed if we don't generate more than one goal. *)
Ltac basicADDSUB :=
  rewrite /makeBOP;
  let R := (lazymatch goal with
              | |- |-- basic ?p (@BOP ?d OP_ADD ?a) ?q => constr:(@ADDSUB_rule false d a)
              | |- |-- basic ?p (@BOP ?d OP_SUB ?a) ?q => constr:(@ADDSUB_rule true d a)
            end) in
  first [ instrrules_basicapply R using (fun H => idtac)
        | instrrules_basicapply R ].


(** ** Special cases *)
(** *** ADD r, v2 *)
Corollary ADD_RI_rule (r:Reg) v1 (v2:DWORD):
  |-- basic (r~=v1 ** OSZCP?) (ADD r, v2)
            (let: (carry,v) := eta_expand (adcB false v1 v2) in
             r~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Corollary ADD_RI_ruleNoFlags (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1) (ADD r1, v2) (r1~=addB v1 v2) @ OSZCP?.
Proof. apply: basicForgetFlags; apply ADD_RI_rule. Qed.

(** *** ADD r1, r2 *)
Corollary ADD_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2)
            (let: (carry,v) := eta_expand (adcB false v1 v2) in
             r1~=v ** r2~=v2 ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Corollary ADD_RR_ruleNoFlags (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2)
            (r1~=addB v1 v2 ** r2~=v2 ** OSZCP?).
Proof. basicADDSUB. Qed.

Corollary ADD_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (ADD r1, [r2 + offset])
            (let: (carry,v) := eta_expand (adcB false v1 v2) in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Corollary ADD_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (ADD r1, [r2 + offset]) (r1~=addB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basicADDSUB. Qed.

Lemma SUB_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (SUB r1, [r2 + offset])
            (let: (carry,v) := eta_expand (sbbB false v1 v2) in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Corollary SUB_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (SUB r1, [r2 + offset]) (r1~=subB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basicADDSUB. Qed.

Lemma SUB_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (SUB r1, r2)
            (let: (carry,v) := eta_expand (sbbB false v1 v2) in r1~=v  ** r2~=v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.

Lemma SUB_RI_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** OSZCP?) (SUB r1, v2)
            (let: (carry,v) := eta_expand (sbbB false v1 v2) in
             r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basicADDSUB. Qed.
