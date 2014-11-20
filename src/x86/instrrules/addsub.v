(** * ADD and SUB instructions *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic ADD/SUB rule *)
Lemma ADDSUB_rule isSUB d (ds:DstSrc d) v1 :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP d (if isSUB then OP_SUB else OP_ADD) ds) empOP
             (let v := (if isSUB then subB v1 v2 else addB v1 v2) in
              let carry := (if isSUB then carry_subB v1 v2 else carry_addB v1 v2) in
              D v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (ds : DstSrc d), instrrule (BOP d OP_SUB ds) := @ADDSUB_rule true.
Global Instance: forall d (ds : DstSrc d), instrrule (BOP d OP_ADD ds) := @ADDSUB_rule false.

(** ** Special cases *)
(** *** ADD r, v2 *)
Corollary ADD_RI_rule (r:GPReg32) v1 (v2:DWORD):
  |-- basic (r~=v1 ** OSZCP?) (ADD r, v2) empOP
            (let: (carry,v) := eta_expand (adcB false v1 v2) in
             r~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basic apply *. Qed.

Corollary ADD_RI_ruleNoFlags (r1:GPReg32) v1 (v2:DWORD):
  |-- basic (r1~=v1) (ADD r1, v2) empOP (r1~=addB v1 v2) @ OSZCP?.
Proof. apply: basicForgetFlags; apply ADD_RI_rule. Qed.

(** *** ADD r1, r2 *)
Corollary ADD_RR_rule (r1 r2:GPReg32) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2) empOP
            (let: (carry,v) := eta_expand (adcB false v1 v2) in
             r1~=v ** r2~=v2 ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basic apply *. Qed.

Corollary ADD_RR_ruleNoFlags (r1 r2:GPReg32) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (ADD r1, r2) empOP
            (r1~=addB v1 v2 ** r2~=v2 ** OSZCP?).
Proof. basic apply *. Qed.

(*
Corollary ADD_RM_rule (pd:ADDR) (r1 r2:GPReg64) v1 (v2:ADDR) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** eval.computeAddr (a:=AdSize8) pd offset :-> v2 ** OSZCP?)
            (ADD r1, QWORD PTR [r2 + offset]) empOP
            (let: (carry,v) := eta_expand (adcB false v1 v2) in
             r1~=v ** r2 ~= pd ** eval.computeAddr (a:=AdSize8) pd offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basic apply *. Qed.
*)

(*
Corollary ADD_RM_ruleNoFlags (pd:DWORD) (r1 r2:GPReg32) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (ADD r1, [r2 + offset]) empOP (r1~=addB v1 v2)
             @ (r2 ~= pd ** eval.computeAddr pd offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basic apply *. Qed.

Lemma SUB_RM_rule (pd:DWORD) (r1 r2:GPReg32) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** eval.computeAddr pd offset :-> v2 ** OSZCP?)
            (SUB r1, [r2 + offset]) empOP
            (let: (carry,v) := eta_expand (sbbB false v1 v2) in
             r1~=v ** r2 ~= pd ** eval.computeAddr pd offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basic apply *. Qed.

Corollary SUB_RM_ruleNoFlags (pd:DWORD) (r1 r2:GPReg32) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (SUB r1, [r2 + offset]) empOP (r1~=subB v1 v2)
             @ (r2 ~= pd ** eval.computeAddr pd offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basic apply *. Qed.

Lemma SUB_RR_rule (r1 r2:GPReg32) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP?) (SUB r1, r2) empOP
            (let: (carry,v) := eta_expand (sbbB false v1 v2) in r1~=v  ** r2~=v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basic apply *. Qed.

Lemma SUB_RI_rule (r1:GPReg32) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** OSZCP?) (SUB r1, v2) empOP
            (let: (carry,v) := eta_expand (sbbB false v1 v2) in
             r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof. basic apply *. Qed.
*)