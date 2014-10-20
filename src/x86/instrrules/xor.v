(** * XOR instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic XOR *)
Lemma XOR_rule s (ds:DstSrc s) (v1: VWORD s) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP _ OP_XOR ds) 
             (let v := xorB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (ds : DstSrc s), instrrule (BOP s OP_XOR ds) | 2 := @XOR_rule.

Lemma XOR_RR_rule s (r1 r2:VReg s) v1 (v2:VWORD s):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (XOR r1, r2) 
            (r1 ~= (xorB v1 v2) ** r2 ~= v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).
Proof. destruct s; basic apply *. Qed.

Lemma XOR_RM_rule (pd:DWORD) (r1 r2:VReg OpSize4) (v1 v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (XOR r1, [r2 + offset]) 
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. move => ?; subst. basic apply *. Qed.

(** We make the more specific rule have a higher priority *)
Global Instance: forall (r1 r2 : Reg) (offset : nat), instrrule (XOR r1, [r2 + offset]) | 0
  := fun r1 r2 offset pd v1 v2 => @XOR_RM_rule pd r1 r2 v1 v2 offset _ (refl_equal _).
Global Instance: forall d (r1 r2 : VReg d), instrrule (BOP d OP_XOR (DstSrcRR d r1 r2)) | 1
  := @XOR_RR_rule.

Corollary XOR_RM_ruleNoFlags (pd:DWORD) (r1 r2:VReg OpSize4) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) (r1~=xorB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basic apply *. Qed.
