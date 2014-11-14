(** * XOR instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic XOR *)
Lemma XOR_rule s (ds:DstSrc s) (v1: VWORD s) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP _ OP_XOR ds) empOP
             (let v := xorB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof. do_instrrule_triple. Qed.

Lemma XOR_self_rule s (r:GPReg s) (v:VWORD s) :
  |-- basic (r ~= v ** OSZCP?) (XOR r, r) empOP
            (r ~= #0 ** OSZCP false false true false false).
Proof.
  destruct s; do_instrrule (instrrule_triple_bazooka; rewrite bitsopsprops.xorBB eq_refl; instrrule_triple_bazooka).
Qed.


Global Instance: forall s (r: GPReg s), instrrule (XOR r, r) | 1 := @XOR_self_rule.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (ds : DstSrc s), instrrule (BOP s OP_XOR ds) | 2 := @XOR_rule.

(* Our original formalization defined a bunch of more specific rules such as the following.
   These are now simple corollaries of the general rule above i.e. "examples" *)
Example XOR_RR_rule s (r1 r2:GPReg s) v1 (v2:VWORD s):
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP?) (XOR r1, r2) empOP
            (r1 ~= (xorB v1 v2) ** r2 ~= v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).
Proof. destruct s; basic apply *. Qed.

Example XOR_RM_rule (pd:DWORD) (r1 r2:GPReg OpSize4) (v1 v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** eval.computeAddr (a:=AdSize4) pd offset :-> v2 ** OSZCP?)
            (XOR r1, [r2 + offset]) empOP
            (r1~=v ** r2 ~= pd ** eval.computeAddr (a:=AdSize4) pd offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. move => ?; subst. basic apply *. Qed.

Example XOR_RM_ruleNoFlags (pd:DWORD) (r1 r2:GPReg OpSize4) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) empOP (r1~=xorB v1 v2)
             @ (r2 ~= pd ** eval.computeAddr (a:=AdSize4) pd offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. basic apply *. Qed.
