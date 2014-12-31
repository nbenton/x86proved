(** * XOR instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.
Require Import program.

Lemma XOR_rule s (ds:DstSrc s) (v1: VWORD s) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP _ OP_XOR ds) 
             (let v := xorB v1 v2 in

              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof. do_instrrule_triple. Qed. 

Lemma XOR_self_rule s (r:GPReg s) (v:VWORD s) :
  |-- basic (r ~= v ** OSZCP?) (XOR r, r) 
            (r ~= #0 ** OSZCP false false true false false).
Proof. 
  Hint Rewrite bitsopsprops.xorBB eq_refl : triple.
  destruct s; do_instrrule_triple.
Qed.

Global Instance: forall s (r: GPReg s), instrrule (XOR r, r) | 1 := @XOR_self_rule.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (ds : DstSrc s), instrrule (BOP s OP_XOR ds) | 2 := @XOR_rule.

