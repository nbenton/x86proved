(** * TEST instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.bitsopsprops (* for [andBB] *).

Lemma TEST_self_rule (r:VReg OpSize4) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP?) (TEST r, r) empOP
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  do_instrrule (instrrule_triple_bazooka; rewrite andBB; instrrule_triple_bazooka).
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (r : Reg), instrrule (TEST r, r) := @TEST_self_rule.
