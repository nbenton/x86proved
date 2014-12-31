(** * TEST instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.bitsopsprops (* for [andBB] *).

Lemma TEST_self_rule s (r:GPReg s) (v:VWORD s) :
  |-- basic (r ~= v ** OSZCP?) (TEST r, r) 
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  Hint Rewrite andBB : triple.
  do_instrrule_triple.
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (r : GPReg s), instrrule (TEST r, r) := @TEST_self_rule.

