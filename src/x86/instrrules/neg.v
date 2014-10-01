(** * NEG instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for negation *)
Lemma NEG_R_rule s (r:VReg s) (v:VWORD s) :
  let w := negB v in
  |-- basic
    (r ~= v ** OSZCP?) (NEG r) empOP
    (r ~= w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof. destruct s; do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (r : VReg s), instrrule (NEG r) := @NEG_R_rule.
