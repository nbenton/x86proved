(** * IN instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for literal port *)
Require Import x86proved.triple.
Lemma IN_I_rule (c: BYTE) v w :
  |-- basic
      (AL ~= v) (IN c, AL) (inOP (zeroExtend n8 c) w) (AL ~= w).
Proof. instrrule_triple_bazooka. triple.core.triple_by_compute.
apply: separateSetRegPiece; eassumption. by rewrite !eq_refl. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Instance: forall (c : BYTE), instrrule (IN c, AL) := @IN_I_rule.
