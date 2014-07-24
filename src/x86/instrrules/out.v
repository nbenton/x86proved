(** * OUT instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for literal port *)
Lemma OUT_I_rule (c: BYTE) d :
  |-- basic
      (BYTEregIs AL d) (OUT c, AL) (outOP (zeroExtend 8 c) d) (BYTEregIs AL d).
Proof. instrrule_triple_bazooka. by triple.core.triple_by_compute. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Instance: forall (c : BYTE), instrrule (OUT c, AL) := @OUT_I_rule.
