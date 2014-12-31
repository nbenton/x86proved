(** * NEG instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** Special case for negation *)
Lemma NEG_rule s (src: RegMem s) (v:VWORD s) :
  let w := negB v in
  |-- specAtRegMemDst src (fun V =>
    basic (V v ** OSZCP?) (UOP s OP_NEG src)
          (V w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (src : RegMem s), instrrule (UOP _ OP_NOT src) := @NEG_rule.
