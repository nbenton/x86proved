(** * NOT instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma NOT_rule d (src:RegMem d) v:
  |-- specAtRegMemDst src (fun V => basic (V v) (UOP d OP_NOT src) empOP (V (invB v))).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall d (src : RegMem d), instrrule (UOP d OP_NOT src) := @NOT_rule.

