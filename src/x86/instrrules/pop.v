(** * POP instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic POP *)
Lemma POP_rule s (rm:RegMem s) (sp:ADDR) (oldv v:VWORD s):
  |-- specAtRegMemDst rm (fun V =>
      basic (V oldv ** RSP ~= sp    ** sp:->v) (POP rm)
            (V v    ** RSP ~= sp+#opSizeToNat s ** sp:->v)).
Proof. do_instrrule_triple. Qed. 

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (rm : RegMem s), instrrule (POP rm) := @POP_rule.
