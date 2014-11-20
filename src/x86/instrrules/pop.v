(** * POP instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic POP *)
Lemma POP_rule (rm:RegMem OpSize8) (sp:ADDR) (oldv v:QWORD):
  |-- specAtRegMemDst rm (fun V =>
      basic (V oldv ** RSP ~= sp    ** sp:->v) (POP rm) empOP
            (V v    ** RSP ~= sp+#8 ** sp:->v)).
Proof. do_instrrule_triple. Qed. 

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (rm : RegMem _), instrrule (POP rm) := @POP_rule.
