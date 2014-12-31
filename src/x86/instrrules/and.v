(** * AND instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic AND *)
Lemma AND_rule s (ds:DstSrc s) (v1: VWORD s) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP?)
             (BOP _ OP_AND ds) 
             (let v := andB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof. destruct ds; do_instrrule_triple. Qed. 

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (ds : DstSrc s), instrrule (BOP _ OP_AND ds) := @AND_rule.

