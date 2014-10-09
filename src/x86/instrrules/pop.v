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


(** ** POP r *)
Corollary POP_R_rule (r:GPReg64) (sp oldv v:QWORD) :
  |-- basic (r ~= oldv ** RSP ~= sp    ** sp:->v) (POP (RegMemR OpSize8 r)) empOP
            (r ~= v    ** RSP ~= sp+#8 ** sp:->v).
Proof. basic apply *. Qed.

(** ** POP [r + offset] *)
(*Corollary POP_M_rule (r:GPReg64) (offset:nat) (sp oldv v pbase:QWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> oldv ** RSP ~= sp ** sp :-> v)
            (POP [r + offset]) empOP
            (r ~= pbase ** pbase +# offset :-> v ** RSP ~= sp+#8 ** sp :-> v).

Proof. basic apply *. Qed.

(** ** POP [r] *)
Corollary POP_M0_rule (r: GPReg32) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> oldv ** ESP ~= sp    ** sp :-> v)
            (POP [r]) empOP
            (r ~= pbase ** pbase :-> v    ** ESP ~= sp+#4 ** sp :-> v).
Proof. basic apply *. Qed.
*)