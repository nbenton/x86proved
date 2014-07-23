(** * POP instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic POP *)
Lemma POP_rule (rm:RegMem true) (sp:DWORD) (oldv v:DWORD):
  |-- specAtRegMemDst rm (fun V =>
      basic (V oldv ** ESP ~= sp    ** sp:->v) (POP rm) empOP
            (V v    ** ESP ~= sp+#4 ** sp:->v)).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, after unfolding various things in its type. *)
Section handle_type_of_rule.
  Context (rm : RegMem true).
  Let rule := @POP_rule rm.
  Let T := Eval cbv beta iota zeta delta [specAtRegMemDst] in (fun T (x : T) => T) _ rule.
  Global Instance: instrrule (POP rm) := rule : T.
End handle_type_of_rule.

Ltac basicPOP :=
  let R := lazymatch goal with
             | |- |-- basic ?p (POP ?a) ?O ?q => constr:(POP_rule a)
           end in
  instrrules_basicapply R.


(** ** POP r *)
Corollary POP_R_rule (r:Reg) (sp oldv v:DWORD) :
  |-- basic (r ~= oldv ** ESP ~= sp    ** sp:->v) (POP (RegMemR true r)) empOP
            (r ~= v    ** ESP ~= sp+#4 ** sp:->v).
Proof. basicPOP. Qed.

(** ** POP [r + offset] *)
Corollary POP_M_rule (r:Reg) (offset:nat) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> oldv ** ESP ~= sp ** sp :-> v)
            (POP [r + offset]) empOP
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp+#4 ** sp :-> v).
Proof. basicPOP. Qed.

(** ** POP [r] *)
Corollary POP_M0_rule (r: Reg) (sp oldv v pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> oldv ** ESP ~= sp    ** sp :-> v)
            (POP [r]) empOP
            (r ~= pbase ** pbase :-> v    ** ESP ~= sp+#4 ** sp :-> v).
Proof. basicPOP. Qed.
