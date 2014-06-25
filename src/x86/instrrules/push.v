(** * PUSH instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic rule *)
Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w =>
      basic    (ESP ~= sp    ** sp-#4 :-> v) (PUSH src)
               (ESP ~= sp-#4 ** sp-#4 :-> w)).
Proof. do_instrrule_triple. Qed.

Ltac basicPUSH :=
  let R := lazymatch goal with
             | |- |-- basic ?p (PUSH ?a) ?q => constr:(PUSH_rule a)
           end in
  instrrules_basicapply R.

(** ** PUSH r *)
Corollary PUSH_R_rule (r:Reg) sp (v w:DWORD) :
  |-- basic (r ~= v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH r)
            (r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(** ** PUSH v *)
Corollary PUSH_I_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w)
            (PUSH v)
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(** ** PUSH [r + offset] *)
Corollary PUSH_M_rule (r: Reg) (offset:nat) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r + offset])
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.

(** ** PUSH [r] *)
Corollary PUSH_M0_rule (r: Reg) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r])
            (r ~= pbase ** pbase :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicPUSH. Qed.
