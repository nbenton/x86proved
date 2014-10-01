(** * PUSH instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic rule *)
Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w =>
      basic    (ESP ~= sp    ** sp-#4 :-> v) (PUSH src) empOP
               (ESP ~= sp-#4 ** sp-#4 :-> w)).
Proof. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall src : Src, instrrule (PUSH src) := @PUSH_rule.


(** ** PUSH r *)
Corollary PUSH_R_rule (r:GPReg32) sp (v w:DWORD) :
  |-- basic (r ~= v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH r) empOP
            (r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basic apply *. Qed.

(** ** PUSH v *)
Corollary PUSH_I_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w)
            (PUSH v) empOP
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basic apply *. Qed.

(** ** PUSH [r + offset] *)
Corollary PUSH_M_rule (r: GPReg32) (offset:nat) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r + offset]) empOP
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basic apply *. Qed.

(** ** PUSH [r] *)
Corollary PUSH_M0_rule (r: GPReg32) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** ESP ~= sp    ** sp-#4 :-> w)
            (PUSH [r]) empOP
            (r ~= pbase ** pbase :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basic apply *. Qed.
