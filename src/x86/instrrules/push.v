(** * PUSH instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

(** ** Generic rule *)
Lemma PUSH_rule s (src:Src s) sp (v:VWORD s) :
  |-- specAtSrc src (fun w =>
      basic    (RSP ~= sp    ** sp-#opSizeToNat s :-> v) (PUSH src)
               (RSP ~= sp-#opSizeToNat s ** sp-#opSizeToNat s :-> w)).
Proof. destruct src; do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall s (src : Src s), instrrule (PUSH src) := @PUSH_rule.


(** ** PUSH r *)
Corollary PUSH_R_rule s (r:GPReg s) sp (v w:VWORD s) :
  |-- basic (r ~= v ** RSP ~= sp    ** sp-#opSizeToNat s :-> w)
            (PUSH r) 
            (r ~= v ** RSP ~= sp-#opSizeToNat s ** sp-#opSizeToNat s :-> v).
Proof. basic apply *. Qed.

(** ** PUSH v *)
Corollary PUSH_I_rule (sp w:QWORD) (v:DWORD) :
  |-- basic (RSP ~= sp    ** sp-#8 :-> w)
            (PUSH (SrcI OpSize8 v)) 
            (RSP ~= sp-#8 ** sp-#8 :-> signExtend _ v).
Proof. basic apply *. Qed.

(** ** PUSH [r + offset] *)
(*Corollary PUSH_M_rule (r: GPReg64) (offset:nat) (sp w pbase:QWORD) (v:QWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** RSP ~= sp    ** sp-#8 :-> w)
            (PUSH [r + offset]) 
            (r ~= pbase ** pbase +# offset :-> v ** RSP ~= sp-#8 ** sp-#8 :-> v).
Proof. basic apply *. Qed.

(** ** PUSH [r] *)
Corollary PUSH_M0_rule (r: GPReg32) (sp v w pbase:QWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** RSP ~= sp    ** sp-#8 :-> w)
            (PUSH [r]) 
            (r ~= pbase ** pbase :-> v ** RSP ~= sp-#8 ** sp-#8 :-> v).
Proof. basic apply *. Qed.
*)
