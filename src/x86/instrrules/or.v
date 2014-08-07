(** * OR instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma OR_RM_rule (pd:DWORD) (r1:Reg) (r2:Reg) (v1 v2:DWORD) (offset:nat) (v:DWORD) :
  orB v1 v2 = v ->
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (OR r1, [r2 + offset]) empOP
            (r1 ~= v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. move => ?; subst. 
change (stateIs r1) with (@VRegIs OpSize4 r1). 
do_instrrule_triple. 
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Instance: forall (r1 r2 : Reg) (offset : nat), instrrule (OR r1, [r2 + offset]) := fun r1 r2 offset pd v1 v2 => @OR_RM_rule pd r1 r2 v1 v2 offset _ (refl_equal _).

Corollary OR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (OR r1, [r2 + offset]) empOP (r1~=orB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. do_basic'. Qed.
