(** * XOR instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma XOR_RR_rule d (r1 r2:DWORDorBYTEReg d) v1 (v2:DWORDorBYTE d):
  |-- basic (DWORDorBYTEregIs r1 v1 ** DWORDorBYTEregIs r2 v2 ** OSZCP?) (XOR r1, r2) empOP
            (DWORDorBYTEregIs r1 (xorB v1 v2) ** DWORDorBYTEregIs r2 v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).
Proof. destruct d; do_instrrule_triple. Qed.

Lemma XOR_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (XOR r1, [r2 + offset]) empOP
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. change (stateIs r1) with (@DWORDorBYTEregIs true r1). move => ?; subst. do_instrrule_triple. Qed.

(** We make this rule an instance of the typeclass, after unfolding various things in its type. *)
(** We make the more specific rule have a higher priority *)
Global Instance: forall (r1 r2 : Reg) (offset : nat), instrrule (XOR r1, [r2 + offset]) | 0
  := fun r1 r2 offset pd v1 v2 => @XOR_RM_rule pd r1 r2 v1 v2 offset.
Global Instance: forall d (r1 r2 : DWORDorBYTEReg d), instrrule (XOR r1, r2) | 1
  := @XOR_RR_rule.

Corollary XOR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) empOP (r1~=xorB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. instrrules_basicapply (@XOR_RM_rule pd r1 r2 v1 v2 offset (xorB v1 v2) (refl_equal _)). Qed.
