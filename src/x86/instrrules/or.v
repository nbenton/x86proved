(** * OR instruction *)
Require Import x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Lemma OR_RM_rule (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  orB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?)
            (OR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. change (stateIs r1) with (@DWORDorBYTEregIs true r1). move => ?; subst. do_instrrule_triple. Qed.

Corollary OR_RM_ruleNoFlags (pd:DWORD) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (OR r1, [r2 + offset]) (r1~=orB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP?).
Proof. autorewrite with push_at. instrrules_basicapply (@OR_RM_rule pd r1 r2 v1 v2 offset (orB v1 v2) (refl_equal _)). Qed.
