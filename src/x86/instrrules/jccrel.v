(** * JCC (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.triple (* for [triple_apply] *).
Require Import x86proved.spectac (* for [eforalls] *).
Require Import x86proved.common_tactics (* for [f_equiv'] *).

Lemma JCCrel_rule (rel: DWORD) cc cv (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (EIP ~= (if b == cv then addB q rel else q) ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv rel).
Proof.
  apply: TRIPLE_safeLater => R. autounfold with instrrules_eval.
  triple_apply triple_letGetCondition.
  case: (b == cv).
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR1 ]. }
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR2 ]. }
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (rel : DWORD) cc cv, instrrule (@JCCrel cc cv rel) := @JCCrel_rule.
