(** * JCC (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.triple (* for [triple_apply] *).

Lemma JCCrel_rule (rel: DWORD) cc cv (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (EIP ~= (if b == cv then addB q rel else q) ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b)
    ) c@ (p -- q :-> JCCrel cc cv rel).
Proof.
 case E: (b == cv); instrrule_triple_bazooka; rewrite E; instrrule_triple_bazooka. 
Qed.   

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (rel : DWORD) cc cv, instrrule (@JCCrel cc cv rel) := @JCCrel_rule.
