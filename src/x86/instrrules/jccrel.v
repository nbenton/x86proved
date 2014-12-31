(** * JCC (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.triple (* for [triple_apply] *).

Lemma JCCrel_rule (rel: QWORD) cc cv (b:bool) (p q: ADDR) :
  |-- (
      |> safe @ (UIP ~= (if b == cv then addB q rel else q) ** ConditionIs cc b) -->>
      safe @ (UIP ~= p ** ConditionIs cc b)
    ) c@ (p -- q :-> JCCrel cc cv (mkTgt AdSize8 rel)).
Proof.
 case E: (b == cv); instrrule_triple_bazooka; rewrite E; instrrule_triple_bazooka. 
Qed.   

Global Instance: forall (rel : QWORD) cc cv, instrrule (@JCCrel cc cv (mkTgt AdSize8 rel)) := @JCCrel_rule.
