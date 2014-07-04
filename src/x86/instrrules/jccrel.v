(** * JCC (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.triple (* for [triple_apply] *).

(** For convenience, the [~~b] branch is not under a [|>] operator
    since [q] will never be equal to [p], and thus there is no risk of
    recursion. *)
Lemma JCCrel_rule (rel: DWORD) cc cv (b:bool) (p q: DWORD) :
  |-- Forall O, (
      |> obs O @ (b == cv /\\ EIP ~= (addB q rel) ** ConditionIs cc b) //\\
         obs O @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv rel).
Proof.
  specintros => O.
  rewrite ->(spec_later_weaken (obs O @ (b == (~~ cv) /\\ EIP~=q ** ConditionIs cc b))).
  rewrite <-spec_later_and. rewrite ->spec_at_and_or; last apply _.
  apply TRIPLE_safeLater => R. autounfold with instrrules_eval.
  triple_apply triple_letGetCondition.
  replace (b == (~~cv)) with (~~(b == cv)); last first.
  { case: b; case: cv; reflexivity. }
  case: (b == cv).
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR1 ]. }
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR2 ]. }
Qed.
