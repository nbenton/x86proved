(** * JCC (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.triple (* for [triple_apply] *).
Require Import x86proved.spectac (* for [eforalls] *).
Require Import x86proved.common_tactics (* for [f_equiv'] *).

Lemma JCCrel_rule_later (rel: DWORD) cc cv (b:bool) (p q: DWORD) :
  |-- Forall (O : PointedOPred), (
      |> obs O @ (EIP ~= (if b == cv then addB q rel else q) ** ConditionIs cc b) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv rel).
Proof.
  specintros => O.
  apply: TRIPLE_safeLater => R. autounfold with instrrules_eval.
  triple_apply triple_letGetCondition.
  case: (b == cv).
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR1 ]. }
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR2 ]. }
Qed.

(** For convenience, the [~~b] branch is not under a [|>] operator
    since [q] will never be equal to [p], and thus there is no risk of
    recursion. *)
Lemma JCCrel_loopy_rule (rel: DWORD) cc cv (b:bool) (p q: DWORD) :
  |-- Forall (O : PointedOPred), (
      |> obs O @ (b == cv /\\ EIP ~= (addB q rel) ** ConditionIs cc b) //\\
         obs O @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv rel).
Proof.
  specintros => O.
  rewrite ->(spec_later_weaken (obs O @ (b == (~~ cv) /\\ EIP~=q ** ConditionIs cc b))).
  rewrite <-spec_later_and. rewrite ->spec_at_and_or; last apply _.
  replace (b == (~~cv)) with (~~(b == cv)); last by case: b; case: cv; reflexivity.
  (** There should be a better way to instantiate the hypotheses of [H] and make use of it *)
  move: (@JCCrel_rule_later rel cc cv b p q) => H. eforalls H. setoid_rewrite H. clear H.
  do !f_cancel.
  case: (b == cv); simpl negb;
  do [ by apply: lorR1; sbazooka
     | by apply: lorR2; sbazooka ].
Qed.

(** We also have a version where neither is under a [|>] operator,
    which doesn't require pointedness of the OPred, and does not
    support loopy behavior. *)
Lemma JCCrel_rule (rel: DWORD) cc cv (b:bool) (p q: DWORD) :
  |-- Forall O, (
      obs O @ (EIP ~= (if b == cv then addB q rel else q) ** ConditionIs cc b ) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv rel).
Proof.
  specintros => O.
  apply: TRIPLE_safe => R. autounfold with instrrules_eval.
  triple_apply triple_letGetCondition.
  case: (b == cv).
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR1 ]. }
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR2 ]. }
Qed.
