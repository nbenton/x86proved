(** * JCC (rel) instruction *)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred OPred septac spec obs triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax.

Local Open Scope instr_scope.

Require Import x86.instrrules.core.

(** For convenience, the [~~b] branch is not under a [|>] operator
    since [q] will never be equal to [p], and thus there is no risk of
    recursion. *)
Lemma JCCrel_rule rel cc cv (b:bool) (p q: DWORD) :
  |-- Forall O, (
      |> obs O @ (b == cv /\\ EIP ~= (addB q rel) ** ConditionIs cc b) //\\
         obs O @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      obs O @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv (mkTgt rel)).
Proof.
  specintros => O.
  rewrite ->(spec_later_weaken (obs O @ (b == (~~ cv) /\\ EIP~=q ** ConditionIs cc b))).
  rewrite <-spec_later_and. rewrite ->spec_at_and_or; last apply _.
  apply TRIPLE_safe => R. rewrite /evalInstr.
  triple_apply triple_letGetCondition.
  replace (b == (~~cv)) with (~~(b == cv)); last first.
  { case: b; case: cv; reflexivity. }
  case: (b == cv).
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR1 ]. }
  { instrrule_triple_bazooka using do [ progress sbazooka | apply: lorR2 ]. }
Qed.
