Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [ST] *).
Require x86proved.pointsto (* for [ssimpl] *).

Require Import x86proved.triple.roc.

Import Prenex Implicits.

Hint Rewrite -> (@assoc ST _ _) (@id_l ST _ _) : triple.

Ltac triple_apply lemma tac :=
 autounfold with spred;
 autorewrite with triple;
 eapply triple_roc; [| | |eapply lemma];
 do ?(instantiate;
      match goal with
        | [ |- _ |-- _ ] => reflexivity
        | [ |- entailsOP _ _ ] => reflexivity
        | [ |- _ |-- _ ] => progress pointsto.ssimpl
        | [ |- _ |-- _ ] => done
        | [ |- entailsOP _ _ ] => done
        | [ |- _ |-- _ ] => progress tac
        | [ |- _ |-- _ ] => fail 2 "Cannot fully solve side-conditions of triple_roc"
      end).

Tactic Notation "triple_apply" constr(lemma) "using" tactic3(tac) := triple_apply lemma tac.
Tactic Notation "triple_apply" constr(lemma) := triple_apply lemma using idtac.
(** The [idtac; fail 1] is a hack to short-circuit the [fail 2] in the [match]... *)
(** TODO(t-jagro): Find a more systematic way to deal with things. *)
Ltac try_triple_apply lemma := triple_apply lemma using (idtac; fail 1).
