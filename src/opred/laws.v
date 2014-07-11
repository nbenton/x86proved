(** * Laws about predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import Ssreflect.bigop.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.opred.core.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.
Require Import x86proved.common_tactics.

Generalizable All Variables.
Set Implicit Arguments.

(** [catOP] has [empOP] as left and right unit, and is associative *)

(** We need to [move H at bottom] first because otherwise [progress]
    will pick up the fact that [rewrite /foo in H] moves [H] at bottom
    even if it does nothing else. *)
Local Transparent ILFun_Ops ILPre_Ops.

Create HintDb opred_laws_t discriminated.

Hint Resolve List.app_assoc List.app_nil_l List.app_nil_r symmetry : opred_laws_t.

(** Tactics that will never need to be undone *)
Local Ltac t'_safe_without_evars :=
  do [ eassumption
     | done
     | by hyp_apply *; try eassumption
     | by eauto with opred_laws_t
     | by left
     | by right ].

(** We do replacement without disturbing evars, or if an evar can only
    be one thing (like when we have [x = y ++ z] and [x] and [y] are
    syntactically the same), then we can make progress. *)
Local Ltac progress_lists' :=
  idtac;
  lazymatch goal with
    | [ |- appcontext[(nil ++ ?a)%list] ] => replace (nil ++ a)%list with a by by symmetry; apply List.app_nil_l
    | [ |- appcontext[(?a ++ nil)%list] ] => replace (a ++ nil)%list with a by by symmetry; apply List.app_nil_r
    | [ |- appcontext[((?a ++ ?b) ++ ?c)%list] ] => replace ((a ++ b) ++ c)%list with (a ++ (b ++ c))%list by by apply List.app_assoc
    | [ |- ?x = ?y ] => progress (structurally_unify_lists x y; change (x = y))
                                 (** the [change (x = y)] above is a hack to get [progress] to notice instantiation of evars; see https://coq.inria.fr/bugs/show_bug.cgi?id=3412 *)
  end.

Local Ltac t'_safe :=
  do [ move => ?
     | progress instantiate
     | progress evar_safe_reflexivity
     | progress split_safe_goals
     | progress destruct_safe_hyps
     | progress destruct_head_hnf or
     | progress destruct_head_hnf sum
     | progress destruct_head_hnf sumbool
     | progress change @cat with @app
     | progress_lists'
     | progress hnf
     | not goal_has_evar; t'_safe_without_evars ].

Local Ltac t' :=
  do ![do ![ do !do !t'_safe
           | hnf; match goal with |- ex _ => idtac end; esplit
           | eassumption ]
      | by hyp_apply *; try eassumption ].

(** Solving evars is a side effect, so sometimes we need to let [do
    ?t'] fail on a goal, solve the other goals, and then try again. *)
Local Ltac t := do ?do ?[ do !t'
                        | by left; do ?t'
                        | by right; do ?t' ].

Add Parametric Morphism : catOP with signature lentails ==> lentails ==> lentails as catOP_entails_m.
Proof. t. Qed.

Add Parametric Morphism : catOP with signature lequiv ==> lequiv ==> lequiv as catOP_equiv_m.
Proof. t. Qed.

Lemma empOPR P : catOP P empOP -|- P.
Proof. t. Qed.

Lemma empOPL P : catOP empOP P -|- P.
Proof. t. Qed.

Lemma catOPA (P Q R : OPred) : catOP (catOP P Q) R -|- catOP P (catOP Q R).
Proof. t. Qed.

Lemma catOP_trueL P : P |-- catOP ltrue P.
Proof. t. Qed.

Lemma catOP_trueR P : P |-- catOP P ltrue.
Proof. t. Qed.

Lemma catOP_eq_opred (O: OPred) o1 o2
: O o2 ->
  catOP (eq_opred o1) O (o1++o2).
Proof. t. Qed.


Hint Extern 0 (catOP ?empOP ?O |-- ?P) => by apply empOPL.
Hint Extern 0 (catOP ?O ?empOP |-- ?P) => by apply empOPR.

Lemma starOP_def (P: OPred) : starOP P -|- empOP \\// catOP P (starOP P).
Proof.
  t;
  match goal with
    | _ => by instantiate (1 := 0); t
    | _ => by instantiate (1 := S _); t
    | [ x : nat |- _ ] => induction x; by t
  end.
Qed.

Lemma catOP_landL P Q R : catOP (P//\\Q) R |-- (catOP P R) //\\ (catOP Q R).
Proof. t. Qed.

Lemma catOP_landR P Q R : catOP P (Q//\\R) |-- (catOP P Q) //\\ (catOP P R).
Proof. t. Qed.

Lemma catOP_lfalseL P : catOP lfalse P -|- lfalse.
Proof. t. Qed.

Lemma catOP_lfalseR P : catOP P lfalse -|- lfalse.
Proof. t. Qed.

Lemma catOP_O_starOP_O' O O' : catOP O (catOP (starOP O) O') |-- catOP (starOP O) O'.
Proof.
  do !t'_safe.
  do 2 esplit; do !t'_safe; try eassumption; do?t'_safe.
  eexists (S _).
  t.
Qed.

Lemma starOP1 O : O |-- starOP O.
Proof.
  t.
  instantiate (1 := 1).
  t.
Qed.

Lemma repOP_rollOP n O : repOP n O -|- rollOP n (fun _ => O).
Proof.
  induction n; first by reflexivity.
  rewrite /repOP/rollOP-/repOP-/rollOP.
  rewrite IHn.
  reflexivity.
Qed.
