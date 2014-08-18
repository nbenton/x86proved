(** * Laws about predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import Ssreflect.bigop.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.opred.core.
Require Import x86proved.charge.iltac.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.
Require Import x86proved.common_tactics.

Generalizable All Variables.
Set Implicit Arguments.

Local Transparent ILFun_Ops ILPre_Ops osepILogicOps osepILogic lentails ltrue lfalse limpl land lor lforall lexists.
Local Transparent catOP empOP eq_opred starOP repOP roll_starOP partial_rollOP.

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

(** [catOP] has [empOP] as left and right unit, and is associative *)
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

Lemma catOP_lexists1 T P Q : catOP (Exists x : T, P x) Q -|- Exists x : T, catOP (P x) Q.
Proof. t. Qed.

Lemma catOP_lexists2 T P Q : catOP P (Exists x : T, Q x) -|- Exists x : T, catOP P (Q x).
Proof. t. Qed.

Lemma catOP_lforall1 T P Q : catOP (Forall x : T, P x) Q |-- Forall x : T, catOP (P x) Q.
Proof. t. Qed.

Lemma catOP_lforall2 T P Q : catOP P (Forall x : T, Q x) |-- Forall x : T, catOP P (Q x).
Proof. t. Qed.

Lemma catOP_O_starOP_O' O O' : catOP O (catOP (starOP O) O') |-- catOP (starOP O) O'.
Proof.
  do !t'_safe.
  do 2 esplit; do !t'_safe; try eassumption; do?t'_safe.
  eexists (S _).
  t.
Qed.

Lemma catOP_O_roll_starOP_O' start O O' : catOP (O start) (catOP (roll_starOP O (S start)) O') |-- catOP (roll_starOP O start) O'.
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

Lemma roll_starOP__starOP n O : roll_starOP (fun _ => O) n -|- starOP O.
Proof.
  rewrite /starOP/roll_starOP.
  split; (lexistsL => n'; lexistsR n');
  revert n; (induction n'; first by reflexivity) => n;
  rewrite /repOP-/repOP/partial_rollOP-/partial_rollOP;
  f_cancel;
  hyp_apply *.
Qed.

Lemma roll_starOP_def O n : roll_starOP O n -|- empOP \\// catOP (O n) (roll_starOP O (S n)).
Proof.
  t;
  match goal with
    | _ => by instantiate (1 := 0); t
    | _ => by instantiate (1 := S _); t
    | [ x : nat |- _ ] => induction x; by t
  end.
Qed.

Lemma starOP_empOP : starOP empOP -|- empOP.
Proof.
  t;
  match goal with
    | [ H : nat |- _ ] => induction H
    | [ |- context[?E] ] => is_evar E; unify E 0
  end;
  t.
Qed.

Lemma roll_starOP_empOP n : roll_starOP (fun _ => empOP) n -|- empOP.
Proof.
  rewrite -> roll_starOP__starOP.
  exact starOP_empOP.
Qed.

Local Ltac t_catOP_fold :=
    repeat match goal with
           | _ => reflexivity
           | _ => progress rewrite ?empOPL ?empOPR ?catOPA
           | _ => (test intros) => ?
           | _ => progress simpl in *
           | [ IH : _ |- context[?a] ] => not constr_eq a empOP; rewrite -> (IH a)
         end.

Lemma foldl_catOP_pull xs
: forall x, foldl catOP x xs -|- catOP x (foldl catOP empOP xs).
Proof. induction xs; t_catOP_fold. Qed.
Lemma foldr_catOP_pull xs
: forall x, foldr catOP x xs -|- catOP (foldr catOP empOP xs) x.
Proof. induction xs; t_catOP_fold. Qed.

Lemma foldl_flip_catOP_pull xs
: forall x, foldl (Basics.flip catOP) x xs -|- catOP (foldl (Basics.flip catOP) empOP xs) x.
Proof. induction xs; t_catOP_fold. Qed.
Lemma foldr_flip_catOP_pull xs
: forall x, foldr (Basics.flip catOP) x xs -|- catOP x (foldr (Basics.flip catOP) empOP xs).
Proof. rewrite /Basics.flip; induction xs; t_catOP_fold. Qed.

Lemma foldl_fun_catOP_pull {T} (xs : seq T) f
: forall x, foldl (fun x (y : T) => catOP x (f y)) x xs -|- catOP x (foldl (fun x (y : T) => catOP x (f y)) empOP xs).
Proof. induction xs; t_catOP_fold. Qed.
Lemma foldr_fun_catOP_pull {T} (xs : seq T) f
: forall x, foldr (fun (x : T) y => catOP y (f x)) x xs -|- catOP x (foldr (fun (x : T) y => catOP y (f x)) empOP xs).
Proof. induction xs; t_catOP_fold. Qed.

Lemma foldl_fun_flip_catOP_pull {T} (xs : seq T) f
: forall x, foldl (fun x (y : T) => catOP (f y) x) x xs -|- catOP (foldl (fun x (y : T) => catOP (f y) x) empOP xs) x.
Proof. induction xs; t_catOP_fold. Qed.
Lemma foldr_fun_flip_catOP_pull {T} (xs : seq T) f
: forall x, foldr (fun (x : T) y => catOP (f x) y) x xs -|- catOP (foldr (fun (x : T) y => catOP (f x) y) empOP xs) x.
Proof. induction xs; t_catOP_fold. Qed.

(** This tactic pulls the initial value of a [foldl] or [foldr] out *)
Ltac fold_catOP_pull' :=
  idtac;
  match goal with
    | [ |- context[catOP empOP ?a] ] => rewrite -> (empOPL a)
    | [ |- context[catOP ?a empOP] ] => rewrite -> (empOPR a)
    | [ |- context[foldl catOP ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldl_catOP_pull xs a)
    | [ |- context[foldr catOP ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldr_catOP_pull xs a)
    | [ |- context[foldl (Basics.flip catOP) ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldl_flip_catOP_pull xs a)
    | [ |- context[foldr (Basics.flip catOP) ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldr_flip_catOP_pull xs a)
    | [ |- context[foldl (fun x y => catOP x (@?f y)) ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldl_fun_catOP_pull xs f a)
    | [ |- context[foldr (fun x y => catOP y (@?f x)) ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldr_fun_catOP_pull xs f a)
    | [ |- context[foldl (fun x y => catOP (@?f y) x) ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldl_fun_flip_catOP_pull xs f a)
    | [ |- context[foldr (fun x y => catOP (@?f x) y) ?a ?xs] ] => not constr_eq a empOP; rewrite -> (foldr_fun_flip_catOP_pull xs f a)
  end.

Ltac fold_catOP_pull := do !fold_catOP_pull'.

Local Ltac foldl_catOP_foldr_t :=
  let ls := match goal with ls : seq _ |- _ => constr:(ls) end in
  (induction ls => //=; []);
    repeat match goal with
             | [ IHls : context[ls] |- _ ] => rewrite <- IHls; clear IHls
             | _ => progress fold_catOP_pull
             | _ => done
             | _ => rewrite /Basics.flip
           end.

Lemma foldl_catOP_foldr ls
: foldl catOP empOP ls -|- foldr catOP empOP ls.
Proof. foldl_catOP_foldr_t. Qed.

Lemma foldl_flip_catOP_foldr ls
: foldl (Basics.flip catOP) empOP ls -|- foldr (Basics.flip catOP) empOP ls.
Proof. foldl_catOP_foldr_t. Qed.

Lemma foldl_fun_catOP_foldr {T} (ls : seq T) f
: foldl (fun x (y : T) => catOP x (f y)) empOP ls -|- foldr (fun (x : T) y => catOP (f x) y) empOP ls.
Proof. foldl_catOP_foldr_t. Qed.

Lemma foldl_fun_flip_catOP_foldr {T} (ls : seq T) f
: foldl (fun x (y : T) => catOP (f y) x) empOP ls -|- foldr (fun (x : T) y => catOP y (f x)) empOP ls.
Proof. foldl_catOP_foldr_t. Qed.
