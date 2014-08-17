(** ** The equivalent of [pointwise_relation], but for [list]. *)
Require Import Ssreflect.ssreflect Ssreflect.seq.
Require Import Coq.Lists.List Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.

(** Element-wise lifting *)
Fixpoint elementwise_relation {A} (R : relation A) (ls1 ls2 : list A) {struct ls1} : Prop
  := match ls1, ls2 with
       | nil, nil => True
       | _, nil => False
       | nil, _ => False
       | x::xs, y::ys => R x y /\ elementwise_relation R xs ys
     end.

Local Ltac list_rel_t' :=
  idtac;
  match goal with
    | _ => solve [ eauto ]
    | [ |- forall ls : Ssreflect.seq.seq ?T, _ ] => let ls := fresh "ls" in intro ls; induction ls
    | [ |- forall ls : list ?T, _ ] => let ls := fresh "ls" in intro ls; induction ls
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ |- _ /\ _ ] => split
    | _ => progress hnf
    | _ => progress simpl in *
    | _ => progress unfold subrelation, impl, predicate_implication, respectful in *
    | _ => intro
    | [ H : False |- _ ] => solve [ destruct H ]
    | _ => solve [ etransitivity; eauto ]
  end.
Local Ltac list_rel_t := repeat list_rel_t'.

Local Obligation Tactic := list_rel_t.

Global Program Instance elementwise_subrelation {A} {R R'} `(sub : subrelation A R R')
: subrelation (elementwise_relation R) (elementwise_relation R') | 4.

Typeclasses Opaque elementwise_relation.
Arguments elementwise_relation A%type R%signature (_ _)%SEQ : clear implicits.

Program Instance elementwise_reflexive {A R} `{@Reflexive A R} : Reflexive (elementwise_relation A R).
Program Instance elementwise_symmetric {A R} `{@Symmetric A R} : Symmetric (elementwise_relation A R).
Program Instance elementwise_transitive {A R} `{@Transitive A R} : Transitive (elementwise_relation A R).
Program Instance elementwise_equivalence {A R} `{@Equivalence A R} : Equivalence (elementwise_relation A R).

Add Parametric Morphism A B R R' : (@List.map A B)
with signature (R ==> R') ==> elementwise_relation _ R ==> elementwise_relation _ R'
  as map_elementwise_mor.
Proof. list_rel_t. Qed.

Add Parametric Morphism A B R : (@List.map A B)
with signature (pointwise_relation _ R) ==> @eq (list A) ==> elementwise_relation _ R
  as map_elementwise_pointwise_mor.
Proof. list_rel_t. Qed.

Add Parametric Morphism A B R R' : (@Ssreflect.seq.map A B)
with signature (R ==> R') ==> elementwise_relation _ R ==> elementwise_relation _ R'
  as srrmap_elementwise_mor.
Proof. list_rel_t. Qed.

Add Parametric Morphism A B R : (@Ssreflect.seq.map A B)
with signature (pointwise_relation _ R) ==> @eq (list A) ==> elementwise_relation _ R
  as ssrmap_elementwise_pointwise_mor.
Proof. list_rel_t. Qed.

Add Parametric Morphism A B R R' : (@fold_left A B)
with signature (R ==> R' ==> R) ==> elementwise_relation B R' ==> R ==> R
  as fold_left_mor.
Proof. list_rel_t. Qed.

Add Parametric Morphism A B R R' : (@fold_right A B)
with signature (R' ==> R ==> R) ==> R ==> elementwise_relation B R' ==> R
  as fold_right_mor.
Proof. list_rel_t. Qed.

Add Parametric Morphism A B R R' : (@foldl A B)
with signature (R ==> R' ==> R) ==> R ==> elementwise_relation A R' ==> R
  as foldl_mor.
Proof. intros f g H x y H' ls1 ls2; revert ls1 ls2 x y H'. list_rel_t. Qed.

Add Parametric Morphism A B R R' : (@foldr A B)
with signature (R' ==> R ==> R) ==> R ==> elementwise_relation A R' ==> R
  as foldr_mor.
Proof. intros f g H x y H' ls1 ls2; revert ls1 ls2 x y H'. list_rel_t. Qed.
