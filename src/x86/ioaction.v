(*===========================================================================
    I/O actions
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun eqtype tuple seq.
Require Import bitsrep bitsops bitsprops.

Definition Chan := BYTE.
Definition Data := BYTE.

Inductive Action :=
| Out (c:Chan) (d:Data)
| In (c:Chan) (d:Data).

Definition actionEq a1 a2 :=
  match a1, a2 with
  | Out c1 d1, Out c2 d2 => (c1 == c2) && (d1 == d2)
  | In c1 d1, In c2 d2 => (c1 == c2) && (d1 == d2)
  | _, _ => false
  end.

Lemma action_eqP: Equality.axiom actionEq.
Proof. case => c1 d1.  case => c2 d2. simpl.
+ case E1: (c1 == c2).
  case E2: (d1 == d2).
  simpl. rewrite (eqP E1) (eqP E2). by apply ReflectT.
  apply ReflectF => H.  inversion H.
  rewrite H2 in E2. by rewrite eq_refl in E2.
  apply ReflectF => H. inversion H.
  rewrite H1 in E1. by rewrite eq_refl in E1.
  by apply ReflectF => H.
  case => c2 d2.
  by apply ReflectF => H.
simpl.
case E1: (c1 == c2).
case E2: (d1 == d2).
  simpl. rewrite (eqP E1) (eqP E2). by apply ReflectT.
  apply ReflectF => H.  inversion H.
  rewrite H2 in E2. by rewrite eq_refl in E2.
  apply ReflectF => H. inversion H.
  rewrite H1 in E1. by rewrite eq_refl in E1.
Qed.

Canonical action_eqMixin := EqMixin action_eqP.
Canonical action_eqType := Eval hnf in EqType _ action_eqMixin.

Definition Actions := seq Action.
Definition preActions (a1 a2: Actions) := exists a', a2 = a1 ++ a'.

Require Import RelationClasses Program.Basics.
Instance preActions_Pre: PreOrder preActions.
Proof. repeat constructor; hnf.
move => a. exists nil. by rewrite cats0.
move => x y z [a1 ->] [a2 ->]. exists (a1++a2). by rewrite catA. 
Qed. 

Lemma cat_preActions a : forall a1 a2, preActions a1 a2 -> preActions (a++a1) (a++a2). 
Proof. induction a => // a1 a2 [a' ->]. exists a'. by rewrite catA. Qed.

Require Import Setoid CSetoid RelationClasses Morphisms.

Instance ActionsEquiv : Equiv Actions := {
   equiv a1 a2 := a1 = a2
}.

Instance ActionsType : type Actions.
Proof.
  split.
  move => x; by reflexivity.
  move => x y H; by symmetry. 
  move => x y z H1 H2; by rewrite H1 H2. 
Qed.

Definition outputToActions o : Actions := map (fun p => Out p.1 p.2) o.
