(*===========================================================================
    I/O actions
  ===========================================================================*)
Require Import ssreflect ssrbool eqtype tuple seq.
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

Definition Obs := seq (Chan*Data).
Definition preObs (o1 o2: Obs) := exists o', o2 = o1 ++ o'.

Require Import RelationClasses Program.Basics.
Instance preObs_Pre: PreOrder preObs.
Proof. repeat constructor; hnf.
move => o. exists nil. by rewrite cats0.
move => x y z [o1 H1] [o2 H2]. subst. exists (o1++o2). by rewrite catA. 
Qed. 

Lemma cat_preObs o : forall o1 o2, preObs o1 o2 -> preObs (o++o1) (o++o2). 
Proof. induction o => // o1 o2 [o' PO]. subst. exists o'. by rewrite catA. Qed.

