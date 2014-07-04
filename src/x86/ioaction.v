(*===========================================================================
    I/O actions
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsprops.

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
Definition preActionsOp a1 a2 := preActions a2 a1.
Definition strictPreActions (a1 a2: Actions) := 
  exists o a', a2 = a1 ++ o::a'.

Definition postActions (a1 a2: Actions) := exists a', a2 = a'++a1.
Definition postActionsOp a1 a2 := postActions a2 a1.
Definition strictPostActions (a1 a2: Actions) := 
  exists o a', a2 = a'++o::a1.

Require Import Coq.Classes.RelationClasses Coq.Program.Basics.

Instance preActions_Pre: PreOrder preActions.
Proof. repeat constructor; hnf.
move => a. exists nil. by rewrite cats0.
move => x y z [a1 ->] [a2 ->]. exists (a1++a2). by rewrite catA. 
Qed. 


Instance preActionsOp_Pre: PreOrder preActionsOp.
Proof. repeat constructor; hnf.
move => a. exists nil. by rewrite cats0.
move => x y z [a1 ->] [a2 ->]. exists (a2++a1). by rewrite catA. 
Qed. 

Instance postActionsOp_Pre: PreOrder postActionsOp.
Proof. repeat constructor; hnf.
move => a. by exists nil. 
move => x y z [a1 ->] [a2 ->]. exists (a1++a2). by rewrite catA. 
Qed. 

Lemma cat_preActions a : forall a1 a2, preActions a1 a2 -> preActions (a++a1) (a++a2). 
Proof. induction a => // a1 a2 [a' ->]. exists a'. by rewrite catA. Qed.

Require Import Coq.Setoids.Setoid x86proved.charge.csetoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.

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

Lemma preActionsOp_strictPre x t t':
  preActionsOp t t' -> strictPreActions x t' -> strictPreActions x t. 
Proof. move => PRE [a [b H]]. destruct t'. destruct x => //. 
+ destruct x. destruct PRE as [d ->]. simpl. by exists a0, (t'++d).
+ inversion H. subst. destruct PRE as [d ->]. simpl. 
exists a, (b++d). by rewrite /= -!catA. Qed. 

Lemma strictPre_implies_preActionsOp x y :
  strictPreActions x y -> preActionsOp y x.
Proof. move => [a [b ->]]. by exists (a::b).  Qed.

Lemma preActionsOpDef o o' : preActions o o' <-> preActionsOp o' o.
Proof. by unfold preActionsOp. Qed.

Lemma strictPost_implies_postActionsOp x y :
  strictPostActions x y -> postActionsOp y x.
Proof. move => [a [b ->]]. unfold postActionsOp. exists (b++[::a]). by rewrite -catA/=. Qed.

Lemma postActionsOpDef o o' : postActions o o' <-> postActionsOp o' o.
Proof. by unfold postActionsOp. Qed.