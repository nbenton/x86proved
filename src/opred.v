(*===========================================================================
    Predicates over observations (sequences of actions)
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction x86proved.charge.ilogic.
Require Import Coq.Setoids.Setoid x86proved.charge.csetoid Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Obligation Tactic := idtac.

(* We require predicates on observations to be non-empty i.e. for there to be
   some sequence of actions for which it holds *)
Record OPred := mkOPred {
  OPred_pred :> Actions -> Prop;
  OPred_inhabited: exists x: Actions, OPred_pred x
}.

Implicit Arguments mkOPred [].

(* Singleton predicate *)
Program Definition eq_opred s := mkOPred (fun s' => s === s') _.
Next Obligation. move => s. by exists s. Qed.

(* The empty sequence of actions *)
Definition empOP : OPred := eq_opred nil.

(* A single output action *)
Definition outOP (c:Chan) (d:Data) : OPred := eq_opred [::Out c d].

(* A sequence of actions that splits into the concatenation of one
satisfying P and one satisfying Q *)
Program Definition catOP (P Q: OPred) : OPred
 := mkOPred (fun o => exists o1 o2, o = o1++o2 /\ P o1 /\ Q o2) _.
Next Obligation.
move => [P [Px PH]] [Q [Qx QH]]. exists (Px++Qx). exists Px, Qx.
intuition.
Qed.

(* Any sequence of actions *)
Program Definition trueOP : OPred := @mkOPred (fun _ => True) _.
Next Obligation. by exists nil. Qed.

(* Union *)
Program Definition orOP (P Q: OPred) : OPred
  := mkOPred (fun o => P o \/ Q o) _.
Next Obligation.
move => [P [Px PH]] [Q [Qx QH]]. exists Px. by left.
Qed.

(* Repetition *)
Fixpoint repOP n P := if n is n.+1 then catOP P (repOP n P) else empOP.

(* Existential quantification, for inhabited types *)
Program Definition existsOP X {_: inhabited X} (f: X -> OPred) : OPred :=
  mkOPred (fun o => exists x: X, f x o) _.
Next Obligation.
move => X [x] f.
destruct (OPred_inhabited (f x)) as [y H]. by exists y, x.
Qed.

(* Kleene star *)
Definition starOP P := @existsOP _ (inhabits 0) (fun n => repOP n P).

(* Inclusion and equivalence on predicates *)
Definition entailsOP (O O': OPred) := forall s, O s -> O' s.
Definition equivOP (O O': OPred) := entailsOP O O' /\ entailsOP O' O.

Instance equivOPEquiv : Equiv OPred := equivOP.

Instance entailsOPpre : PreOrder entailsOP.
Proof. constructor; hnf. move => P s. intuition.
move => P Q R H1 H2 s. intuition. Qed.


Instance equivOP_entailOP : subrelation equivOP entailsOP.
Proof. firstorder. Qed.

Instance equivOP_inverse_entailsOP: subrelation equivOP (inverse entailsOP).
Proof. firstorder. Qed.

Instance equivOP_entailsOP_m : Proper (equivOP ==> equivOP ==> iff) entailsOP.
Proof. move => P P' HP Q Q' QP. split => H s H'; firstorder. Qed.

Instance entailsOP_entailsOP_m: Proper (entailsOP --> entailsOP ++> impl) entailsOP.
Proof. move => P P' HP Q Q' QP H s H'. intuition. Qed.

(* Morphisms for operators *)
Instance catOP_entails_m: Proper (entailsOP ==> entailsOP ==> entailsOP) catOP.
Proof.
move => O1 O1' HO1 O2 O2' HO2. move => s/= H.
destruct H as [o1 [o2 [H1 [H2 H3]]]]. subst.
exists o1, o2. split => //. split. by apply HO1. by apply HO2.
Qed.

Instance catOP_equiv_m: Proper (equivOP ==> equivOP ==> equivOP) catOP.
Proof. move => P P' HP Q Q' HQ. split; apply catOP_entails_m; (apply HP || apply HQ). Qed.

(* catOP has empOP has left and right unit, and is associative *)
Lemma empOPR P : equivOP (catOP P empOP) P.
Proof. split.
move => o [s1 [s2 [-> [H2 /= E2]]]]. by rewrite -E2 cats0.
move => o H. exists o, nil. by rewrite cats0.
Qed.

Lemma empOPL P : equivOP (catOP empOP P) P.
Proof. split.
move => o [s1 [s2 [-> [/=E2 H]]]]. by rewrite <- E2. move => o H. by exists nil, o.
Qed.

Lemma catOPA (P Q R : OPred) : equivOP (catOP (catOP P Q) R) (catOP P (catOP Q R)).
Proof.
split.
+ move => o [s1 [s2 [/=-> [[s3 [s4 [/=-> [H3 H4]]]] H5]]]].
  exists s3, (s4++s2). rewrite catA. split => //. split => //. by exists s4, s2.
+ move => o [s1 [s2 [/=-> [H2 [s3 [s4 [/=-> [H4 H5]]]]]]]].
  exists (s1++s3), s4. rewrite catA. split => //. split => //. by exists s1, s3.
Qed.

Lemma catOP_trueL P : entailsOP P (catOP trueOP P).
Proof. move => s H/=. by exists nil, s. Qed.

Lemma catOP_trueR P : entailsOP P (catOP P trueOP).
Proof. move => s H/=. exists s, nil. by rewrite cats0. Qed.

Lemma orOPR1 C P Q : entailsOP C P -> entailsOP C (orOP P Q).
Proof. move => H s H'. left. by apply H. Qed.

Lemma orOPR2 C P Q : entailsOP C Q -> entailsOP C (orOP P Q).
Proof. move => H s H'. right. by apply H. Qed.

Lemma inhabitedOP (O: OPred) : exists s, O s.
Proof. by destruct O. Qed.

Lemma catOP_eq_opred (O: OPred) o1 o2 :
  O o2 ->
  catOP (eq_opred o1) O (o1++o2).
Proof. move => H.
exists o1, o2. firstorder.  reflexivity.
Qed.

Hint Extern 0 (entailsOP (catOP empOP ?O) ?P) => by apply empOPL.
Hint Extern 0 (entailsOP (catOP ?O ?empOP) ?P) => by apply empOPR.

Lemma starOP_def (P: OPred) : equivOP (starOP P) (orOP empOP (catOP P (starOP P))).
Proof. split => s /= H.
destruct H as [n H].
destruct n.
rewrite H. by left.
destruct H as [s1 [s2 [H1 [H2 H3]]]].
subst. right.
exists s1, s2. intuition. by exists n.
destruct s. by exists 0.
destruct H => //.
destruct H as [s1 [s2 [H1 [H2 [n H3]]]]].
exists n.+1.  simpl. exists s1, s2. intuition.
Qed.

(*Local Transparent ILFun_Ops ILPre_Ops.

Lemma land_catOP P Q R : catOP (P//\\Q) R |-- (catOP P R) //\\ (catOP Q R).
Proof. apply landR. apply catOP_entails_m => //. by apply landL1.
                    apply catOP_entails_m => //. by apply landL2.
Qed.

Lemma catOP_land P Q R : catOP P (Q//\\R) |-- (catOP P Q) //\\ (catOP P R).
Proof. apply landR. apply catOP_entails_m => //. by apply landL1.
                    apply catOP_entails_m => //. by apply landL2.
Qed.

Lemma catOP_lfalseL P : catOP lfalse P -|- lfalse.
Proof. split => //. by move => s [s1 [s2 [H1 [H2 H3]]]]/=. Qed.

Lemma catOP_lfalseR P : catOP P lfalse -|- lfalse.
Proof. split => //. by move => s [s1 [s2 [H1 [H2 H3]]]]/=. Qed.

*)