(** * Laws about predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import Ssreflect.bigop.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.opred.core.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.
Require Import x86proved.common_tactics.

Generalizable All Variables.
Set Implicit Arguments.

(** ** catOP has empOP has left and right unit, and is associative *)
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
