Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.ioaction (* for [outputToActions] *).

Require Import x86proved.triple.roc.

Import Prenex Implicits.

Lemma triple_skip P : TRIPLE P (retn tt) empOP P.
Proof.  move => s pre; exists s, nil; intuition. done. Qed.

Lemma triple_seqcat P P' P'' O1 O2 c1 c2 O :
  catOP O1 O2 |-- O ->
  TRIPLE P c1 O1 P' ->
  TRIPLE P' c2 O2 P'' ->
  TRIPLE P (do! c1; c2) O P''.
Proof. move => HO T1 T2. rewrite <- HO.
move => s H. rewrite /TRIPLE in T1, T2.
destruct (T1 _ H) as [s' [o [e [OH H']]]].
destruct (T2 _ H') as [s'' [o' [e' [OH' H'']]]].
exists s''. exists (o++o'). rewrite /= e e'. split => //.
split => //. exists (outputToActions o), (outputToActions o').
rewrite /outputToActions map_cat. firstorder.
Qed.

Lemma triple_seq P P' P'' c1 c2 O :
  TRIPLE P c1 empOP P' ->
  TRIPLE P' c2 O P'' ->
  TRIPLE P (do! c1; c2) O P''.
Proof. move => T1 T2. apply: triple_seqcat T1 T2. by apply empOPL. Qed.
