Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.ioaction (* for [outputToActions] *).
Require Import x86proved.common_tactics.

Require Import x86proved.triple.roc.

Import Prenex Implicits.

Lemma triple_skip P : TRIPLE P (retn tt) nil P.
Proof.  move => s pre; exists s; intuition. Qed.

Require Import monadinst step.
Lemma valued_triple_seqcat {A B} P P' P'' o1 o2 c1 c2 (v : A) (v' : B) o :
  o1 ++ o2 = o ->
  valued_TRIPLE v P c1 o1 P' ->
  valued_TRIPLE v' P' (c2 v) o2 P'' ->
  valued_TRIPLE v' P (bind c1 c2) o P''.
Proof.
  move => HO T1 T2. rewrite <- HO; clear HO. 
  move => s pre. 
  elim (T1 s pre) => [s' [H pre']].
  elim (T2 s' pre') => [s'' [H' post]].
  exists s''. split => //.
  by apply: (IOM_matches_bind H).
Qed.   

Lemma triple_seqcat P P' P'' o1 o2 c1 c2 o :
  o1 ++ o2 = o ->
  TRIPLE P c1 o1 P' ->
  TRIPLE P' c2 o2 P'' ->
  TRIPLE P (do! c1; c2) o P''.
Proof. apply (valued_triple_seqcat (c2 := fun _ => c2)). Qed.

Lemma triple_seq P P' P'' c1 c2 o :
  TRIPLE P c1 nil P' ->
  TRIPLE P' c2 o P'' ->
  TRIPLE P (do! c1; c2) o P''.
Proof. move => T1 T2. apply: triple_seqcat T1 T2. done. Qed.

