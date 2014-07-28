Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.ioaction (* for [outputToActions] *).
Require Import x86proved.common_tactics.

Require Import x86proved.triple.roc.

Import Prenex Implicits.

Lemma triple_skip P : TRIPLE P (retn tt) empOP P.
Proof.  move => s pre; exists s, nil; intuition. done. Qed.

Lemma valued_triple_seqcat {A B} P P' P'' O1 O2 c1 c2 (v : A) (v' : B) O :
  catOP O1 O2 |-- O ->
  valued_TRIPLE v P c1 O1 P' ->
  valued_TRIPLE v' P' (c2 v) O2 P'' ->
  valued_TRIPLE v' P (bind c1 c2) O P''.
Proof.
  move => HO T1 T2. rewrite <- HO; clear HO.
  do !(idtac;
       match goal with
         | _ => move => ?
         | _ => progress hnf in *
         | _ => progress destruct_head_hnf ex
         | _ => progress destruct_head_hnf and
         | _ => progress hyp_rewrite *
         | [ H : forall s : ProcState, ILFunFrm_pred ?P (toPState s) -> _, Ps : _ |- _ ] => specialize (H _ Ps)
       end).
  do !esplit; by [ eassumption | rewrite /outputToActions map_cat ].
Qed.

Lemma triple_seqcat P P' P'' O1 O2 c1 c2 O :
  catOP O1 O2 |-- O ->
  TRIPLE P c1 O1 P' ->
  TRIPLE P' c2 O2 P'' ->
  TRIPLE P (do! c1; c2) O P''.
Proof. apply (valued_triple_seqcat (c2 := fun _ => c2)). Qed.

Lemma triple_seq P P' P'' c1 c2 O :
  TRIPLE P c1 empOP P' ->
  TRIPLE P' c2 O P'' ->
  TRIPLE P (do! c1; c2) O P''.
Proof. move => T1 T2. apply: triple_seqcat T1 T2. by apply empOPL. Qed.
