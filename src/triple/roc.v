Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.triple.morphisms.

Import Prenex Implicits.

Lemma triple_roc P' Q' P c o Q:
  P |-- P' -> Q' |-- Q -> TRIPLE P' c o Q' -> TRIPLE P c o Q.
Proof. move=> HP HQ H. setoid_rewrite ->HP. by setoid_rewrite <-HQ. Qed.

Lemma triple_roc_pre P' P c O Q:
  P |-- P' -> TRIPLE P' c O Q -> TRIPLE P c O Q.
Proof. move=> HP H. by rewrite ->HP. Qed.

Lemma triple_roc_post Q' P c O Q:
  Q' |-- Q -> TRIPLE P c O Q' -> TRIPLE P c O Q.
Proof. move=> HQ H. by rewrite <-HQ. Qed.
