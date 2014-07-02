Require Import triple.core.
Import triple.core.tripleconfig.

Require Import triple.morphisms.

Import Prenex Implicits.

Lemma triple_roc P' Q' O' P c O Q:
  P |-- P' -> entailsOP O' O -> Q' |-- Q -> TRIPLE P' c O' Q' -> TRIPLE P c O Q.
Proof. move=> HP HO HQ H. setoid_rewrite<-HO. setoid_rewrite ->HP. by setoid_rewrite <-HQ. Qed.

Lemma triple_roc_pre P' P c O Q:
  P |-- P' -> TRIPLE P' c O Q -> TRIPLE P c O Q.
Proof. move=> HP H. by rewrite ->HP. Qed.

Lemma triple_roc_post Q' P c O Q:
  Q' |-- Q -> TRIPLE P c O Q' -> TRIPLE P c O Q.
Proof. move=> HQ H. by rewrite <-HQ. Qed.
