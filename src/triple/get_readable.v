Require Import triple.core.
Import triple.core.tripleconfig.

Require Import x86.procstatemonad (* for [getRegFromProcState] *).
Require Import reader (* for [Reader] *) pointsto (* for [interpReader] *) cursor (* for [PTR >-> DWORDCursor] *).

Require Import triple.read.

Import Prenex Implicits.

Local Transparent PStateSepAlgOps.

(** Get readables from memory *)
Lemma triple_letGetSepGen R {r:Reader R} (p:PTR) (v:R) P c O Q :
  P |-- p:->v ** ltrue ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getFromProcState p) c) O Q.
Proof. move => PTIS T s pre.
destruct (T _ pre) as [f [o [H1 H2]]].
exists f.
exists o. split; last done.
rewrite /getFromProcState. specialize (PTIS _ pre).
rewrite /= -H1.
destruct PTIS as [s1 [s2 [Hs [[q Hs1] _]]]].
have Hread := pointsto_read Hs1 _. rewrite Hread. by destruct (c v s).
by edestruct stateSplitsAsIncludes.
Qed.

Lemma triple_letGetSep R {r:Reader R} (p:PTR) (v:R) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getFromProcState p) c) O Q.
Proof. move => S. apply triple_letGetSepGen. by cancel2. Qed.

Lemma triple_letReadSep R {r:Reader R} (p q:PTR) (v:R) c (P:SPred) O Q :
  P |-- p -- q :-> v ** ltrue ->
  TRIPLE P (c (v,q)) O Q ->
  TRIPLE P (bind (readFromProcState p) c) O Q.
Proof. move => PTIS T s pre.
specialize (T _ pre).
destruct T as [f [o [H1 H2]]].
exists f. exists o.
split; last done. clear H2.
rewrite /readFromProcState. specialize (PTIS _ pre).
rewrite /= -H1.
edestruct PTIS as [s1 [s2 [Hs [Hs1 _]]]].
have Hread := pointsto_read Hs1 _.
rewrite Hread. by destruct (c _ s).
edestruct stateSplitsAsIncludes; [apply Hs | eassumption].
Qed.
