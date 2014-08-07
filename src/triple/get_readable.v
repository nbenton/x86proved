Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [getRegFromProcState] *).
Require Import x86proved.reader (* for [Reader] *) x86proved.pointsto (* for [interpReader] *) x86proved.cursor (* for [PTR >-> DWORDCursor] *).
Require Import x86proved.common_tactics.

Require Import x86proved.triple.read.
Require Import x86proved.triple.monad.

Import Prenex Implicits.

Local Transparent PStateSepAlgOps.

Local Transparent ILFun_Ops SABIOps PStateSepAlgOps.

Local Ltac pre_let :=
  eapply valued_triple_seqcat; first by apply cat0s.

Local Ltac triple_by_compute_using lem
  := pre_let; triple_by_compute; trivial;
     erewrite lem by eassumption;
     triple_post_compute;
     do !esplit; try eassumption.

Lemma separateGetGen_helper R {r : Reader R} (p : PTR) (v : R) (P : SPred) (s : ProcState)
      (HP : P |-- p :-> v ** ltrue)
      (Ps : P s)
: exists q, readMem readNext s p = readerOk v q.
Proof.
  specialize (HP _ Ps).
  do ![ progress destruct_head_hnf ex
      | destruct_head_hnf and ].
  erewrite pointsto_read by do [ eassumption | by edestruct stateSplitsAsIncludes ].
  eexists; reflexivity.
Qed.

Lemma separateGetGen_match R {r : Reader R} T (p : PTR) (v : R) (P : SPred) (s : ProcState) Ok W F
      (HP : P |-- p :-> v ** ltrue)
      (Ps : P s)
: match readMem readNext s p return T with
    | readerOk v0 _ => Ok v0
    | readerWrap => W
    | readerFail => F
  end = Ok v.
Proof. by elim (separateGetGen_helper HP Ps) => ? ->. Qed.

(** Get readables from memory *)
Lemma triple_letGetSepGen R {r:Reader R} (p:PTR) (v:R) P c O Q :
  P |-- p:->v ** ltrue ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getFromProcState p) c) O Q.
Proof. move => ?. triple_by_compute_using separateGetGen_match. Qed.

Lemma triple_letGetSep R {r:Reader R} (p:PTR) (v:R) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getFromProcState p) c) O Q.
Proof. move => S. apply triple_letGetSepGen. by cancel2. Qed.

Lemma separateGetGen_match' R {r : Reader R} (p q : PTR) (v : R) (P : SPred) (s : ProcState)
      (HP : P |-- p -- q :-> v ** ltrue)
      (Ps : P s)
: readMem readNext s p = readerOk v q.
Proof.
  specialize (HP _ Ps).
  do ![ progress destruct_head_hnf ex
      | destruct_head_hnf and ].
  erewrite pointsto_read by do [ eassumption | by edestruct stateSplitsAsIncludes ].
  eexists; reflexivity.
Qed.

Lemma triple_letReadSep R {r:Reader R} (p q:PTR) (v:R) c (P:SPred) O Q :
  P |-- p -- q :-> v ** ltrue ->
  TRIPLE P (c (v,q)) O Q ->
  TRIPLE P (bind (readFromProcState p) c) O Q.
Proof. move => ?. triple_by_compute_using separateGetGen_match'. Qed.
