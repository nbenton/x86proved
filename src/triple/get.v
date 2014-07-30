Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [getRegFromProcState] *).
Require Import x86proved.pointsto (* for [:->] *) x86proved.cursor (* for [PTR >-> DWORDCursor] *).
Require Import x86proved.common_tactics.

Require Import x86proved.triple.morphisms.
Require Import x86proved.triple.get_readable.
Require Import x86proved.triple.monad.

Import Prenex Implicits.

(** * Get registers *)

Local Transparent ILFun_Ops SABIOps PStateSepAlgOps.

Local Ltac pre_let :=
  let lem := match goal with
               | [ |- valued_TRIPLE ?v' ?P' _ ?O2 ?P'' -> valued_TRIPLE ?v' ?P0 (bind ?c1 ?c2) ?O0 ?P'' ]
                 => constr:(fun O1 v => @valued_triple_seqcat _ _ P0 P' P'' O1 O2 c1 c2 v v' O0)
             end in
  eapply lem; first by apply empOPL.

(** In order to get [specialize_all_ways] to pick up values to
    [specialize] hypotheses with, such as [Registers] or [Flags],
    we'll have to [pose] them before we start. *)

Local Ltac get_t :=
  do 5?[ do ![ move => ?
             | progress hnf in *
             | progress rewrite -> eq_refl in *
             | congruence
             | progress destruct_head_hnf and
             | progress destruct_head_hnf ex
             | progress destruct_head_hnf or ]
       | specialize_all_ways ].

Lemma getRegSep (r : AnyReg) v (P : SPred) (s : ProcState)
: P |-- r ~= v ** ltrue -> P s -> v = registers s r.
Proof. pose Registers. get_t. Qed.

Lemma triple_letGetReg (r:AnyReg) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getRegFromProcState r) c) O Q.
Proof. move => ?. pre_let. triple_by_compute; trivial. apply: getRegSep; eassumption. Qed.

Lemma getFlagSep (fl : Flag) (v : bool) (P : SPred) (s : ProcState)
: P |-- fl ~= v ** ltrue -> P s -> v = flags s fl :> FlagVal.
Proof. pose Flags. get_t. Qed.

Lemma triple_letGetFlag (fl:Flag) (v:bool) (P Q: SPred) O c:
  (P |-- fl ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getFlagFromProcState fl) c) O Q.
Proof.
  move => ?. pre_let. triple_by_compute; trivial.
  erewrite <- getFlagSep by eassumption.
  triple_post_compute; by do !split.
Qed.

(*
Lemma letGetReg_ruleIgnore r (P: SPred) c :
  forall S:Facts,
  (forall v, TRIPLE P (c v) [* regIs r v & S]) ->
  TRIPLE P (bind (getRegFromProcState r) c) S.
Proof. move => S T s pre. specialize (T (registers s r)).
simpl. destruct (T s pre) as [f [eq H]]. exists f. intuition.
apply: separateDrop. apply H.
Qed.
*)

Lemma triple_letGetRegSep (r:AnyReg) v c O Q :
 forall S,
 TRIPLE (r~=v ** S) (c v) O Q ->
 TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) O Q.
Proof. move => S T. apply: triple_letGetReg. cancel2. reflexivity. done. Qed.

Lemma triple_letGetFlagSep (fl:Flag) (v:bool) c O Q :
  forall S,
  TRIPLE (fl~=v ** S) (c v) O Q ->
  TRIPLE (fl~=v ** S) (bind (getFlagFromProcState fl) c) O Q.
Proof. move => S T. apply: triple_letGetFlag. cancel2. reflexivity. done. Qed.

Lemma triple_doGetReg (r:AnyReg) (P Q: SPred) O c :
  TRIPLE P c O Q ->
  TRIPLE P (do! getRegFromProcState r; c) O Q.
Proof. move => T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f. eexists o.
simpl. by destruct (c s). Qed.

Lemma triple_doGetFlag (f:Flag) (v:bool) (Q: SPred) O c :
  forall S,
  TRIPLE (f~=v ** S) c O Q ->
  TRIPLE (f~=v ** S) (do! getFlagFromProcState f; c) O Q.
Proof. apply (triple_letGetFlagSep (c:=fun _ => c)). Qed.

(** Get DWORDs from memory *)
Lemma triple_letGetDWORDSep (p:PTR) (v:DWORD) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getDWORDFromProcState p) c) O Q.
Proof. apply triple_letGetSep. Qed.

Lemma triple_letGetDWORDSepGen (p:PTR) (v:DWORD) P c O Q :
  P |-- p:->v ** ltrue ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getDWORDFromProcState p) c) O Q.
Proof. apply triple_letGetSepGen. Qed.

Lemma triple_letGetBYTESep (p:PTR) (v:BYTE) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getBYTEFromProcState p) c) O Q.
Proof. apply triple_letGetSep. Qed.
