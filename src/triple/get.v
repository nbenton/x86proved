Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [getRegFromProcState] *).
Require Import x86proved.pointsto (* for [:->] *) x86proved.cursor (* for [PTR >-> DWORDCursor] *).

Require Import x86proved.triple.morphisms.
Require Import x86proved.triple.get_readable.

Import Prenex Implicits.

Lemma triple_letGetFlag (fl:Flag) (v:bool) (P Q: SPred) O c:
  (P |-- fl ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getFlagFromProcState fl) c) O Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f.
  eexists o.
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  rewrite /flagIs in Hs1. rewrite /getFlagFromProcState/=.
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Flags fl v). rewrite /= in Hs.
  injection Hs. move => ->. simpl. by destruct (c v s).
  by rewrite -Hs1 /= eq_refl.
Qed.


(** * Get registers *)

Lemma triple_letGetRegPiece rp (v:BYTE) (P Q:SPred) O c:
  (P |-- regPieceIs rp v  ** ltrue) ->  
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getRegPieceFromProcState rp) c) O Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f, o.
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Registers rp v). 
  rewrite /= in Hs.  elim E: rp => [r ix]. rewrite E in Hs. 
  rewrite /getRegPieceFromProcState/=. 
  injection Hs. move => ->. by destruct (c v s).
  by rewrite -Hs1/= E eq_refl. 
Qed.


Lemma triple_letGetRegPieceSep rp v c O Q :
 forall S,
 TRIPLE (regPieceIs rp v ** S) (c v) O Q ->
 TRIPLE (regPieceIs rp v ** S) (bind (getRegPieceFromProcState rp) c) O Q.
Proof. move => S T. apply: triple_letGetRegPiece. cancel2. reflexivity. done. Qed.

Lemma triple_letGetReg (r:AnyReg) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  TRIPLE P (c v) O Q ->
  TRIPLE P (bind (getRegFromProcState r) c) O Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f, o.
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  rewrite /stateIs/regIs in Hs1.
admit. 
(*  specialize (Hs Registers r v). rewrite /= in Hs.
  injection Hs. move => ->. by destruct (c v s).
  by rewrite -Hs1 /= eq_refl.
*)
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
