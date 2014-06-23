(*===========================================================================
  Hoare triples for reasoning about instruction semantics
  This is architecture-neutral, and assumes only a model that supports
  registers, flags and memory.
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple seq fintype.
Require Import bitsrep bitsprops bitsops bitsopsprops procstate procstatemonad pmapprops.
Require Import monad monadinst reader SPred OPred SPredTotal septac pointsto pfun cursor writer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Hoare triple for machine state monad *)
Definition OTRIPLE (P:SPred) (c:ST unit) (O:OPred) (Q:SPred) :=
  forall s:ProcState, P s ->
    exists f o, c s = (o, Success _ (f,tt)) /\ O o /\ Q f.

(* This is the old definition: we don't care about output *)
Definition TRIPLE P c Q := OTRIPLE P c ltrue Q.

Require Import Setoid Program.Basics.

(* Triples behave contravariantly in the precondition and covariantly in the postcondition wrt
   entailment *)
Add Morphism (@OTRIPLE) with signature lentails --> eq ==> lentails ==> lentails ==> impl as OTRIPLE_mor2.
Proof. move => P P' PP' c O O' OO' Q Q' QQ' H.
move => s H'. assert (H'' : P s) by firstorder.
specialize (H _ H''). destruct H as [f [o [H1 [H2 H3]]]].
exists f, o. firstorder. 
Qed.

Add Morphism (@TRIPLE) with signature lentails --> eq ==> lentails ==> impl as TRIPLE_mor2.
Proof. move => P P' PP' c Q Q' QQ' H. unfold TRIPLE. rewrite -> PP'. rewrite <- QQ'.
apply H. Qed. 

(* Unfortunately we need special case for equivalence *)
Add Morphism (@OTRIPLE) with signature lequiv ==> eq ==> lequiv ==> lequiv ==> iff as OTRIPLE_mor.
Proof. move => P P' PP' c O O' OO' Q Q' QQ'.
split => H.
move => s H'. assert (H'' : P s) by firstorder.
specialize (H _ H''). destruct H as [f [o [H1 [H2 H3]]]].
exists f, o. firstorder. 

move => s H'. assert (H'' : P' s) by firstorder.
specialize (H _ H''). destruct H as [f [o [H1 [H2 H3]]]].
exists f, o. firstorder. 
Qed.

Add Morphism (@TRIPLE) with signature lequiv --> eq ==> lequiv ==> iff as TRIPLE_mor.
Proof. move => P P' PP' c Q Q' QQ'. unfold TRIPLE. rewrite -> PP'. rewrite <- QQ'. done. 
Qed. 


Lemma otriple_roc P' Q' O' P c O Q:
  P |-- P' -> O' |-- O -> Q' |-- Q -> OTRIPLE P' c O' Q' -> OTRIPLE P c O Q.
Proof. move=> HP HO HQ H. by rewrite ->HP, <-HQ, <-HO. Qed.

Lemma triple_roc P' Q' P c Q:
  P |-- P' -> Q' |-- Q -> TRIPLE P' c Q' -> TRIPLE P c Q.
Proof. move => HP HO. by apply otriple_roc. Qed.

Lemma otriple_roc_pre P' P c O Q:
  P |-- P' -> OTRIPLE P' c O Q -> OTRIPLE P c O Q.
Proof. move=> HP H. by rewrite ->HP. Qed.

Lemma otriple_roc_post Q' P c O Q:
  Q' |-- Q -> OTRIPLE P c O Q' -> OTRIPLE P c O Q.
Proof. move=> HQ H. by rewrite <-HQ. Qed.

Lemma triple_skip P : TRIPLE P (retn tt) P.
Proof.  move => s pre; exists s, nil; intuition. done. Qed.

Lemma triple_pre_exists T (Pf: T -> SPred) c O Q :
  (forall t:T, OTRIPLE (Pf t) c O Q) -> OTRIPLE (Exists t, Pf t) c O Q.
Proof. move => TR.
move => s [t' H]. by apply (TR t' s H).
Qed.

Lemma triple_pre_existsOp T (Pf: T -> _) c O Q :
  OTRIPLE (Exists t, Pf t) c O Q -> (forall t:T, OTRIPLE (Pf t) c O Q).
Proof. move => TR t s pre.
apply (TR s). by exists t.
Qed.

Lemma triple_pre_existsSep T (Pf: T -> _) c O Q S :
  (forall t, OTRIPLE (Pf t ** S) c O Q) -> OTRIPLE ((Exists t, Pf t) ** S) c O Q.
Proof.
  move => TR. apply otriple_roc_pre with (Exists t, Pf t ** S).
  - sbazooka.
  move => s [t H]. apply (TR t s H).
Qed.

Lemma triple_pre_existsSepOp T (Pf: T -> _) c O Q S :
  OTRIPLE ((Exists t, Pf t) ** S) c O Q -> (forall t, OTRIPLE (Pf t ** S) c O Q).
Proof.
  move=> TR t. eapply otriple_roc_pre; [|eassumption]. ssplit; reflexivity.
Qed.

Lemma triple_post_disjL P c O Q1 Q2 :
   OTRIPLE P c O Q1 -> OTRIPLE P c O (Q1 \\// Q2).
Proof. move => TR s H.
specialize (TR s H).
destruct TR as [f [o [EQ HH]]].
exists f, o. firstorder. by left. 
Qed.

Lemma triple_post_disjR P c O Q1 Q2 :
   OTRIPLE P c O Q2 -> OTRIPLE P c O (Q1 \\// Q2).
Proof. move => TR s H.
specialize (TR s H).
destruct TR as [f [o [EQ [HO HH]]]].
exists f, o. split => //. split => //. by right. 
Qed.

Lemma triple_post_existsSep T (t:T) P (Qf: T -> _) c O S :
  OTRIPLE P c O (Qf t ** S) -> OTRIPLE P c O ((Exists t, Qf t) ** S).
Proof.
  move=> TR. eapply otriple_roc_post; [|eassumption]. ssplit; reflexivity.
Qed.

Lemma triple_pre_hideFlag (f:Flag) v P c O Q :
  OTRIPLE (f? ** P) c O Q ->
  OTRIPLE (f ~= v ** P) c O Q.
Proof. move => H. by apply (triple_pre_existsSepOp). Qed.


Lemma triple_pre_instFlag (f:Flag) P c O Q :
  (forall v, OTRIPLE (f ~= v ** P) c O Q) ->
  OTRIPLE (f? ** P) c O Q.
Proof. move => TR. apply triple_pre_existsSep => v. apply TR. Qed.

Lemma otriple_seq P P' P'' O1 O2 c1 c2 :
  OTRIPLE P c1 O1 P' ->
  OTRIPLE P' c2 O2 P'' ->
  OTRIPLE P (do! c1; c2) (catOP O1 O2) P''.
Proof. move => T1 T2.
move => s H. rewrite /OTRIPLE in T1, T2.
destruct (T1 _ H) as [s' [o [e [OH H']]]].
destruct (T2 _ H') as [s'' [o' [e' [OH' H'']]]].
exists s''. exists (o++o'). rewrite /= e e'. split => //. 
split => //. exists o, o'. firstorder.
Qed.

Lemma triple_seq P P' P'' c1 c2 :
  TRIPLE P c1 P' ->
  TRIPLE P' c2 P'' ->
  TRIPLE P (do! c1; c2) P''.
Proof. move => T1 T2.
move => s H. 
destruct (T1 _ H) as [s' [o [e [OH H']]]].
destruct (T2 _ H') as [s'' [o' [e' [OH' H'']]]].
exists s''. exists (o++o'). rewrite /= e e'.
firstorder.  
Qed.

(* Set and get registers *)
Lemma triple_letGetReg (r:AnyReg) v (P Q:SPred) O c:
  (P |-- r ~= v ** ltrue) ->
  OTRIPLE P (c v) O Q ->
  OTRIPLE P (bind (getRegFromProcState r) c) O Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f, o.
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Registers r v). rewrite /= in Hs.
  injection Hs. move => ->. by destruct (c v s).
  rewrite -Hs1 /=. by rewrite (eq_refl).
Qed.

Lemma triple_letGetFlag (fl:Flag) (v:bool) (P Q: SPred) O c:
  (P |-- fl ~= v ** ltrue) ->
  OTRIPLE P (c v) O Q ->
  OTRIPLE P (bind (getFlagFromProcState fl) c) O Q.
Proof.
  move => H T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f.
  eexists o.
  rewrite /=. rewrite <-eq. split; last done.
  move/(_ (toPState s) pre): H => [s1 [s2 [Hs [Hs1 _]]]].
  rewrite /flagIs in Hs1. rewrite /getFlagFromProcState/=.
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Flags fl v). rewrite /= in Hs.
  injection Hs. move => ->. simpl. by destruct (c v s).
  rewrite -Hs1 /=. by rewrite eq_refl.
Qed.

Local Transparent PStateSepAlgOps.

Lemma separateSetReg (r:AnyReg) (v w:DWORD) Q s :
  (r~=v ** Q) (toPState s) -> (r~=w ** Q) (toPState (s!r:=w)).
Proof.
simpl.
move => [s1 [s2 [H1 [H2 H3]]]].

rewrite /= in H2.

exists (addRegToPState s1 r w), s2.

split.
move => fr. specialize (H1 fr).
destruct fr => //.
  (* registers *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => r'. specialize (H1 r').
case E: (r == r').
- rewrite (eqP E).
  rewrite setThenGetSame.
  destruct H1.
  * left. split => //. by destruct H.
  * rewrite (eqP E) in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.
- rewrite setThenGetDistinct => //. by apply negbT in E.
simpl.
split; [|assumption].
rewrite -H2 /addRegToPState.
apply: state_extensional => [[]] //. move=> r' /=.
by case E: (r == r').
Qed.


(* This is the crucial lemma that relates the *logical* interpretation of a reader
   (interpReader) with the *operational* interpretation of a reader (readMem) *)
Lemma readMemMemIs R (rt: Reader R) : forall p q (v:R) s s',
  interpReader rt p q v s ->
  stateIncludedIn s (toPState s') ->
  readMem rt s' p = readerOk v q.
Proof.
induction rt => p q v s s' H1 H2/=.
(* readerRetn *)
destruct H1 as [H3 [H4 H5]]. by subst.
(* readerNext *)
simpl in H1.
case E: p => [pp |]. subst.
destruct H1 as [b [s1 [s2 [H5 [H6 H7]]]]].
rewrite /byteIs in H6.
rewrite /addBYTEToPState/emptyPState/= in H6.

destruct (stateSplitsAsIncludes H5) as [H8 H9].
have H10 := stateIncludedIn_trans H9 H2.
rewrite <- H6 in H8.
rewrite /includedIn/= in H8.  specialize (H8 Memory pp (Some b)).
rewrite /=eq_refl in H8. specialize (H8 (refl_equal _)).
rewrite /stateIncludedIn in H2.
specialize (H2 Memory pp _ H8).
inversion H2.
rewrite H1.
specialize (H b (next pp) q v s2).
apply (H _ H7 H10).

by subst.

(* readerSkip *)
simpl in H1.
case E: p => [pp |]. subst.
destruct H1 as [b [s1 [s2 [H5 [H6 H7]]]]].
rewrite /byteIs in H6.
rewrite /addBYTEToPState/emptyPState/= in H6.

destruct (stateSplitsAsIncludes H5) as [H8 H9].
have H10 := stateIncludedIn_trans H9 H2.
rewrite <- H6 in H8.
rewrite /includedIn/= in H8.  specialize (H8 Memory pp (Some b)).
rewrite /=eq_refl in H8. specialize (H8 (refl_equal _)).
rewrite /stateIncludedIn in H2.
specialize (H2 Memory pp _ H8).
inversion H2.
rewrite H0.
specialize (IHrt (next pp) q v s2).
apply (IHrt _ H7 H10).

by subst.

(* readerCursor *)
rewrite /interpReader-/interpReader in H1.
apply: H => //. assumption.
Qed.

Corollary pointsto_read R {r: Reader R} p q (v:R) s s' :
  (p -- q :-> v) s ->
  stateIncludedIn s (toPState s') ->
  readMem readNext s' p = readerOk v q.
Proof. apply readMemMemIs. Qed.

Lemma separateSetBYTE p v w Q s :
  (byteIs p v ** Q) (toPState s) -> (byteIs p w ** Q) (toPState (s!p:=w)).
Proof.
move => [s1 [s2 [H1 [H2 H3]]]].
rewrite /byteIs/= in H2.

exists (addBYTEToPState s1 p w), s2.

split.
move => fr. specialize (H1 fr).
destruct fr => //.
  (* memory *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => p'. specialize (H1 p').
case E: (p == p').
rewrite (eqP E).
  rewrite updateThenLookup.
  destruct H1.
  * left. split => //. by destruct H.
  * rewrite (eqP E) in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.

rewrite updateThenLookupDistinct => //.
apply negbT in E. move => H. by rewrite H eq_refl in E.

split => //.
eapply byteIsEquiv_m; [reflexivity | reflexivity| rewrite <- H2; reflexivity|].
apply: state_extensional => [[]] //. move=> p' /=.
by case E: (p == p').

Qed.

Lemma separateSetFlag (f:Flag) v w Q s :
  (f ~= v ** Q) (toPState s) -> (f ~= w ** Q) (toPState (s!f:=w)).
Proof.
move => [s1 [s2 [H1 [H2 H3]]]].
rewrite /flagIs/= in H2.

exists (addFlagToPState s1 f w), s2.

split.

move => fr. specialize (H1 fr).
destruct fr => //.
(* flags *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => f'. specialize (H1 f').
case E: (f == f').
- rewrite (eqP E).
  rewrite setFlagThenGetSame.
  destruct H1.
  * left. split => //. by destruct H.
  * rewrite (eqP E) in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.
- rewrite setFlagThenGetDistinct => //. by apply negbT in E.

split => //.
eapply flagIsEquiv_m; [reflexivity | reflexivity | rewrite <- H2; reflexivity|].
apply: state_extensional => [[]] //. move=> f' /=.
by case E: (f == f').
Qed.

Lemma separateForgetFlag (f:Flag) v Q s :
  (f ~= v ** Q) (toPState s) -> (f? ** Q) (toPState (s!f:=FlagUnspecified)).
Proof.
 move=> H. apply lentails_eq.
 assert (Hany: f ~= FlagUnspecified |-- f?). unfold stateIsAny. sbazooka.
 rewrite <-Hany => {Hany}. apply-> lentails_eq.
 eapply separateSetFlag. apply H.
Qed.


(*
Lemma pointsToBYTEdef (p:DWORD) (v: BYTE) (s:PState) : (p:->v) s -> s Memory p = Some (Some v).
Proof. move => [q H].
destruct H as [b [s1 [s2 [H1 [H2 H3]]]]].
rewrite /byteIs in H2. rewrite -H2 in H1.
rewrite /addBYTEToPState in H2. simpl in H2. apply f_equal in H2. firstorder. congruence. simpl in H2. rewrite /MemIs in H.
simpl.
destruct H as [m [H1 H2]].
simpl getReader in H1.
rewrite /readBYTE /= /readBYTE_op in H1.
case e': (m p) => [b |]; rewrite e' in H1; last done.
rewrite H2. congruence.
rewrite /inRange leCursor_refl andTb. replace q with (next p) by congruence.
apply ltNext.
Qed.
*)

Lemma triple_setRegSep (r:AnyReg) v w :
  forall S, TRIPLE (r~=v ** S) (setRegInProcState r w) (r~=w ** S).
Proof.
move => S s pre. eexists _, _. split => //. split => //. apply: separateSetReg pre.
Qed.

(*
Lemma triple_setBYTERegSep r (v:DWORD) (w:BYTE) :
  forall S, TRIPLE (regIs r v ** S) (setBYTERegInProcState r w) (regIs r (@high 24 8 v ## w) ** S).
Proof.
move => S s pre. eexists _. split. by rewrite /setBYTERegInProcState/setProcState.
have SRR := separateSetReg _ pre.
elim pre => [s1 [s2 [Hs [Hs1 _]]]].
rewrite /regIs in Hs1.
specialize (Hs1 Registers r); simpl in Hs1.
assert (r == r) by intuition.
rewrite H in Hs1.
specialize (Hs Registers r); destruct Hs as [[H1 H2] | [H1 H2]]; subst.
rewrite H1 in Hs1. inversion Hs1; subst.
apply SRR.
by congruence.
Qed.
*)

Lemma triple_setRegSepGen (r:AnyReg) v w P R:
  P |-- r~=v ** R ->
  TRIPLE P (setRegInProcState r w) (r~=w ** R).
Proof. move=> HP. rewrite ->HP. apply: triple_setRegSep. Qed.

Lemma triple_doSetRegSep (r:AnyReg) (v w:DWORD) c Q :
  forall S,
  TRIPLE (r~=w ** S) c Q ->
  TRIPLE (r~=v ** S) (do! setRegInProcState r w; c) Q.
Proof. move => S T s pre. rewrite /TRIPLE in T.
simpl. have H:= separateSetReg w pre.  specialize (T _ H).
destruct T as [f [o [T]]]. exists f, o.
by destruct (c _).
Qed.

Lemma triple_doSetFlagSep (f:Flag) v (w:bool) c Q :
  forall S,
  TRIPLE (f~=w ** S) c Q ->
  TRIPLE (f~=v ** S) (do! updateFlagInProcState f w; c) Q.
Proof. move => S T s pre. rewrite /TRIPLE in T.
simpl. have H:= separateSetFlag w pre. specialize (T _ H).
destruct T as [fs [o T]]. exists fs, o.
by destruct (c _). Qed.

Lemma triple_doForgetFlagSep (f:Flag) v c Q :
  forall S,
  TRIPLE (f? ** S) c Q ->
  TRIPLE (f~=v ** S) (do! forgetFlagInProcState f; c) Q.
Proof. move => S T s pre. rewrite /TRIPLE in T.
simpl. have H:=separateForgetFlag pre. specialize (T _ H).
destruct T as [fs [o T]]. exists fs, o.
by destruct (c _). Qed.

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

Lemma triple_letGetRegSep (r:AnyReg) v c Q :
 forall S,
 TRIPLE (r~=v ** S) (c v) Q ->
 TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) Q.
Proof. move => S T. apply: triple_letGetReg. cancel2. reflexivity. done. Qed.

Lemma triple_letGetFlagSep (fl:Flag) (v:bool) c Q :
  forall S,
  TRIPLE (fl~=v ** S) (c v) Q ->
  TRIPLE (fl~=v ** S) (bind (getFlagFromProcState fl) c) Q.
Proof. move => S T. apply: triple_letGetFlag. cancel2. reflexivity. done. Qed.

Lemma triple_doGetReg (r:AnyReg) (P Q: SPred) c :
  TRIPLE P c Q ->
  TRIPLE P (do! getRegFromProcState r; c) Q.
Proof. move => T s pre. move: (T s pre) => [f [o [eq H']]]. eexists f. eexists o.
simpl. by destruct (c s). Qed.

Lemma triple_doGetFlag (f:Flag) (v:bool) (Q: SPred) c :
  forall S,
  TRIPLE (f~=v ** S) c Q ->
  TRIPLE (f~=v ** S) (do! getFlagFromProcState f; c) Q.
Proof. apply (triple_letGetFlagSep (c:=fun _ => c)). Qed.

(* Set and get readables from memory *)
Lemma triple_letGetSepGen R {r:Reader R} (p:PTR) (v:R) P c Q :
  P |-- p:->v ** ltrue ->
  TRIPLE P (c v) Q ->
  TRIPLE P (bind (getFromProcState p) c) Q.
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

Lemma triple_letGetSep R {r:Reader R} (p:PTR) (v:R) c Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) Q ->
  TRIPLE (p:->v ** S) (bind (getFromProcState p) c) Q.
Proof. move => S. apply triple_letGetSepGen. by cancel2. Qed.

Lemma triple_letReadSep R {r:Reader R} (p q:PTR) (v:R) c (P:SPred) Q :
  P |-- p -- q :-> v ** ltrue ->
  TRIPLE P (c (v,q)) Q ->
  TRIPLE P (bind (readFromProcState p) c) Q.
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

(* Set and get DWORDs from memory *)
Lemma triple_letGetDWORDSep (p:PTR) (v:DWORD) c Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) Q ->
  TRIPLE (p:->v ** S) (bind (getDWORDFromProcState p) c) Q.
Proof. apply triple_letGetSep. Qed.

Lemma triple_letGetDWORDSepGen (p:PTR) (v:DWORD) P c Q :
  P |-- p:->v ** ltrue ->
  TRIPLE P (c v) Q ->
  TRIPLE P (bind (getDWORDFromProcState p) c) Q.
Proof. apply triple_letGetSepGen. Qed.

Lemma triple_letGetBYTESep (p:PTR) (v:BYTE) c Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) Q ->
  TRIPLE (p:->v ** S) (bind (getBYTEFromProcState p) c) Q.
Proof. apply triple_letGetSep. Qed.

Lemma byteIsMapped (p:PTR) (v: BYTE) S s :
  (byteIs p v ** S) (toPState s) -> isMapped p s.
Proof.
move => [s1 [s2 [H1 [H2 H3]]]].
destruct (stateSplitsAsIncludes H1) as [H4 H5].
rewrite /byteIs/addBYTEToPState in H2; simpl in H2.
rewrite <- H2 in H4.
specialize (H4 Memory p). rewrite /= eq_refl/= in H4.
specialize (H4 (Some v) (refl_equal _)).
inversion H4. rewrite /isMapped H0. done.
Qed.

Lemma triple_setBYTESep (p:PTR) (v w:BYTE) :
  forall S,
  TRIPLE (p:->v ** S) (setBYTEInProcState p w) (p:->w ** S).
Proof.
move => S.
rewrite 2!pointsToBYTE_byteIs.

move => s pre. rewrite /setBYTEInProcState/setInProcState/writeMem/=.
rewrite (byteIsMapped pre).
eexists _, _.
split => //. split => //. apply: (separateSetBYTE _ pre). 
Qed.

Lemma triple_setBYTEbind (v w: BYTE) (p: DWORD) Q (W: WriterTm unit) Q' :
  TRIPLE
  (p :-> w ** Q)
  (let!s = getProcState;
   if writeMemTm W s (next p) is Some(_, m')
   then setProcState {| registers := s; flags := s; memory := m' |}
   else raiseUnspecified)
  (p :-> w ** Q') ->
 TRIPLE
 (p :-> v ** Q)
  (let!s = getProcState;
   if writeMemTm (do! writeNext w; W) s p is Some(_, m')
   then setProcState {| registers := s; flags := s; memory := m' |}
   else raiseUnspecified)
  (p :-> w ** Q').
Proof.
rewrite 2!pointsToBYTE_byteIs.
move => H.
move => s pre.
simpl.
rewrite (byteIsMapped pre).
have post := separateSetBYTE w pre.
specialize (H _ post).
destruct H as [f' H]. simpl in H.
exists f'.
by case E: (writeMemTm W _ _) => [[p' m] |]; rewrite E in H.
Qed.

Lemma triple_setDWORDSep (p:PTR) (v w:DWORD) S:
  TRIPLE (p:->v ** S) (setDWORDInProcState p w) (p:->w ** S).
Proof.
elim Ev: (@split4 8 8 8 8 v) => [[[v3 v2] v1] v0].
elim Ew: (@split4 8 8 8 8 w) => [[[w3 w2] w1] w0].
rewrite /setDWORDInProcState/setInProcState.
rewrite /writeNext/writeDWORD/writeMem Ew.

have PTv := pointsToDWORD_asBYTES v.
have PTw := pointsToDWORD_asBYTES w.
rewrite Ev in PTv.
rewrite Ew in PTw.
rewrite -PTv -PTw {PTv PTw}.

rewrite 2!pointsTo_consBYTE 2!sepSPA.
apply triple_setBYTEbind.

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE sepSPA.
rewrite [in X in TRIPLE _ _ X]sepSPC sepSPA pointsTo_consBYTE sepSPA.
apply triple_setBYTEbind.

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
rewrite [in X in TRIPLE _ _ X]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
apply triple_setBYTEbind.

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
rewrite [in X in TRIPLE _ _ X]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
apply triple_setBYTEbind.

rewrite ->seqPointsToNil.
rewrite /writeMem !empSPL.
move => s pre. exists s. eexists _. by destruct s.

rewrite topPointsTo_consBYTE. eapply otriple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
rewrite topPointsTo_consBYTE. eapply otriple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
rewrite topPointsTo_consBYTE. eapply otriple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
Qed.

Lemma triple_setDWORDorBYTESep dword (p:PTR) (v w: DWORDorBYTE dword) S :
  TRIPLE (p:->v ** S) (setDWORDorBYTEInProcState p w) (p:->w ** S).
Proof. destruct dword. apply triple_setDWORDSep. apply triple_setBYTESep. Qed.

Lemma triple_doSetDWORDSep (p:PTR) (v w: DWORD) c Q S :
  TRIPLE (p:->w ** S) c Q ->
  TRIPLE (p:->v ** S) (do! setDWORDInProcState p w; c) Q.
Proof. move => T s pre.
destruct (triple_setDWORDSep w pre) as [f [o [H1 [H3 H2]]]].
specialize (T _ H2).
destruct T as [f' [o' [H4 H5]]]. exists f'. rewrite /= H1.
eexists _.
destruct (c f). destruct H5. split => //. injection H4 => -> ->. 
simpl in H, H3. subst. done.
Qed.

Hint Rewrite -> (@assoc ST _ _) (@id_l ST _ _) : triple.

Ltac triple_apply lemma tac :=
 autounfold with spred;
 autorewrite with triple;
 eapply triple_roc; [| |eapply lemma];
 do ?(instantiate;
      match goal with
        | [ |- _ |-- _ ] => reflexivity
        | [ |- _ |-- _ ] => progress ssimpl
        | [ |- _ |-- _ ] => done
        | [ |- _ |-- _ ] => progress tac
        | [ |- _ |-- _ ] => fail 2 "Cannot fully solve side-conditions of triple_roc"
      end).

Tactic Notation "triple_apply" constr(lemma) "using" tactic3(tac) := triple_apply lemma tac.
Tactic Notation "triple_apply" constr(lemma) := triple_apply lemma using idtac.
(** The [idtac; fail 1] is a hack to short-circuit the [fail 2] in the [match]... *)
(** TODO(t-jagro): Find a more systematic way to deal with things. *)
Ltac try_triple_apply lemma := triple_apply lemma using (idtac; fail 1).
