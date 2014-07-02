Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [setRegInProcState] *) x86proved.pmapprops (* for [updateThenLookup] *) x86proved.x86.ioaction (* for [outputToActions] *).
Require Import x86proved.septac (* for [sbazoooka] *) x86proved.pointsto (* for [:->] *) x86proved.pfun (* for [splitsAs] *) x86proved.cursor (* for [PTR >-> DWORDCursor *) x86proved.writer (* for [WriterTm] *).

Require Import x86proved.triple.morphisms x86proved.triple.roc.

Import Prenex Implicits.

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

Lemma triple_setRegSep (r:AnyReg) v w :
  forall S, TRIPLE (r~=v ** S) (setRegInProcState r w) empOP (r~=w ** S).
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
  TRIPLE P (setRegInProcState r w) empOP (r~=w ** R).
Proof. move=> HP. rewrite ->HP. apply: triple_setRegSep. Qed.

Lemma triple_doSetRegSep (r:AnyReg) (v w:DWORD) c O Q :
  forall S,
  TRIPLE (r~=w ** S) c O Q ->
  TRIPLE (r~=v ** S) (do! setRegInProcState r w; c) O Q.
Proof. move => S T s pre. rewrite /TRIPLE in T.
simpl. have H:= separateSetReg w pre.  specialize (T _ H).
destruct T as [f [o [T]]]. exists f, o.
by destruct (c _).
Qed.

Lemma triple_doSetFlagSep (f:Flag) v (w:bool) c O Q :
  forall S,
  TRIPLE (f~=w ** S) c O Q ->
  TRIPLE (f~=v ** S) (do! updateFlagInProcState f w; c) O Q.
Proof. move => S T s pre. rewrite /TRIPLE in T.
simpl. have H:= separateSetFlag w pre. specialize (T _ H).
destruct T as [fs [o T]]. exists fs, o.
by destruct (c _). Qed.

Lemma triple_doForgetFlagSep (f:Flag) v c O Q :
  forall S,
  TRIPLE (f? ** S) c O Q ->
  TRIPLE (f~=v ** S) (do! forgetFlagInProcState f; c) O Q.
Proof. move => S T s pre. rewrite /TRIPLE in T.
simpl. have H:=separateForgetFlag pre. specialize (T _ H).
destruct T as [fs [o T]]. exists fs, o.
by destruct (c _). Qed.

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
  TRIPLE (p:->v ** S) (setBYTEInProcState p w) empOP (p:->w ** S).
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
   else raiseUnspecified) empOP
  (p :-> w ** Q') ->
 TRIPLE
 (p :-> v ** Q)
  (let!s = getProcState;
   if writeMemTm (do! writeNext w; W) s p is Some(_, m')
   then setProcState {| registers := s; flags := s; memory := m' |}
   else raiseUnspecified) empOP
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
  TRIPLE (p:->v ** S) (setDWORDInProcState p w) empOP (p:->w ** S).
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
rewrite [in X in TRIPLE _ _ _ X]sepSPC sepSPA pointsTo_consBYTE sepSPA.
apply triple_setBYTEbind.

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
rewrite [in X in TRIPLE _ _ _ X]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
apply triple_setBYTEbind.

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
rewrite [in X in TRIPLE _ _ _ X]sepSPC sepSPA pointsTo_consBYTE !sepSPA.
apply triple_setBYTEbind.

rewrite ->seqPointsToNil.
rewrite /writeMem !empSPL.
move => s pre. exists s. eexists _. by destruct s.

rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
Qed.

Lemma triple_setDWORDorBYTESep dword (p:PTR) (v w: DWORDorBYTE dword) S :
  TRIPLE (p:->v ** S) (setDWORDorBYTEInProcState p w) empOP (p:->w ** S).
Proof. destruct dword. apply triple_setDWORDSep. apply triple_setBYTESep. Qed.

Lemma triple_doSetDWORDSep (p:PTR) (v w: DWORD) c O Q S :
  TRIPLE (p:->w ** S) c O Q ->
  TRIPLE (p:->v ** S) (do! setDWORDInProcState p w; c) O Q.
Proof. move => T s pre.
destruct (triple_setDWORDSep w pre) as [f [o [H1 [H3 H2]]]].
specialize (T _ H2).
destruct T as [f' [o' [H4 H5]]]. exists f'. rewrite /= H1.
eexists _.
destruct (c f). destruct H5. split => //. injection H4 => -> ->.
simpl in H, H3. subst. done. intuition. simpl in H3.
rewrite /=/outputToActions in H, H3.
rewrite /outputToActions. rewrite map_cat. by setoid_rewrite <- H3.
Qed.
