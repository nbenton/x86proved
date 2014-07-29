Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [setRegInProcState] *) x86proved.pmapprops (* for [updateThenLookup] *) x86proved.x86.ioaction (* for [outputToActions] *).
Require Import x86proved.septac (* for [sbazoooka] *) x86proved.pointsto (* for [:->] *) x86proved.pfun (* for [splitsAs] *) x86proved.cursor (* for [PTR >-> DWORDCursor *) x86proved.writer (* for [WriterTm] *).

Require Import x86proved.triple.morphisms x86proved.triple.roc.

Import Prenex Implicits.

Local Transparent PStateSepAlgOps.

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

Require Import bitsprops.
Lemma updateSliceGetSame n1 n2 n3 d v : slice n1 n2 n3 (updateSlice n1 n2 n3 d v) = v.
Proof. by rewrite /slice/updateSlice/split3/split2 low_catB high_catB. Qed.

(*Lemma updateSliceGetDistinct n1 n2 n3 d v : slice n1 n2 n3 (updateSlice n1' n2' n3 d v) = slice n1 n2 n3 d.
Proof. rewrite /slice/updateSlice/split3/split2 low_catB high_catB. Qed.
*)


Lemma setThenGetRegPieceSame d ix v : getRegPiece (putRegPiece d ix v) ix = v.
Proof. rewrite /getRegPiece/putRegPiece. case ix; apply updateSliceGetSame. Qed.

(* This proof is absurd *)
Lemma setThenGetRegPieceDistinct d ix1 ix2 v : ix1 != ix2 ->
  getRegPiece (putRegPiece d ix1 v) ix2 = getRegPiece d ix2.
Proof. move => H. rewrite /getRegPiece/putRegPiece. 
destruct ix2. 
  destruct ix1.  
  + done. 
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    have LT': i < 8+8. by apply ltn_addr.
    rewrite (@getBit_catB 16 16) => //. 
    rewrite (@getBit_catB 8 8) => //. 
    rewrite getBit_low LT. rewrite getBit_low. by rewrite LT'. 
  + apply sliceEq => i /andP [LE LT]. 
    have LT' : i < 8+8 by apply ltn_addr.
    have LT'' : i < 8+8+8 by apply ltn_addr.
    rewrite /updateSlice/split3/split2. 
    rewrite (@getBit_catB 8 24) => //. 
    rewrite (@getBit_catB 8 16) => //. 
    rewrite getBit_low LT'.  
    by rewrite getBit_low LT''.  
  + apply sliceEq => i /andP [LE LT]. 
    have LT' : i < 8+8 by apply ltn_addr.
    have LT'' : i < 8+8+8 by apply ltn_addr.
    have LT''' : i < 8+8+8+8 by apply ltn_addr.
    rewrite /updateSlice/split3/split2. 
    rewrite (@getBit_catB 0 32) => //. 
    rewrite (@getBit_catB 8 24) => //. 
    rewrite getBit_low LT''. 
    by rewrite getBit_low LT'''.  
  destruct ix1. 
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2.
    rewrite (@getBit_catB 24 8). have NLT: ~~(i<8). by rewrite ltnNge in LE. 
    apply negbTE in NLT. rewrite NLT. rewrite getBit_high. by rewrite subnK. 
  + done.
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    have LT'' : i < 8+8+8 by apply ltn_addr.
    rewrite (@getBit_catB 8 24) => //. 
    rewrite (@getBit_catB 8 16) => //. 
    rewrite getBit_low LT.  
    by rewrite getBit_low LT''.  
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    have LT'' : i < 8+8+8 by apply ltn_addr.
    have LT''' : i < 8+8+8+8 by apply ltn_addr.
    rewrite (@getBit_catB 0 32) => //. 
    rewrite (@getBit_catB 8 24) => //. 
    rewrite getBit_low LT''.  
    by rewrite getBit_low LT'''.  

  destruct ix1. 
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    have LT''' : i < 8+8+8+8 by apply ltn_addr.
    rewrite (@getBit_catB 24 8). 
    have NLT: ~~(i<8). rewrite ltnNge negbK. by apply: ltn_trans LE. 
    rewrite (negbTE NLT). rewrite getBit_high. rewrite subnK. done. 
    by rewrite ltnNge. 
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    have LT''' : i < 8+8+8+8 by apply ltn_addr.
    rewrite (@getBit_catB 16 16) => //. 
    have NLT: ~~(i<16). by rewrite ltnNge in LE. 
    rewrite (negbTE NLT). rewrite getBit_high. by rewrite subnK. 
  + by elim H. 
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    have LT''' : i < 8+8+8+8 by apply ltn_addr.
    rewrite (@getBit_catB 0 32) => //. rewrite LT'''. 
    rewrite (@getBit_catB 8 24) => //. rewrite LT. 
    rewrite getBit_low LT. by rewrite getBit_low LT'''.
  destruct ix1. 
  + apply sliceEq => i /andP [LE LT]. 
    rewrite /updateSlice/split3/split2. 
    rewrite (@getBit_catB 24 8) => //. 
    have NLT: ~~(i<8). rewrite ltnNge. rewrite negbK.
    by apply: ltn_trans LE. 
    rewrite (negbTE NLT). rewrite getBit_high. rewrite subnK. done.
    by  rewrite ltnNge. 
  + apply sliceEq => i /andP [LE LT]. 
  rewrite /updateSlice/split3/split2. 
  rewrite (@getBit_catB 16 16) => //. 
  have NLT: ~~(i<16). rewrite ltnNge negbK. by apply: ltn_trans LE. 
  rewrite (negbTE NLT). rewrite getBit_high. rewrite subnK. done.
  by rewrite ltnNge.
  + apply sliceEq => i /andP [LE LT]. 
  rewrite /updateSlice/split3/split2. 
  rewrite (@getBit_catB 8 24) => //. 
  have NLT: ~~(i<24). by rewrite ltnNge in LE. 
  rewrite (negbTE NLT). rewrite getBit_high. by rewrite subnK.
discriminate H.  
Qed.   

Lemma AnyRegPiece_eqE r1 ix1 r2 ix2 : 
  AnyRegPiece r1 ix1 == AnyRegPiece r2 ix2 = (r1 == r2) && (ix1 == ix2).
Proof. done. Qed. 

Lemma separateSetRegPiece (r:AnyReg) ix (v w:BYTE) Q s :
  (regPieceIs (AnyRegPiece r ix) v ** Q) (toPState s) -> 
  (regPieceIs (AnyRegPiece r ix) w ** Q) (s ! r := putRegPiece (registers s r) ix w).
Proof. 
rewrite /regPieceIs. rewrite /update/ProcStateUpdateOps/=.
move => [s1 [s2 [H1 [H2 H3]]]].
exists (addRegPieceToPState s1 (AnyRegPiece r ix) w), s2.

split.
move => fr. specialize (H1 fr).
destruct fr => //.
  (* registers *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => [r0 ix0]. specialize (H1 (AnyRegPiece r0 ix0)). 
case Er: (r == r0). rewrite (eqP Er). rewrite (eqP Er) in H2.
case Ei: (ix == ix0). rewrite (eqP Ei) eq_refl. rewrite (eqP Ei) in H2. 
- rewrite setThenGetSame.
  destruct H1.
  * left. destruct H as [Ha Hb]. by rewrite setThenGetRegPieceSame.    
  * rewrite -H2 in H. case: H => _ H. simpl in H. by rewrite eqxx in H. 
- rewrite AnyRegPiece_eqE. rewrite Ei andbF.
  rewrite setThenGetSame => //. 
  rewrite setThenGetRegPieceDistinct => //. by rewrite  Ei. 
  rewrite AnyRegPiece_eqE. rewrite Er andFb.
  rewrite setThenGetDistinct => //. by rewrite Er. 

simpl. 
split; [|assumption].
simpl in H2. rewrite -H2 /addRegPieceToPState.
apply: state_extensional => [[]] //. move=> r' /=.
by case E: (AnyRegPiece r ix  == r').
Qed. 

Lemma separateSetReg (r:AnyReg) (v w:DWORD) Q s :
  (r~=v ** Q) (toPState s) -> (r~=w ** Q) (toPState (s!r:=w)).
Proof.
simpl. rewrite /regIs. rewrite /update/ProcStateUpdateOps/=.  simpl.
move => [s1 [s2 [H1 [H2 H3]]]].
admit. 
(*
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
*)
Qed.


(** TODO(t-jagro): Add [separateSetDWORD] *)
(*
Lemma separateSetDWORD (p:PTR) (v w:DWORD) Q s :
  (p:->v ** Q) (toPState s) -> (p:->w ** Q) (toPState (s!p:=w)).
Proof.
  move => [s1 [s2 [H1 [H2 H3]]]].
  rewrite /pointsTo/= in H2. *)

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

Lemma triple_setRegSep (r:AnyReg) v w S
: TRIPLE (r~=v ** S) (setRegInProcState r w) empOP (r~=w ** S).
Proof. triple_by_compute. apply: separateSetReg; eassumption. Qed.

Lemma triple_setBYTERegSep (r:BYTEReg) v w S
: TRIPLE (BYTEregIs r v ** S) (setBYTERegInProcState r w) empOP (BYTEregIs r w ** S).
Proof. rewrite /BYTEregIs/=/setBYTERegInProcState. elim E: (BYTERegToRegPiece r) => [r' b]. 
triple_by_compute. apply: separateSetRegPiece; eassumption. Qed.

Lemma triple_setRegSepGen (r:AnyReg) v w P R:
  P |-- r~=v ** R ->
  TRIPLE P (setRegInProcState r w) empOP (r~=w ** R).
Proof. move=> HP. rewrite ->HP. apply: triple_setRegSep. Qed.

Lemma triple_setFlagSep (f:Flag) v (w:bool) S
: TRIPLE (f~=v ** S) (updateFlagInProcState f w) empOP (f~=w ** S).
Proof. triple_by_compute. apply: separateSetFlag; eassumption. Qed.

Lemma triple_forgetFlagSep (f:Flag) v S
: TRIPLE (f~=v ** S) (forgetFlagInProcState f) empOP (f? ** S).
Proof. triple_by_compute. apply: separateForgetFlag; eassumption. Qed.

Lemma triple_forgetFlagSep' (f : Flag) v S
: TRIPLE (f ~= v ** S) (forgetFlagInProcState f) empOP ((Exists v, f ~= v) ** S).
Proof. exact (@triple_forgetFlagSep f v S). Qed.

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

Lemma triple_setBYTESep (p:PTR) (v w:BYTE) S
: TRIPLE (p:->v ** S) (setBYTEInProcState p w) empOP (p:->w ** S).
Proof.
  rewrite 2!pointsToBYTE_byteIs.
  triple_by_compute.
  rewrite /=/writeMem/=.
  erewrite byteIsMapped by eassumption.
  split; first by reflexivity.
  apply: separateSetBYTE; eassumption.
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

(** TODO(t-jagro): Maybe write [separateSetDWORD] and make this proof shorter. *)
Lemma triple_setDWORDSep (p:PTR) (v w:DWORD) S
: TRIPLE (p:->v ** S) (setDWORDInProcState p w) empOP (p:->w ** S).
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
