Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.x86.procstatemonad (* for [setRegInProcState] *) x86proved.pmapprops (* for [updateThenLookup] *) x86proved.x86.ioaction (* for [outputToActions] *).
Require Import x86proved.spred x86proved.pfun (* for [splitsAs] *) x86proved.writer (* for [WriterTm] *) x86proved.cursor.

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
Lemma setThenGetRegPieceSame d ix v : ix<8 -> getRegPiece (putRegPiece d ix v) ix = v.
Proof. move => LT. rewrite /getRegPiece/putRegPiece.
- do 8 (destruct ix; first apply getUpdateSlice). 
- done. 
Qed. 

(* This proof is absurd *)
Lemma setThenGetRegPieceDistinct d ix1 ix2 v : ix1 != ix2 ->
  getRegPiece (putRegPiece d ix1 v) ix2 = getRegPiece d ix2.
Proof. admit. (* move => H. rewrite /getRegPiece/putRegPiece. 
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
discriminate H.  *)
Qed.   

Lemma AnyRegPiece_eqE r1 ix1 r2 ix2 : 
  mkRegPiece r1 ix1 == mkRegPiece r2 ix2 = (r1 == r2) && (ix1 == ix2).
Proof. done. Qed. 

Lemma separateSetRegPiece (r:Reg64) ix (v w:BYTE) Q s :
  ix < 8 ->
  (regPieceIs (mkRegPiece r ix) v ** Q) (toPState s) -> 
  (regPieceIs (mkRegPiece r ix) w ** Q) (s ! r := putRegPiece (registers s r) ix w).
Proof. move => LT.
rewrite /regPieceIs. rewrite /update/ProcStateUpdateOps/=.
move => [s1 [s2 [H1 [H2 H3]]]].
exists (addRegPieceToPState s1 (mkRegPiece r ix) w), s2.

split.
move => fr. specialize (H1 fr).
destruct fr => //.
  (* registers *)
rewrite /splitsAs/= in H1. rewrite /splitsAs/=.
move => [r0 ix0]. specialize (H1 (mkRegPiece r0 ix0)). 
case Er: (r == r0). rewrite (eqP Er). rewrite (eqP Er) in H2.
case Ei: (ix == ix0). rewrite (eqP Ei) eq_refl. rewrite (eqP Ei) in H2. 
- rewrite setThenGetSame.
  destruct H1.
  * left. destruct H as [Ha Hb]. rewrite setThenGetRegPieceSame. split => //. by rewrite -(eqP Ei). 
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
by case E: (mkRegPiece r ix  == r').
Qed. 

Lemma RegPieceFromStateDefAux r P s b i : (regPieceIs (mkRegPiece r i) b ** P) s -> 
  s Registers (mkRegPiece r i) = Some b. 
Proof. move => [s1 [s2 [Hs [Hs1 Hs2]]]].
  case: (stateSplitsAsIncludes Hs) => {Hs} Hs _.
  specialize (Hs Registers (mkRegPiece r i) b). 
  rewrite /= in Hs. apply Hs. by rewrite -Hs1/= eq_refl. 
Qed.

Lemma RegPieceFromStateDef (r:Reg OpSize8) (v:QWORD) (s: PState) :
  (r~=v) s -> 
  forall ix,
  ix<8 ->
  s Registers (mkRegPiece r ix) = Some (getRegPiece v ix).
Proof. move => H. 
rewrite /stateIs/reg64Is in H.
move => ix LT.  
destruct ix => //. 
- by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 2 rewrite <- sepSPA in H. 
rewrite -> (sepSPC (regPieceIs (mkRegPiece r 0) _)) in H. do 2 rewrite -> sepSPA in H.
apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 1 rewrite <- sepSPA in H. rewrite -> sepSPC in H.
rewrite -> sepSPA in H. apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 2 rewrite <- sepSPA in H. rewrite -> sepSPC in H.
rewrite -> sepSPA in H. apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 3 rewrite <- sepSPA in H. rewrite -> sepSPC in H.
rewrite -> sepSPA in H. apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 4 rewrite <- sepSPA in H. rewrite -> sepSPC in H.
rewrite -> sepSPA in H. apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 5 rewrite <- sepSPA in H. rewrite -> sepSPC in H.
rewrite -> sepSPA in H. apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
destruct ix => //. 
- apply lentails_eq in H. do 6 rewrite <- sepSPA in H. rewrite -> sepSPC in H.
rewrite -> sepSPA in H. apply lentails_eq in H. by apply RegPieceFromStateDefAux in H. 
Qed. 

Lemma addRegPieceIsSepAux rp b b' (P:SPred) s : 
  (regPieceIs rp b' ** P) s ->
  (regPieceIs rp b ** P) (addRegPieceToPState s rp b).
Proof. move => [s1 [s2 [Hs [Hs1 Hs2]]]].
exists (addRegPieceToPState emptyPState rp b), s2. split => //. 
elim. 
(* registers *)
- specialize (Hs Registers).  
destruct (splitsAsIncludes Hs) as [Hsa Hsb].
move => rp'. simpl. case E: (rp == rp'). 
  + specialize (Hs rp'). 
    destruct (s Registers rp'). destruct Hs. intuition. 
    specialize (Hs1 Registers rp'). rewrite /= E in Hs1. rewrite -Hs1 in H. by destruct H. 
    left. intuition.
  + specialize (Hs rp'). 
    destruct (s Registers rp'). 
    destruct Hs. specialize (Hs1 _ rp'). rewrite/= E in Hs1. rewrite -Hs1 in H. by destruct H. 
    right. by destruct H. by destruct Hs.  
(* memory *)
- move => v. specialize (Hs Memory v). simpl. destruct (s Memory v). 
  destruct Hs. specialize (Hs1 Memory v). simpl in Hs1. rewrite <- Hs1 in H. by destruct H. 
  right. intuition. by destruct Hs. 
(* flags *)
- move => v. specialize (Hs Flags v). simpl. destruct (s Flags v). 
  destruct Hs. specialize (Hs1 Flags v). simpl in Hs1. rewrite <- Hs1 in H. by destruct H. 
  right. intuition. by destruct Hs. 
Qed. 

Lemma addRegPieceIsSep rp b (P:SPred) s : 
  P s ->
  (s Registers rp = None) ->
  (regPieceIs rp b ** P) 
  (addRegPieceToPState s rp b).
Proof. move => pre.
exists (addRegPieceToPState emptyPState rp b). 
exists s.
split => //. 
simpl. move => fr/=. destruct fr. move => rp'. simpl. 
case E: (rp == rp'). left. rewrite -(eqP E). done.
case E': (s Registers rp') => [x |]. by right. done.
move => p. simpl. case E': (s Memory p) => [x |]. by right. done.
move => p. simpl. case E': (s Flags p) => [x |]. by right. done.
Qed. 

Lemma separateSetReg64 (r:Reg64) (v w:QWORD) Q (s:ProcState) :
  (r~=v ** Q) s -> (r~=w ** Q) (s!r:=w).
Proof.
Admitted.
(*move => [s1 [s2 [Hs [Hs1 Hs2]]]].
rewrite /stateIs/reg64Is in Hs1.
exists
 (addRegPieceToPState 
 (addRegPieceToPState 
 (addRegPieceToPState
 (addRegPieceToPState 
 (addRegPieceToPState 
 (addRegPieceToPState
 (addRegPieceToPState
 (addRegPieceToPState s1
         (mkRegPiece r 0) (getRegPiece w 0))
         (mkRegPiece r 1) (getRegPiece w 1))
         (mkRegPiece r 2) (getRegPiece w 2))
         (mkRegPiece r 3) (getRegPiece w 3))
         (mkRegPiece r 4) (getRegPiece w 4))
         (mkRegPiece r 5) (getRegPiece w 5))
         (mkRegPiece r 6) (getRegPiece w 6))
         (mkRegPiece r 7) (getRegPiece w 7))
, s2.
have RPS := RegPieceFromStateDef Hs1. 

split; last first. 
rewrite /stateIs/reg64Is in Hs1. rewrite /stateIs/reg64Is.
split.
apply lentails_eq. do 6 rewrite <- sepSPA. rewrite sepSPC. rewrite sepSPA. apply lentails_eq.
eapply addRegPieceIsSepAux. 
apply lentails_eq. do 5 rewrite <- sepSPA. rewrite sepSPC. rewrite sepSPA. apply lentails_eq.
eapply addRegPieceIsSepAux. 
apply lentails_eq. do 4 rewrite <- sepSPA. rewrite sepSPC. rewrite sepSPA. apply lentails_eq.
eapply addRegPieceIsSepAux. 
apply lentails_eq. do 3 rewrite <- sepSPA. rewrite sepSPC. rewrite sepSPA. apply lentails_eq.
eapply addRegPieceIsSepAux. 
apply lentails_eq. do 2 rewrite <- sepSPA. rewrite sepSPC. rewrite sepSPA. apply lentails_eq.
eapply addRegPieceIsSepAux. 
apply lentails_eq. do 1 rewrite <- sepSPA. rewrite sepSPC. rewrite sepSPA. apply lentails_eq.

eapply addRegPieceIsSepAux. 
apply Hs1. 

move => fr. 
specialize (Hs fr).
destruct fr => //.
  (* registers *)
rewrite /splitsAs/= in Hs. rewrite /splitsAs/=. 
elim => [r0 ix0].
case Er: (r == r0). rewrite (eqP Er). rewrite (eqP Er) in Hs1, RPS.
specialize (RPS ix0). 
specialize (Hs (AnyRegPiece r0 ix0)). simpl in Hs. rewrite RPS in Hs. 
destruct Hs. 
- left. destruct ix0; rewrite eq_refl setThenGetSame;
  do 3 (try replace (_ == _) with false by by rewrite AnyRegPiece_eqE andbF); intuition.
- by destruct H. 

(* r != r0 *)
do 4 replace (_ == _) with false by by rewrite AnyRegPiece_eqE Er.
rewrite setThenGetDistinct; last by rewrite Er. simpl. apply (Hs (AnyRegPiece r0 ix0)). 
Qed. 
*)

(** TODO(t-jagro): Add [separateSetDWORD] *)
(*
Lemma separateSetDWORD (p:ADDR) (v w:DWORD) Q s :
  (p:->v ** Q) (toPState s) -> (p:->w ** Q) (toPState (s!p:=w)).
Proof.
  move => [s1 [s2 [H1 [H2 H3]]]].
  rewrite /pointsTo/= in H2. *)

Lemma separateSetFlag (f:Flag) v w Q (s: ProcState) :
  (f ~= v ** Q) s -> (f ~= w ** Q) (s!f:=w).
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
  * rewrite (eqP E)/stateIs in H2. rewrite -H2 in H. case: H => _ H.
    simpl in H. by rewrite eqxx in H.
- rewrite setFlagThenGetDistinct => //. by apply negbT in E.

split => //.
rewrite /stateIs/= in H2. 
eapply flagIsEquiv_m; [reflexivity | reflexivity | rewrite /stateIs; rewrite <- H2; reflexivity|].
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

Lemma triple_setReg64Sep (r:Reg OpSize8) v w S
: TRIPLE (r~=v ** S) (setReg64InProcState r w) nil (r~=w ** S).
Proof. (* try eassmption goes into loop here triple_by_compute.*) 
triple_hnf. 
apply triple_fin. 
move => s H. 
triple_post_compute. repeat split. triple_post_compute. by apply: (separateSetReg64 (v:=v)). 
Qed. 

(*Lemma separateSetReg32 (r:Reg32) (v w:DWORD) Q (s:ProcState) :
  (r~=v ** Q) s -> (r~=w ** Q) (s!r:=w).
*)
Lemma triple_setReg32Sep (r:Reg OpSize4) v w S
: TRIPLE (r~=v ** S) (setReg32InProcState r w) nil (r~=w ** S).
Proof. rewrite /stateIs/reg32Is/=/setReg32InProcState. 
triple_by_compute. 
admit. Qed.

Lemma triple_setReg8Sep (r:Reg OpSize1) v w S
: TRIPLE (r ~= v ** S) (setReg8InProcState r w) nil (r ~= w ** S).
Proof. rewrite /stateIs/reg8Is/=/setReg8InProcState.
destruct r; triple_by_compute; apply: separateSetRegPiece => //; eassumption. Qed.

Lemma triple_setReg16Sep (r:Reg OpSize2) v w S
: TRIPLE (r ~= v ** S) (setReg16InProcState r w) nil (r ~= w ** S).
Proof. rewrite /stateIs/reg16Is/setReg16InProcState.
triple_by_compute. admit. Qed.

Lemma triple_setFlagSep (f:Flag) v (w:bool) S
: TRIPLE (f~=v ** S) (updateFlagInProcState f w) nil (f~=w ** S).
Proof. triple_by_compute. apply: separateSetFlag; eassumption. Qed.

Lemma triple_forgetFlagSep (f:Flag) v S
: TRIPLE (f~=v ** S) (forgetFlagInProcState f) nil (f? ** S).
Proof. triple_by_compute. apply: separateForgetFlag; eassumption. Qed.

Lemma triple_forgetFlagSep' (f : Flag) v S
: TRIPLE (f ~= v ** S) (forgetFlagInProcState f) nil ((Exists v, f ~= v) ** S).
Proof. exact (@triple_forgetFlagSep f v S). Qed.

Lemma byteIsMapped (p:ADDR) (v: BYTE) S s :
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

Lemma triple_setBYTESep (p:ADDR) (v w:BYTE) S
: TRIPLE (p:->v ** S) (setInProcState p w) nil (p:->w ** S).
Proof.
  rewrite 2!pointsToBYTE_byteIs.
  triple_by_compute; erewrite byteIsMapped by eassumption; do ?split.
    by apply: separateSetBYTE; eassumption.
Qed.

Lemma triple_setBYTEbind (v w: BYTE) (p: ADDR) Q (W: WriterTm unit) Q' :
  TRIPLE
  (p :-> w ** Q)
  (let!s = getProcState;
   if writeMemTm W s (next p) is Some(_, m')
   then setProcState {| segregisters := s; registers := s; flags := s; memory := m' |}
   else raiseUnspecified) nil
  (p :-> w ** Q') ->
 TRIPLE
 (p :-> v ** Q)
  (let!s = getProcState;
   if writeMemTm (do! writeNext w; W) s p is Some(_, m')
   then setProcState {| segregisters := s; registers := s; flags := s; memory := m' |}
   else raiseUnspecified) nil
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
case E: (writeMemTm W _ _) => [[p' m] |]. by rewrite E in H.
rewrite E in H. by destruct H. Qed.

(** TODO(t-jagro): Maybe write [separateSetDWORD] and make this proof shorter. *)

Require Import reader writer roundtrip.
Lemma triple_setSep {X} {R:Reader X} {W:Writer X} {RT:Roundtrip R W} (p:ADDR) (v w:X) S
: TRIPLE (p:->v ** S) (setInProcState p w) nil (p:->w ** S).
Admitted.

Lemma triple_setVWORDSep {s} (p: ADDR) (v w: VWORD s) S
: TRIPLE (p:->v ** S) (setInProcState p w) nil (p:->w ** S).
destruct s; apply triple_setSep.
Qed. 

(*
Lemma triple_setDWORDSep (p:ADDR) (v w:DWORD) S
: TRIPLE (p:->v ** S) (setDWORDInProcState p w) nil (p:->w ** S).
Proof.
elim Ev: (@split4 8 8 8 8 v) => [[[v3 v2] v1] v0].
elim Ew: (@split4 8 8 8 8 w) => [[[w3 w2] w1] w0].
rewrite /setDWORDInProcState/setInProcState.
admit.
(*rewrite /writeNext/writeDWORD/writeMem Ew.

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
move => s pre. exists s. by destruct s.

rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
*)
Qed.

Lemma triple_setWORDSep (p:ADDR) (v w:WORD) S
: TRIPLE (p:->v ** S) (setWORDInProcState p w) nil (p:->w ** S).
Proof.
elim Ev: (@split2 8 8 v) => [v1 v0].
elim Ew: (@split2 8 8 w) => [w1 w0].
rewrite /setWORDInProcState/setInProcState.
admit. (*rewrite /writeNext/writeWORD/writeMem Ew.

have PTv := pointsToWORD_asBYTES v.
have PTw := pointsToWORD_asBYTES w.
rewrite Ev in PTv.
rewrite Ew in PTw.
rewrite -PTv -PTw {PTv PTw}.

rewrite 2!pointsTo_consBYTE 2!sepSPA.
apply triple_setBYTEbind.

destruct (next _).
rewrite [in X in TRIPLE X _ _]sepSPC sepSPA pointsTo_consBYTE sepSPA.
rewrite [in X in TRIPLE _ _ _ X]sepSPC sepSPA pointsTo_consBYTE sepSPA.
apply triple_setBYTEbind.

rewrite ->seqPointsToNil.
rewrite /writeMem !empSPL.
move => s pre. exists s. by destruct s.

rewrite topPointsTo_consBYTE. eapply triple_roc_pre. instantiate (1:=lfalse); by ssimpl. done.
*)
Qed.

Lemma triple_setQWORDSep (p:ADDR) (v w:QWORD) S
: TRIPLE (p:->v ** S) (setQWORDInProcState p w) nil (p:->w ** S).
Admitted.

Lemma triple_setVWORDSep s (p:ADDR) (v w: VWORD s) S :
  TRIPLE (p:->v ** S) (setVWORDInProcState p w) nil (p:->w ** S).
Proof. destruct s.  
apply triple_setBYTESep. apply triple_setWORDSep. apply triple_setDWORDSep. 
apply triple_setQWORDSep. Qed.
*)