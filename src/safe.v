(*===========================================================================
    "safe" predicate
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import bitsrep procstate procstatemonad SPred SPredTotal septac spec.
Require Import ioaction step bilogic CSetoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Obligation Tactic := idtac.

Program Definition safe := 
  mkspec (fun k P => forall (s: ProcState), (P ** ltrue) s -> runsFor k s) _ _.
Next Obligation. move=> k P Hsafe s Hs. by apply: runsForLe (Hsafe _ _). Qed.
Next Obligation. move=> k P P' [R HR] Hsafe s Hs. 
  apply Hsafe.
  rewrite ->lentails_eq in Hs. rewrite <-HR in Hs.
  apply lentails_eq. rewrite ->Hs. by ssimpl.
Qed.

Local Transparent ILFun_Ops ILPre_Ops.

Lemma safeAtState (s: ProcState) : 
  |-- safe @ eq_pred s <-> runsForever s. 
Proof. 
split => H. 
+ move => k. 
  specialize (H k empSP I). simpl in H. 
  apply H. apply lentails_eq. by ssimpl. 
+ move => k R _ s' H0. 
  apply lentails_eq in H0. rewrite -> sepSPA in H0. 
  rewrite -> eqPredProcState_sepSP in H0. 
  apply lentails_eq in H0. simpl in H0. apply toPState_inj in H0. by subst. 
Qed. 

Lemma runsTo_safeClosed s s':
  runsTo s s' ->
  |-- safe @ eq_pred s' -> 
  |-- safe @ eq_pred s.
Proof. rewrite 2!safeAtState. by apply runsTo_runsForever. Qed. 

Instance AtEx_safe: AtEx safe.
Proof.
  move=> A f.
  move=> k P Hf.
  move=> s Hs.
  sdestruct: Hs => a Hs.
  eapply Hf; eassumption.
Qed.

Instance AtContra_safe: AtContra safe.
Proof.
  move=> R R' HR. move=> k P HP.
  move=> s Hs. apply HP.
  rewrite lentails_eq. rewrite <-HR. by rewrite -lentails_eq.
Qed.

Lemma runsTo_safe s s':
  runsTo s s' ->
  safe @ eq_pred s' |-- safe @ eq_pred s.
Proof. move => RED. 

move => k0 R /=H. 
case E: k0 => [| k0']. move => ? ?. by apply runsFor0.

subst.

move => s0 H0. 
specialize (H s').
have: runsFor k0'.+1 s'.  
apply H.
apply lentails_eq. ssimpl.
apply lentails_eq in H0. 
rewrite -> sepSPC in H0. rewrite<-sepSPA in H0. rewrite ->(sepSPC ltrue) in H0. 
rewrite <- (eqPredTotal_sepSP_trueR) in H0; last by apply totalProcState.
apply eqPredTotal_sepSP in H0; last by apply totalProcState.  
rewrite -> H0. by ssimpl.

apply runsTo_runsFor. 
apply lentails_eq in H0.
rewrite -> sepSPA in H0. 
rewrite -> eqPredProcState_sepSP in H0. 
apply lentails_eq in H0. simpl in H0. 
apply toPState_inj in H0. by subst. 
Qed. 

Lemma properRunsTo_safe s s':
  properRunsTo s s' ->
  |> safe @ eq_pred s' |-- safe @ eq_pred s.
Proof. move => RED k0 R H. 

case E: k0 => [| k0']. move => ? ?. by apply runsFor0.

subst.

move => s0 H0.

Local Transparent ILLaterPreOps.
 
have LT: (k0' < k0'.+1)%coq_nat by done. specialize (H _ LT s'). clear LT.
apply lentails_eq in H0. 
rewrite -> sepSPC in H0. rewrite<-sepSPA in H0. rewrite ->(sepSPC ltrue) in H0. 
rewrite <- (eqPredTotal_sepSP_trueR) in H0; last by apply totalProcState.
have H0' := H0.
apply eqPredTotal_sepSP in H0; last by apply totalProcState.
rewrite -> eqPredProcState_sepSP in H0'.  
apply lentails_eq in H0'. simpl in H0'. 
apply toPState_inj in H0'. subst. 
apply: (properRunsTo_runsFor RED). 
apply: H. 
apply lentails_eq. rewrite <-H0. by ssimpl. 
Qed. 
