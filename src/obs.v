(*===========================================================================
    obs specification    
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.SPred x86proved.SPredTotal x86proved.septac x86proved.spec.
Require Import x86proved.x86.ioaction x86proved.x86.step x86proved.charge.bilogic x86proved.OPred.
Require Import x86proved.safe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Local Obligation Tactic := idtac.

Program Definition obs (O: OPred) := mkspec (fun k P =>
  forall (s: ProcState), (P ** ltrue) s -> exists o, O o /\ runsForWithPrefixOf k s o) _ _.
Next Obligation. move=> O k P Hsafe s Hs. 
destruct (Hsafe _ Hs) as [o [OH RUNS]]. 
have LE: k <= k.+1 by done.
exists o. split; [done | by apply: runsForWithPrefixOfLe]. 
Qed. 
Next Obligation. move=> O k P P' [R HR] Hsafe s Hs. 
  apply Hsafe.
  rewrite ->lentails_eq in Hs. rewrite <-HR in Hs.
  apply lentails_eq. rewrite ->Hs. by ssimpl.
Qed.

Local Transparent ILFun_Ops ILPre_Ops.

(* Morphism for obs *)
Instance obs_entails_m: Proper (entailsOP ==> lentails) obs.
Proof.
move => O O' HO k R H1 s H2.  
destruct (H1 s H2) as [o1 [H3 H5]]. 
exists o1. by split; [apply: HO |].
Qed. 

Instance obs_equiv_m: Proper (equivOP ==> lequiv) obs.
Proof. move => O O' [HO HO']. split; by apply obs_entails_m. Qed. 

Lemma safeAsObs : safe -|- obs trueOP. 
Proof. 
apply spec_equiv => k R. 
rewrite /safe/obs/mkspec/spec_fun/=.  
rewrite /runsFor/runsForWithPrefixOf. split => H1 s H2.
specialize (H1 _ H2). 
destruct H1 as [s' [o STEPS]]. 
exists o. split => //. exists s', o. split => //. reflexivity.
specialize (H1 _ H2). 
destruct H1 as [o1 [_ [s1 [o2 [H STEPS]]]]]. 
by exists s1, o2. 
Qed. 

Lemma catOP_eq_opred (O: OPred) o1 o2 :
  O o2 ->
  catOP (eq_opred o1) O (o1++o2).
Proof. move => H. 
exists o1, o2. firstorder.  reflexivity. 
Qed. 


Lemma runsToWithObs s o s':
  runsToWith s o s' ->
  forall O, obs O @ eq_pred s' |-- obs (catOP (eq_opred o) O) @ eq_pred s.
Proof. move => RED O k0 R /=H s0 H0.
have H1 := eq_pred_aux s' H0. 
rewrite -(eq_pred_aux2 H0). 
specialize (H _ H1). clear H0 H1.
destruct H as [o1 [H4 H5]]. 
exists (o++o1). split. by apply catOP_eq_opred. 
apply: runsToWith_runsForWithPrefixOf. apply RED. done. 
Qed. 

Lemma oneStepLaterObs s o s':
  oneStep s o s' ->
  forall O,
  |> obs O @ eq_pred s' |-- obs (catOP (eq_opred o) O) @ eq_pred s.
Proof. move => RED O k0 R /=H s0 H0.
have H1 := eq_pred_aux s' H0. 
rewrite -(eq_pred_aux2 H0). 
destruct k0. 
destruct (inhabitedOP O) as [o' Ho']. rewrite /runsForWithPrefixOf/manyStep.
exists (o++o').
split.  
by apply catOP_eq_opred.
exists s. exists nil. split => //. by exists (o++o'). 

have LT: (k0 < k0.+1)%coq_nat by done. specialize (H _ LT s' H1).
destruct H as [o' [Ho [s1 [o1 [PRE RUNS]]]]].
rewrite /runsForWithPrefixOf/manyStep-/manyStep. 
exists (o++o').
split. by apply catOP_eq_opred.
exists s1. eexists _. split; last first. eexists s', o, o1. 
intuition. by apply cat_preActions. 
Qed. 

Instance AtEx_obs O: AtEx (obs O).
Proof.
  move=> A f. 
  move=> k P Hf.
  move=> s Hs.
  sdestruct: Hs => a Hs.
  eapply Hf; eassumption.
Qed.

Instance AtContra_obs O: AtContra (obs O).
Proof.
  move=> R R' HR. move=> k P HP.
  move=> s Hs. apply HP.
  rewrite lentails_eq. rewrite <-HR. by rewrite -lentails_eq.
Qed.


