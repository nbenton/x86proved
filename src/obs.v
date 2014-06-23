(*===========================================================================
    obs specification    
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import bitsrep procstate procstatemonad SPred SPredTotal septac spec.
Require Import ioaction step bilogic OPred.
Require Import safe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Setoid RelationClasses Morphisms.
Local Obligation Tactic := idtac.

Program Definition obs (O: OPred) := mkspec (fun k P =>
    forall (s: ProcState), (P ** ltrue) s -> exists o1 o2, preObs o1 o2 /\ O o2 /\ runsForWith k s o1) _ _.
Next Obligation. move=> O k P Hsafe s Hs. 
destruct (Hsafe _ Hs) as [o1 [o2 [PRE [OH RUNS]]]]. 
have LE: k <= k.+1 by done.
destruct (runsForWithLe LE RUNS) as [o' [PRE' RUNS']]. 
exists o', o2. split => //. by rewrite -> PRE'. Qed.
Next Obligation. move=> O k P P' [R HR] Hsafe s Hs. 
  apply Hsafe.
  rewrite ->lentails_eq in Hs. rewrite <-HR in Hs.
  apply lentails_eq. rewrite ->Hs. by ssimpl.
Qed.

Local Transparent ILFun_Ops ILPre_Ops.


(* Morphism for obs *)
Instance obs_entails_m: Proper (lentails ==> lentails) obs.
Proof.
move => O O' HO. move => k R. 
move => H1 s H2.  
specialize (H1 s H2). 
destruct H1 as [o1 [o2 [H3 [H4 H5]]]]. 
exists o1, o2. split => //. split => //. 
by apply: HO. 
Qed. 

Instance obs_equiv_m: Proper (lequiv ==> lequiv) obs.
Proof.
move => O O' HO. split. by rewrite HO. by rewrite <-HO. 
Qed. 


Lemma safeAsObs : safe -|- obs ltrue. 
Proof. 
apply spec_equiv => k R. 
rewrite /safe/obs/mkspec/spec_fun/=.  
rewrite /runsFor/runsForWith. split => H1 s H2.
specialize (H1 _ H2). 
destruct H1 as [s' [o STEPS]]. 
exists o, o. split. reflexivity. split => //. by exists s'. 
specialize (H1 _ H2). 
destruct H1 as [o1 [o2 [H1 [_ [s' STEPS]]]]]. 
by exists s', o1. 
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


