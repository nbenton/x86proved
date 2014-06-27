(*===========================================================================
    Predicates over observations (sequences of actions)
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool eqtype fintype finfun seq tuple.
Require Import bitsrep ioaction ilogic.
Require Import Setoid CSetoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Obligation Tactic := idtac.

Definition OPred := ILFunFrm Actions Prop. 

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Instance OLogicOps : ILogicOps OPred := _.
Instance OLogic : ILogic OPred := _. 

Implicit Arguments mkILFunFrm [[e] [ILOps]].

Definition mkOPred (P : Actions -> Prop) 
        (f : forall t t', t === t' -> P t |-- P t') : OPred := mkILFunFrm _ _ P f.

Implicit Arguments mkOPred [].

Program Definition eq_opred s := mkOPred (fun s' => s === s') _.
Next Obligation. move => s t t' EQ. by rewrite EQ. Qed.

Program Definition catOP (P Q: OPred) : OPred
 := @mkILFunFrm _ _ Prop _ (fun o => exists o1 o2, o = o1++o2 /\ P o1 /\ Q o2) _.
Next Obligation.
move => P Q o o' EQ [o1 [o2 [H1 [H2 H3]]]]. 
exists o1, o2. by subst.
Qed.

Program Definition empOP : OPred :=   
  mkILFunFrm _ _ (fun o => o = nil) _.
Next Obligation.
move => o o' EQ. by setoid_rewrite EQ. 
Qed. 


Local Transparent ILFun_Ops ILPre_Ops.

Instance catOP_entails_m: Proper (lentails ==> lentails ==> lentails) catOP.
Proof.
move => O1 O1' HO1 O2 O2' HO2. move => s/= H. 
destruct H as [o1 [o2 [H1 [H2 H3]]]]. subst. 
exists o1, o2. split => //. split. by apply HO1. by apply HO2. 
Qed. 

Instance catSP_lequiv_m: Proper (lequiv ==> lequiv ==> lequiv) catOP.
Proof.
  intros P P' HP Q Q' HQ.
  split; apply catOP_entails_m; (apply HP || apply HQ).
Qed.

Definition outOP (c:Chan) (d:Data) : OPred := eq_opred [::Out c d]. 
Definition seqOP (o:Actions) : OPred := eq_opred o.

Lemma empOPR P : catOP P empOP -|- P.
Proof.
split.
move => o [s1 [s2 [-> [H2 ->]]]]. by rewrite cats0. 
move => o H. exists o, nil. by rewrite cats0. 
Qed. 

Lemma empOPL P : catOP empOP P -|- P.
Proof.
split.
by move => o [s1 [s2 [-> [-> H]]]]. 
move => o H. by exists nil, o. 
Qed.

Lemma catOPA (P Q R : OPred) : catOP (catOP P Q) R -|- catOP P (catOP Q R).
Proof.
split. 
+ move => o [s1 [s2 [-> [[s3 [s4 [-> [H3 H4]]]] H5]]]]. simpl.
  exists s3, (s4++s2). rewrite catA. split => //. split => //. by exists s4, s2. 
+ move => o [s1 [s2 [-> [H2 [s3 [s4 [-> [H4 H5]]]]]]]]. simpl. 
  exists (s1++s3), s4. rewrite catA. split => //. split => //. by exists s1, s3. 
Qed. 

Lemma land_catOP P Q R : catOP (P//\\Q) R |-- (catOP P R) //\\ (catOP Q R).
Proof. apply landR. apply catOP_entails_m => //. by apply landL1. 
                    apply catOP_entails_m => //. by apply landL2. 
Qed.

Lemma catOP_land P Q R : catOP P (Q//\\R) |-- (catOP P Q) //\\ (catOP P R).
Proof. apply landR. apply catOP_entails_m => //. by apply landL1. 
                    apply catOP_entails_m => //. by apply landL2. 
Qed.

Lemma catOP_ltrueL P : P |-- catOP ltrue P.
Proof. move => s H/=. by exists nil, s. Qed.

Lemma catOP_ltrueR P : P |-- catOP P ltrue.
Proof. move => s H/=. exists s, nil. by rewrite cats0. Qed.

Lemma catOP_lfalseL P : catOP lfalse P -|- lfalse.
Proof. split => //. by move => s [s1 [s2 [H1 [H2 H3]]]]/=. Qed. 

Lemma catOP_lfalseR P : catOP P lfalse -|- lfalse.
Proof. split => //. by move => s [s1 [s2 [H1 [H2 H3]]]]/=. Qed. 

Lemma catOP_eq_opred (O: OPred) o1 o2 :
  O o2 ->
  catOP (eq_opred o1) O (o1++o2).
Proof. move => H. 
exists o1, o2. firstorder.  reflexivity. 
Qed. 

Hint Extern 0 (catOP empOP ?O |-- ?P) => by rewrite -> empOPL.  
Hint Extern 0 (catOP ?O ?empOP |-- ?P) => by rewrite -> empOPR.  
