(*===========================================================================
    Single-step transition function and extension to multiple steps,
    with various lemmas
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool eqtype tuple seq.
Require Import instr monad reader procstate procstatemonad exn eval instrcodec
               monadinst ioaction bitsrep bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Decode instruction at EIP, move EIP to next instruction, execute instruction *)
(*=step *)
Definition step : ST unit :=
  let! oldIP = getRegFromProcState EIP;
  let! (instr,newIP) = readFromProcState oldIP;
  do! setRegInProcState EIP newIP;
  evalInstr instr.
(*=End *)

(* Takes one step from s to s' with output o *)
Definition oneStep s o s' := step s = (o, Success _ (s', tt)). 

(* Takes k steps from s to s' with output o *)
Definition manyStep k s o s' := doMany k step s = (o, Success _ (s', tt)).

(* Takes at least k steps from s *)
Definition runsFor k s := exists s' o, manyStep k s o s'.
Definition runsForWith k o s := exists s', manyStep k o s s'. 

(* Runs forever from s without failing *)
Definition runsForever s := forall k, runsFor k s.

(* Takes some number of steps from s to s' *)
Definition runsTo s s' := exists k o, manyStep k s o s'.
Definition runsToWith s o s' := exists k, manyStep k s o s'. 

(* Takes at least one step from s to s' *)
Definition properRunsTo s s' := exists k o, manyStep k.+1 s o s'.
Definition properRunsToWith s o s' := exists k, manyStep k.+1 s o s'. 

Lemma seqManyStep k1 : forall k2 s s' s'' o1 o2,
  manyStep k1 s o1 s' -> 
  manyStep k2 s' o2 s'' ->
  manyStep (k1+k2) s (o1++o2) s''.
Proof. induction k1 => k2 s s' s'' o1 o2 R1 R2.
+ rewrite add0n. injection R1 => [E1 E2]. by subst. 
+ rewrite /manyStep/= in R1, R2. 
  elim E1: (step s) => [o'' r]. rewrite E1 in R1. 
  elim E2: r => [e| [s''' []]]. by rewrite E2 in R1. 
  rewrite E2 in R1. 
  elim E3: (doMany k1 step s''') => [o''' r']. rewrite E3 in R1. 
  injection R1 => [R1a R2b]. subst.   
  specialize (IHk1 _ _ _ _ _ _ E3 R2). rewrite /manyStep/=. by rewrite E1 IHk1 catA.  
Qed. 

Lemma runsFor0 s : runsFor 0 s.
Proof. by exists s, nil. Qed. 

Lemma runsForWith0 s : runsForWith 0 s nil.
Proof. by exists s. Qed. 

Lemma runsForSinv s k : runsFor k.+1 s ->
  exists s' o, (oneStep s o s' /\ runsFor k s').
Proof. rewrite /runsFor. move => [s' [o RED]]. 
rewrite /manyStep/= in RED. 
case E1: (step s) => [o'' r]. rewrite E1 in RED. 
elim E2: r => [e| [s''' []]]. by rewrite E2 in RED. 
rewrite E2 in RED. 
exists s''', o''. split. by rewrite /oneStep E1 E2. 
elim E3: (doMany k step s''') => [o''' r']. rewrite E3 in RED. 
injection RED => [EQ1 EQ2]. subst.
rewrite /manyStep E3. by eexists _, _. Qed. 

Lemma runsForWithSinv s k o : runsForWith k.+1 s o ->
  exists s' o1 o2, (oneStep s o1 s' /\ runsForWith k s' o2 /\ o = o1++o2).
Proof. rewrite /runsForWith. move => [s' RED]. 
rewrite /manyStep/= in RED. 
case E1: (step s) => [o1 r]. rewrite E1 in RED. 
elim E2: r => [e| [s''' []]]. by rewrite E2 in RED. 
rewrite E2 in RED. 
elim E3: (doMany k step s''') => [o''' r']. rewrite E3 in RED.
exists s''', o1, o'''. split. by rewrite /oneStep E1 E2. 
injection RED => [EQ1 EQ2]. subst.
rewrite /manyStep E3. split => //. by eexists. 
Qed. 

Lemma runsForS k s o s' : oneStep s o s' -> runsFor k s' -> runsFor k.+1 s.
Proof. move => RED1 RED2. rewrite /oneStep in RED1. 
destruct RED2 as [s'' [o'' RED2]]. rewrite /runsFor.
rewrite /manyStep/=. rewrite RED1 RED2. by eexists _, _. 
Qed. 

Lemma runsForWithS k s o s' o' : 
  oneStep s o s' -> runsForWith k s' o' -> runsForWith k.+1 s (o++o').
Proof. move => RED1 [s'' RED2]. rewrite /oneStep in RED1. 
rewrite /runsForWith.
rewrite /manyStep/=. rewrite RED1 RED2. by eexists _. 
Qed. 

Lemma runsForLe k : forall k', k' <= k -> forall s, runsFor k s -> runsFor k' s.
Proof. induction k => k' LT s RED => //.
+ destruct k' => //. 
+ destruct k' => //. apply runsFor0. 
+ specialize (IHk _ LT). 
apply runsForSinv in RED. destruct RED as [s' [o [R1 RED]]]. 
apply: runsForS. apply R1. by apply IHk. 
Qed. 

Lemma cat_preObs o : forall o1 o2, preObs o1 o2 -> preObs (o++o1) (o++o2). 
Proof. induction o => // o1 o2 [o' PO]. subst. exists o'. by rewrite catA. Qed.

Lemma runsForWithLe k : forall o k', k' <= k -> forall s, runsForWith k s o -> 
  exists o', preObs o' o /\ runsForWith k' s o'.
Proof. induction k => o k' LT s RED => //.
+ destruct k' => //. exists o. split => //. reflexivity. 
+ destruct k' => //. exists nil. split => //. by exists o. apply runsForWith0. 
+ apply runsForWithSinv in RED. destruct RED as [s' [o' [o'' [R1 [RED E]]]]].
subst. 
destruct (IHk o'' _ LT _ RED) as [o0 [OBS RUNS]]. 
exists (o'++o0). split. by apply cat_preObs. 
apply: runsForWithS. apply R1. done. 
Qed. 

Lemma runsTo_runsForever s s' :runsTo s s' -> runsForever s' -> runsForever s.
Proof. 
move => [k [o RED]] RF k0. 
case LE: (k <= k0). 
specialize (RF (k0-k)). 
destruct RF as [s'' [o' RF]]. 
have RED1 := seqManyStep RED RF. rewrite subnKC in RED1 => //. eexists _, _. apply RED1.
have LT: k0 < k. by rewrite ltnNge LE. 
apply: runsForLe. apply ltnW in LT. apply LT. by exists s', o.
Qed. 

Lemma runsTo_runsFor k : forall s s', runsTo s s' -> runsFor k s' -> runsFor k s. 
Proof. move => s s' [k1 [o1 R2]] [k0 [o0 R1]].  
have REDS:= seqManyStep R2 R1. 
apply: runsForLe; last first.
eexists _, _. apply REDS. 
rewrite addnC. apply leq_addr. 
Qed. 

Lemma properRunsTo_runsFor k : forall s s', properRunsTo s s' -> runsFor k s' -> runsFor k.+1 s. 
Proof. move => s s' [k1 [o1 R2]] [k0 [o0 R1]].  
have REDS:= seqManyStep R2 R1. 
apply: runsForLe; last first.
eexists _, _. apply REDS. 
rewrite addnC. rewrite -(addn1 k1). rewrite (addnC k1) addnA. rewrite addn1. 
apply leq_addr. 
Qed. 

