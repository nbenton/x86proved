(*===========================================================================
    Single-step transition function and extension to multiple steps,
    with various lemmas
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq.
Require Import x86proved.x86.instr x86proved.monad x86proved.reader x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.x86.exn x86proved.x86.eval x86proved.x86.instrcodec
               x86proved.monadinst x86proved.x86.ioaction x86proved.bitsrep x86proved.bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Decode instruction at EIP, move EIP to next instruction *)
Definition decodeAndAdvance : ST Instr :=
  let! oldIP = getRegFromProcState EIP;
  let! (instr,newIP) = readFromProcState oldIP;
  do! setRegInProcState EIP newIP;
  retn instr.

(*=step *)
Definition step : ST unit :=
  let! instr = decodeAndAdvance;
  evalInstr instr.
(*=End *)

Fixpoint IOM_matches T (m:IOM Chan Data T) (o:Actions) : option T :=
  match m, o with
  | monadinst.Out ch d rest, ioaction.Out ch' d'::o' => 
    if (ch==ch') && (d==d') then IOM_matches rest o' else None
  | monadinst.In ch f, ioaction.In ch' d::o' => 
    if ch==ch' then IOM_matches (f d) o' else None
  | retnIO v, nil => Some v
  | _, _ => None              
  end.

Lemma IOM_matches_bind o1 : forall T (m: IOM Chan Data T) U  v1 (f: T -> IOM Chan Data U) o2 v2, 
  IOM_matches m o1 = Some v1 -> 
  IOM_matches (f v1) o2 = Some v2 ->
  IOM_matches (bind m f) (o1++o2) = Some v2.
Proof. induction o1. 
- move => T m U v1 f o2 v2. destruct m => //. move => /= [->] H. by rewrite H. 
- move => T m U v1 f o2 v2 H1 H2. 
  destruct m => //. destruct a => //. 
  simpl in H1. 
  case E: (ch==c); last by rewrite E in H1. 
  case E': (d == d0); last by rewrite E' andbF in H1.  
  rewrite E E'/= in H1. 
  rewrite /= E E' /=. apply: IHo1. apply H1. apply H2. 
- destruct a => //. 
  simpl in H1. 
  case E: (ch==c); last by rewrite E in H1. 
  rewrite E/= in H1. 
  rewrite /= E /=. apply: IHo1. apply H1. apply H2. 
Qed.
 
(* Labelled transition from s to s' with actions o *)
Definition oneStep s o s' := IOM_matches (step s) o = Some (s', Success _ tt). 

(* Takes k steps from s to s' with events o *)
Fixpoint manyStep k s o s' :=
  if k is k'.+1
  then exists s'' o1 o2, o = o1 ++ o2 /\ oneStep s o1 s'' /\ manyStep k' s'' o2 s'
  else o = nil /\ s = s'.

Lemma manyStepLe k : forall k', k' <= k ->
  forall s o s', manyStep k s o s' -> exists o' s'', preActions o' o /\ manyStep k' s o' s''.
Proof. induction k => k' LE s o s' /=R1.
+ destruct k' => //. elim R1 => [-> ->]. exists nil, s'. split => //. reflexivity.
+ destruct R1 as [s'' [o1 [o2 [EQ [ONE MANY]]]]]. subst.
  destruct k'. rewrite /manyStep. exists nil, s. intuition. by exists (o1++o2).
  specialize (IHk _ LE _ _ _ MANY).
  destruct IHk as [o' [s2 [[o3 EQ] MANY']]].
  subst.
  exists (o1 ++ o'), s2. split. exists o3. by rewrite catA.
  simpl.
  by exists s'', o1, o'.
Qed.

(* Takes at least k steps from s *)
Definition runsFor k s := exists s' o', manyStep k s o' s'.
Definition runsForWithPrefixOf k s o := exists s' o', preActions o' o /\ manyStep k s o' s'.

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
Proof. induction k1 => k2 s s' s'' o1 o2 /= R1 R2.
+ rewrite add0n. destruct R1 as [E1 E2]. by subst.
+ destruct R1 as [s0 [o3 [o4 [E1 [STEP R1]]]]]. subst.
  specialize (IHk1 _ _ _ _ _ _ R1 R2).
  exists s0, o3, (o4 ++ o2). split. by rewrite catA.
  intuition.
Qed.

Lemma runsFor0 s : runsFor 0 s.
Proof. by exists s, nil. Qed.

Lemma runsForWithPrefixOf0 s o : runsForWithPrefixOf 0 s o.
Proof. exists s, nil. split. unfold preActions. by exists o. done. Qed.

Lemma runsForSinv s k : runsFor k.+1 s ->
  exists s' o, (oneStep s o s' /\ runsFor k s').
Proof. rewrite /runsFor. move => [s' [o RED]].
rewrite /manyStep-/manyStep in RED.
destruct RED as [s'' [o1 [o2 [H1 [ONE MANY]]]]].
exists s'', o1. split => //.
by exists s', o2.
Qed.

Lemma runsForWithPrefixOfSinv s k o : runsForWithPrefixOf k.+1 s o ->
  exists s' o1 o2, (oneStep s o1 s' /\ runsForWithPrefixOf k s' o2 /\ o = o1++o2).
Proof. rewrite /runsForWithPrefixOf. move => [s' [o' [PRE RED]]].
rewrite /manyStep-/manyStep in RED.
destruct RED as [s'' [o1 [o2 [H [ONE MANY]]]]].
subst. destruct PRE as [o' PRE]. subst.
exists s'', o1, (o2++o'). split => //.
split; last by rewrite catA.
exists s', o2. split => //. by exists o'.
Qed.

Lemma runsForS k s o s' : oneStep s o s' -> runsFor k s' -> runsFor k.+1 s.
Proof. move => ONE [s1 [o1 MANY]]. exists s1, (o++o1). by exists s', o, o1. Qed.

Lemma runsForWithPrefixOfS k s o s' o' :
  oneStep s o s' -> runsForWithPrefixOf k s' o' -> runsForWithPrefixOf k.+1 s (o++o').
Proof. move => ONE [s1 [o1 [PRE MANY]]]. exists s1, (o++o1).
split. by apply cat_preActions. by exists s', o, o1.
Qed.

Lemma runsForLe k : forall k', k' <= k -> forall s, runsFor k s -> runsFor k' s.
Proof. induction k => k' LT s RED => //.
+ destruct k' => //.
+ destruct k' => //. apply runsFor0.
+ specialize (IHk _ LT).
apply runsForSinv in RED. destruct RED as [s' [o [R1 RED]]].
apply: runsForS.  apply R1. apply IHk => //.
Qed.


Lemma runsForWithPrefixOfLe k :
  forall k' s o, k' <= k -> runsForWithPrefixOf k s o -> runsForWithPrefixOf k' s o.
Proof. induction k => k' s o LE RED => //.
+ by destruct k' => //.
+ destruct k' => //. apply runsForWithPrefixOf0.
  apply runsForWithPrefixOfSinv in RED.
  destruct RED as [s' [o' [o'' [ONE [RED EQ]]]]]. subst.
  apply: runsForWithPrefixOfS. apply ONE. apply IHk => //.
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

Lemma runsToWith_runsForWithPrefixOf k : forall s o s' o',
  runsToWith s o s' -> runsForWithPrefixOf k s' o' ->
  runsForWithPrefixOf k s (o++o').
Proof. move => s o s' o' R1 R2.
destruct R1 as [k1 R1].
destruct R2 as [s2 [o2 [PRE R2]]].
have R3 := seqManyStep R1 R2.
rewrite /runsForWithPrefixOf.
have LE: k <= k1 + k. rewrite addnC. by apply leq_addr.
have MSLE:= manyStepLe LE R3.
destruct MSLE as [o3 [s3 [PRE' MANY]]].
exists s3, o3. split => //.
destruct PRE' as [o4 PRE'].
destruct PRE as [o5 PRE]. subst.
exists (o4++o5). rewrite catA. rewrite PRE'. by rewrite catA.
Qed.

Lemma properRunsTo_runsFor k : forall s s', properRunsTo s s' -> runsFor k s' -> runsFor k.+1 s.
Proof. move => s s' [k1 [o1 R2]] [k0 [o0 R1]].
have REDS:= seqManyStep R2 R1.
apply: runsForLe; last first.
eexists _, _. apply REDS.
rewrite addnC. rewrite -(addn1 k1). rewrite (addnC k1) addnA. rewrite addn1.
apply leq_addr.
Qed.
