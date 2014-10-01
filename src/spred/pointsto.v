(*===========================================================================
    Points-to predicates
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.choice Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.addr.
Require Import x86proved.monad x86proved.reader x86proved.writer x86proved.roundtrip x86proved.spred.core x86proved.spred.stateis x86proved.spred.tactics x86proved.pfun x86proved.cursor x86proved.charge.iltac x86proved.charge.ilogic x86proved.spred.memis.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
   Points-to is a derived notion:
      p :-> v
   iff there exists some q such that p -- q :-> v.
  ---------------------------------------------------------------------------*)


Lemma byteIs_disjoint p1 p2 v1 v2 : byteIs p1 v1 ** byteIs p2 v2 |-- p1 <> p2 /\\ (byteIs p1 v1 ** byteIs p2 v2).
Proof. case E: (p1 == p2). rewrite (eqP E). by setoid_rewrite byteIs_same at 1.
ssplit; last done. move => H. by rewrite H eq_refl in E.
Qed.



Definition pointsTo {R} {_:MemIs R} p v := Exists q, memIs p q v.
Notation "p :-> ? : t" := (Exists x:t, pointsTo p x)(at level 50, no associativity).
Notation "p :-> x" := (pointsTo p x) (at level 50, no associativity).

(* Trivial consequence *)
Lemma memIs_pointsTo {R} {_:MemIs R} p q v :
  p -- q :-> v |-- p :-> v.
Proof. rewrite /pointsTo. by apply lexistsR with q. Qed.

(* This isn't true for n = 2^32 *)
Lemma fixedMemIs_pointsTo X `{_:FixedMemIs X} (p:ADDR) v :
  n<2^naddrBits -> leB p (p+#n) -> p :-> v |-- p -- (p+#n) :-> v.
Proof. move => LT LE.
rewrite /pointsTo. sdestruct => q. 
rewrite -> memIsFixed. sdestruct => AP.
rewrite (leB_apart LT LE AP).  reflexivity. 
Qed.

Tactic Notation "not" tactic1(t) := try (t; fail 1).

  Ltac cheap_unify p :=
    match p with
    | (?a,?b) => is_evar a; first [unify a b | fail 1]
    | (?a,?b) => is_evar b; first [unify a b | fail 1]
    | (?a,?b) => not (has_evar a); not (has_evar b); first [constr_eq a b | fail 1]
    | (?fa ?xa,?fb ?xb) => cheap_unify (fa, fb); cheap_unify (xa, xb)
    end.

Ltac unifyPT P :=
  match P with
    (* These are surely safe *)
  | (byteIs ?p ?v, byteIs ?p ?w) => unify v w
  | (?p :-> ?v, ?p :-> ?w) => unify v w
  | (?i -- ?j :-> ?v, ?i -- ?k :-> ?v) => unify j k
    (* These might be overlapping ranges, but typically we don't expect to see this *)
  | (?i -- ?j :-> ?v, ?i -- ?k :-> ?w) => (unify j k; unify v w)
    (* This seems risky. There might be multiple ranges pointing to the same value *)
  | (?i -- ?j :-> ?v, ?k -- ?l :-> ?v) => (unify i k; unify j l)

  | (stateIs (@RegOrFlagR ?s ?r) ?v, stateIs (@RegOrFlagR ?s ?t) ?w) => 
    (not (has_evar r); not (has_evar t); (unify r t; cheap_unify (v,w)))
  | (stateIs (@RegOrFlagF ?r) ?v, stateIs (@RegOrFlagF ?t) ?w) => 
    (not (has_evar r); not (has_evar t); (unify r t; cheap_unify (v,w)))
  | (stateIs ?r ?v, stateIs ?r ?w) => Solving.cheap_unify (v, w)
  | (?s ?v,?s ?w) => cheap_unify (v, w)
  | _ => Solving.cheap_unify P
  end.

Ltac ssimpl := ssimpl_with unifyPT.
Ltac sbazooka := sbazooka_with unifyPT.


(* In fact p :-> b for b:BYTE is just a long-winded way of saying byteIs p b *)
Lemma pointsToBYTE_byteIs (p:ADDR) b : p :-> b -|- byteIs p b.
Proof.
rewrite /pointsTo. split.
sdestruct => q. rewrite readerMemIsSimpl interpReader_bindBYTE.
rewrite /interpReader. sdestructs => b' -> _. by ssimpl.
apply lexistsR with (next p).
rewrite readerMemIsSimpl interpReader_bindBYTE.
sbazooka. rewrite interpReader_retn. sbazooka.
Qed.

  Lemma seqPointsToNil {X} {MX: MemIs X} (p:ADDRCursor) : p :-> ([::]: seq X) -|- empSP.
  Proof.
    rewrite /pointsTo. split.
    + sdestructs => q. rewrite -> seqMemIsNil. by sdestruct => _.
    + apply lexistsR with p. rewrite seqMemIsNil. sbazooka.
  Qed.

Lemma memIs_consBYTE (p:ADDR) q (b:BYTE) bs : p -- q :-> (b::bs) -|- p :-> b ** (next p) -- q :-> bs.
Proof.
split.
  rewrite -> seqMemIsCons. sdestruct => q'.
  rewrite -> memIsBYTE_next_entails.
  sdestructs => ->. rewrite /pointsTo. sbazooka.

  rewrite /pointsTo. sdestructs => p'. rewrite -> memIsBYTE_next_entails.
  rewrite -> seqMemIsCons.
  sdestructs => ->. sbazooka.
Qed.

Lemma pointsToBYTE_NonTop (c : ADDRCursor) (b:BYTE) :
  c :-> b |-- Exists bits, c = mkCursor bits /\\ c :-> b.
Proof.
elim c => [bits |].
sbazooka.
rewrite {1}/pointsTo.
setoid_rewrite interpReader_bindBYTE_top.
by sdestructs => _.
Qed.

Lemma pointsTo_consBYTE (p:ADDR) (b:BYTE) bs : p :-> (b::bs) -|- p :-> b ** (next p) :-> bs.
Proof.
rewrite /pointsTo.
split.
  sdestruct => q. rewrite -> seqMemIsCons. sdestruct => q'.
  rewrite -> memIsBYTE_next_entails.
  sdestructs => ->. sbazooka.

  sdestructs => q q'.
  apply lexistsR with q'.
  rewrite -> seqMemIsCons. rewrite -> memIsBYTE_next_entails.
  sdestructs => ->. sbazooka.
Qed.


Lemma topPointsTo_consBYTE (x:BYTE) (xs: seq BYTE) : top _ :-> (x::xs) -|- lfalse.
Proof. split => //.
rewrite /pointsTo. sdestruct => q. rewrite -> seqMemIsCons. sdestruct => p'.
rewrite readerMemIsSimpl /readBYTE/=. sbazooka.
Qed.

Fixpoint catBYTES (xs: seq BYTE) : BITS (size xs * 8) :=
  if xs is x::xs return BITS (size xs * 8) then catBYTES xs ## x else nilB.

Lemma cursorPointsTo_consBYTE (p:ADDRCursor) (b:BYTE) bs :
  p :-> (b::bs) -|- Exists p', (p = mkCursor p' /\\ p' :-> b ** (next p') :-> bs).
Proof.
elim p => [p' |]. rewrite pointsTo_consBYTE. split.  apply lexistsR with p'. sbazooka.
sdestructs => p0 [->]. sbazooka.
rewrite topPointsTo_consBYTE.
split => //.
by sdestructs => p' H.
Qed.

(*
Require Import tuplehelp.
Lemma pointsToBITS_BYTES n : forall (p:ADDR) (bs: n.-tuple BYTE),
  p :-> bs -|- p :-> bytesToBits bs.
Proof. induction n => p bs.
- rewrite (tuple0 _). simpl. admit. 
- case/tupleP: bs => [b bs]. simpl. rewrite beheadCons theadCons. admit. 
Qed. 
*)


Lemma pointsToDWORD_BYTES (p:ADDR) (b0 b1 b2 b3:BYTE):
  p :-> [::b0;b1;b2;b3] -|- p :-> (b3 ## b2 ## b1 ## b0).
Proof.
Admitted.
(*rewrite {2}/pointsTo.
rewrite /memIs/readerMemIs/readNext/readDWORD.
split => //.

ssplit.

rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite cursorPointsTo_consBYTE. sdestructs => p0 H0. rewrite pointsToBYTE_byteIs.
rewrite cursorPointsTo_consBYTE. sdestructs => p1 H1. rewrite pointsToBYTE_byteIs.
rewrite cursorPointsTo_consBYTE. sdestructs => p2 H2. rewrite pointsToBYTE_byteIs.
rewrite seqPointsToNil.
rewrite H0. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite H1. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite H2. setoid_rewrite interpReader_bindBYTE. ssplit.
setoid_rewrite interpReader_retn.
rewrite /bytesToDWORD.
sbazooka.
have H0':= (nextIsInc H0).
have H1':= (nextIsInc H1).
have H2':= (nextIsInc H2).
subst. reflexivity.


sdestruct => q.
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b0'.
case E: (next p) => [p' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b1'.
case E': (next p') => [p'' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b2'.
case E'': (next p'') => [p''' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b3'.
rewrite interpReader_retn.
rewrite -> seqPointsToNil.
rewrite /bytesToDWORD.
sdestructs => H1 H2. ssimpl.
destruct (catB_inj (n1:=8) (n2:=24) H2) as [H2a H2'].
destruct (catB_inj (n1:=8) (n2:=16) H2') as [H2b H2''].
destruct (catB_inj (n1:=8) (n2:=8) H2'') as [H2c H2d].
subst. by ssimpl.

rewrite interpReader_bindBYTE_top. by ssimpl.
rewrite interpReader_bindBYTE_top. by ssimpl.
rewrite interpReader_bindBYTE_top. by ssimpl.
Qed.
*)

Corollary pointsToDWORD_asBYTES (d: DWORD) (p:ADDR):
  let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
  p :-> [::b0;b1;b2;b3] -|- p :-> d.
Proof.
have SE := @split4eta 8 8 8 8 d.
elim E: (split4 8 8 8 8 d) => [[[b3 b2] b1] b0].
rewrite E in SE. rewrite -SE. apply pointsToDWORD_BYTES.
Qed.

Lemma pointsToWORD_BYTES (p:ADDR) (b0 b1:BYTE):
  p :-> [::b0;b1] -|- p :-> (b1 ## b0).
Proof.
Admitted.
(*rewrite {2}/pointsTo.
rewrite /memIs/readerMemIs/readNext/readWORD.
split => //.

ssplit.

rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE. ssplit.
rewrite cursorPointsTo_consBYTE. sdestructs => p0 H0. rewrite pointsToBYTE_byteIs.
rewrite seqPointsToNil.
rewrite H0. setoid_rewrite interpReader_bindBYTE. ssplit.
setoid_rewrite interpReader_retn.
rewrite /bytesToWORD.
sbazooka.
have H0':= (nextIsInc H0).
subst. reflexivity.


sdestruct => q.
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b0'.
case E: (next p) => [p' |].
rewrite pointsTo_consBYTE pointsToBYTE_byteIs. setoid_rewrite interpReader_bindBYTE.
sdestruct => b1'.
rewrite interpReader_retn.
rewrite -> seqPointsToNil.
rewrite /bytesToWORD.
sdestructs => H1 H2. ssimpl.
destruct (catB_inj (n1:=8) (n2:=8) H2) as [H2c H2d].
subst. by ssimpl.

rewrite interpReader_bindBYTE_top. by ssimpl.
Qed.
*)
Corollary pointsToWORD_asBYTES (d: WORD) (p:ADDR):
  let: (b1,b0) := split2 8 8 d in
  p :-> [::b0;b1] -|- p :-> d.
Proof.
split; rewrite pointsToWORD_BYTES. rewrite {3}(@split2eta 8 8 d); reflexivity. 
rewrite {1}(@split2eta 8 8 d); reflexivity. 
Qed. 




Definition memAny p q := Exists bs: seq BYTE, p -- q :-> bs.

Lemma memAnyEmpty p : empSP |-- memAny p p.
Proof. apply lexistsR  with nil. simpl. sbazooka. Qed.

Lemma memAnyMerge p q r : memAny p q ** memAny q r |-- memAny p r.
Proof.
  rewrite /memAny. sdestructs => s1 s2.

  apply lexistsR with (s1 ++ s2). setoid_rewrite seqMemIsCat.
  rewrite -> pairMemIsPair.
  by apply lexistsR with q.
Qed.

Lemma entails_memAnyNext (p: ADDR) q :
  ltCursor p q -> memAny p q |-- Exists b: BYTE, p :-> b ** memAny (next p) q.
Proof.
  rewrite -leCursor_next.
  move => LT.
  rewrite /memAny. sdestruct => bs.
  destruct bs.
  rewrite -> seqMemIsNil.
  sdestructs => EQ.
  rewrite <- EQ in LT.
  rewrite leCursor_next in LT.
  rewrite /ltCursor in LT.
  rewrite ltB_nat in LT. by rewrite ltnn in LT.

  rewrite -> seqMemIsCons.
  sdestruct => q'. apply lexistsR with b.
  rewrite /pointsTo.
  rewrite -> memIsBYTE_next_entails. sdestructs => ->. sbazooka.
Qed.

Lemma entails_memAnySplit p q r :
  leCursor p q -> leCursor q r -> memAny p r |-- memAny p q ** memAny q r.
Proof.
move/LeCursorP. elim.
  - move=> _. rewrite <-empSPL at 1. ssimpl. apply lexistsR with nil.
    rewrite seqMemIsNil. sbazooka.
  - move => {q} q Hpq Hind Hqr. rewrite leCursor_next in Hqr.
    etransitivity; [apply Hind|]; first exact: leCursor_weaken.
    rewrite ->entails_memAnyNext; last done.
    sdestruct => b. ssimpl.
    rewrite {1}/memAny. sdestructs => s.
    rewrite /memAny. apply lexistsR with (s ++ [:: b]).
    rewrite -> seqMemIsCat. rewrite -> pairMemIsPair.
    apply lexistsR with q. cancel2. rewrite -> seqMemIsCons.
    apply lexistsR with (next q). rewrite -> seqMemIsNil.
    rewrite /pointsTo. sdestruct => q'. rewrite -> memIsBYTE_next_entails.
    sdestructs => ->. sbazooka.
Qed.

Corollary memAnySplit p q r :
  leCursor p q -> leCursor q r -> memAny p r -|- memAny p q ** memAny q r.
Proof. move => H1 H2.
split. by apply entails_memAnySplit. by apply memAnyMerge.
Qed.

Lemma byteIs_entails_memAny (p:ADDR)  b : byteIs p b |-- memAny p (next p).
Proof. rewrite /memAny. apply lexistsR with (b::nil).
simpl. apply lexistsR with (next p). sbazooka.
Qed.

Lemma readerMemIs_entails_memAny R {r: Reader R} : forall p q (v: R),
  p -- q :-> v |-- memAny p q.
Proof. rewrite /memIs/=/readNext.
induction r =>  p q v//=.
+ sdestructs => H ->. apply memAnyEmpty.
+ destruct p => //=. sdestruct => b.
  rewrite -> H. rewrite -> byteIs_entails_memAny.
  by rewrite -> memAnyMerge.
+ destruct p => //=. sdestruct => b.
  rewrite -> IHr. rewrite -> byteIs_entails_memAny.
  by rewrite -> memAnyMerge.
Qed.

Lemma four X (bs: seq X) : size bs = 4 -> exists b1 b2 b3 b4, bs = [::b1;b2;b3;b4].
move => H.
destruct bs => //.
destruct bs => //.
destruct bs => //.
destruct bs => //.
exists x, x0, x1, x2.
destruct bs => //.
Qed.

(*
Lemma memAny_entails_fixedReaderMemIs R {r: Reader R} n : fixedSizeReader r n ->
  forall p q, apart n p q ->
  memAny p q |-- Exists v:R, p :-> v.
Proof.
move => F p q A.
rewrite /memAny. sdestruct => bs.
destruct p => //.
destruct q => //.
rewrite -> (apart_addBn A). setoid_rewrite seqMemIsBYTE_addn.
done. sdestruct => EQ.
destruct (four EQ) as [b0 [b1 [b2 [b3 H]]]]. rewrite H.
apply lexistsR with (b3 ## b2 ## b1 ## b0).
rewrite <- pointsToDWORD_BYTES. rewrite /pointsTo. ssplit.
reflexivity.
Qed.
*)

Lemma memAny_entails_pointsToDWORD (p:ADDR) :
  memAny p (p+#4) |-- Exists d:DWORD, p :-> d.
Proof.
rewrite /memAny. sdestruct => bs.
setoid_rewrite seqMemIsBYTE_addn; last done. sdestruct => EQ.
destruct (four EQ) as [b0 [b1 [b2 [b3 H]]]]. rewrite H.
apply lexistsR with (b3 ## b2 ## b1 ## b0).
rewrite <- pointsToDWORD_BYTES. rewrite /pointsTo. ssplit.
reflexivity.
Qed.

Inductive AnyMemT := AnyMem.


Lemma memAnyLe p q : memAny p q |-- leCursor p q /\\ memAny p q.
Proof. rewrite /memAny. sdestruct => bs. rewrite -> memIsLe. sbazooka. Qed.

Instance AnyMemIs : MemIs AnyMemT.
refine (@Build_MemIs _ (fun p q _ => memAny p q) _).
move => p q _. apply memAnyLe.
Qed.


(* Without this, the Qed check after memAnySplitAdd loops forever. *)
Local Opaque leB.

Corollary memAnySplitAdd (p:ADDR) m1 m2 :
  m1 + m2 < 2 ^ naddrBits ->
  memAny p (p+#(m1+m2)) -|- memAny p (p+#m1) ** memAny (p+#m1) (p+#(m1+m2)).
Proof. move => BOUND.
split.
+ rewrite -> (@memAnyLe). sdestruct => MAL.
apply entails_memAnySplit.
rewrite -{1}(addB0 p). apply (leB_bounded_weaken BOUND) => //. apply leq_addr.
apply (leB_bounded_weaken BOUND) => //. apply leq_addr.

+ apply memAnyMerge.
Qed.


