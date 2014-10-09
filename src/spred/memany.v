(*===========================================================================
    MemAny predicates
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.choice Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.addr.
Require Import x86proved.monad x86proved.reader x86proved.writer x86proved.roundtrip x86proved.spred.core x86proved.spred.stateis x86proved.spred.tactics x86proved.pfun x86proved.cursor x86proved.charge.iltac x86proved.charge.ilogic x86proved.spred.memis x86proved.spred.pointsto.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

Lemma entails_memAnyNext (p: ADDR) (q:ADDRCursor) :
  ltCursor (mkCursor p:ADDRCursor) q -> memAny (mkCursor p) q |-- Exists b: BYTE, mkCursor p :-> b ** memAny (next p) q.
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
  rewrite (*/ADDRtoADDRCursor*) ltB_nat in LT. by rewrite ltnn in LT.

  rewrite -> seqMemIsCons.
  sdestruct => q'. eapply lexistsR. 
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
    apply lexistsR with (mkCursor q). cancel2. (* by unfold ADDRtoADDRCursor. *) rewrite -> seqMemIsCons.
    apply lexistsR with (next q). rewrite -> seqMemIsNil.
    rewrite /pointsTo. sdestruct => q'. sbazooka. rewrite -> memIsBYTE_next_entails.
    sdestructs => ->. sbazooka.
Qed.

Corollary memAnySplit p q r :
  leCursor p q -> leCursor q r -> memAny p r -|- memAny p q ** memAny q r.
Proof. move => H1 H2.
split. by apply entails_memAnySplit. by apply memAnyMerge.
Qed.

Lemma byteIs_entails_memAny (p:ADDR)  b : byteIs p b |-- memAny (mkCursor p) (next p).
Proof. rewrite /memAny. apply lexistsR with (b::nil).
simpl. apply lexistsR with (next p). sbazooka.
Qed.

Lemma readerMemIs_entails_memAny R {r: Reader R} : forall p q (v: R),
  p -- q :-> v |-- memAny p q.
Proof. rewrite /memIs/=/readNext.
induction r =>  p q v//=.
+ sdestructs => H ->. apply memAnyEmpty.
+ destruct p => //=. sdestruct => b.
  rewrite -> H. rewrite -> byteIs_entails_memAny. unfold adSizeToOpSize. 
  ssimpl. by rewrite -> memAnyMerge.
+ destruct p => //=. sdestruct => b.
  rewrite -> IHr. rewrite -> byteIs_entails_memAny.
  unfold adSizeToOpSize. ssimpl. by rewrite -> memAnyMerge.
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
  memAny (mkCursor p) (mkCursor (p+#4)) |-- Exists d:DWORD, mkCursor p :-> d.
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
  memAny (mkCursor p) (mkCursor (p+#(m1+m2))) -|- memAny (mkCursor p) (mkCursor (p+#m1)) ** memAny (p+#m1) (p+#(m1+m2)).
Proof. move => BOUND.
split.
+ rewrite -> (@memAnyLe). sdestruct => MAL.
apply entails_memAnySplit.
rewrite -{1}(addB0 p). apply (leB_bounded_weaken BOUND) => //. apply leq_addr.
apply (leB_bounded_weaken BOUND) => //. apply leq_addr.

+ apply memAnyMerge.
Qed.


