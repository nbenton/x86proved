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
  n<2^naddrBits -> leB p (p+#n) -> mkCursor p :-> v |-- mkCursor p -- mkCursor (p+#n:ADDR) :-> v.
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

(* Various hacks in here to avoid expensive unification *)
Ltac unifyPT P :=
  match P with
    (* These are surely safe *)
  | (byteIs ?p ?v, byteIs ?p ?w) => unify v w
  | (?p :-> ?v, ?p :-> ?w) => unify v w
  | (@mkCursor ?m ?p :-> ?v, @mkCursor ?n ?p :-> ?w) => unify v w
  | (@mkCursor ?m (@zeroExtend _ _ ?p) :-> ?v, @mkCursor ?m (@zeroExtend _ _ ?p) :-> ?w) => unify v w
  | (@mkCursor ?m ?i -- ?j :-> ?v, @mkCursor ?n ?i -- ?k :-> ?v) => unify j k
    (* These might be overlapping ranges, but typically we don't expect to see this *)
  | (@mkCursor ?m ?i -- ?j :-> ?v, @mkCursor ?n ?i -- ?k :-> ?w) => (unify j k; unify v w)
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

Hint Unfold adSizeToOpSize : ssimpl.
Ltac ssimpl := ssimpl_with unifyPT.
Ltac sbazooka := sbazooka_with unifyPT.


(* In fact p :-> b for b:BYTE is just a long-winded way of saying byteIs p b *)
Lemma pointsToBYTE_byteIs (p:ADDR) b : mkCursor p :-> b -|- byteIs p b.
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

Lemma memIs_consBYTE (p:ADDR) q (b:BYTE) bs : mkCursor p -- q :-> (b::bs) -|- mkCursor p :-> b ** (next p) -- q :-> bs.
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

Lemma pointsTo_consBYTE (p:ADDR) (b:BYTE) bs : mkCursor p :-> (b::bs) -|- mkCursor p :-> b ** (next p) :-> bs.
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
  p :-> (b::bs) -|- Exists p':ADDR, (p = mkCursor p' /\\ mkCursor p' :-> b ** (next p') :-> bs).
Proof.
elim p => [p' |]. rewrite pointsTo_consBYTE. split.  apply lexistsR with p'. unfold adSizeToOpSize. sbazooka.
sdestructs => p0 [->]. unfold adSizeToOpSize. by sbazooka.
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
  mkCursor p :-> [::b0;b1;b2;b3] -|- mkCursor p :-> (b3 ## b2 ## b1 ## b0).
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
  mkCursor p :-> [::b0;b1;b2;b3] -|- mkCursor p :-> d.
Proof.
have SE := @split4eta 8 8 8 8 d.
elim E: (split4 8 8 8 8 d) => [[[b3 b2] b1] b0].
rewrite E in SE. rewrite -SE. apply pointsToDWORD_BYTES.
Qed.

Lemma pointsToWORD_BYTES (p:ADDR) (b0 b1:BYTE):
  mkCursor p :-> [::b0;b1] -|- mkCursor p :-> (b1 ## b0).
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
  mkCursor p :-> [::b0;b1] -|- mkCursor p :-> d.
Proof.
split; rewrite pointsToWORD_BYTES. rewrite {3}(@split2eta 8 8 d); reflexivity. 
rewrite {1}(@split2eta 8 8 d); reflexivity. 
Qed. 

Lemma pointsToQWORD_BYTES (p:ADDR) (b0 b1 b2 b3 b4 b5 b6 b7:BYTE):
  mkCursor p :-> [::b0;b1;b2;b3;b4;b5;b6;b7] -|- mkCursor p :-> (b7 ## b6 ## b5 ## b4 ## b3 ## b2 ## b1 ## b0).
Proof. Admitted.




