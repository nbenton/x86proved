(*===========================================================================
   Embedding of total states (ProcState) into partial states (PState)
   and associate lemmas regarding SPreds
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.bitsprops x86proved.bitsops x86proved.bitsopsprops x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.pmapprops.
Require Import x86proved.monad x86proved.monadinst x86proved.reader x86proved.spred x86proved.septac x86proved.pointsto x86proved.pfun x86proved.cursor x86proved.writer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Transparent ILFun_Ops.

(* A full machine state can be interpreted as a partial state *)
Definition toPState (s:ProcState) : PState :=
  fun f:Frag =>
  match f return fragDom f -> option (fragTgt f) with
  | Registers => fun rp => let: AnyRegPiece r ix := rp in Some (getRegPiece (registers s r) ix)
  | Flags => fun f => Some (flags s f)
  | Memory => fun p => Some (memory s p)
  end.

Coercion toPState : ProcState >-> PState.

Lemma totalProcState (s: ProcState) : isTotalPState s.
Proof. move => f x. destruct f; destruct x => //.  Qed.

Require Import Coq.Logic.FunctionalExtensionality x86proved.charge.csetoid.

Corollary sliceEqSome n1 n2 n3 (p q: BITS (n1+n2+n3)) : 
  Some (slice n1 n2 n3 p) = Some (slice n1 n2 n3 q) ->
  (forall i, n1 <= i < n1+n2 -> getBit p i = getBit q i).
Proof. move => [H]. by apply sliceEq. Qed. 

Lemma toPState_inj s1 s2 : toPState s1 === toPState s2 -> s1 = s2.
Proof. move => H.
destruct s1 as [s1r s1f s1m].
destruct s2 as [s2r s2f s2m].
unfold "===", toPState in H.
simpl in H.
have E1: s1r = s2r. extensionality x. 
have H0 := H Registers (AnyRegPiece x #0).
have H1 := H Registers (AnyRegPiece x #1).
have H2 := H Registers (AnyRegPiece x #2).
have H3 := H Registers (AnyRegPiece x #3).
clear H.
rewrite /getRegPiece eq_refl in H0. 
rewrite /getRegPiece eq_refl in H1. replace (#1 == #0) with false in H1 by done. 
rewrite /getRegPiece eq_refl in H2. 
replace (#2 == #1) with false in H2 by done. replace (#2 == #0) with false in H2 by done. 
rewrite /getRegPiece in H3. 
replace (#3 == #0) with false in H3 by done. 
replace (#3 == #1) with false in H3 by done. 
replace (#3 == #2) with false in H3 by done.
have S0 := sliceEqSome H0. 
have S1 := sliceEqSome H1. 
have S2 := sliceEqSome H2. 
have S3 := sliceEqSome H3.
apply allBitsEq. 
move => i LT. 
case LT8: (i < n8). apply (S0 _ LT8). 
case LT16: (i < n16). apply S1. by rewrite LT16 leqNgt LT8. 
case LT24: (i < n24). apply S2. by rewrite LT24 leqNgt LT16. 
apply S3. by rewrite LT leqNgt LT24. 

have E2: s1f = s2f.
extensionality x. specialize (H Flags x). by injection H.
have E3: s1m = s2m.
apply extensional_PMAP => x. specialize (H Memory x). by injection H.
by rewrite E1 E2 E3.
Qed.

Lemma eqPredProcState_sepSP (s: ProcState) R :
  eq_pred s ** R |-- eq_pred s.
Proof. rewrite (eqPredTotal_sepSP_trueR _); last by apply totalProcState. by ssimpl. Qed.

Definition isClosed (P: SPred) :=
  forall s s', stateIncludedIn s s' -> P s -> P s'.

Lemma isClosed_sepSP_ltrue P:
  isClosed P -> P ** ltrue -|- P.
Proof.
  move=> HClosed. split.
  - move=> s [s1 [s2 [Hs [HPs _]]]]. eapply HClosed; [|eassumption].
    edestruct stateSplitsAsIncludes; [eapply Hs | assumption].
  - rewrite <-empSPR at 1. cancel2.
Qed.

Lemma eq_pred_aux (s1 s2 s3: ProcState) R :
  ((eq_pred s1 ** R) ** ltrue) s2 ->
  ((eq_pred s3 ** R) ** ltrue) s3.
Proof. move => H0.
apply lentails_eq. ssimpl.
apply lentails_eq in H0.
rewrite -> sepSPC in H0. rewrite <-sepSPA in H0. rewrite ->(sepSPC ltrue) in H0.
rewrite <- (eqPredTotal_sepSP_trueR) in H0; last by apply totalProcState.
apply eqPredTotal_sepSP in H0; last by apply totalProcState.
rewrite -> H0. by ssimpl.
Qed.

Lemma eq_pred_aux2 (s1 s2: ProcState) R :
  ((eq_pred s1 ** R) ** ltrue) s2 -> s1 = s2.
Proof. move => H0.
apply lentails_eq in H0. rewrite -> sepSPA in H0.
  rewrite -> eqPredProcState_sepSP in H0.
  apply lentails_eq in H0. simpl in H0. by apply toPState_inj in H0.
Qed.
