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
  | Registers => fun r => Some (registers s r)
  | Flags => fun f => Some (flags s f)
  | Memory => fun p => Some (memory s p)
  end. 

Coercion toPState : ProcState >-> PState.

Lemma totalProcState (s: ProcState) : isTotalPState s.
Proof. move => f x. destruct f; destruct x => //.  Qed. 

Require Import Coq.Logic.FunctionalExtensionality x86proved.charge.csetoid.
Lemma toPState_inj s1 s2 : toPState s1 === toPState s2 -> s1 = s2. 
Proof. move => H. 
destruct s1 as [s1r s1f s1m]. 
destruct s2 as [s2r s2f s2m].
unfold "===", toPState in H.
simpl in H. 
have E1: s1r = s2r.
extensionality x. specialize (H Registers x). by injection H.  
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
