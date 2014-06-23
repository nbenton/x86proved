(*===========================================================================
   Embedding of total states (ProcState) into partial states (PState)
   and associate lemmas regarding SPreds
  ===========================================================================*)
Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple seq fintype.
Require Import bitsrep bitsprops bitsops bitsopsprops procstate procstatemonad pmapprops.
Require Import monad monadinst reader SPred septac pointsto pfun cursor writer.

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

Require Import FunctionalExtensionality CSetoid.
Lemma toPState_inj s1 s2 : toPState s1 === toPState s2 -> s1 = s2. 
Proof. move => H. 
destruct s1 as [s1r s1f s1m]. 
destruct s2 as [s2r s2f s2m].
unfold "===", toPState in H.
simpl in H. 
Admitted.

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

