(*===========================================================================
    "safe" predicate
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.tuple Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.bitsrep x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.spred x86proved.spredtotal x86proved.septac x86proved.spec.
Require Import x86proved.x86.ioaction x86proved.x86.step x86proved.charge.bilogic x86proved.charge.csetoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Obligation Tactic := idtac.

Program Definition safe :=
  mkspec (fun k P => forall (s: ProcState), (P ** ltrue) s -> runsFor k s) _ _.
Next Obligation. move=> k P Hsafe s Hs. by apply: runsForLe (Hsafe _ _). Qed.
Next Obligation. move=> k P P' [R HR] Hsafe s Hs.
  apply Hsafe.
  rewrite ->lentails_eq in Hs. rewrite <-HR in Hs.
  apply lentails_eq. rewrite ->Hs. by ssimpl.
Qed.

Local Transparent ILFun_Ops ILPre_Ops lentails.

Lemma safeAtState (s: ProcState):
  |-- safe @ eq_pred s <-> runsForever s.
Proof.
split => H.
+ move => k. apply (H k empSP I). apply lentails_eq. by ssimpl.
+ move => k R _ s' H0. apply eq_pred_aux2 in H0. by subst.
Qed.

Lemma runsTo_safeClosed s s':
  runsTo s s' ->
  |-- safe @ eq_pred s' ->
  |-- safe @ eq_pred s.
Proof. rewrite 2!safeAtState. by apply runsTo_runsForever. Qed.

Instance AtEx_safe: AtEx safe.
Proof.
  move=> A f. move=> k P Hf. move=> s Hs.
  sdestruct: Hs => a Hs.
  apply: Hf; eassumption.
Qed.

Instance AtContra_safe: AtContra safe.
Proof.
  move=> R R' HR. move=> k P HP. move=> s Hs.
  apply HP. rewrite lentails_eq. rewrite <-HR. by rewrite -lentails_eq.
Qed.

Lemma safe_safe_context P P' R' R S S' S'':
  S'' |-- (S' -->> safe @ P') @ R' ->
  S |-- S'' ->
  (* The order of separating conjuncts in the following premise is crucial for
     allowing ssimpl to solve it in practice. *)
  P |-- P' ** R' ** R ->
  S |-- S' @ (R' ** R) ->
  S |-- safe @ P.
Proof.
  move=> HS' HS'' HP HS. rewrite ->HP.
  lforwardR HS'.
  - etransitivity; [apply (spec_frame R)|]. autorewrite with push_at. done.
  apply landAdj in HS'. lforwardL HS'.
  - apply landR; last apply HS. apply HS''.
  apply HS'.
Qed.

Lemma safe_safe P P' R' R S S':
  |-- (S' -->> safe @ P') @ R' ->
  (* The order of separating conjuncts in the following premise is crucial for
     allowing ssimpl to solve it in practice. *)
  P |-- P' ** R' ** R ->
  S |-- S' @ (R' ** R) ->
  S |-- safe @ P.
Proof. move=> HS' HP HS. eapply safe_safe_context; try eassumption. done. Qed.

Lemma safe_safe_pre P P' R' R S S' S0 S0':
  S0' |-- (S' -->> safe @ P') @ R' ->
  S0 |-- S0' ->
  (* The order of separating conjuncts in the following premise is crucial for
     allowing ssimpl to solve it in practice. *)
  P |-- P' ** R' ** R ->
  S0 |-- S -->> S' @ (R' ** R) ->
  S0 |-- S -->> safe @ P.
Proof. move=> HS0' HS' HP HS. apply limplAdj. eapply safe_safe_context; try eassumption. by apply landL1. 
apply landAdj. assumption. Qed.

Lemma runsTo_safe s s':
  runsTo s s' ->
  safe @ eq_pred s' |-- safe @ eq_pred s.
Proof. move => RED k0 R /=H s0 H0.
have H1 := eq_pred_aux s' H0.
rewrite -(eq_pred_aux2 H0).
apply: runsTo_runsFor RED (H _ H1).
Qed.

Local Transparent ILLaterPreOps.
Lemma properRunsTo_safe s s':
  properRunsTo s s' ->
  |> safe @ eq_pred s' |-- safe @ eq_pred s.
Proof. move => RED k0 R /=H s0 H0.
have H1 := eq_pred_aux s' H0.
rewrite -(eq_pred_aux2 H0).
destruct k0.
- by apply: runsFor0.
- by apply: properRunsTo_runsFor RED (H k0 _ _ H1).
Qed.
