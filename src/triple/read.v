Require Import x86proved.triple.core.
Import triple.core.tripleconfig.

Require Import x86proved.reader (* for [Reader] *) x86proved.spred (* for [interpReader] *) x86proved.pfun (* for [includedIn] *) x86proved.cursor (* for [next] *).

Import Prenex Implicits.

(** This is the crucial lemma that relates the *logical*
    interpretation of a reader (interpReader) with the *operational*
    interpretation of a reader (readMem) *)
Lemma readMemMemIs R (rt: Reader R) : forall p q (v:R) s s',
  interpReader rt p q v s ->
  stateIncludedIn s (toPState s') ->
  readMem rt s' p = readerOk v q.
Proof.
induction rt => p q v s s' H1 H2/=.
(* readerRetn *)
destruct H1 as [H3 [H4 H5]]. by subst.
(* readerNext *)
simpl in H1.
case E: p => [pp |]. subst.
destruct H1 as [b [s1 [s2 [H5 [H6 H7]]]]].
rewrite /byteIs in H6.
rewrite /addBYTEToPState/emptyPState/= in H6.

destruct (stateSplitsAsIncludes H5) as [H8 H9].
have H10 := stateIncludedIn_trans H9 H2.
rewrite <- H6 in H8.
rewrite /includedIn/= in H8.  specialize (H8 Memory pp (Some b)).
rewrite /=eq_refl in H8. specialize (H8 (refl_equal _)).
rewrite /stateIncludedIn in H2.
specialize (H2 Memory pp _ H8).
inversion H2.
rewrite H1.
specialize (H b (next pp) q v s2).
apply (H _ H7 H10).

by subst.

(* readerSkip *)
simpl in H1.
case E: p => [pp |]. subst.
destruct H1 as [b [s1 [s2 [H5 [H6 H7]]]]].
rewrite /byteIs in H6.
rewrite /addBYTEToPState/emptyPState/= in H6.

destruct (stateSplitsAsIncludes H5) as [H8 H9].
have H10 := stateIncludedIn_trans H9 H2.
rewrite <- H6 in H8.
rewrite /includedIn/= in H8.  specialize (H8 Memory pp (Some b)).
rewrite /=eq_refl in H8. specialize (H8 (refl_equal _)).
rewrite /stateIncludedIn in H2.
specialize (H2 Memory pp _ H8).
inversion H2.
rewrite H0.
specialize (IHrt (next pp) q v s2).
apply (IHrt _ H7 H10).

by subst.

(* readerCursor *)
rewrite /interpReader-/interpReader in H1.
apply: H => //. assumption.
Qed.

Corollary pointsto_read R {r: Reader R} p q (v:R) s s' :
  (p -- q :-> v) s ->
  stateIncludedIn s (toPState s') ->
  readMem readNext s' p = readerOk v q.
Proof. apply readMemMemIs. Qed.
