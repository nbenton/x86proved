(*===========================================================================
  Auxiliary lemmas for Hoare triples on *programs*
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import x86proved.x86.procstate x86proved.x86.procstatemonad x86proved.bitsops x86proved.bitsprops x86proved.bitsopsprops.
Require Import x86proved.SPred x86proved.OPred x86proved.septac x86proved.spec x86proved.spectac x86proved.obs x86proved.pointsto x86proved.cursor x86proved.x86.instr x86proved.reader x86proved.x86.instrcodec.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import x86proved.x86.program x86proved.x86.basic x86proved.charge.ilogic.

(* Morphism for program equivalence *)
Global Instance basic_progEq_m:
Proper (lequiv ==> progEq ==> equivOP ==> lequiv ==> lequiv) basic.
  Proof.
    move => P P' HP c c' Hc O O' HO Q Q' HQ. split. 
    setoid_rewrite -> HQ. setoid_rewrite HP. setoid_rewrite HO. 
    unfold basic. by setoid_rewrite Hc. 
    setoid_rewrite <- HQ. setoid_rewrite <- HP. setoid_rewrite <- HO. 
    unfold basic. by setoid_rewrite <-Hc. 
  Qed.

(* Skip rule *)
Lemma basic_skip P: |-- basic P prog_skip empOP P.
Proof.
  rewrite /basic. specintros => i j O'. unfold_program.
  specintro => ->. 
  rewrite -> empOPL. rewrite emp_unit spec_reads_eq_at; rewrite <- emp_unit.
  rewrite spec_at_emp. by apply limplValid. 
Qed.

(* Sequencing rule *)
Lemma basic_seq (c1 c2: program) S P O1 Q O2 R O:
  entailsOP (catOP O1 O2) O ->
  S |-- basic P c1 O1 Q ->
  S |-- basic Q c2 O2 R ->
  S |-- basic P (c1;; c2) O R.
Proof.
  rewrite /basic. move=> HO Hc1 Hc2. specintros => i j O'. unfold_program.
  specintro => i'. rewrite -> memIsNonTop. specintros => p' EQ. subst. 
  rewrite <- HO. rewrite -> catOPA. 
  specapply Hc1. by ssimpl. 
  specapply Hc2. by ssimpl. 
  rewrite <-spec_reads_frame. apply: limplAdj. apply: landL2.
  by rewrite spec_at_emp.
Qed.
 
(* Scoped label rule *)
Lemma basic_local S P c O Q:
  (forall l, S |-- basic P (c l) O Q) ->
  S |-- basic P (prog_declabel c) O Q.
Proof.
  move=> H. rewrite /basic. rewrite /memIs /=. specintros => i j O' l.
  specialize (H l). lforwardR H.
  - apply lforallL with i. apply lforallL with j. apply lforallL with O'. reflexivity.
  apply H.
Qed.

(* Needed to avoid problems with coercions *)
Lemma basic_instr S P i O Q :
  S |-- basic P i O Q ->
  S |-- basic P (prog_instr i) O Q.
Proof. done. Qed.

(* Attempts to apply "basic" lemma on a single command (basic_basic) or
   on the first of a sequence (basic_seq). Note that it attempts to use sbazooka
   to discharge subgoals, so be careful if existentials are exposed in the goal --
   they will be instantiated! *)
  Hint Unfold not : basicapply.
  Hint Rewrite eq_refl : basicapply.
  Ltac instRule R H :=
    move: (R) => H;
    repeat (autounfold with basicapply in H);
    eforalls H;
    autorewrite with push_at in H.


  (* This is all very sensitive to use of "e" versions of apply/exact. Beware! *)
  (* We ensure that we leave at most one goal remaining. *)
  Ltac basicatom R tacfin :=
  lazymatch goal with
    | |- |-- basic ?P (prog_instr ?i) ?O ?Q =>
          (eapply basic_basic; first eapply basic_instr; [ eexact R | tacfin .. | try tacfin ])

    | _ => eapply basic_basic; [ eexact R | tacfin .. | try tacfin ]
    end.

  Ltac  basicseq R tacfin :=
  lazymatch goal with
    | |- |-- basic ?P (prog_seq ?p1 ?p2) ?O ?Q => (eapply basic_seq; [ try done | basicatom R tacfin |])
    | _ => basicatom R tacfin
    end.

  Ltac basicapply R tac tacfin :=
    let Hlem := fresh "Hlem" in
    instRule R Hlem;
    tac Hlem;
    first basicseq Hlem tacfin;
    clear Hlem.

  Tactic Notation "basicapply" open_constr(R) "using" tactic3(tac) "side" "conditions" tactic(tacfin) := basicapply R tac tacfin.
  Tactic Notation "basicapply" open_constr(R) "using" tactic3(tac) := basicapply R using (tac) side conditions by autounfold with spred; sbazooka.
  Tactic Notation "basicapply" open_constr(R) "side" "conditions" tactic(tacfin) := basicapply R using (fun Hlem => autorewrite with basicapply in Hlem) side conditions tacfin.
  Tactic Notation "basicapply" open_constr(R) := basicapply R using (fun Hlem => autorewrite with basicapply in Hlem).
  (** Variant of [basicapply] that doesn't require that the side conditions be fully solved. *)
  Tactic Notation "try_basicapply" open_constr(R) "using" tactic3(tac) := basicapply R using (tac) side conditions autounfold with spred; sbazooka.
  Tactic Notation "try_basicapply" open_constr(R) := try_basicapply R using (fun Hlem => autorewrite with basicapply in Hlem).
