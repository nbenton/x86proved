(** * Inhabitation (pointedness) of predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.pointed x86proved.ilogic_pointed x86proved.opred.core.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.

Notation IsPointed_OPred P := (IsPointed (exists x : Actions, (P : OPred) x)).
Notation point_OPred P := (@point _ (_ : IsPointed_OPred P)).

(* We require predicates on observations to be non-empty i.e. for there to be
   some sequence of actions for which it holds *)
Record PointedOPred := mkPointedOPred {
  OPred_pred :> OPred;
  OPred_inhabited: IsPointed_OPred OPred_pred
}.

Existing Instance OPred_inhabited.

Canonical default_PointedOPred O `{IsPointed_OPred O} : PointedOPred
  := {| OPred_pred := O ; OPred_inhabited := _ |}.

Arguments mkPointedOPred : clear implicits.

Lemma inhabitedOP (O: PointedOPred) : exists s, O s.
Proof. by destruct O. Qed.

Instance IsPointed_Actions : IsPointed Actions := nil.
Instance IsPointed_eq_opred x : IsPointed_OPred (eq_opred x) := ex_intro _ x (reflexivity _).
Instance IsPointed_empOP : IsPointed_OPred empOP := _.
Instance IsPointed_outOP c d : IsPointed_OPred (outOP c d) := _.
Instance IsPointed_catOP `{IsPointed_OPred P, IsPointed_OPred Q} : IsPointed_OPred (catOP P Q).
Proof.
  hnf.
  destruct (point_OPred P), (point_OPred Q).
  eexists (_ ++ _), _, _.
  do !esplit; eassumption.
Qed.
Instance IsPointed_repOP0 P : IsPointed_OPred (repOP 0 P) | 0 := _.
Instance IsPointed_rollOP0 f : IsPointed_OPred (rollOP 0 f) | 0 := _.
Instance IsPointed_partial_rollOP0 f start : IsPointed_OPred (partial_rollOP f start 0) | 0 := _.
Instance IsPointed_repOP n `{IsPointed_OPred P} : IsPointed_OPred (repOP n P).
Proof.
  induction n; typeclasses eauto.
Qed.
Instance IsPointed_rollOP n f `{forall n, IsPointed_OPred (f (S n))} : IsPointed_OPred (rollOP n f).
Proof.
  induction n; typeclasses eauto.
Qed.
Instance IsPointed_partial_rollOP f count `{forall n, IsPointed_OPred (f n)} : forall start, IsPointed_OPred (partial_rollOP f start count).
Proof.
  induction count; typeclasses eauto.
Qed.

Instance IsPointed_ltrueOP : IsPointed_OPred ltrue := _.
Instance IsPointed_lexistsOP {T P} `{IsPointed T, IsPointed_OPred (P (point T))} : IsPointed_OPred (lexists P).
Proof.
  hnf.
  destruct (point_OPred (P (point T))).
  do 2 esplit; eassumption.
Qed.
Instance IsPointed_lorLOP {P Q} `{IsPointed_OPred P} : IsPointed_OPred (P \\// Q).
Proof.
  hnf.
  destruct (point_OPred P).
  esplit; left; eassumption.
Qed.
Instance IsPointed_lorROP {P Q} `{IsPointed_OPred Q} : IsPointed_OPred (P \\// Q).
Proof.
  hnf.
  destruct (point_OPred Q).
  esplit; right; eassumption.
Qed.
Instance IsPointed_limplOP {P Q} `{IsPointed_OPred Q} : IsPointed_OPred (P -->> Q).
Proof.
  hnf.
  destruct (point_OPred Q).
  esplit.
  setoid_rewrite <- (@limplAdj _ _ _ _ _ ltrue); first by exact I.
  move => ?; eassumption.
Qed.

Instance IsPointed_starOP P : IsPointed_OPred (starOP P) := let _ := 0 : IsPointed nat in IsPointed_lexistsOP.
Instance IsPointed_roll_starOP f start : IsPointed_OPred (roll_starOP f start) := let _ := 0 : IsPointed nat in IsPointed_lexistsOP.

(** Common case *)
Instance IsPointed_lorLempOP {Q} : IsPointed_OPred (empOP \\// Q) := _.
Instance IsPointed_lorRempOP {P} : IsPointed_OPred (P \\// empOP) := _.
