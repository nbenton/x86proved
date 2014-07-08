(** * Morphisms for predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.opred.core.
Require Import x86proved.charge.csetoid.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Program.Basics.
Require Import common_tactics.

Generalizable All Variables.
Set Implicit Arguments.

Local Transparent ILFun_Ops ILPre_Ops.

Instance equivOPEquiv : Equiv OPred := equivOP.

Instance entailsOPpre : PreOrder entailsOP.
Proof. constructor; hnf. move => P s. intuition.
move => P Q R H1 H2 s. intuition. Qed.


Instance equivOP_entailOP : subrelation equivOP entailsOP.
Proof. firstorder. Qed.

Instance equivOP_inverse_entailsOP: subrelation equivOP (inverse entailsOP).
Proof. firstorder. Qed.

Instance equivOP_entailsOP_m : Proper (equivOP ==> equivOP ==> iff) entailsOP.
Proof. move => P P' HP Q Q' QP. split => H s H'; firstorder. Qed.

Instance entailsOP_entailsOP_m: Proper (entailsOP --> entailsOP ++> impl) entailsOP.
Proof. move => P P' HP Q Q' QP H s H'. intuition. Qed.

(* Morphisms for operators *)
Instance catOP_entails_m: Proper (entailsOP ==> entailsOP ==> entailsOP) catOP.
Proof.
move => O1 O1' HO1 O2 O2' HO2. move => s/= H.
destruct H as [o1 [o2 [H1 [H2 H3]]]]. subst.
exists o1, o2. split => //. split. by apply HO1. by apply HO2.
Qed.

Instance catOP_equiv_m: Proper (equivOP ==> equivOP ==> equivOP) catOP.
Proof. move => P P' HP Q Q' HQ. split; apply catOP_entails_m; (apply HP || apply HQ). Qed.
