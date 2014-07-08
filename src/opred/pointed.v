(** * Inhabitation (pointedness) of predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.pointed x86proved.ilogic_pointed x86proved.opred.core.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.
Set Implicit Arguments.

Notation IsPointed_OPred P := (IsPointed (exists x : Actions, (P : OPred) x)).
Notation point_OPred P := (@point _ (_ : IsPointed_OPred P)).

Lemma inhabitedOP (O: OPred) : exists s, O s.
Proof. by destruct O. Qed.
