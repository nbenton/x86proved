(** * Various tactics for dealing with charge logics and separation logics. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.
Require Import x86proved.charge.ilogic x86proved.charge.sepalg x86proved.charge.bilogic x86proved.charge.later x86proved.charge.csetoid.
Require Import Coq.Setoids.Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Generalizable All Variables.

(** TODO(t-jagro): Figure out if this already exists somewhere *)
Lemma lentails_def1  `{@ILogic Frm ILOps'} P Q (H' : forall C, C |-- P -> C |-- Q) : P |-- Q.
Proof.
  rewrite <- H'; reflexivity.
Qed.

Lemma bilpropandR {Frm BILO ILO} `{@BILogic Frm ILO BILO, @ILogic Frm ILO} A (B C : Frm) : A /\\ (B ** C) -|- B ** (A /\\ C).
Proof.
  unfold lpropand.
  split; do [ by rewrite <- bilexistsscL
            | by rewrite <- bilexistsscR ].
Qed.

Lemma bilpropandL {Frm BILO ILO} `{@BILogic Frm ILO BILO, @ILogic Frm ILO} A (B C : Frm) : A /\\ (B ** C) -|- (A /\\ B) ** C.
Proof.
  unfold lpropand.
  setoid_rewrite -> sepSPC.
  apply: bilpropandR.
Qed.
