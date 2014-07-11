(** * Morphisms for predicates over observations. *)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.fintype Ssreflect.finfun Ssreflect.seq Ssreflect.tuple.
Require Import x86proved.bitsrep x86proved.x86.ioaction.
Require Import x86proved.opred.core.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.
Require Import common_tactics.

Generalizable All Variables.
Set Implicit Arguments.

Local Transparent ILFun_Ops ILPre_Ops.

Local Ltac t :=
  do ![ move => ?
      | progress destruct_head_hnf ex
      | progress destruct_head_hnf and
      | progress destruct_head_hnf or
      | progress subst
      | esplit
      | by hyp_apply *
      | by left; hyp_apply *
      | by right; hyp_apply * ].

Add Parametric Morphism : catOP with signature lentails ==> lentails ==> lentails as catOP_entails_m.
Proof. t. Qed.

Add Parametric Morphism : catOP with signature lequiv ==> lequiv ==> lequiv as catOP_equiv_m.
Proof. t. Qed.
